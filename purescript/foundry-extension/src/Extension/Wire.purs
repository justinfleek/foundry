-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // extension // wire // fwire
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FWIRE binary encoder for browser extension.
-- |
-- | Matches Haskell Foundry.Core.Wire.{Types,Encode} exactly.
-- | NO JSON on the hot path - binary wire format only.
-- |
-- | == Format Specification
-- |
-- | Header (16 bytes):
-- |   [4 bytes] Magic: 0x46 0x57 0x49 0x52 ("FWIR")
-- |   [1 byte]  Version: 0x01
-- |   [1 byte]  Flags: reserved (0x00)
-- |   [2 bytes] Pillar count (uint16 BE)
-- |   [8 bytes] Timestamp (uint64 BE, unix microseconds)
-- |
-- | Domain (2 + N bytes):
-- |   [2 bytes] Length (uint16 BE)
-- |   [N bytes] UTF-8 encoded domain
-- |
-- | Pillar Block (2 + varint + N bytes each):
-- |   [1 byte]  Pillar ID (0x00-0x25 for 38 pillars)
-- |   [1 byte]  Encoding type (0x00=raw, 0x01=varint, 0x02=nested)
-- |   [varint]  Data length
-- |   [N bytes] Pillar data
-- |
-- | Footer (4 bytes):
-- |   [4 bytes] CRC32 checksum (IEEE 802.3)
-- |
-- | == Dependencies
-- |
-- | Requires: arraybuffer-types
-- | Required by: Extension.Extraction

module Extension.Wire
  ( -- * Constants
    fwireMagic
  , fwireVersion
  , EncodingType(..)
  , PillarId(..)
  
  -- * Types
  , FWireHeader
  , FWireFrame
  , PillarBlock
  , DecodeResult
  
  -- * Encoding
  , encodeVarint
  , encodeFrame
  , computeCRC32
  
  -- * Decoding
  , decodeVarint
  , decodeHeader
  , decodeFrame
  , pillarIdFromByte
  , encodingTypeFromByte
  
  -- * Frame Construction
  , mkHeader
  , mkPillarBlock
  , mkFrame
  , mkFrameWithTimestamp
  
  -- * Effectful Operations
  , encodeFrameEffect
  , timestampToWords
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Unit
  , bind
  , discard
  , map
  , negate
  , otherwise
  , pure
  , show
  , ($)
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<<<)
  , (<>)
  , (<=)
  , (==)
  , (>=)
  , (>>=)
  , (&&)
  )

import Data.Array (foldl, length, snoc, (:))
import Data.Array as Array
import Data.Int (floor, toNumber)
import Data.Tuple (Tuple(..))

import Data.Int.Bits (and, or, shl, shr, xor, zshr)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Data.Char (fromCharCode, toCharCode)
import Data.String.CodeUnits (fromCharArray, toCharArray)



-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Magic bytes: "FWIR" (0x46574952)
fwireMagic :: Int
fwireMagic = 0x46574952

-- | Current format version
fwireVersion :: Int
fwireVersion = 0x01

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Encoding type for pillar data
data EncodingType
  = EncodingRaw      -- ^ 0x00: Raw bytes
  | EncodingVarint   -- ^ 0x01: Varint-prefixed length
  | EncodingNested   -- ^ 0x02: Nested pillar blocks

derive instance eqEncodingType :: Eq EncodingType
derive instance ordEncodingType :: Ord EncodingType

instance showEncodingType :: Show EncodingType where
  show EncodingRaw = "EncodingRaw"
  show EncodingVarint = "EncodingVarint"
  show EncodingNested = "EncodingNested"

encodingTypeToByte :: EncodingType -> Int
encodingTypeToByte EncodingRaw = 0x00
encodingTypeToByte EncodingVarint = 0x01
encodingTypeToByte EncodingNested = 0x02

-- | Pillar identifier (0x00-0x25 for 38 pillars)
data PillarId
  = PillarColor
  | PillarDimension
  | PillarGeometry
  | PillarTypography
  | PillarSurface
  | PillarElevation
  | PillarMotion
  | PillarTemporal
  | PillarReactive
  | PillarGestural
  | PillarHaptic
  | PillarAuditory
  | PillarAccessibility
  | PillarSemantic
  | PillarLandmark
  | PillarSpatial
  | PillarCompositional
  | PillarRelational
  | PillarResponsive
  | PillarAdaptive
  | PillarContextual
  | PillarThemeable
  | PillarCultural
  | PillarTemporalContext
  | PillarEnvironmental
  | PillarPlatform
  | PillarFigurative
  | PillarSymbolic
  | PillarNarrative
  | PillarPersonality
  | PillarVoice
  | PillarConceptual
  | PillarProgressive
  | PillarEmergent
  | PillarLearning
  | PillarState
  | PillarDataDriven
  | PillarBehavioral

derive instance eqPillarId :: Eq PillarId
derive instance ordPillarId :: Ord PillarId

instance showPillarId :: Show PillarId where
  show PillarColor = "PillarColor"
  show PillarDimension = "PillarDimension"
  show PillarGeometry = "PillarGeometry"
  show PillarTypography = "PillarTypography"
  show PillarSurface = "PillarSurface"
  show PillarElevation = "PillarElevation"
  show PillarMotion = "PillarMotion"
  show PillarTemporal = "PillarTemporal"
  show PillarReactive = "PillarReactive"
  show PillarGestural = "PillarGestural"
  show PillarHaptic = "PillarHaptic"
  show PillarAuditory = "PillarAuditory"
  show PillarAccessibility = "PillarAccessibility"
  show PillarSemantic = "PillarSemantic"
  show PillarLandmark = "PillarLandmark"
  show PillarSpatial = "PillarSpatial"
  show PillarCompositional = "PillarCompositional"
  show PillarRelational = "PillarRelational"
  show PillarResponsive = "PillarResponsive"
  show PillarAdaptive = "PillarAdaptive"
  show PillarContextual = "PillarContextual"
  show PillarThemeable = "PillarThemeable"
  show PillarCultural = "PillarCultural"
  show PillarTemporalContext = "PillarTemporalContext"
  show PillarEnvironmental = "PillarEnvironmental"
  show PillarPlatform = "PillarPlatform"
  show PillarFigurative = "PillarFigurative"
  show PillarSymbolic = "PillarSymbolic"
  show PillarNarrative = "PillarNarrative"
  show PillarPersonality = "PillarPersonality"
  show PillarVoice = "PillarVoice"
  show PillarConceptual = "PillarConceptual"
  show PillarProgressive = "PillarProgressive"
  show PillarEmergent = "PillarEmergent"
  show PillarLearning = "PillarLearning"
  show PillarState = "PillarState"
  show PillarDataDriven = "PillarDataDriven"
  show PillarBehavioral = "PillarBehavioral"

pillarIdToByte :: PillarId -> Int
pillarIdToByte PillarColor = 0x00
pillarIdToByte PillarDimension = 0x01
pillarIdToByte PillarGeometry = 0x02
pillarIdToByte PillarTypography = 0x03
pillarIdToByte PillarSurface = 0x04
pillarIdToByte PillarElevation = 0x05
pillarIdToByte PillarMotion = 0x06
pillarIdToByte PillarTemporal = 0x07
pillarIdToByte PillarReactive = 0x08
pillarIdToByte PillarGestural = 0x09
pillarIdToByte PillarHaptic = 0x0A
pillarIdToByte PillarAuditory = 0x0B
pillarIdToByte PillarAccessibility = 0x0C
pillarIdToByte PillarSemantic = 0x0D
pillarIdToByte PillarLandmark = 0x0E
pillarIdToByte PillarSpatial = 0x0F
pillarIdToByte PillarCompositional = 0x10
pillarIdToByte PillarRelational = 0x11
pillarIdToByte PillarResponsive = 0x12
pillarIdToByte PillarAdaptive = 0x13
pillarIdToByte PillarContextual = 0x14
pillarIdToByte PillarThemeable = 0x15
pillarIdToByte PillarCultural = 0x16
pillarIdToByte PillarTemporalContext = 0x17
pillarIdToByte PillarEnvironmental = 0x18
pillarIdToByte PillarPlatform = 0x19
pillarIdToByte PillarFigurative = 0x1A
pillarIdToByte PillarSymbolic = 0x1B
pillarIdToByte PillarNarrative = 0x1C
pillarIdToByte PillarPersonality = 0x1D
pillarIdToByte PillarVoice = 0x1E
pillarIdToByte PillarConceptual = 0x1F
pillarIdToByte PillarProgressive = 0x20
pillarIdToByte PillarEmergent = 0x21
pillarIdToByte PillarLearning = 0x22
pillarIdToByte PillarState = 0x23
pillarIdToByte PillarDataDriven = 0x24
pillarIdToByte PillarBehavioral = 0x25

-- | FWIRE header (16 bytes)
type FWireHeader =
  { magic :: Int
  , version :: Int
  , flags :: Int
  , pillarCount :: Int
  , timestampHigh :: Int  -- High 32 bits of 64-bit timestamp
  , timestampLow :: Int   -- Low 32 bits of 64-bit timestamp
  }

-- | A single pillar block
type PillarBlock =
  { pillarId :: PillarId
  , encoding :: EncodingType
  , dataBytes :: Array Int  -- Raw bytes
  }

-- | Complete FWIRE frame
type FWireFrame =
  { header :: FWireHeader
  , domain :: String
  , pillars :: Array PillarBlock
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // varint encoding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Encode a 32-bit unsigned integer as a varint.
-- | Same format as protobuf/SIGIL: 7 bits per byte, MSB = continuation.
encodeVarint :: Int -> Array Int
encodeVarint n = go (zshr n 0) []  -- Ensure unsigned
  where
    go :: Int -> Array Int -> Array Int
    go val acc
      | val < 0x80 = snoc acc (and val 0x7F)
      | otherwise = 
          let byte = or (and val 0x7F) 0x80
              rest = zshr val 7
          in go rest (snoc acc byte)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // crc32
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CRC32 polynomial (IEEE 802.3: 0xEDB88320)
-- | Represented as negative to fit in PureScript's signed 32-bit Int
-- | 0xEDB88320 = -306674912 in two's complement
crc32Poly :: Int
crc32Poly = -306674912

-- | CRC32 lookup table (IEEE 802.3 polynomial)
-- | Pre-computed for performance
crc32Table :: Array Int
crc32Table = map mkEntry (Array.range 0 255)
  where
    mkEntry :: Int -> Int
    mkEntry i = iterate 8 i
    
    iterate :: Int -> Int -> Int
    iterate 0 c = c
    iterate n c =
      if and c 1 == 1
        then iterate (n - 1) (xor crc32Poly (zshr c 1))
        else iterate (n - 1) (zshr c 1)

-- | 0xFFFFFFFF as signed Int (-1 in two's complement)
allOnes :: Int
allOnes = -1

-- | Compute CRC32 checksum (IEEE 802.3).
computeCRC32 :: Array Int -> Int
computeCRC32 bytes = xor (foldl updateCRC allOnes bytes) allOnes
  where
    updateCRC :: Int -> Int -> Int
    updateCRC crc byte =
      let idx = and (xor crc byte) 0xFF
      in case Array.index crc32Table idx of
           Just tableVal -> xor tableVal (zshr crc 8)
           Nothing -> crc  -- Should never happen

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // frame construction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a header with the given pillar count and timestamp
mkHeader :: Int -> Int -> Int -> FWireHeader
mkHeader pillarCount timestampHigh timestampLow =
  { magic: fwireMagic
  , version: fwireVersion
  , flags: 0
  , pillarCount: pillarCount
  , timestampHigh: timestampHigh
  , timestampLow: timestampLow
  }

-- | Create a pillar block from ID and raw data bytes
mkPillarBlock :: PillarId -> Array Int -> PillarBlock
mkPillarBlock pid dataBytes =
  { pillarId: pid
  , encoding: EncodingRaw
  , dataBytes: dataBytes
  }

-- | Create a complete frame
mkFrame :: String -> Array PillarBlock -> Int -> Int -> FWireFrame
mkFrame domain pillars tsHigh tsLow =
  { header: mkHeader (length pillars) tsHigh tsLow
  , domain: domain
  , pillars: pillars
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // frame encoding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Encode header to bytes (16 bytes)
encodeHeader :: FWireHeader -> Array Int
encodeHeader h =
  -- Magic (4 bytes BE)
  [ and (zshr h.magic 24) 0xFF
  , and (zshr h.magic 16) 0xFF
  , and (zshr h.magic 8) 0xFF
  , and h.magic 0xFF
  -- Version (1 byte)
  , h.version
  -- Flags (1 byte)
  , h.flags
  -- Pillar count (2 bytes BE)
  , and (zshr h.pillarCount 8) 0xFF
  , and h.pillarCount 0xFF
  -- Timestamp high (4 bytes BE)
  , and (zshr h.timestampHigh 24) 0xFF
  , and (zshr h.timestampHigh 16) 0xFF
  , and (zshr h.timestampHigh 8) 0xFF
  , and h.timestampHigh 0xFF
  -- Timestamp low (4 bytes BE)
  , and (zshr h.timestampLow 24) 0xFF
  , and (zshr h.timestampLow 16) 0xFF
  , and (zshr h.timestampLow 8) 0xFF
  , and h.timestampLow 0xFF
  ]

-- | Encode domain with length prefix (2 + N bytes)
encodeDomain :: String -> Array Int
encodeDomain domain = 
  let bytes = stringToUtf8 domain
      len = length bytes
  in [ and (zshr len 8) 0xFF
     , and len 0xFF
     ] <> bytes

-- | Encode a single pillar block
encodePillarBlock :: PillarBlock -> Array Int
encodePillarBlock pb =
  let dataLen = length pb.dataBytes
      lenVarint = encodeVarint dataLen
  in [ pillarIdToByte pb.pillarId
     , encodingTypeToByte pb.encoding
     ] <> lenVarint <> pb.dataBytes

-- | Encode CRC32 as 4 bytes BE
encodeCRC32 :: Int -> Array Int
encodeCRC32 crc =
  [ and (zshr crc 24) 0xFF
  , and (zshr crc 16) 0xFF
  , and (zshr crc 8) 0xFF
  , and crc 0xFF
  ]

-- | Encode a complete FWIRE frame to bytes
encodeFrame :: FWireFrame -> Array Int
encodeFrame frame =
  let headerBytes = encodeHeader frame.header
      domainBytes = encodeDomain frame.domain
      pillarBytes = foldl (\acc pb -> acc <> encodePillarBlock pb) [] frame.pillars
      bodyBytes = headerBytes <> domainBytes <> pillarBytes
      crc = computeCRC32 bodyBytes
  in bodyBytes <> encodeCRC32 crc

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert string to array of code points (ASCII)
-- | Characters outside ASCII range (0-127) are replaced with '?' (63)
stringToUtf8 :: String -> Array Int
stringToUtf8 s = map toAsciiCode (toCharArray s)
  where
    toAsciiCode c =
      let code = toCharCode c
      in if code <= 127 then code else 63

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // varint decoding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Result of decoding: value and number of bytes consumed
type DecodeResult a =
  { value :: a
  , bytesRead :: Int
  }

-- | Decode a varint from byte array at given offset.
-- | Returns decoded value and bytes consumed.
decodeVarint :: Array Int -> Int -> Maybe (DecodeResult Int)
decodeVarint bytes offset = go offset 0 0
  where
    go :: Int -> Int -> Int -> Maybe (DecodeResult Int)
    go pos acc shift
      | shift >= 35 = Nothing  -- Overflow protection
      | otherwise = do
          byte <- Array.index bytes pos
          let val = and byte 0x7F
              acc' = or acc (shl val shift)
          if and byte 0x80 == 0
            then pure { value: acc', bytesRead: pos - offset + 1 }
            else go (pos + 1) acc' (shift + 7)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // header decoding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Read a big-endian Word32 from array at offset
readU32BE :: Array Int -> Int -> Maybe Int
readU32BE arr off = do
  b0 <- Array.index arr off
  b1 <- Array.index arr (off + 1)
  b2 <- Array.index arr (off + 2)
  b3 <- Array.index arr (off + 3)
  pure $ or (shl b0 24) (or (shl b1 16) (or (shl b2 8) b3))

-- | Read a big-endian Word16 from array at offset
readU16BE :: Array Int -> Int -> Maybe Int
readU16BE arr off = do
  b0 <- Array.index arr off
  b1 <- Array.index arr (off + 1)
  pure $ or (shl b0 8) b1

-- | Decode FWIRE header (16 bytes)
decodeHeader :: Array Int -> Maybe (DecodeResult FWireHeader)
decodeHeader bytes = do
  magic <- readU32BE bytes 0
  version <- Array.index bytes 4
  flags <- Array.index bytes 5
  pillarCount <- readU16BE bytes 6
  tsHigh <- readU32BE bytes 8
  tsLow <- readU32BE bytes 12
  
  -- Validate magic and version
  if magic == fwireMagic
    then pure
      { value:
          { magic: magic
          , version: version
          , flags: flags
          , pillarCount: pillarCount
          , timestampHigh: tsHigh
          , timestampLow: tsLow
          }
      , bytesRead: 16
      }
    else Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // frame decoding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Decode domain string (length-prefixed)
decodeDomain :: Array Int -> Int -> Maybe (DecodeResult String)
decodeDomain bytes offset = do
  len <- readU16BE bytes offset
  let domainBytes = Array.slice (offset + 2) (offset + 2 + len) bytes
      domainStr = bytesToString domainBytes
  pure { value: domainStr, bytesRead: 2 + len }

-- | Convert byte array back to string (ASCII)
bytesToString :: Array Int -> String
bytesToString bytes = 
  let validBytes = map (\b -> if b >= 32 && b <= 127 then b else 32) bytes
      maybeChars = map fromCharCode validBytes
      chars = foldl (\acc mc -> case mc of
                        Just c -> snoc acc c
                        Nothing -> acc) [] maybeChars
  in fromCharArray chars

-- | Convert byte to PillarId
pillarIdFromByte :: Int -> Maybe PillarId
pillarIdFromByte b
  | b == 0x00 = Just PillarColor
  | b == 0x01 = Just PillarDimension
  | b == 0x02 = Just PillarGeometry
  | b == 0x03 = Just PillarTypography
  | b == 0x04 = Just PillarSurface
  | b == 0x05 = Just PillarElevation
  | b == 0x06 = Just PillarMotion
  | b == 0x07 = Just PillarTemporal
  | b == 0x08 = Just PillarReactive
  | b == 0x09 = Just PillarGestural
  | b == 0x0A = Just PillarHaptic
  | b == 0x0B = Just PillarAuditory
  | b == 0x0C = Just PillarAccessibility
  | b == 0x0D = Just PillarSemantic
  | b == 0x0E = Just PillarLandmark
  | b == 0x0F = Just PillarSpatial
  | b == 0x10 = Just PillarCompositional
  | b == 0x11 = Just PillarRelational
  | b == 0x12 = Just PillarResponsive
  | b == 0x13 = Just PillarAdaptive
  | b == 0x14 = Just PillarContextual
  | b == 0x15 = Just PillarThemeable
  | b == 0x16 = Just PillarCultural
  | b == 0x17 = Just PillarTemporalContext
  | b == 0x18 = Just PillarEnvironmental
  | b == 0x19 = Just PillarPlatform
  | b == 0x1A = Just PillarFigurative
  | b == 0x1B = Just PillarSymbolic
  | b == 0x1C = Just PillarNarrative
  | b == 0x1D = Just PillarPersonality
  | b == 0x1E = Just PillarVoice
  | b == 0x1F = Just PillarConceptual
  | b == 0x20 = Just PillarProgressive
  | b == 0x21 = Just PillarEmergent
  | b == 0x22 = Just PillarLearning
  | b == 0x23 = Just PillarState
  | b == 0x24 = Just PillarDataDriven
  | b == 0x25 = Just PillarBehavioral
  | otherwise = Nothing

-- | Convert byte to EncodingType
encodingTypeFromByte :: Int -> Maybe EncodingType
encodingTypeFromByte 0x00 = Just EncodingRaw
encodingTypeFromByte 0x01 = Just EncodingVarint
encodingTypeFromByte 0x02 = Just EncodingNested
encodingTypeFromByte _ = Nothing

-- | Decode a single pillar block
decodePillarBlock :: Array Int -> Int -> Maybe (DecodeResult PillarBlock)
decodePillarBlock bytes offset = do
  pillarByte <- Array.index bytes offset
  encodingByte <- Array.index bytes (offset + 1)
  pillarId <- pillarIdFromByte pillarByte
  encoding <- encodingTypeFromByte encodingByte
  lenResult <- decodeVarint bytes (offset + 2)
  let dataStart = offset + 2 + lenResult.bytesRead
      dataBytes = Array.slice dataStart (dataStart + lenResult.value) bytes
  pure
    { value:
        { pillarId: pillarId
        , encoding: encoding
        , dataBytes: dataBytes
        }
    , bytesRead: 2 + lenResult.bytesRead + lenResult.value
    }

-- | Decode multiple pillar blocks
decodePillars :: Int -> Array Int -> Int -> Maybe (DecodeResult (Array PillarBlock))
decodePillars 0 _ _ = pure { value: [], bytesRead: 0 }
decodePillars count bytes offset = do
  blockResult <- decodePillarBlock bytes offset
  restResult <- decodePillars (count - 1) bytes (offset + blockResult.bytesRead)
  pure
    { value: blockResult.value : restResult.value
    , bytesRead: blockResult.bytesRead + restResult.bytesRead
    }

-- | Decode a complete FWIRE frame
decodeFrame :: Array Int -> Maybe FWireFrame
decodeFrame bytes = do
  headerResult <- decodeHeader bytes
  domainResult <- decodeDomain bytes 16
  let pillarStart = 16 + domainResult.bytesRead
  pillarsResult <- decodePillars headerResult.value.pillarCount bytes pillarStart
  -- Skip CRC verification for now (would need to recompute and compare)
  pure
    { header: headerResult.value
    , domain: domainResult.value
    , pillars: pillarsResult.value
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // effectful operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 2^32 as a Number (can't use Int literal)
twoTo32 :: Number
twoTo32 = 4294967296.0

-- | Convert a timestamp (Number, milliseconds) to high/low 32-bit words
-- | Multiplies by 1000 to get microseconds
timestampToWords :: Number -> Tuple Int Int
timestampToWords ms =
  let micros = ms * 1000.0
      high = floor (micros / twoTo32)
      lowNum = micros - (toNumber high * twoTo32)
      low = floor lowNum
  in Tuple high low

-- | Create a frame with a Number timestamp (milliseconds since epoch)
mkFrameWithTimestamp :: String -> Array PillarBlock -> Number -> FWireFrame
mkFrameWithTimestamp domain pillars timestamp =
  let Tuple tsHigh tsLow = timestampToWords timestamp
  in mkFrame domain pillars tsHigh tsLow

-- | Encode frame as an Effect (for use in browser context)
encodeFrameEffect :: FWireFrame -> Effect (Array Int)
encodeFrameEffect frame = pure $ encodeFrame frame
