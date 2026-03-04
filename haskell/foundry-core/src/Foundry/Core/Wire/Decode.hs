{-# LANGUAGE BangPatterns #-}

{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // foundry // wire // decode
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Wire.Decode
Description : FWIRE binary decoding
Copyright   : (c) Straylight, 2026
License     : MIT

Decodes ByteString to FWireFrame.

== Dependencies

Requires: Foundry.Core.Wire.Types, Foundry.Core.Wire.Varint
Required by: BrandIngestMachine

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Wire.Decode
  ( -- * Frame decoding
    decodeFrame
  , DecodeError (..)

    -- * Component decoding
  , decodeHeader
  , decodePillarBlock
  ) where

import Data.Bits (shiftL, (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Word (Word8, Word16, Word32, Word64)

import Foundry.Core.Wire.Types
import Foundry.Core.Wire.Varint (decodeVarint)

-- ════════════════════════════════════════════════════════════════════════════
-- Error Types
-- ════════════════════════════════════════════════════════════════════════════

-- | Decode errors
data DecodeError
  = InvalidMagic !Word32
    -- ^ Magic bytes don't match FWIRE_MAGIC
  | UnsupportedVersion !Word8
    -- ^ Version not supported
  | TruncatedHeader
    -- ^ Not enough bytes for header
  | TruncatedDomain
    -- ^ Not enough bytes for domain
  | TruncatedPillar
    -- ^ Not enough bytes for pillar block
  | InvalidVarint
    -- ^ Malformed varint
  | InvalidCRC32 !Word32 !Word32
    -- ^ CRC mismatch (expected, actual)
  | InvalidEncodingType !Word8
    -- ^ Unknown encoding type byte
  deriving stock (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
-- Frame Decoding
-- ════════════════════════════════════════════════════════════════════════════

-- | Decode a complete FWIRE frame.
decodeFrame :: ByteString -> Either DecodeError FWireFrame
decodeFrame bs = do
  -- Need at least 16 (header) + 2 (domain len) + 4 (crc) = 22 bytes minimum
  if BS.length bs < 22
    then Left TruncatedHeader
    else do
      -- Decode header
      (header, afterHeader) <- decodeHeader bs
      
      -- Decode domain
      (domain, afterDomain) <- decodeDomain afterHeader
      
      -- Decode pillars
      let pillarCount = fromIntegral (fwhPillarCount header)
      (pillars, afterPillars) <- decodePillars pillarCount afterDomain
      
      -- Decode and verify CRC32
      (crc, _) <- decodeCRC32 afterPillars
      
      -- TODO: Verify CRC against computed value
      
      Right FWireFrame
        { fwfHeader  = header
        , fwfDomain  = domain
        , fwfPillars = pillars
        , fwfCrc32   = crc
        }

-- ════════════════════════════════════════════════════════════════════════════
-- Header Decoding
-- ════════════════════════════════════════════════════════════════════════════

-- | Decode FWIRE header (16 bytes).
decodeHeader :: ByteString -> Either DecodeError (FWireHeader, ByteString)
decodeHeader bs
  | BS.length bs < 16 = Left TruncatedHeader
  | otherwise =
      let !magic       = getWord32BE bs 0
          !version     = BS.index bs 4
          !flags       = BS.index bs 5
          !pillarCount = getWord16BE bs 6
          !timestamp   = getWord64BE bs 8
          !rest        = BS.drop 16 bs
      in if magic /= FWIRE_MAGIC
           then Left (InvalidMagic magic)
           else if version /= FWIRE_VERSION
             then Left (UnsupportedVersion version)
             else Right
               ( FWireHeader
                   { fwhMagic       = magic
                   , fwhVersion     = version
                   , fwhFlags       = flags
                   , fwhPillarCount = pillarCount
                   , fwhTimestamp   = timestamp
                   }
               , rest
               )

-- ════════════════════════════════════════════════════════════════════════════
-- Domain Decoding
-- ════════════════════════════════════════════════════════════════════════════

-- | Decode domain with length prefix.
decodeDomain :: ByteString -> Either DecodeError (ByteString, ByteString)
decodeDomain bs
  | BS.length bs < 2 = Left TruncatedDomain
  | otherwise =
      let !len = fromIntegral (getWord16BE bs 0)
          !rest = BS.drop 2 bs
      in if BS.length rest < len
           then Left TruncatedDomain
           else Right (BS.take len rest, BS.drop len rest)

-- ════════════════════════════════════════════════════════════════════════════
-- Pillar Block Decoding
-- ════════════════════════════════════════════════════════════════════════════

-- | Decode N pillar blocks.
decodePillars :: Int -> ByteString -> Either DecodeError ([PillarBlock], ByteString)
decodePillars 0 bs = Right ([], bs)
decodePillars n bs = do
  (pillar, rest) <- decodePillarBlock bs
  (pillars, rest') <- decodePillars (n - 1) rest
  Right (pillar : pillars, rest')

-- | Decode a single pillar block.
decodePillarBlock :: ByteString -> Either DecodeError (PillarBlock, ByteString)
decodePillarBlock bs
  | BS.length bs < 2 = Left TruncatedPillar
  | otherwise =
      let !pillarId = PillarId (BS.index bs 0)
          !encByte  = BS.index bs 1
          !rest     = BS.drop 2 bs
      in do
        encoding <- parseEncodingType encByte
        case decodeVarint rest of
          Nothing -> Left InvalidVarint
          Just (len, afterLen) ->
            let !dataLen = fromIntegral len
            in if BS.length afterLen < dataLen
                 then Left TruncatedPillar
                 else Right
                   ( PillarBlock
                       { pbPillarId = pillarId
                       , pbEncoding = encoding
                       , pbData     = BS.take dataLen afterLen
                       }
                   , BS.drop dataLen afterLen
                   )

-- | Parse encoding type byte.
parseEncodingType :: Word8 -> Either DecodeError EncodingType
parseEncodingType 0x00 = Right EncodingRaw
parseEncodingType 0x01 = Right EncodingVarint
parseEncodingType 0x02 = Right EncodingNested
parseEncodingType b    = Left (InvalidEncodingType b)

-- ════════════════════════════════════════════════════════════════════════════
-- CRC32 Decoding
-- ════════════════════════════════════════════════════════════════════════════

-- | Decode CRC32 footer.
decodeCRC32 :: ByteString -> Either DecodeError (Word32, ByteString)
decodeCRC32 bs
  | BS.length bs < 4 = Left TruncatedHeader  -- Reuse error
  | otherwise = Right (getWord32BE bs 0, BS.drop 4 bs)

-- ════════════════════════════════════════════════════════════════════════════
-- Binary Helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Read Word16 big-endian at offset.
getWord16BE :: ByteString -> Int -> Word16
getWord16BE bs off =
  let !b0 = BS.index bs off
      !b1 = BS.index bs (off + 1)
  in (fromIntegral b0 `shiftL` 8) .|. fromIntegral b1
{-# INLINE getWord16BE #-}

-- | Read Word32 big-endian at offset.
getWord32BE :: ByteString -> Int -> Word32
getWord32BE bs off =
  let !b0 = BS.index bs off
      !b1 = BS.index bs (off + 1)
      !b2 = BS.index bs (off + 2)
      !b3 = BS.index bs (off + 3)
  in (fromIntegral b0 `shiftL` 24)
       .|. (fromIntegral b1 `shiftL` 16)
       .|. (fromIntegral b2 `shiftL` 8)
       .|. fromIntegral b3
{-# INLINE getWord32BE #-}

-- | Read Word64 big-endian at offset.
getWord64BE :: ByteString -> Int -> Word64
getWord64BE bs off =
  let !hi = fromIntegral (getWord32BE bs off)
      !lo = fromIntegral (getWord32BE bs (off + 4))
  in (hi `shiftL` 32) .|. lo
{-# INLINE getWord64BE #-}
