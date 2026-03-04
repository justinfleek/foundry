{-# LANGUAGE BangPatterns #-}

{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // foundry // wire // encode
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Wire.Encode
Description : FWIRE binary encoding
Copyright   : (c) Straylight, 2026
License     : MIT

Encodes FWireFrame to binary ByteString.

== Dependencies

Requires: Foundry.Core.Wire.Types, Foundry.Core.Wire.Varint
Required by: Extension output, BrandIngestMachine

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Wire.Encode
  ( -- * Frame encoding
    encodeFrame
  , encodeFrameBuilder

    -- * Component encoding
  , encodeHeader
  , encodePillarBlock
  ) where

import Data.Bits ((.&.), shiftR, xor)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Builder (Builder)
import Data.ByteString.Builder qualified as B
import Data.ByteString.Lazy qualified as LBS
import Data.Vector.Unboxed qualified as VU
import Data.Word (Word8, Word16, Word32)

import Foundry.Core.Wire.Types
import Foundry.Core.Wire.Varint (encodeVarintBuilder)

-- ════════════════════════════════════════════════════════════════════════════
-- Frame Encoding
-- ════════════════════════════════════════════════════════════════════════════

-- | Encode a complete FWIRE frame to ByteString.
encodeFrame :: FWireFrame -> ByteString
encodeFrame = LBS.toStrict . B.toLazyByteString . encodeFrameBuilder
{-# INLINE encodeFrame #-}

-- | Encode a complete FWIRE frame as a Builder.
encodeFrameBuilder :: FWireFrame -> Builder
encodeFrameBuilder frame =
  let headerB  = encodeHeader (fwfHeader frame)
      domainB  = encodeDomain (fwfDomain frame)
      pillarsB = foldMap encodePillarBlock (fwfPillars frame)
      bodyB    = headerB <> domainB <> pillarsB
      -- Compute CRC32 of body
      bodyBS   = LBS.toStrict (B.toLazyByteString bodyB)
      crc      = computeCRC32 bodyBS
  in bodyB <> B.word32BE crc

-- ════════════════════════════════════════════════════════════════════════════
-- Header Encoding
-- ════════════════════════════════════════════════════════════════════════════

-- | Encode FWIRE header (16 bytes).
encodeHeader :: FWireHeader -> Builder
encodeHeader hdr =
     B.word32BE (fwhMagic hdr)
  <> B.word8 (fwhVersion hdr)
  <> B.word8 (fwhFlags hdr)
  <> B.word16BE (fwhPillarCount hdr)
  <> B.word64BE (fwhTimestamp hdr)

-- ════════════════════════════════════════════════════════════════════════════
-- Domain Encoding
-- ════════════════════════════════════════════════════════════════════════════

-- | Encode domain with length prefix.
encodeDomain :: ByteString -> Builder
encodeDomain domain =
  let !len = fromIntegral (BS.length domain) :: Word16
  in B.word16BE len <> B.byteString domain

-- ════════════════════════════════════════════════════════════════════════════
-- Pillar Block Encoding
-- ════════════════════════════════════════════════════════════════════════════

-- | Encode a single pillar block.
encodePillarBlock :: PillarBlock -> Builder
encodePillarBlock pb =
     B.word8 (unPillarId (pbPillarId pb))
  <> B.word8 (encodingTypeByte (pbEncoding pb))
  <> encodeVarintBuilder (fromIntegral (BS.length (pbData pb)))
  <> B.byteString (pbData pb)

-- | Convert EncodingType to byte.
encodingTypeByte :: EncodingType -> Word8
encodingTypeByte EncodingRaw    = 0x00
encodingTypeByte EncodingVarint = 0x01
encodingTypeByte EncodingNested = 0x02
{-# INLINE encodingTypeByte #-}

-- ════════════════════════════════════════════════════════════════════════════
-- CRC32
-- ════════════════════════════════════════════════════════════════════════════

-- | Compute CRC32 checksum (IEEE 802.3 polynomial).
computeCRC32 :: ByteString -> Word32
computeCRC32 bs = BS.foldl' updateCRC 0xFFFFFFFF bs `xor` 0xFFFFFFFF
  where
    updateCRC :: Word32 -> Word8 -> Word32
    updateCRC !crc !byte =
      let !idx = fromIntegral ((crc `xor` fromIntegral byte) .&. 0xFF)
      in (crc `shiftR` 8) `xor` (crc32Table VU.! idx)

-- | CRC32 lookup table (IEEE 802.3 polynomial 0xEDB88320)
crc32Table :: VU.Vector Word32
crc32Table = VU.generate 256 mkEntry
  where
    mkEntry :: Int -> Word32
    mkEntry i = go 8 (fromIntegral i)
      where
        go :: Int -> Word32 -> Word32
        go 0 !c = c
        go n !c
          | c .&. 1 == 1 = go (n - 1) ((c `shiftR` 1) `xor` 0xEDB88320)
          | otherwise    = go (n - 1) (c `shiftR` 1)
{-# NOINLINE crc32Table #-}
