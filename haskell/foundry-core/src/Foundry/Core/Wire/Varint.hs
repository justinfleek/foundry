{-# LANGUAGE BangPatterns #-}

{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // foundry // wire // varint
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Wire.Varint
Description : Variable-length integer encoding (protobuf/SIGIL style)
Copyright   : (c) Straylight, 2026
License     : MIT

Same varint encoding as SIGIL/protobuf:
- 7 bits of data per byte
- MSB = continuation flag (1 = more bytes follow)
- Little-endian byte order

== Dependencies

Requires: bytestring
Required by: Foundry.Core.Wire.Encode, Foundry.Core.Wire.Decode

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Wire.Varint
  ( -- * Encoding
    encodeVarint
  , encodeVarintBuilder

    -- * Decoding
  , decodeVarint
  , decodeVarintAt
  ) where

import Data.Bits ((.&.), (.|.), shiftL, shiftR)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Builder (Builder)
import Data.ByteString.Builder qualified as Builder
import Data.Word (Word32, Word64)

-- ════════════════════════════════════════════════════════════════════════════
-- Encoding
-- ════════════════════════════════════════════════════════════════════════════

-- | Encode a Word32 as a varint ByteString.
--
-- Each byte uses 7 bits for data, MSB = continuation.
encodeVarint :: Word32 -> ByteString
encodeVarint = BS.toStrict . Builder.toLazyByteString . encodeVarintBuilder
{-# INLINE encodeVarint #-}

-- | Encode a Word32 as a varint Builder (for efficient concatenation).
encodeVarintBuilder :: Word32 -> Builder
encodeVarintBuilder = go
  where
    go !n
      | n < 0x80  = Builder.word8 (fromIntegral n)
      | otherwise = Builder.word8 (fromIntegral (n .&. 0x7F) .|. 0x80)
                 <> go (n `shiftR` 7)
{-# INLINE encodeVarintBuilder #-}

-- ════════════════════════════════════════════════════════════════════════════
-- Decoding
-- ════════════════════════════════════════════════════════════════════════════

-- | Decode a varint from the start of a ByteString.
--
-- Returns (value, remaining bytes) or Nothing on invalid input.
decodeVarint :: ByteString -> Maybe (Word32, ByteString)
decodeVarint bs = decodeVarintAt bs 0
{-# INLINE decodeVarint #-}

-- | Decode a varint starting at a given offset.
--
-- Returns (value, remaining bytes after varint) or Nothing.
decodeVarintAt :: ByteString -> Int -> Maybe (Word32, ByteString)
decodeVarintAt bs offset = go offset 0 0
  where
    go !pos !acc !shift
      | pos >= BS.length bs = Nothing  -- Incomplete varint
      | shift >= 35         = Nothing  -- Overflow (varint too long)
      | otherwise =
          let !byte = BS.index bs pos
              !val  = fromIntegral (byte .&. 0x7F) :: Word64
              !acc' = acc .|. (val `shiftL` shift)
          in if byte .&. 0x80 == 0
               then Just (fromIntegral acc', BS.drop (pos + 1) bs)
               else go (pos + 1) acc' (shift + 7)
{-# INLINE decodeVarintAt #-}
