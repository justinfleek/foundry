{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms #-}

{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // foundry // wire // types
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Wire.Types
Description : FWIRE binary format types for brand ingestion
Copyright   : (c) Straylight, 2026
License     : MIT

FWIRE (Foundry Wire) is a binary format for 38-pillar brand data.
Designed for io_uring, NOT JSON.

== Header Layout (16 bytes)

@
[4 bytes] Magic: 0x46 0x57 0x49 0x52 ("FWIR")
[1 byte]  Version: 0x01
[1 byte]  Flags: reserved
[2 bytes] Pillar count (uint16 BE)
[8 bytes] Timestamp (uint64 BE, unix micros)
@

== Dependencies

Requires: bytestring, word
Required by: Foundry.Core.Wire.Encode, Foundry.Core.Wire.Decode

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Wire.Types
  ( -- * Magic and Version
    pattern FWIRE_MAGIC
  , pattern FWIRE_VERSION

    -- * Pillar IDs
  , PillarId (..)
  , pattern PILLAR_COLOR
  , pattern PILLAR_DIMENSION
  , pattern PILLAR_GEOMETRY
  , pattern PILLAR_TYPOGRAPHY
  , pattern PILLAR_SURFACE
  , pattern PILLAR_ELEVATION
  , pattern PILLAR_MOTION
  , pattern PILLAR_TEMPORAL

    -- * Header
  , FWireHeader (..)
  
    -- * Pillar Block
  , PillarBlock (..)
  , EncodingType (..)
  
    -- * Complete Frame
  , FWireFrame (..)
  ) where

import Data.ByteString (ByteString)
import Data.Word (Word8, Word16, Word32, Word64)

-- ════════════════════════════════════════════════════════════════════════════
-- Magic and Version
-- ════════════════════════════════════════════════════════════════════════════

-- | FWIRE magic bytes: "FWIR" (0x46 0x57 0x49 0x52)
pattern FWIRE_MAGIC :: Word32
pattern FWIRE_MAGIC = 0x46574952

-- | Current FWIRE version
pattern FWIRE_VERSION :: Word8
pattern FWIRE_VERSION = 0x01

-- ════════════════════════════════════════════════════════════════════════════
-- Pillar IDs
-- ════════════════════════════════════════════════════════════════════════════

-- | Pillar identifier (0x00-0x25 for 38 pillars)
newtype PillarId = PillarId { unPillarId :: Word8 }
  deriving stock (Eq, Ord, Show)
  deriving newtype (Enum, Bounded)

pattern PILLAR_COLOR :: PillarId
pattern PILLAR_COLOR = PillarId 0x00

pattern PILLAR_DIMENSION :: PillarId
pattern PILLAR_DIMENSION = PillarId 0x01

pattern PILLAR_GEOMETRY :: PillarId
pattern PILLAR_GEOMETRY = PillarId 0x02

pattern PILLAR_TYPOGRAPHY :: PillarId
pattern PILLAR_TYPOGRAPHY = PillarId 0x03

pattern PILLAR_SURFACE :: PillarId
pattern PILLAR_SURFACE = PillarId 0x04

pattern PILLAR_ELEVATION :: PillarId
pattern PILLAR_ELEVATION = PillarId 0x05

pattern PILLAR_MOTION :: PillarId
pattern PILLAR_MOTION = PillarId 0x06

pattern PILLAR_TEMPORAL :: PillarId
pattern PILLAR_TEMPORAL = PillarId 0x07

-- ════════════════════════════════════════════════════════════════════════════
-- Header
-- ════════════════════════════════════════════════════════════════════════════

-- | FWIRE header (16 bytes)
data FWireHeader = FWireHeader
  { fwhMagic       :: !Word32
    -- ^ Magic bytes (must be FWIRE_MAGIC)
  , fwhVersion     :: !Word8
    -- ^ Format version
  , fwhFlags       :: !Word8
    -- ^ Reserved flags
  , fwhPillarCount :: !Word16
    -- ^ Number of pillar blocks
  , fwhTimestamp   :: !Word64
    -- ^ Unix timestamp in microseconds
  }
  deriving stock (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
-- Pillar Block
-- ════════════════════════════════════════════════════════════════════════════

-- | Encoding type for pillar data
data EncodingType
  = EncodingRaw      -- ^ 0x00: Raw bytes
  | EncodingVarint   -- ^ 0x01: Varint-prefixed length
  | EncodingNested   -- ^ 0x02: Nested pillar blocks
  deriving stock (Eq, Show, Enum, Bounded)

-- | A single pillar block
data PillarBlock = PillarBlock
  { pbPillarId :: !PillarId
    -- ^ Which pillar this is
  , pbEncoding :: !EncodingType
    -- ^ How the data is encoded
  , pbData     :: !ByteString
    -- ^ Raw pillar data
  }
  deriving stock (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
-- Complete Frame
-- ════════════════════════════════════════════════════════════════════════════

-- | Complete FWIRE frame
data FWireFrame = FWireFrame
  { fwfHeader  :: !FWireHeader
    -- ^ Frame header
  , fwfDomain  :: !ByteString
    -- ^ Domain (UTF-8 encoded)
  , fwfPillars :: ![PillarBlock]
    -- ^ Pillar blocks
  , fwfCrc32   :: !Word32
    -- ^ CRC32 checksum
  }
  deriving stock (Eq, Show)
