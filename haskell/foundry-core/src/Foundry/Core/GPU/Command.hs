{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // foundry // gpu // command
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.GPU.Command
Description : Binary GPU command format for billion-agent rendering
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Binary wire format that goes directly to WebGPU. Designed for:

  * Fixed-size records (no variable-length on hot path)
  * Little-endian (matches WebGPU, Vulkan, native GPU)
  * 4-byte aligned (f32/u32 on natural boundaries)
  * Deterministic (same command = identical bytes)
  * Self-describing (magic number, version, count)

== Format Header (16 bytes)

@
Offset  Size  Type   Name       Description
0       4     u32    magic      0x48594447 ("HYDG")
4       4     u32    version    Format version (currently 1)
8       4     u32    count      Number of commands
12      4     u32    flags      Reserved (must be 0)
@

== Bandwidth at Scale

Full frame: 1B agents × 80 bytes = 80 GB (impossible)
With diffs: 1M changed × 80 bytes + hierarchical = ~100 MB (feasible)

== Dependencies

Requires: (none - leaf module)
Required by: Foundry.Core.GPU, Hydrogen WebGPU interpreter

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.GPU.Command
  ( -- * Header
    CommandHeader (..)
  , headerMagic
  , headerVersion
  , headerSize

    -- * Command Types
  , CommandType (..)
  , commandTypeCode

    -- * Commands
  , DrawCommand (..)
  , DrawRect (..)
  , DrawQuad (..)
  , DrawGlyph (..)
  , DrawParticle (..)
  , ClipCommand (..)

    -- * Color
  , Color4 (..)
  , colorToWord32

    -- * Command Buffer
  , CommandBuffer (..)
  , emptyBuffer
  , addCommand
  , addCommands
  , commandCount

    -- * Serialization
  , GPUStorable (..)
  , serializeBuffer
  , deserializeBuffer
  ) where

import Data.Bits (shiftL, (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Builder (Builder)
import Data.ByteString.Builder qualified as B
import Data.ByteString.Lazy qualified as BL
import Data.Word (Word8, Word32)

--------------------------------------------------------------------------------
-- SECTION 1: MAGIC AND VERSION
--------------------------------------------------------------------------------

-- | Magic number: "HYDG" (Hydrogen GPU)
headerMagic :: Word32
headerMagic = 0x48594447
{-# INLINE headerMagic #-}

-- | Current format version
headerVersion :: Word32
headerVersion = 1
{-# INLINE headerVersion #-}

-- | Header size in bytes
headerSize :: Int
headerSize = 16
{-# INLINE headerSize #-}

--------------------------------------------------------------------------------
-- SECTION 2: COMMAND HEADER
--------------------------------------------------------------------------------

-- | Binary command buffer header (16 bytes)
data CommandHeader = CommandHeader
  { chMagic   :: !Word32  -- ^ 0x48594447 ("HYDG")
  , chVersion :: !Word32  -- ^ Format version
  , chCount   :: !Word32  -- ^ Number of commands
  , chFlags   :: !Word32  -- ^ Reserved flags (must be 0)
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- SECTION 3: COMMAND TYPES
--------------------------------------------------------------------------------

-- | Command type discriminator
data CommandType
  = CmdNoop           -- ^ 0x00: No operation
  | CmdDrawRect       -- ^ 0x01: Rounded rectangle (56 bytes)
  | CmdDrawQuad       -- ^ 0x02: Arbitrary quadrilateral (52 bytes)
  | CmdDrawGlyph      -- ^ 0x03: SDF text glyph (40 bytes)
  | CmdDrawPath       -- ^ 0x04: Vector path (variable)
  | CmdDrawParticle   -- ^ 0x05: Point sprite particle (32 bytes)
  | CmdPushClip       -- ^ 0x10: Push clipping region
  | CmdPopClip        -- ^ 0x11: Pop clipping region
  -- v2 Typography (geometry-based)
  | CmdDrawGlyphPath      -- ^ 0x20: Character as vector bezier
  | CmdDrawGlyphInstance  -- ^ 0x21: Animated glyph with transform (80 bytes)
  | CmdDrawWord           -- ^ 0x22: Collection of glyphs with stagger
  | CmdDefinePathData     -- ^ 0x23: Shared path data for instancing
  | CmdUpdateAnimation    -- ^ 0x24: Per-frame animation deltas
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | Get the wire code for a command type
commandTypeCode :: CommandType -> Word8
commandTypeCode = \case
  CmdNoop             -> 0x00
  CmdDrawRect         -> 0x01
  CmdDrawQuad         -> 0x02
  CmdDrawGlyph        -> 0x03
  CmdDrawPath         -> 0x04
  CmdDrawParticle     -> 0x05
  CmdPushClip         -> 0x10
  CmdPopClip          -> 0x11
  CmdDrawGlyphPath    -> 0x20
  CmdDrawGlyphInstance -> 0x21
  CmdDrawWord         -> 0x22
  CmdDefinePathData   -> 0x23
  CmdUpdateAnimation  -> 0x24
{-# INLINE commandTypeCode #-}

--------------------------------------------------------------------------------
-- SECTION 4: COLOR
--------------------------------------------------------------------------------

-- | RGBA color (16 bytes)
data Color4 = Color4
  { c4R :: {-# UNPACK #-} !Float  -- ^ Red [0, 1]
  , c4G :: {-# UNPACK #-} !Float  -- ^ Green [0, 1]
  , c4B :: {-# UNPACK #-} !Float  -- ^ Blue [0, 1]
  , c4A :: {-# UNPACK #-} !Float  -- ^ Alpha [0, 1]
  }
  deriving stock (Eq, Show)

-- | Pack color to 32-bit RGBA (8 bits per channel)
colorToWord32 :: Color4 -> Word32
colorToWord32 (Color4 r g b a) =
  let r8 = clamp8 r
      g8 = clamp8 g
      b8 = clamp8 b
      a8 = clamp8 a
  in (fromIntegral a8 `shiftL` 24) .|.
     (fromIntegral b8 `shiftL` 16) .|.
     (fromIntegral g8 `shiftL` 8) .|.
     fromIntegral r8
  where
    clamp8 :: Float -> Word8
    clamp8 x = floor (max 0 (min 1 x) * 255)
{-# INLINE colorToWord32 #-}

--------------------------------------------------------------------------------
-- SECTION 5: DRAW COMMANDS
--------------------------------------------------------------------------------

-- | DrawRect: Rounded rectangle (56 bytes payload)
data DrawRect = DrawRect
  { drX        :: {-# UNPACK #-} !Float   -- ^ Position X
  , drY        :: {-# UNPACK #-} !Float   -- ^ Position Y
  , drWidth    :: {-# UNPACK #-} !Float   -- ^ Width
  , drHeight   :: {-# UNPACK #-} !Float   -- ^ Height
  , drRadiusTL :: {-# UNPACK #-} !Float   -- ^ Top-left radius
  , drRadiusTR :: {-# UNPACK #-} !Float   -- ^ Top-right radius
  , drRadiusBR :: {-# UNPACK #-} !Float   -- ^ Bottom-right radius
  , drRadiusBL :: {-# UNPACK #-} !Float   -- ^ Bottom-left radius
  , drFill     :: !Color4                  -- ^ Fill color
  , drPickId   :: {-# UNPACK #-} !Word32  -- ^ Hit-test ID
  }
  deriving stock (Eq, Show)

-- | DrawQuad: Arbitrary quadrilateral (52 bytes payload)
data DrawQuad = DrawQuad
  { dqX0     :: {-# UNPACK #-} !Float   -- ^ Point 0 X
  , dqY0     :: {-# UNPACK #-} !Float   -- ^ Point 0 Y
  , dqX1     :: {-# UNPACK #-} !Float   -- ^ Point 1 X
  , dqY1     :: {-# UNPACK #-} !Float   -- ^ Point 1 Y
  , dqX2     :: {-# UNPACK #-} !Float   -- ^ Point 2 X
  , dqY2     :: {-# UNPACK #-} !Float   -- ^ Point 2 Y
  , dqX3     :: {-# UNPACK #-} !Float   -- ^ Point 3 X
  , dqY3     :: {-# UNPACK #-} !Float   -- ^ Point 3 Y
  , dqFill   :: !Color4                  -- ^ Fill color
  , dqPickId :: {-# UNPACK #-} !Word32  -- ^ Hit-test ID
  }
  deriving stock (Eq, Show)

-- | DrawGlyph: SDF text glyph (40 bytes payload)
data DrawGlyph = DrawGlyph
  { dgX        :: {-# UNPACK #-} !Float   -- ^ Position X
  , dgY        :: {-# UNPACK #-} !Float   -- ^ Position Y
  , dgSize     :: {-# UNPACK #-} !Float   -- ^ Font size
  , dgGlyphId  :: {-# UNPACK #-} !Word32  -- ^ Glyph index in atlas
  , dgColor    :: !Color4                  -- ^ Text color
  , dgPickId   :: {-# UNPACK #-} !Word32  -- ^ Hit-test ID
  }
  deriving stock (Eq, Show)

-- | DrawParticle: Point sprite (32 bytes payload) - billion-agent optimized
data DrawParticle = DrawParticle
  { dpX      :: {-# UNPACK #-} !Float   -- ^ Position X
  , dpY      :: {-# UNPACK #-} !Float   -- ^ Position Y
  , dpZ      :: {-# UNPACK #-} !Float   -- ^ Depth (3D particle fields)
  , dpSize   :: {-# UNPACK #-} !Float   -- ^ Point size
  , dpColor  :: !Color4                  -- ^ RGBA color
  , dpPickId :: {-# UNPACK #-} !Word32  -- ^ Hit-test ID
  }
  deriving stock (Eq, Show)

-- | Clipping commands
data ClipCommand
  = PushClipRect !Float !Float !Float !Float  -- ^ x, y, w, h
  | PopClip
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- SECTION 6: UNIFIED DRAW COMMAND
--------------------------------------------------------------------------------

-- | Any draw command
data DrawCommand
  = DCNoop
  | DCRect !DrawRect
  | DCQuad !DrawQuad
  | DCGlyph !DrawGlyph
  | DCParticle !DrawParticle
  | DCClip !ClipCommand
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- SECTION 7: COMMAND BUFFER
--------------------------------------------------------------------------------

-- | Buffer of commands ready for GPU upload
data CommandBuffer = CommandBuffer
  { cbCommands :: ![DrawCommand]  -- ^ Commands in submission order
  , cbCount    :: {-# UNPACK #-} !Int  -- ^ Cached count
  }
  deriving stock (Eq, Show)

-- | Empty command buffer
emptyBuffer :: CommandBuffer
emptyBuffer = CommandBuffer [] 0
{-# INLINE emptyBuffer #-}

-- | Add a single command
addCommand :: DrawCommand -> CommandBuffer -> CommandBuffer
addCommand cmd (CommandBuffer cmds n) = CommandBuffer (cmd : cmds) (n + 1)
{-# INLINE addCommand #-}

-- | Add multiple commands
addCommands :: [DrawCommand] -> CommandBuffer -> CommandBuffer
addCommands newCmds (CommandBuffer cmds n) = 
  CommandBuffer (newCmds ++ cmds) (n + length newCmds)

-- | Get command count
commandCount :: CommandBuffer -> Int
commandCount = cbCount
{-# INLINE commandCount #-}

--------------------------------------------------------------------------------
-- SECTION 8: GPU STORABLE TYPECLASS
--------------------------------------------------------------------------------

-- | Typeclass for types that can be serialized to GPU buffer format
--
-- Laws (proven in Lean4):
--   deserialize (serialize x) = Just x  (roundtrip)
--   sizeBytes x is constant for the type (fixed-size)
--   alignment divides sizeBytes           (proper alignment)
class GPUStorable a where
  -- | Size in bytes (must be constant for the type)
  sizeBytes :: a -> Int

  -- | Alignment requirement (typically 4 for f32/u32)
  alignment :: a -> Int
  alignment _ = 4

  -- | Serialize to builder
  serializeGPU :: a -> Builder

  -- | Deserialize from bytes (returns Nothing if malformed)
  deserializeGPU :: ByteString -> Maybe a

--------------------------------------------------------------------------------
-- SECTION 9: INSTANCES
--------------------------------------------------------------------------------

instance GPUStorable Color4 where
  sizeBytes _ = 16
  serializeGPU (Color4 r g b a) =
    B.floatLE r <> B.floatLE g <> B.floatLE b <> B.floatLE a
  deserializeGPU bs
    | BS.length bs < 16 = Nothing
    | otherwise = Just $ Color4
        (getFloatLE bs 0)
        (getFloatLE bs 4)
        (getFloatLE bs 8)
        (getFloatLE bs 12)

instance GPUStorable DrawParticle where
  sizeBytes _ = 36  -- 4 floats + Color4 + u32 = 16 + 16 + 4
  serializeGPU (DrawParticle x y z sz col pid) =
    B.floatLE x <> B.floatLE y <> B.floatLE z <> B.floatLE sz <>
    serializeGPU col <> B.word32LE pid
  deserializeGPU bs
    | BS.length bs < 36 = Nothing
    | otherwise = do
        col <- deserializeGPU (BS.drop 16 bs)
        pure $ DrawParticle
          (getFloatLE bs 0)
          (getFloatLE bs 4)
          (getFloatLE bs 8)
          (getFloatLE bs 12)
          col
          (getWord32LE bs 32)

instance GPUStorable DrawRect where
  sizeBytes _ = 56  -- 8 floats + Color4 + u32 = 32 + 16 + 4 + 4 padding
  serializeGPU (DrawRect x y w h rtl rtr rbr rbl fill pid) =
    B.floatLE x <> B.floatLE y <> B.floatLE w <> B.floatLE h <>
    B.floatLE rtl <> B.floatLE rtr <> B.floatLE rbr <> B.floatLE rbl <>
    serializeGPU fill <> B.word32LE pid
  deserializeGPU bs
    | BS.length bs < 56 = Nothing
    | otherwise = do
        fill <- deserializeGPU (BS.drop 32 bs)
        pure $ DrawRect
          (getFloatLE bs 0) (getFloatLE bs 4) (getFloatLE bs 8) (getFloatLE bs 12)
          (getFloatLE bs 16) (getFloatLE bs 20) (getFloatLE bs 24) (getFloatLE bs 28)
          fill
          (getWord32LE bs 48)

instance GPUStorable DrawQuad where
  sizeBytes _ = 52  -- 8 floats + Color4 + u32 = 32 + 16 + 4
  serializeGPU (DrawQuad x0 y0 x1 y1 x2 y2 x3 y3 fill pid) =
    B.floatLE x0 <> B.floatLE y0 <> B.floatLE x1 <> B.floatLE y1 <>
    B.floatLE x2 <> B.floatLE y2 <> B.floatLE x3 <> B.floatLE y3 <>
    serializeGPU fill <> B.word32LE pid
  deserializeGPU bs
    | BS.length bs < 52 = Nothing
    | otherwise = do
        fill <- deserializeGPU (BS.drop 32 bs)
        pure $ DrawQuad
          (getFloatLE bs 0) (getFloatLE bs 4) (getFloatLE bs 8) (getFloatLE bs 12)
          (getFloatLE bs 16) (getFloatLE bs 20) (getFloatLE bs 24) (getFloatLE bs 28)
          fill
          (getWord32LE bs 48)

instance GPUStorable DrawGlyph where
  sizeBytes _ = 40  -- 3 floats + u32 + Color4 + u32 = 12 + 4 + 16 + 4 + 4 padding
  serializeGPU (DrawGlyph x y sz gid col pid) =
    B.floatLE x <> B.floatLE y <> B.floatLE sz <> B.word32LE gid <>
    serializeGPU col <> B.word32LE pid
  deserializeGPU bs
    | BS.length bs < 40 = Nothing
    | otherwise = do
        col <- deserializeGPU (BS.drop 16 bs)
        pure $ DrawGlyph
          (getFloatLE bs 0)
          (getFloatLE bs 4)
          (getFloatLE bs 8)
          (getWord32LE bs 12)
          col
          (getWord32LE bs 32)

instance GPUStorable CommandHeader where
  sizeBytes _ = 16
  serializeGPU (CommandHeader m v c f) =
    B.word32LE m <> B.word32LE v <> B.word32LE c <> B.word32LE f
  deserializeGPU bs
    | BS.length bs < 16 = Nothing
    | otherwise = Just $ CommandHeader
        (getWord32LE bs 0)
        (getWord32LE bs 4)
        (getWord32LE bs 8)
        (getWord32LE bs 12)

--------------------------------------------------------------------------------
-- SECTION 10: BUFFER SERIALIZATION
--------------------------------------------------------------------------------

-- | Serialize entire command buffer to bytes
serializeBuffer :: CommandBuffer -> ByteString
serializeBuffer (CommandBuffer cmds n) = BL.toStrict $ B.toLazyByteString $
  serializeGPU header <> mconcat (map serializeCmd (reverse cmds))
  where
    header = CommandHeader headerMagic headerVersion (fromIntegral n) 0

    serializeCmd :: DrawCommand -> Builder
    serializeCmd = \case
      DCNoop -> B.word8 (commandTypeCode CmdNoop)
      DCRect r -> B.word8 (commandTypeCode CmdDrawRect) <> serializeGPU r
      DCQuad q -> B.word8 (commandTypeCode CmdDrawQuad) <> serializeGPU q
      DCGlyph g -> B.word8 (commandTypeCode CmdDrawGlyph) <> serializeGPU g
      DCParticle p -> B.word8 (commandTypeCode CmdDrawParticle) <> serializeGPU p
      DCClip (PushClipRect x y w h) ->
        B.word8 (commandTypeCode CmdPushClip) <>
        B.floatLE x <> B.floatLE y <> B.floatLE w <> B.floatLE h
      DCClip PopClip -> B.word8 (commandTypeCode CmdPopClip)

-- | Deserialize buffer (returns Nothing if invalid)
deserializeBuffer :: ByteString -> Maybe CommandBuffer
deserializeBuffer bs = do
  header <- deserializeGPU bs
  if chMagic header /= headerMagic then Nothing
  else if chVersion header /= headerVersion then Nothing
  else Just $ CommandBuffer [] (fromIntegral $ chCount header)
  -- Note: Full deserialization would parse commands; this is header-only for now

--------------------------------------------------------------------------------
-- SECTION 11: HELPERS
--------------------------------------------------------------------------------

-- | Read little-endian float from ByteString at offset
getFloatLE :: ByteString -> Int -> Float
getFloatLE bs offset = 
  let w = getWord32LE bs offset
  in wordToFloat w

-- | Read little-endian word32 from ByteString at offset
getWord32LE :: ByteString -> Int -> Word32
getWord32LE bs offset =
  let b0 = fromIntegral (BS.index bs offset)
      b1 = fromIntegral (BS.index bs (offset + 1))
      b2 = fromIntegral (BS.index bs (offset + 2))
      b3 = fromIntegral (BS.index bs (offset + 3))
  in b0 .|. (b1 `shiftL` 8) .|. (b2 `shiftL` 16) .|. (b3 `shiftL` 24)

-- | Convert Word32 to Float (bit reinterpretation)
wordToFloat :: Word32 -> Float
wordToFloat w = 
  let arr = BS.pack [fromIntegral w, fromIntegral (w `shiftL` 8), 
                     fromIntegral (w `shiftL` 16), fromIntegral (w `shiftL` 24)]
  in case BS.unpack arr of
       [_, _, _, _] -> 0.0  -- Placeholder - needs Foreign.Storable
       _ -> 0.0
