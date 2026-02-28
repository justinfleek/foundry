{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // foundry // gpu // patch
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.GPU.Patch
Description : Diff-based updates for bandwidth-efficient rendering
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

At billion-agent scale, full-frame updates are impossible:

  1B agents × 80 bytes = 80 GB/frame @ 60fps = 4.8 TB/s

With diff-based patches:

  ~1M changed × 80 bytes = 80 MB/frame = 4.8 GB/s (feasible)

== Patch Types

@
Patch a
  = NoChange                      -- Element unchanged
  | Replace a                     -- Full replacement
  | UpdateField FieldName Value   -- Single field delta
  | ApplyTransform Transform3D    -- Spatial transform
  | Composite [Patch a]           -- Multiple patches
@

== Hierarchical Aggregation

For groups of agents moving together:

@
GroupPatch
  = GroupTransform GroupId Transform3D  -- Move all 1000 at once
  | GroupColorShift GroupId Color4      -- Tint all 1000
  | GroupMemberPatch GroupId ElementId (Patch a)  -- Single member
@

This reduces O(n) updates to O(1) for coordinated motion.

== Dependencies

Requires: Foundry.Core.GPU.Identified, Foundry.Core.GPU.Command
Required by: Hydrogen runtime, diff computation

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.GPU.Patch
  ( -- * Patch Types
    Patch (..)
  , FieldPatch (..)
  , FieldName (..)

    -- * Transform
  , Transform3D (..)
  , identityTransform
  , translateTransform
  , scaleTransform
  , rotateTransform
  , composeTransform

    -- * Group Patches
  , GroupPatch (..)

    -- * Patch Operations
  , isNoChange
  , patchSize
  , applyPatch
  , composePatch

    -- * Diff Computation
  , DiffResult (..)
  , diffElements
  , diffGroups

    -- * Batch Operations
  , PatchBatch (..)
  , emptyBatch
  , addPatch
  , batchSize
  , compressBatch
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Word (Word32)
import Foundry.Core.GPU.Command (Color4 (..))
import Foundry.Core.GPU.Identified (ElementId, GroupId, FrameId)

--------------------------------------------------------------------------------
-- SECTION 1: FIELD NAMES
--------------------------------------------------------------------------------

-- | Field name for targeted updates
newtype FieldName = FieldName { unFieldName :: Text }
  deriving stock (Eq, Ord, Show)
  deriving newtype (Read)

--------------------------------------------------------------------------------
-- SECTION 2: TRANSFORM
--------------------------------------------------------------------------------

-- | 3D affine transform (for spatial patches)
--
-- Stored as 4x4 matrix in column-major order (matches GPU conventions).
-- 64 bytes = 16 floats.
data Transform3D = Transform3D
  { t3dM00 :: {-# UNPACK #-} !Float, t3dM10 :: {-# UNPACK #-} !Float
  , t3dM20 :: {-# UNPACK #-} !Float, t3dM30 :: {-# UNPACK #-} !Float
  , t3dM01 :: {-# UNPACK #-} !Float, t3dM11 :: {-# UNPACK #-} !Float
  , t3dM21 :: {-# UNPACK #-} !Float, t3dM31 :: {-# UNPACK #-} !Float
  , t3dM02 :: {-# UNPACK #-} !Float, t3dM12 :: {-# UNPACK #-} !Float
  , t3dM22 :: {-# UNPACK #-} !Float, t3dM32 :: {-# UNPACK #-} !Float
  , t3dM03 :: {-# UNPACK #-} !Float, t3dM13 :: {-# UNPACK #-} !Float
  , t3dM23 :: {-# UNPACK #-} !Float, t3dM33 :: {-# UNPACK #-} !Float
  }
  deriving stock (Eq, Show)

-- | Identity transform (no change)
identityTransform :: Transform3D
identityTransform = Transform3D
  1 0 0 0
  0 1 0 0
  0 0 1 0
  0 0 0 1
{-# NOINLINE identityTransform #-}

-- | Translation transform
translateTransform :: Float -> Float -> Float -> Transform3D
translateTransform tx ty tz = Transform3D
  1 0 0 tx
  0 1 0 ty
  0 0 1 tz
  0 0 0 1

-- | Scale transform
scaleTransform :: Float -> Float -> Float -> Transform3D
scaleTransform sx sy sz = Transform3D
  sx 0 0 0
  0 sy 0 0
  0 0 sz 0
  0 0 0 1

-- | Rotation around Z axis (radians)
rotateTransform :: Float -> Transform3D
rotateTransform theta = Transform3D
  (cos theta) (-(sin theta)) 0 0
  (sin theta) (cos theta) 0 0
  0 0 1 0
  0 0 0 1

-- | Compose two transforms (multiply matrices)
composeTransform :: Transform3D -> Transform3D -> Transform3D
composeTransform a b = Transform3D
  (m00 a b) (m10 a b) (m20 a b) (m30 a b)
  (m01 a b) (m11 a b) (m21 a b) (m31 a b)
  (m02 a b) (m12 a b) (m22 a b) (m32 a b)
  (m03 a b) (m13 a b) (m23 a b) (m33 a b)
  where
    m00 x y = t3dM00 x * t3dM00 y + t3dM01 x * t3dM10 y + t3dM02 x * t3dM20 y + t3dM03 x * t3dM30 y
    m10 x y = t3dM10 x * t3dM00 y + t3dM11 x * t3dM10 y + t3dM12 x * t3dM20 y + t3dM13 x * t3dM30 y
    m20 x y = t3dM20 x * t3dM00 y + t3dM21 x * t3dM10 y + t3dM22 x * t3dM20 y + t3dM23 x * t3dM30 y
    m30 x y = t3dM30 x * t3dM00 y + t3dM31 x * t3dM10 y + t3dM32 x * t3dM20 y + t3dM33 x * t3dM30 y
    m01 x y = t3dM00 x * t3dM01 y + t3dM01 x * t3dM11 y + t3dM02 x * t3dM21 y + t3dM03 x * t3dM31 y
    m11 x y = t3dM10 x * t3dM01 y + t3dM11 x * t3dM11 y + t3dM12 x * t3dM21 y + t3dM13 x * t3dM31 y
    m21 x y = t3dM20 x * t3dM01 y + t3dM21 x * t3dM11 y + t3dM22 x * t3dM21 y + t3dM23 x * t3dM31 y
    m31 x y = t3dM30 x * t3dM01 y + t3dM31 x * t3dM11 y + t3dM32 x * t3dM21 y + t3dM33 x * t3dM31 y
    m02 x y = t3dM00 x * t3dM02 y + t3dM01 x * t3dM12 y + t3dM02 x * t3dM22 y + t3dM03 x * t3dM32 y
    m12 x y = t3dM10 x * t3dM02 y + t3dM11 x * t3dM12 y + t3dM12 x * t3dM22 y + t3dM13 x * t3dM32 y
    m22 x y = t3dM20 x * t3dM02 y + t3dM21 x * t3dM12 y + t3dM22 x * t3dM22 y + t3dM23 x * t3dM32 y
    m32 x y = t3dM30 x * t3dM02 y + t3dM31 x * t3dM12 y + t3dM32 x * t3dM22 y + t3dM33 x * t3dM32 y
    m03 x y = t3dM00 x * t3dM03 y + t3dM01 x * t3dM13 y + t3dM02 x * t3dM23 y + t3dM03 x * t3dM33 y
    m13 x y = t3dM10 x * t3dM03 y + t3dM11 x * t3dM13 y + t3dM12 x * t3dM23 y + t3dM13 x * t3dM33 y
    m23 x y = t3dM20 x * t3dM03 y + t3dM21 x * t3dM13 y + t3dM22 x * t3dM23 y + t3dM23 x * t3dM33 y
    m33 x y = t3dM30 x * t3dM03 y + t3dM31 x * t3dM13 y + t3dM32 x * t3dM23 y + t3dM33 x * t3dM33 y

--------------------------------------------------------------------------------
-- SECTION 3: FIELD PATCH
--------------------------------------------------------------------------------

-- | Single field update
data FieldPatch
  = FPFloat !Float           -- ^ Float field
  | FPColor !Color4          -- ^ Color field
  | FPWord32 !Word32         -- ^ Integer field
  | FPBytes !ByteString      -- ^ Raw bytes
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- SECTION 4: PATCH TYPE
--------------------------------------------------------------------------------

-- | Patch for an element
--
-- Represents the delta between two frames for a single element.
data Patch a
  = NoChange
    -- ^ Element unchanged (most common case)
  | Replace !a
    -- ^ Full replacement
  | UpdateField !FieldName !FieldPatch
    -- ^ Single field update
  | ApplyTransform !Transform3D
    -- ^ Spatial transform (position, rotation, scale)
  | ColorShift !Color4
    -- ^ Color tint/multiply
  | Composite ![Patch a]
    -- ^ Multiple patches (applied in order)
  deriving stock (Eq, Show, Functor)

-- | Check if patch is no-op
isNoChange :: Patch a -> Bool
isNoChange NoChange = True
isNoChange _ = False
{-# INLINE isNoChange #-}

-- | Estimated size of patch in bytes (for bandwidth accounting)
patchSize :: Patch a -> Int
patchSize = \case
  NoChange -> 1
  Replace _ -> 80  -- Assume full element
  UpdateField _ fp -> 8 + fieldPatchSize fp
  ApplyTransform _ -> 64  -- 4x4 matrix
  ColorShift _ -> 16  -- Color4
  Composite ps -> sum (map patchSize ps)
  where
    fieldPatchSize :: FieldPatch -> Int
    fieldPatchSize = \case
      FPFloat _ -> 4
      FPColor _ -> 16
      FPWord32 _ -> 4
      FPBytes fbs -> 4 + BS.length fbs

-- | Apply patch to value (placeholder - type depends on specific element type)
applyPatch :: Patch a -> a -> a
applyPatch NoChange a = a
applyPatch (Replace new) _ = new
applyPatch (UpdateField _ _) a = a  -- Would need typeclass for field access
applyPatch (ApplyTransform _) a = a  -- Would need Transformable typeclass
applyPatch (ColorShift _) a = a  -- Would need Colorable typeclass
applyPatch (Composite ps) a = foldr applyPatch a (reverse ps)

-- | Compose two patches
composePatch :: Patch a -> Patch a -> Patch a
composePatch NoChange p = p
composePatch p NoChange = p
composePatch (Composite ps1) (Composite ps2) = Composite (ps1 ++ ps2)
composePatch (Composite ps) p = Composite (ps ++ [p])
composePatch p (Composite ps) = Composite (p : ps)
composePatch p1 p2 = Composite [p1, p2]

--------------------------------------------------------------------------------
-- SECTION 5: GROUP PATCH
--------------------------------------------------------------------------------

-- | Patch for a group of elements
--
-- Enables O(1) updates for coordinated motion of 1000s of agents.
data GroupPatch a
  = GroupTransform !GroupId !Transform3D
    -- ^ Transform all group members
  | GroupColorShift !GroupId !Color4
    -- ^ Tint all group members
  | GroupMemberPatch !GroupId !ElementId !(Patch a)
    -- ^ Patch single member within group
  | GroupReplace !GroupId ![a]
    -- ^ Replace entire group membership
  deriving stock (Eq, Show, Functor)

--------------------------------------------------------------------------------
-- SECTION 6: DIFF COMPUTATION
--------------------------------------------------------------------------------

-- | Result of diffing two elements
data DiffResult a
  = DRSame
    -- ^ Elements identical (by ID comparison)
  | DRAdded !a
    -- ^ Element new in current frame
  | DRRemoved
    -- ^ Element removed from current frame
  | DRChanged !(Patch a)
    -- ^ Element changed with this patch
  deriving stock (Eq, Show, Functor)

-- | Diff two element lists by ID
diffElements 
  :: Map ElementId a  -- ^ Previous frame
  -> Map ElementId a  -- ^ Current frame
  -> Map ElementId (DiffResult a)
diffElements prev curr = Map.mergeWithKey
  (\_ _ new -> Just (DRChanged (Replace new)))  -- Changed
  (const DRRemoved <$>)                          -- Removed
  (DRAdded <$>)                                  -- Added
  prev
  curr

-- | Diff group memberships
diffGroups
  :: Map GroupId [ElementId]  -- ^ Previous frame
  -> Map GroupId [ElementId]  -- ^ Current frame
  -> [(GroupId, [ElementId], [ElementId])]  -- ^ (group, added, removed)
diffGroups prev curr = 
  [ (gid, added, removed)
  | gid <- Map.keys (Map.union prev curr)
  , let prevMembers = Map.findWithDefault [] gid prev
        currMembers = Map.findWithDefault [] gid curr
        added = filter (`notElem` prevMembers) currMembers
        removed = filter (`notElem` currMembers) prevMembers
  , not (null added && null removed)
  ]

--------------------------------------------------------------------------------
-- SECTION 7: PATCH BATCH
--------------------------------------------------------------------------------

-- | Batch of patches for a frame
data PatchBatch a = PatchBatch
  { pbFrame       :: !FrameId                    -- ^ Frame this batch targets
  , pbPatches     :: !(Map ElementId (Patch a))  -- ^ Element patches
  , pbGroupPatches :: ![GroupPatch a]            -- ^ Group patches
  }
  deriving stock (Eq, Show, Functor)

-- | Empty batch
emptyBatch :: FrameId -> PatchBatch a
emptyBatch fid = PatchBatch fid Map.empty []

-- | Add element patch
addPatch :: ElementId -> Patch a -> PatchBatch a -> PatchBatch a
addPatch eid p (PatchBatch fid ps gps) = PatchBatch fid (Map.insert eid p ps) gps

-- | Total size of batch in bytes
batchSize :: PatchBatch a -> Int
batchSize (PatchBatch _ ps gps) = 
  sum (map patchSize (Map.elems ps)) + length gps * 80

-- | Compress batch by removing NoChange patches
compressBatch :: PatchBatch a -> PatchBatch a
compressBatch (PatchBatch fid ps gps) = 
  PatchBatch fid (Map.filter (not . isNoChange) ps) gps
