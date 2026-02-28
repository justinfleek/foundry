{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // foundry // gpu // identified
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.GPU.Identified
Description : Temporal identity wrapper for caching and deduplication
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Every element that persists across frames needs identity for:

  * Diff computation (what changed?)
  * Caching (have we seen this before?)
  * Hit-testing (what did the user click?)
  * Animation (interpolate between states)

== Design

@
Identified a = { id :: ElementId, value :: a }

where ElementId = UUID5(namespace, content_hash)
@

This ensures:

  * Same content → same ID (deterministic)
  * Different frames, same element → same ID (temporal stability)
  * Content changes → new ID (invalidates caches)

== Bandwidth Optimization

At billion-agent scale:

  Full frame: 1B × 80 bytes = 80 GB (impossible)
  With Identified + diff: ~1M changed × 80 = 80 MB (feasible)

The ID enables:

  1. Skip unchanged elements (compare IDs, not content)
  2. Hierarchical grouping (1000 agents moving = 1 transform update)
  3. Content-addressed caching (same ID = same GPU buffer)

== Dependencies

Requires: uuid, crypton
Required by: Foundry.Core.GPU, Hydrogen runtime

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.GPU.Identified
  ( -- * Element Identity
    ElementId (..)
  , mkElementId
  , elementIdNamespace

    -- * Identified Wrapper
  , Identified (..)
  , identify
  , identifyWith

    -- * Group Identity
  , GroupId (..)
  , mkGroupId
  , groupIdNamespace

    -- * Temporal Identity
  , FrameId (..)
  , mkFrameId
  , nextFrameId
  ) where

import Crypto.Hash (Digest, SHA256, hash)
import Data.ByteArray (convert)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as BS8
import Data.Text (Text)
import Data.Text.Encoding qualified as TE
import Data.UUID (UUID)

import Data.UUID.V5 qualified as UUID5
import Data.Word (Word64)

--------------------------------------------------------------------------------
-- SECTION 1: ELEMENT IDENTITY
--------------------------------------------------------------------------------

-- | Unique identifier for a renderable element
--
-- Generated deterministically from content hash via UUID5.
-- Same content always produces the same ElementId.
newtype ElementId = ElementId { unElementId :: UUID }
  deriving stock (Eq, Ord, Show)
  deriving newtype (Read)

-- | Namespace UUID for element IDs
--
-- UUID5 of "foundry:element" under URL namespace
elementIdNamespace :: UUID
elementIdNamespace = UUID5.generateNamed UUID5.namespaceURL (BS.unpack $ TE.encodeUtf8 "foundry:element")
{-# NOINLINE elementIdNamespace #-}

-- | Create element ID from content hash
--
-- @mkElementId content = UUID5(elementIdNamespace, SHA256(content))@
mkElementId :: ByteString -> ElementId
mkElementId content =
  let contentHash = convert (hash content :: Digest SHA256) :: ByteString
  in ElementId (UUID5.generateNamed elementIdNamespace (BS.unpack contentHash))
{-# INLINE mkElementId #-}

--------------------------------------------------------------------------------
-- SECTION 2: IDENTIFIED WRAPPER
--------------------------------------------------------------------------------

-- | Element with temporal identity
--
-- Wraps any value with a deterministic ID based on content.
-- Two Identified values with equal content have equal IDs.
data Identified a = Identified
  { identifiedId    :: !ElementId  -- ^ Stable identity
  , identifiedValue :: !a          -- ^ Wrapped value
  }
  deriving stock (Eq, Show, Functor)

-- | Wrap a value with identity derived from its Show representation
--
-- Note: For production use, implement a proper serialization typeclass.
-- Show is used here for simplicity but may not be stable.
identify :: (Show a) => a -> Identified a
identify a = Identified
  { identifiedId = mkElementId (BS8.pack (show a))
  , identifiedValue = a
  }

-- | Wrap a value with identity from explicit content
identifyWith :: ByteString -> a -> Identified a
identifyWith content a = Identified
  { identifiedId = mkElementId content
  , identifiedValue = a
  }

--------------------------------------------------------------------------------
-- SECTION 3: GROUP IDENTITY
--------------------------------------------------------------------------------

-- | Identity for a group of elements (hierarchical aggregation)
--
-- When 1000 agents move together, we update 1 GroupId instead of 1000 ElementIds.
newtype GroupId = GroupId { unGroupId :: UUID }
  deriving stock (Eq, Ord, Show)
  deriving newtype (Read)

-- | Namespace UUID for group IDs
groupIdNamespace :: UUID
groupIdNamespace = UUID5.generateNamed UUID5.namespaceURL (BS.unpack $ TE.encodeUtf8 "foundry:group")
{-# NOINLINE groupIdNamespace #-}

-- | Create group ID from name
mkGroupId :: Text -> GroupId
mkGroupId name = GroupId (UUID5.generateNamed groupIdNamespace (BS.unpack $ TE.encodeUtf8 name))
{-# INLINE mkGroupId #-}

--------------------------------------------------------------------------------
-- SECTION 4: TEMPORAL IDENTITY
--------------------------------------------------------------------------------

-- | Frame identifier for temporal coherence
--
-- Monotonically increasing, used for:
--   * Cache invalidation
--   * Animation interpolation
--   * Diff baseline
newtype FrameId = FrameId { unFrameId :: Word64 }
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Enum, Bounded)

-- | Create frame ID from counter
mkFrameId :: Word64 -> FrameId
mkFrameId = FrameId
{-# INLINE mkFrameId #-}

-- | Get next frame ID
nextFrameId :: FrameId -> FrameId
nextFrameId (FrameId n) = FrameId (n + 1)
{-# INLINE nextFrameId #-}
