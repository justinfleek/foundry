{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // foundry // storage // hamt
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Storage.HAMT
Description : Content-addressed in-memory storage using HAMT
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Hash Array Mapped Trie (HAMT) implementation for L1 storage.

== Properties

  - Content-addressed: key = SHA-256(content)
  - Immutable: insert returns new HAMT
  - Persistent: structure sharing for efficiency
  - Deterministic: same content → same key

== Usage

@
let hamt0 = empty
    (key, hamt1) = insert content hamt0
    result = lookup key hamt1
@

== Dependencies

Requires: Foundry.Storage.Types
Required by: Foundry.Storage

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Storage.HAMT
  ( -- * HAMT Type
    HAMT

    -- * Construction
  , empty
  , singleton

    -- * Operations
  , insert
  , lookup
  , delete
  , member

    -- * Queries
  , size
  , null
  , keys
  , elems
  , toList

    -- * Batch Operations
  , insertMany
  , fromList
  ) where

import Data.ByteString (ByteString)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Foundry.Storage.Types (StorageKey (..), mkStorageKey)
import Prelude hiding (lookup, null)

--------------------------------------------------------------------------------
-- HAMT Type
--------------------------------------------------------------------------------

-- | Hash Array Mapped Trie for content-addressed storage
--
-- Uses Data.Map internally for simplicity. A production implementation
-- would use a proper HAMT with bit-partitioning for O(log32 n) operations.
--
-- Invariant: all keys are SHA-256 hashes of their corresponding values
newtype HAMT = HAMT {unHAMT :: Map StorageKey ByteString}
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

-- | Empty HAMT
empty :: HAMT
empty = HAMT Map.empty

-- | Create HAMT with single entry
singleton :: ByteString -> (StorageKey, HAMT)
singleton content =
  let key = mkStorageKey content
  in (key, HAMT (Map.singleton key content))

--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

-- | Insert content, returning (key, new HAMT)
--
-- If content already exists (same hash), returns existing key.
-- This is idempotent: inserting the same content twice is a no-op.
insert :: ByteString -> HAMT -> (StorageKey, HAMT)
insert content (HAMT m) =
  let key = mkStorageKey content
      m' = Map.insert key content m
  in (key, HAMT m')

-- | Lookup content by key
lookup :: StorageKey -> HAMT -> Maybe ByteString
lookup key (HAMT m) = Map.lookup key m

-- | Delete entry by key
delete :: StorageKey -> HAMT -> HAMT
delete key (HAMT m) = HAMT (Map.delete key m)

-- | Check if key exists
member :: StorageKey -> HAMT -> Bool
member key (HAMT m) = Map.member key m

--------------------------------------------------------------------------------
-- Queries
--------------------------------------------------------------------------------

-- | Number of entries
size :: HAMT -> Int
size (HAMT m) = Map.size m

-- | Check if empty
null :: HAMT -> Bool
null (HAMT m) = Map.null m

-- | All keys
keys :: HAMT -> [StorageKey]
keys (HAMT m) = Map.keys m

-- | All values
elems :: HAMT -> [ByteString]
elems (HAMT m) = Map.elems m

-- | Convert to list
toList :: HAMT -> [(StorageKey, ByteString)]
toList (HAMT m) = Map.toList m

--------------------------------------------------------------------------------
-- Batch Operations
--------------------------------------------------------------------------------

-- | Insert multiple contents
insertMany :: [ByteString] -> HAMT -> ([StorageKey], HAMT)
insertMany contents hamt0 = foldr go ([], hamt0) contents
  where
    go content (keys', hamt) =
      let (key, hamt') = insert content hamt
      in (key : keys', hamt')

-- | Create HAMT from list of contents
fromList :: [ByteString] -> ([StorageKey], HAMT)
fromList contents = insertMany contents empty
