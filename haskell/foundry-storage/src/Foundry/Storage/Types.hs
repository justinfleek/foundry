{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // foundry // storage // types
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Storage.Types
Description : Core storage types and content-addressed keys
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Content-addressed storage primitives using SHA-256 for deterministic keys.

== Architecture

Storage follows a 3-tier model:

  L1: HAMT - In-memory, content-addressed, immutable
  L2: DuckDB - Analytical queries, columnar storage
  L3: PostgreSQL - Durable, transactional persistence

All data is identified by content hash (StorageKey), ensuring:
  - Determinism: same content → same key
  - Deduplication: identical content stored once
  - Integrity: key validates content

== Dependencies

Requires: crypton (SHA-256), bytestring
Required by: Foundry.Storage.HAMT, Foundry.Storage.DuckDB, Foundry.Storage.Postgres

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Storage.Types
  ( -- * Storage Key
    StorageKey (..)
  , mkStorageKey
  , storageKeyToHex
  , storageKeyFromHex

    -- * Storage Result
  , StorageResult (..)

    -- * Storage Layer
  , StorageLayer (..)

    -- * Brand Storage
  , StoredBrand (..)
  ) where

import Crypto.Hash (SHA256 (..), hashWith)
import Data.ByteArray (convert)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Text (Text)
import Data.Text qualified as T
import Data.Time (UTCTime)
import Data.UUID (UUID)
import Data.Word (Word8)
import GHC.Generics (Generic)
import Numeric (readHex, showHex)

--------------------------------------------------------------------------------
-- Storage Key (Content-Addressed)
--------------------------------------------------------------------------------

-- | Content-addressed storage key (SHA-256 hash)
--
-- Keys are deterministic: same content → same key
newtype StorageKey = StorageKey {unStorageKey :: ByteString}
  deriving stock (Eq, Ord, Show, Generic)

-- | Create storage key from content via SHA-256
mkStorageKey :: ByteString -> StorageKey
mkStorageKey content = StorageKey (convert (hashWith SHA256 content))

-- | Convert storage key to hex string
storageKeyToHex :: StorageKey -> Text
storageKeyToHex (StorageKey bs) = T.pack $ BS.foldr (showHex' . fromIntegral) "" bs
  where
    showHex' :: Int -> String -> String
    showHex' n acc =
      let h = showHex n ""
      in (if length h == 1 then '0' : h else h) ++ acc

-- | Parse storage key from hex string
storageKeyFromHex :: Text -> Maybe StorageKey
storageKeyFromHex hex
  | T.length hex /= 64 = Nothing  -- SHA-256 = 32 bytes = 64 hex chars
  | otherwise = Just $ StorageKey $ BS.pack $ parseBytes (T.unpack hex)
  where
    parseBytes :: String -> [Word8]
    parseBytes [] = []
    parseBytes [_] = []  -- Invalid: odd number of hex chars
    parseBytes (h1:h2:rest) = case readHex [h1, h2] of
      [(n, "")] -> fromIntegral (n :: Int) : parseBytes rest
      _         -> []

--------------------------------------------------------------------------------
-- Storage Result
--------------------------------------------------------------------------------

-- | Result of a storage operation
data StorageResult a
  = StorageOk !a
    -- ^ Operation succeeded
  | StorageNotFound !StorageKey
    -- ^ Key not found
  | StorageError !Text
    -- ^ Storage error occurred
  deriving stock (Eq, Show, Functor, Generic)

--------------------------------------------------------------------------------
-- Storage Layer
--------------------------------------------------------------------------------

-- | Storage tier identifier
data StorageLayer
  = L1HAMT
    -- ^ In-memory content-addressed (fastest, volatile)
  | L2DuckDB
    -- ^ Analytical columnar (fast queries, persistent)
  | L3Postgres
    -- ^ Durable transactional (reliable, slower)
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

--------------------------------------------------------------------------------
-- Stored Brand
--------------------------------------------------------------------------------

-- | Brand data as stored (with metadata)
data StoredBrand = StoredBrand
  { sbKey       :: !StorageKey
    -- ^ Content-addressed key
  , sbDomain    :: !Text
    -- ^ Source domain
  , sbBrandId   :: !UUID
    -- ^ Brand UUID (deterministic from domain)
  , sbCreatedAt :: !UTCTime
    -- ^ When brand was stored
  , sbLayer     :: !StorageLayer
    -- ^ Which storage tier
  , sbContent   :: !ByteString
    -- ^ Serialized brand JSON
  }
  deriving stock (Eq, Show, Generic)
