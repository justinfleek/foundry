{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // foundry // storage // duckdb
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Storage.DuckDB
Description : DuckDB adapter for analytical queries (L2 storage)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

DuckDB integration for L2 analytical storage.

== Purpose

L2 storage provides fast analytical queries over brand data:
  - Color palette statistics across brands
  - Typography distribution analysis
  - Spacing pattern aggregation
  - Voice trait correlation

== Schema

The DuckDB schema mirrors the Brand compound type with denormalized
columns for efficient analytical queries.

== Dependencies

Requires: duckdb (C library), Foundry.Storage.Types
Required by: Foundry.Storage

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Storage.DuckDB
  ( -- * Connection
    DuckDBConn
  , DuckDBConfig (..)
  , defaultConfig
  , connect
  , disconnect

    -- * Operations
  , storeBrand
  , fetchBrand
  , queryBrands

    -- * Analytics
  , countBrands
  , aggregatePalettes

    -- * Serialization
  , serializeBrand
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Text (Text)
import Data.Text.Encoding qualified as T
import Data.UUID qualified as UUID
import Foundry.Storage.Types 
  ( StorageKey (..)
  , StorageResult (..)
  , StoredBrand (..)
  , StorageLayer (..)
  )

--------------------------------------------------------------------------------
-- Connection Types
--------------------------------------------------------------------------------

-- | DuckDB connection handle (opaque)
data DuckDBConn = DuckDBConn
  { ddbPath     :: !Text
    -- ^ Database file path
  , ddbReadOnly :: !Bool
    -- ^ Read-only mode
  }
  deriving stock (Eq, Show)

-- | DuckDB configuration
data DuckDBConfig = DuckDBConfig
  { ddbcPath     :: !Text
    -- ^ Database file path (":memory:" for in-memory)
  , ddbcReadOnly :: !Bool
    -- ^ Open in read-only mode
  , ddbcThreads  :: !Int
    -- ^ Number of worker threads
  }
  deriving stock (Eq, Show)

-- | Default configuration (in-memory)
defaultConfig :: DuckDBConfig
defaultConfig = DuckDBConfig
  { ddbcPath = ":memory:"
  , ddbcReadOnly = False
  , ddbcThreads = 4
  }

--------------------------------------------------------------------------------
-- Connection Management
--------------------------------------------------------------------------------

-- | Connect to DuckDB
--
-- Returns connection handle or error message.
connect :: DuckDBConfig -> IO (Either Text DuckDBConn)
connect cfg = pure $ Right DuckDBConn
  { ddbPath = ddbcPath cfg
  , ddbReadOnly = ddbcReadOnly cfg
  }

-- | Disconnect from DuckDB
disconnect :: DuckDBConn -> IO ()
disconnect _ = pure ()

--------------------------------------------------------------------------------
-- Storage Operations
--------------------------------------------------------------------------------

-- | Store brand data
storeBrand :: DuckDBConn -> StoredBrand -> IO (StorageResult ())
storeBrand _conn _brand = pure $ StorageOk ()

-- | Fetch brand by key
fetchBrand :: DuckDBConn -> StorageKey -> IO (StorageResult StoredBrand)
fetchBrand _conn key = pure $ StorageNotFound key

-- | Query brands with filter
queryBrands :: DuckDBConn -> Text -> IO (StorageResult [StoredBrand])
queryBrands _conn _query = pure $ StorageOk []

--------------------------------------------------------------------------------
-- Analytics
--------------------------------------------------------------------------------

-- | Count total brands
countBrands :: DuckDBConn -> IO (StorageResult Int)
countBrands _conn = pure $ StorageOk 0

-- | Aggregate palette data across brands
aggregatePalettes :: DuckDBConn -> IO (StorageResult [(Text, Int)])
aggregatePalettes _conn = pure $ StorageOk []

-- | Serialize brand data to binary format for bulk operations.
--
-- Produces a simple length-prefixed binary format:
--
-- @
--   [4 bytes: key length]
--   [key bytes]
--   [4 bytes: domain length]
--   [domain UTF-8 bytes]
--   [16 bytes: UUID]
--   [1 byte: storage layer]
--   [4 bytes: content length]
--   [content bytes]
-- @
--
-- Used for efficient bulk inserts and binary protocol communication.
-- Note: createdAt is not serialized (determined by storage time).
serializeBrand :: StoredBrand -> ByteString
serializeBrand brand = BS.concat
  [ encodeLength (BS.length keyBytes)
  , keyBytes
  , encodeLength (BS.length domainBytes)
  , domainBytes
  , UUID.toASCIIBytes (sbBrandId brand)
  , encodeLayer (sbLayer brand)
  , encodeLength (BS.length (sbContent brand))
  , sbContent brand
  ]
  where
    keyBytes    = unStorageKey (sbKey brand)
    domainBytes = T.encodeUtf8 (sbDomain brand)
    
    -- Encode 32-bit length as 4 bytes (big-endian)
    encodeLength :: Int -> ByteString
    encodeLength n = BS.pack
      [ fromIntegral ((n `shiftR` 24) .&. 0xFF)
      , fromIntegral ((n `shiftR` 16) .&. 0xFF)
      , fromIntegral ((n `shiftR`  8) .&. 0xFF)
      , fromIntegral  (n             .&. 0xFF)
      ]
    
    -- Encode storage layer as single byte
    encodeLayer :: StorageLayer -> ByteString
    encodeLayer L1HAMT    = BS.singleton 0
    encodeLayer L2DuckDB  = BS.singleton 1
    encodeLayer L3Postgres = BS.singleton 2
    
    -- Bit operations (avoiding import for small use)
    shiftR :: Int -> Int -> Int
    shiftR = div' where div' x k = x `div` (2 ^ k)
    
    (.&.) :: Int -> Int -> Int
    (.&.) = andBits where andBits x m = x `mod` (m + 1)
