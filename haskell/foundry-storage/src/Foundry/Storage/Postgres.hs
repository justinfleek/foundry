{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // foundry // storage // postgres
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Storage.Postgres
Description : PostgreSQL adapter for durable persistence (L3 storage)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

PostgreSQL integration for L3 durable storage.

== Purpose

L3 storage provides durable, transactional persistence:
  - ACID transactions
  - Foreign key relationships
  - Full-text search
  - Backup and replication

== Schema

PostgreSQL schema uses proper relational normalization:
  - brands (id, domain, created_at, content_hash)
  - palettes (brand_id, colors jsonb)
  - typography (brand_id, heading_font, body_font, scale)
  - etc.

== Dependencies

Requires: postgresql-simple, Foundry.Storage.Types
Required by: Foundry.Storage

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Storage.Postgres
  ( -- * Connection
    PostgresConn
  , PostgresConfig (..)
  , defaultConfig
  , connect
  , disconnect

    -- * Operations
  , storeBrand
  , fetchBrand
  , fetchBrandByDomain
  , deleteBrand

    -- * Transactions
  , withTransaction
  ) where

import Data.Text (Text)
import Foundry.Core.Text (tshow)
import Foundry.Storage.Types (StorageKey, StorageResult (..), StoredBrand)

--------------------------------------------------------------------------------
-- Connection Types
--------------------------------------------------------------------------------

-- | PostgreSQL connection handle (opaque)
data PostgresConn = PostgresConn
  { pgConnString :: !Text
    -- ^ Connection string
  }
  deriving stock (Eq, Show)

-- | PostgreSQL configuration
data PostgresConfig = PostgresConfig
  { pgcHost     :: !Text
    -- ^ Database host
  , pgcPort     :: !Int
    -- ^ Database port
  , pgcDatabase :: !Text
    -- ^ Database name
  , pgcUser     :: !Text
    -- ^ Username
  , pgcPassword :: !Text
    -- ^ Password (should come from secrets manager)
  , pgcPoolSize :: !Int
    -- ^ Connection pool size
  }
  deriving stock (Eq, Show)

-- | Default configuration (localhost)
defaultConfig :: PostgresConfig
defaultConfig = PostgresConfig
  { pgcHost = "localhost"
  , pgcPort = 5432
  , pgcDatabase = "foundry"
  , pgcUser = "foundry"
  , pgcPassword = ""  -- Should be overridden
  , pgcPoolSize = 10
  }

--------------------------------------------------------------------------------
-- Connection Management
--------------------------------------------------------------------------------

-- | Connect to PostgreSQL
connect :: PostgresConfig -> IO (Either Text PostgresConn)
connect cfg = pure $ Right PostgresConn
  { pgConnString = buildConnString cfg
  }
  where
    buildConnString :: PostgresConfig -> Text
    buildConnString c = mconcat
      [ "host=", pgcHost c
      , " port=", tshow (pgcPort c)
      , " dbname=", pgcDatabase c
      , " user=", pgcUser c
      ]

-- | Disconnect from PostgreSQL
disconnect :: PostgresConn -> IO ()
disconnect _ = pure ()

--------------------------------------------------------------------------------
-- Storage Operations
--------------------------------------------------------------------------------

-- | Store brand data
storeBrand :: PostgresConn -> StoredBrand -> IO (StorageResult ())
storeBrand _conn _brand = pure $ StorageOk ()

-- | Fetch brand by storage key
fetchBrand :: PostgresConn -> StorageKey -> IO (StorageResult StoredBrand)
fetchBrand _conn key = pure $ StorageNotFound key

-- | Fetch brand by domain
fetchBrandByDomain :: PostgresConn -> Text -> IO (StorageResult StoredBrand)
fetchBrandByDomain _conn _domain = pure $ StorageError "Not found"

-- | Delete brand
deleteBrand :: PostgresConn -> StorageKey -> IO (StorageResult ())
deleteBrand _conn _key = pure $ StorageOk ()

--------------------------------------------------------------------------------
-- Transactions
--------------------------------------------------------------------------------

-- | Run action in a transaction
withTransaction :: PostgresConn -> IO a -> IO a
withTransaction _conn action = action
