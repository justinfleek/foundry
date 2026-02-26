{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // foundry // storage
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Storage
Description : Brand data persistence layer
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Storage layer for the SMART Brand Ingestion Engine.

== Architecture

Three-tier storage model:

  L1: HAMT (Hash Array Mapped Trie)
      - In-memory, content-addressed
      - Fastest access, volatile
      - Used for hot data and caching

  L2: DuckDB
      - Analytical columnar storage
      - Fast aggregation queries
      - Used for batch analysis

  L3: PostgreSQL
      - Durable, transactional
      - Full ACID compliance
      - Used for persistence

== Data Flow

@
  Scraper → Extract → L1 (HAMT) → L2 (DuckDB) → L3 (Postgres)
                         ↓
                    Analytics
@

== Usage

Import storage adapters qualified to avoid name collisions:

@
import Foundry.Storage.Types (StorageKey, StorageResult (..))
import Foundry.Storage.HAMT qualified as HAMT
import Foundry.Storage.DuckDB qualified as DuckDB
import Foundry.Storage.Postgres qualified as Postgres

-- Store in L1 (hot cache)
HAMT.insert key value hamt

-- Store in L2 (analytics)
DuckDB.storeBrand conn brand

-- Store in L3 (durable)
Postgres.storeBrand conn brand
@

== Dependencies

Requires: Foundry.Storage.Types, Foundry.Storage.HAMT, Foundry.Storage.DuckDB, Foundry.Storage.Postgres
Required by: (top-level module)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Storage
  ( -- * Types (re-exported without qualification)
    module Foundry.Storage.Types
    
    -- * HAMT (L1 - Content-Addressed Cache)
  , module Foundry.Storage.HAMT
  
    -- * DuckDB (L2 - Analytics)
    --
    -- Note: Use @import Foundry.Storage.DuckDB qualified as DuckDB@
    -- for connect, disconnect, storeBrand, fetchBrand to avoid
    -- collision with Postgres names.
  
    -- * PostgreSQL (L3 - Durable)
    --
    -- Note: Use @import Foundry.Storage.Postgres qualified as Postgres@
    -- for connect, disconnect, storeBrand, fetchBrand to avoid
    -- collision with DuckDB names.
  ) where

import Foundry.Storage.HAMT
import Foundry.Storage.Types
