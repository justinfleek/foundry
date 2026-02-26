{- Resource.dhall

   Coeffect algebra for the brand ingestion pipeline.

   EXTENDS: sensenet/dhall/Resource.dhall (base coeffect algebra)

   WHAT IS A COEFFECT:
     Effects:    what a computation DOES to the world (writes, network calls)
     Coeffects:  what a computation NEEDS from the world (reads, auth, sandbox)

   The brand ingestion pipeline has specific coeffect requirements:
     - Discovery needs SearXNG access
     - Scraping needs sandboxed browser (Playwright + gVisor/Bubblewrap)
     - Extraction is pure (no external requirements)
     - Storage needs database connections (DuckDB, PostgreSQL)

   This module extends sensenet's base Resource.dhall with metxt-specific
   coeffect types. The base algebra (tensor, isPure, etc.) is inherited.

   ALGEBRA (from sensenet):
     Resources form a commutative monoid under tensor (⊗):
       - Identity: pure (empty list)
       - Associative: (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)
       - Commutative: a ⊗ b = b ⊗ a

   ALIGNMENT (with Lean4 Continuity.Coeffect):
     - Pure         → Coeffect.pure
     - Network      → Coeffect.network
     - NetworkCA    → Coeffect.networkCA
     - Sandbox      → Coeffect.sandbox
     - Auth         → Coeffect.auth

   STATUS: PRODUCTION
-}

-- ════════════════════════════════════════════════════════════════════════════════
-- RESOURCE TYPE
-- ════════════════════════════════════════════════════════════════════════════════

let Resource
    : Type
    = < -- Pure: needs nothing external (functional core)
        Pure

        -- Network: needs network access to specific endpoint
      | Network : { host : Text, port : Natural }

        -- NetworkCA: needs content-addressed network fetch (reproducible)
      | NetworkCA : { hash : Text }

        -- Sandbox: needs isolation environment
      | Sandbox : { name : Text, type : < GVisor | Bubblewrap | Docker > }

        -- SearXNG: needs SearXNG discovery service
      | SearXNG : { instance : Text }

        -- Playwright: needs browser automation (always sandboxed)
      | Playwright

        -- ZMQ: needs ZeroMQ messaging endpoint
      | ZMQ : { endpoint : Text }

        -- DuckDB: needs DuckDB analytical database
      | DuckDB : { path : Text }

        -- Postgres: needs PostgreSQL durable storage
      | Postgres : { connString : Text }

        -- Auth: needs authentication credential
      | Auth : { provider : Text }
      >

-- ════════════════════════════════════════════════════════════════════════════════
-- RESOURCES (SET OF COEFFECTS)
-- ════════════════════════════════════════════════════════════════════════════════

let Resources : Type = List Resource

-- ════════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ════════════════════════════════════════════════════════════════════════════════

let pure : Resources = [] : List Resource

let network
    : Text -> Natural -> Resources
    = \(host : Text) ->
      \(port : Natural) ->
        [ Resource.Network { host, port } ]

let networkCA
    : Text -> Resources
    = \(hash : Text) -> [ Resource.NetworkCA { hash } ]

let gvisor
    : Text -> Resources
    = \(name : Text) ->
        [ Resource.Sandbox { name, type = < GVisor | Bubblewrap | Docker >.GVisor } ]

let bubblewrap
    : Text -> Resources
    = \(name : Text) ->
        [ Resource.Sandbox { name, type = < GVisor | Bubblewrap | Docker >.Bubblewrap } ]

let searxng
    : Text -> Resources
    = \(instance : Text) -> [ Resource.SearXNG { instance } ]

let playwright : Resources = [ Resource.Playwright ]

let zmq
    : Text -> Resources
    = \(endpoint : Text) -> [ Resource.ZMQ { endpoint } ]

let duckdb
    : Text -> Resources
    = \(path : Text) -> [ Resource.DuckDB { path } ]

let postgres
    : Text -> Resources
    = \(connString : Text) -> [ Resource.Postgres { connString } ]

let auth
    : Text -> Resources
    = \(provider : Text) -> [ Resource.Auth { provider } ]

-- ════════════════════════════════════════════════════════════════════════════════
-- TENSOR PRODUCT (COMBINE COEFFECTS)
-- ════════════════════════════════════════════════════════════════════════════════

let tensor
    : Resources -> Resources -> Resources
    = \(r : Resources) ->
      \(s : Resources) ->
        r # s

-- ASCII alias
let combine = tensor

-- ════════════════════════════════════════════════════════════════════════════════
-- PREDICATES
-- ════════════════════════════════════════════════════════════════════════════════

let isPure
    : Resources -> Bool
    = \(r : Resources) ->
        merge
          { None = True
          , Some = \(_ : Resource) -> False
          }
          (List/head Resource r)

let requiresNetwork
    : Resources -> Bool
    = \(r : Resources) ->
        List/fold
          Resource
          r
          Bool
          ( \(res : Resource) ->
            \(acc : Bool) ->
              acc
              || merge
                   { Pure = False
                   , Network = \(_ : { host : Text, port : Natural }) -> True
                   , NetworkCA = \(_ : { hash : Text }) -> True
                   , Sandbox = \(_ : { name : Text, type : < GVisor | Bubblewrap | Docker > }) -> False
                   , SearXNG = \(_ : { instance : Text }) -> True
                   , Playwright = False
                   , ZMQ = \(_ : { endpoint : Text }) -> False
                   , DuckDB = \(_ : { path : Text }) -> False
                   , Postgres = \(_ : { connString : Text }) -> False
                   , Auth = \(_ : { provider : Text }) -> False
                   }
                   res
          )
          False

let requiresSandbox
    : Resources -> Bool
    = \(r : Resources) ->
        List/fold
          Resource
          r
          Bool
          ( \(res : Resource) ->
            \(acc : Bool) ->
              acc
              || merge
                   { Pure = False
                   , Network = \(_ : { host : Text, port : Natural }) -> False
                   , NetworkCA = \(_ : { hash : Text }) -> False
                   , Sandbox = \(_ : { name : Text, type : < GVisor | Bubblewrap | Docker > }) -> True
                   , SearXNG = \(_ : { instance : Text }) -> False
                   , Playwright = True
                   , ZMQ = \(_ : { endpoint : Text }) -> False
                   , DuckDB = \(_ : { path : Text }) -> False
                   , Postgres = \(_ : { connString : Text }) -> False
                   , Auth = \(_ : { provider : Text }) -> False
                   }
                   res
          )
          False

let requiresDatabase
    : Resources -> Bool
    = \(r : Resources) ->
        List/fold
          Resource
          r
          Bool
          ( \(res : Resource) ->
            \(acc : Bool) ->
              acc
              || merge
                   { Pure = False
                   , Network = \(_ : { host : Text, port : Natural }) -> False
                   , NetworkCA = \(_ : { hash : Text }) -> False
                   , Sandbox = \(_ : { name : Text, type : < GVisor | Bubblewrap | Docker > }) -> False
                   , SearXNG = \(_ : { instance : Text }) -> False
                   , Playwright = False
                   , ZMQ = \(_ : { endpoint : Text }) -> False
                   , DuckDB = \(_ : { path : Text }) -> True
                   , Postgres = \(_ : { connString : Text }) -> True
                   , Auth = \(_ : { provider : Text }) -> False
                   }
                   res
          )
          False

-- ════════════════════════════════════════════════════════════════════════════════
-- EXPORTS
-- ════════════════════════════════════════════════════════════════════════════════

in  { -- Types
      Resource
    , Resources
      -- Constructors
    , pure
    , network
    , networkCA
    , gvisor
    , bubblewrap
    , searxng
    , playwright
    , zmq
    , duckdb
    , postgres
    , auth
      -- Algebra
    , tensor
    , combine
      -- Predicates
    , isPure
    , requiresNetwork
    , requiresSandbox
    , requiresDatabase
    }
