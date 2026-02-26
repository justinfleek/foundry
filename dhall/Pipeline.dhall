{- Pipeline.dhall

   Brand ingestion pipeline stage definitions.

   ARCHITECTURE:
     The pipeline has 5 stages, each with declared coeffects:

     1. DISCOVER  - Find brand pages via SearXNG
                    Coeffects: SearXNG, Network
     2. SCRAPE    - Extract HTML/CSS/fonts via Playwright
                    Coeffects: Playwright, Sandbox(gVisor), ZMQ
     3. EXTRACT   - Parse design tokens (pure computation)
                    Coeffects: Pure (no external requirements)
     4. COMPOSE   - Assemble Brand compound type
                    Coeffects: Pure (no external requirements)
     5. STORE     - Persist to L1/L2/L3 storage
                    Coeffects: DuckDB, Postgres

   DATAFLOW:
     URL -> [Discover] -> List URL
         -> [Scrape]   -> ScrapeResult
         -> [Extract]  -> Molecules (Palette, Typography, Spacing, Voice)
         -> [Compose]  -> Brand
         -> [Store]    -> ()

   STATUS: PRODUCTION
-}

let Resource = ./Resource.dhall

-- ════════════════════════════════════════════════════════════════════════════════
-- STAGE TYPE
-- ════════════════════════════════════════════════════════════════════════════════

let Stage
    : Type
    = { name : Text
      , description : Text
      , coeffects : Resource.Resources
      , inputType : Text
      , outputType : Text
      }

-- ════════════════════════════════════════════════════════════════════════════════
-- STAGE DEFINITIONS
-- ════════════════════════════════════════════════════════════════════════════════

let discoverStage
    : Stage
    = { name = "discover"
      , description = "Find brand pages via SearXNG discovery"
      , coeffects =
          Resource.tensor
            (Resource.searxng "http://searxng.local:8888")
            (Resource.network "searxng.local" 8888)
      , inputType = "Domain"
      , outputType = "List URL"
      }

let scrapeStage
    : Stage
    = { name = "scrape"
      , description = "Extract HTML/CSS/fonts via sandboxed Playwright"
      , coeffects =
          Resource.tensor
            Resource.playwright
            ( Resource.tensor
                (Resource.gvisor "playwright-sandbox")
                (Resource.zmq "ipc:///tmp/metxt-scraper.sock")
            )
      , inputType = "List URL"
      , outputType = "ScrapeResult"
      }

let extractStage
    : Stage
    = { name = "extract"
      , description = "Parse design tokens (colors, typography, spacing, voice)"
      , coeffects = Resource.pure
      , inputType = "ScrapeResult"
      , outputType = "Molecules"
      }

let composeStage
    : Stage
    = { name = "compose"
      , description = "Assemble Brand compound type from molecules"
      , coeffects = Resource.pure
      , inputType = "Molecules"
      , outputType = "Brand"
      }

let storeStage
    : Stage
    = { name = "store"
      , description = "Persist Brand to L1 (HAMT), L2 (DuckDB), L3 (Postgres)"
      , coeffects =
          Resource.tensor
            (Resource.duckdb "/var/lib/metxt/brands.duckdb")
            (Resource.postgres "postgresql://metxt@localhost/brands")
      , inputType = "Brand"
      , outputType = "()"
      }

-- ════════════════════════════════════════════════════════════════════════════════
-- COMPLETE PIPELINE
-- ════════════════════════════════════════════════════════════════════════════════

let stages
    : List Stage
    = [ discoverStage
      , scrapeStage
      , extractStage
      , composeStage
      , storeStage
      ]

let pipelineCoeffects
    : Resource.Resources
    = List/fold
        Stage
        stages
        Resource.Resources
        (\(s : Stage) -> \(acc : Resource.Resources) -> Resource.tensor acc s.coeffects)
        Resource.pure

-- ════════════════════════════════════════════════════════════════════════════════
-- PREDICATES
-- ════════════════════════════════════════════════════════════════════════════════

let isPureStage
    : Stage -> Bool
    = \(s : Stage) -> Resource.isPure s.coeffects

let pureStages
    : List Stage
    = List/filter Stage isPureStage stages

let impureStages
    : List Stage
    = List/filter Stage (\(s : Stage) -> Resource.isPure s.coeffects == False) stages

-- ════════════════════════════════════════════════════════════════════════════════
-- EXPORTS
-- ════════════════════════════════════════════════════════════════════════════════

in  { -- Types
      Stage
      -- Individual stages
    , discoverStage
    , scrapeStage
    , extractStage
    , composeStage
    , storeStage
      -- Complete pipeline
    , stages
    , pipelineCoeffects
      -- Predicates
    , isPureStage
    , pureStages
    , impureStages
    }
