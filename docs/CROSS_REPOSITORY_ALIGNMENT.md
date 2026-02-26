# Cross-Repository Alignment Specification

> **Version**: 1.1.0  
> **Date**: 2026-02-26  
> **Repositories**: FOUNDRY, HYDROGEN, COMPASS
> **Status**: FOUNDRY pipeline operational, COMPASS export ready

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Overview

This document specifies how the three Straylight repositories align for TOTAL
brand ingestion at swarm scale.

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                          STRAYLIGHT ARCHITECTURE                                │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  /home/jpyxal/jpyxal/                                                           │
│  ├── foundry/          BRAND INGESTION ENGINE            ← OPERATIONAL         │
│  │   ├── haskell/        Extraction pipeline, storage     (232 tests passing)  │
│  │   ├── lean/           Proofs, invariants                                    │
│  │   └── scraper/        Playwright, ZMQ                  (4 brands verified)  │
│  │                                                                              │
│  ├── hydrogen/         FRONTEND SCHEMA & UI                                     │
│  │   ├── src/Hydrogen/   PureScript UI framework                                │
│  │   │   └── Schema/     12-pillar design system                                │
│  │   └── proofs/         Lean4 proofs                                           │
│  │                                                                              │
│  └── COMPASS/          MARKETING AUTOMATION                                     │
│      ├── typed-compass/  Haskell + Lean + PureScript                            │
│      ├── apps/           compass-ui, chatbot                                    │
│      └── nix/haskell/    14 packages                                            │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 1. Type Mapping

### 1.1 Brand Types Across Repositories

| Concept | FOUNDRY (Haskell) | HYDROGEN (PureScript) | COMPASS (Haskell) |
|---------|-------------------|----------------------|-------------------|
| **Identity** | `Foundry.Core.Brand.Identity` | `Hydrogen.Schema.Brand.Identity` | `Compass.Core.Brand.Identity` |
| **Palette** | `Foundry.Core.Brand.Palette` | `Hydrogen.Schema.Brand.Palette` | `Compass.Core.Brand.Palette` |
| **Typography** | `Foundry.Core.Brand.Typography` | `Hydrogen.Schema.Brand.Typography` | `Compass.Core.Brand.Typography` |
| **Voice** | `Foundry.Core.Brand.Voice` | `Hydrogen.Schema.Brand.Voice` | `Compass.Core.Brand.Voice` |
| **Logo** | `Foundry.Core.Brand.Logo` | `Hydrogen.Schema.Brand.Logo.*` | N/A (asset reference) |
| **Complete** | `Foundry.Core.Brand.Complete` | `Hydrogen.Schema.Brand.Brand` | `Compass.Core.Brand.Profile` |

### 1.2 Atomic Type Mapping

| Atom | FOUNDRY | HYDROGEN | Notes |
|------|---------|----------|-------|
| **OKLCH** | `Foundry.Core.Brand.Color.OKLCH` | `Hydrogen.Schema.Color.OKLCH` | Identical structure |
| **FontWeight** | `Foundry.Core.Brand.Typography.FontWeight` | `Hydrogen.Schema.Typography.Weight` | 100-900, validated |
| **SpacingUnit** | `Foundry.Core.Brand.Spacing.SpacingUnit` | `Hydrogen.Schema.Dimension.Pixel` | Positive float |
| **ToneDescriptor** | `Foundry.Core.Brand.Voice.ToneDescriptor` | `Hydrogen.Schema.Brand.Voice.Descriptor` | Normalized text |
| **UUID5** | `Data.UUID` | `Data.UUID` (FFI) | RFC 4122 deterministic |

### 1.3 Compound Type Structure

```
FOUNDRY CompleteBrand (18+ fields) — IMPLEMENTED
├── cbIdentity          : BrandIdentity              ✅ COMPLETE
├── cbPalette           : ColorPalette               ✅ COMPLETE
├── cbTypography        : Typography                 ✅ COMPLETE
├── cbSpacing           : Spacing                    ✅ COMPLETE
├── cbVoice             : BrandVoice                 ✅ COMPLETE
├── cbOverview          : BrandOverview              ✅ COMPLETE
├── cbStrategy          : BrandStrategy              ✅ COMPLETE
├── cbTaglines          : [Tagline]                  ✅ COMPLETE
├── cbEditorial         : Editorial                  ✅ COMPLETE
├── cbCustomers         : [CustomerPersona]          ✅ COMPLETE
├── cbLogo              : LogoSpecification          ✅ COMPLETE
├── cbLayout            : LayoutSystem               ✅ COMPLETE
├── cbImagery           : ImageryGuidelines          ✅ COMPLETE
├── cbMaterial          : MaterialSystem             ✅ COMPLETE
├── cbThemes            : ThemeSet                   ✅ COMPLETE
├── cbHierarchy         : Maybe BrandHierarchy       ✅ COMPLETE
├── cbProvenance        : Provenance                 ✅ COMPLETE
├── cbUIElements        : UISpecification            ⏳ PENDING (port from PS)
└── cbGraphics          : GraphicElementsSpec        ⏳ PENDING (port from PS)

HYDROGEN Brand.Brand
├── identity        : Identity                       ✅ EXISTS
├── palette         : Palette                        ✅ EXISTS
├── typography      : Typography                     ✅ EXISTS
├── spacing         : Spacing                        ✅ EXISTS
├── voice           : Voice                          ✅ EXISTS
├── logo            : Logo.System                    ✅ EXISTS
├── theme           : Theme                          ✅ EXISTS
├── tokens          : Token.System                   ✅ EXISTS
├── compound        : Compound.Types                 ✅ EXISTS
├── provenance      : Provenance                     ✅ EXISTS
├── uiElements      : UISpecification                ✅ EXISTS
├── graphicElements : GraphicElementsSpec            ✅ EXISTS
└── mission         : Mission                        ✅ EXISTS

COMPASS AgentBrandContext (for MAESTRO) — IMPLEMENTED
├── abcBrandId         : UUID                        ✅ COMPLETE
├── abcBrandName       : Text                        ✅ COMPLETE
├── abcIndustry        : Text                        ✅ COMPLETE
├── abcVoiceBePrompt   : Text                        ✅ COMPLETE
├── abcVoiceNeverBe    : Text                        ✅ COMPLETE
├── abcPreferredTerms  : Vector Text                 ✅ COMPLETE
├── abcForbiddenTerms  : Vector Text                 ✅ COMPLETE
├── abcPrimaryColor    : Text (hex)                  ✅ COMPLETE
├── abcFontHeading     : Text                        ✅ COMPLETE
├── abcFontBody        : Text                        ✅ COMPLETE
├── abcToneDescription : Text                        ✅ COMPLETE
└── abcCustomContext   : Map Text Text               ✅ COMPLETE
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 2. Data Flow

### 2.1 Ingestion Flow — OPERATIONAL

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  STAGE 1: SCRAPING (FOUNDRY)                                    ✅ OPERATIONAL  │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Location: foundry/scraper/                                                     │
│  Language: TypeScript (Playwright)                                              │
│  Output: ScrapeResult (HTML, CSS, fonts, images)                                │
│  Transport: ZMQ ROUTER on tcp://localhost:5555                                  │
│                                                                                 │
│  Files:                                                                         │
│    scraper/src/scraper.ts          Main scraper logic (~600 lines)              │
│    scraper/src/server.ts           ZMQ ROUTER server                            │
│    scraper/src/types.ts            Protocol types (matches Haskell)             │
│                                                                                 │
│  Verified on: jbreenconsulting.com, linear.app, openrouter.ai, coca-cola.com    │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ ZMQ DEALER (ScrapeResult JSON)
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  STAGE 2: EXTRACTION (FOUNDRY)                                  ✅ OPERATIONAL  │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Location: foundry/haskell/foundry-extract/                                     │
│  Language: Haskell                                                              │
│  Input: ScrapeResult                                                            │
│  Output: BrandExtractionResult                                                  │
│                                                                                 │
│  Files:                                                                         │
│    src/Foundry/Extract/Color.hs         OKLCH extraction, clustering            │
│    src/Foundry/Extract/Typography.hs    Font stack, scale detection             │
│    src/Foundry/Extract/Spacing.hs       Grid inference                          │
│    src/Foundry/Extract/Voice.hs         Tone analysis                           │
│    src/Foundry/Extract/Compose.hs       Brand composition                       │
│                                                                                 │
│  Tests: 48 passing                                                              │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ BrandExtractionResult
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  STAGE 3: COMPOSITION (FOUNDRY)                                 ✅ OPERATIONAL  │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Location: foundry/haskell/foundry-core/                                        │
│  Language: Haskell                                                              │
│  Input: BrandExtractionResult                                                   │
│  Output: CompleteBrand                                                          │
│                                                                                 │
│  Files:                                                                         │
│    src/Foundry/Core/Brand/Complete.hs       CompleteBrand type (18+ fields)     │
│    src/Foundry/Core/Brand/AgentContext.hs   MAESTRO agent context               │
│    src/Foundry/Core/Brand/Ontology.hs       Knowledge graph export              │
│    src/Foundry/Core/Brand/Hierarchy.hs      Sub-brand relationships             │
│    src/Foundry/Core/Brand/Theme.hs          Light/dark/contrast modes           │
│    src/Foundry/Core/Brand/Layout.hs         Grid, breakpoints, containers       │
│    src/Foundry/Core/Brand/Material.hs       Elevation, shadows, surfaces        │
│    src/Foundry/Core/Brand/Imagery.hs        Photography, illustration           │
│                                                                                 │
│  Tests: 148 passing                                                             │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ CompleteBrand
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  STAGE 4: STORAGE (FOUNDRY)                                     ✅ OPERATIONAL  │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Location: foundry/haskell/foundry-storage/                                     │
│  Language: Haskell                                                              │
│                                                                                 │
│  Files:                                                                         │
│    src/Foundry/Storage/HAMT.hs          L1 in-memory cache                      │
│    src/Foundry/Storage/DuckDB.hs        L2 analytical                           │
│    src/Foundry/Storage/Postgres.hs      L3 durable                              │
│    src/Foundry/Storage/Types.hs         Content-addressed keys                  │
│                                                                                 │
│  Tests: 22 passing                                                              │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ NDJSON (brandToOntology → ontologyToNDJSON)
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  STAGE 5: KNOWLEDGE GRAPH (COMPASS)                             ✅ EXPORT READY │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Location: COMPASS/typed-compass/haskell/                                       │
│  Language: Haskell                                                              │
│                                                                                 │
│  FOUNDRY exports via Ontology.hs:                                               │
│    - brandToOntology :: CompleteBrand -> BrandOntology                          │
│    - ontologyToNDJSON :: BrandOntology -> Text                                  │
│                                                                                 │
│  Entity types exported:                                                         │
│    - Brand (with all metadata)                                                  │
│    - BrandColor (OKLCH values, semantic roles)                                  │
│    - BrandFont (families, weights)                                              │
│    - BrandTagline (primary, secondary)                                          │
│    - BrandTrait (personality traits)                                            │
│                                                                                 │
│  Relationship types:                                                            │
│    - hasColor, usesFont, hasTagline, hasTrait                                   │
│                                                                                 │
│  COMPASS receiver needed to complete integration                                │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ gRPC / AgentBrandContext
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  STAGE 6: AGENT CONSUMPTION (COMPASS)                           ✅ CONTEXT READY│
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Location: COMPASS/nix/haskell/compass-maestro/                                 │
│  Language: Haskell                                                              │
│                                                                                 │
│  FOUNDRY provides via AgentContext.hs:                                          │
│    - brandContext :: CompleteBrand -> AgentBrandContext                         │
│    - formatSystemPrompt :: AgentBrandContext -> AgentRole -> Text               │
│                                                                                 │
│  MAESTRO receives AgentBrandContext containing:                                 │
│    - BE: prompt (from IS constraints)                                           │
│    - NEVER BE: prompt (from NOT constraints)                                    │
│    - Preferred/forbidden vocabulary                                             │
│    - Visual context (colors, fonts)                                             │
│                                                                                 │
│  64 agents inject brand context into system prompts                             │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ JSON over WebSocket
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  STAGE 7: VISUALIZATION (HYDROGEN)                              ⏳ PENDING       │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Location: hydrogen/src/Hydrogen/                                               │
│  Language: PureScript                                                           │
│                                                                                 │
│  Brand dashboard components (to create):                                        │
│    - BrandViewer.purs          Complete brand visualization                     │
│    - BrandDiff.purs            Before/after comparison                          │
│    - BrandHierarchy.purs       Tree view of sub-brands                          │
│    - BrandExport.purs          Export to various formats                        │
│                                                                                 │
│  Uses Schema atoms directly — no CSS, no JavaScript                             │
│  Renders via Target.DOM or Target.WebGL                                         │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### 2.2 Type Synchronization Protocol

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  TYPE SYNC PROTOCOL                                                             │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  CANONICAL SOURCE: Haskell (FOUNDRY)                                            │
│                                                                                 │
│  Sync flow:                                                                     │
│                                                                                 │
│    foundry/haskell/foundry-core/src/Foundry/Core/Brand/*.hs                     │
│                              │                                                  │
│                              │ 1. CI generates JSON Schema                      │
│                              ▼                                                  │
│    foundry/schemas/CompleteBrand.json                                           │
│                              │                                                  │
│                              │ 2. Validate PureScript types                     │
│                              ▼                                                  │
│    hydrogen/src/Hydrogen/Schema/Brand/*.purs                                    │
│                              │                                                  │
│                              │ 3. Copy to COMPASS (or shared package)           │
│                              ▼                                                  │
│    COMPASS/typed-compass/haskell/src/TypedCompass/Brand/*.hs                    │
│                                                                                 │
│  On type change:                                                                │
│    1. Update Haskell type in FOUNDRY                                            │
│    2. Update Lean4 proof (if invariants affected)                               │
│    3. Regenerate JSON Schema                                                    │
│    4. Update PureScript type in HYDROGEN                                        │
│    5. Update COMPASS types                                                      │
│    6. CI validates JSON roundtrip across all                                    │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 3. Shared Conventions

### 3.1 UUID5 Namespace

All three repositories use the same UUID5 namespace for determinism:

```haskell
-- Namespace: "straylight.brand"
-- UUID5 namespace ID: 6ba7b810-9dad-11d1-80b4-00c04fd430c8 (DNS namespace)

brandNamespace :: UUID
brandNamespace = uuid5 dnsNamespace "straylight.brand"
-- Result: deterministic UUID for "straylight.brand"

-- Brand identity from domain
brandIdFromDomain :: Text -> UUID
brandIdFromDomain domain = uuid5 brandNamespace domain
-- coca-cola.com → same UUID every time, everywhere
```

### 3.2 Content Addressing

```haskell
-- SHA-256 for content hashes
contentHash :: ByteString -> ContentHash
contentHash bs = ContentHash (convert (hashWith SHA256 bs))

-- Same content → same hash across all repos
-- Used for:
--   - Storage keys (FOUNDRY)
--   - Cache invalidation (COMPASS)
--   - Asset deduplication (all)
```

### 3.3 Graded Monad Laws

All three repositories implement the same graded monad laws:

```
-- Graded monad laws (verified in Lean4)
return a >>= f  ≡  f a            -- Left identity
m >>= return    ≡  m              -- Right identity
(m >>= f) >>= g ≡  m >>= (λx → f x >>= g)  -- Associativity

-- Co-effect algebra laws (verified in Lean4)
f(f(x)) = f(x)                    -- Idempotency
S(x) >= S(y)                      -- Monotonicity
(E₁ ∘ E₂) ∘ E₃ = E₁ ∘ (E₂ ∘ E₃)  -- Associativity
∀ mutation → Event                -- Provenance
```

### 3.4 Error Handling

```haskell
-- Errors are explicit, never thrown
data BrandError
  = ErrNotFound UUID
  | ErrInvalidPalette Text
  | ErrMissingPrimary
  | ErrContrastViolation OKLCH OKLCH Double
  | ErrVoiceEmpty
  | ErrScrapeTimeout URL
  | ErrNetworkUnreachable
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- All operations return Either BrandError a
-- No exceptions, no bottoms, no partial functions
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 4. Integration Points

### 4.1 FOUNDRY → COMPASS — IMPLEMENTED

```haskell
-- foundry-core/src/Foundry/Core/Brand/Ontology.hs

-- | Export brand to COMPASS knowledge graph format
brandToOntology :: CompleteBrand -> BrandOntology

-- | Convert to NDJSON for transport
ontologyToNDJSON :: BrandOntology -> Text

-- | Entity projection
data OntologyEntity = OntologyEntity
  { oeType         :: !EntityType
  , oeId           :: !UUID
  , oeLabel        :: !Text
  , oeProperties   :: !Value  -- JSON
  }

-- | Relationship types
data OntologyRelation = OntologyRelation
  { orType         :: !RelationType
  , orSourceId     :: !UUID
  , orTargetId     :: !UUID
  }
```

### 4.2 COMPASS → MAESTRO — IMPLEMENTED

```haskell
-- foundry-core/src/Foundry/Core/Brand/AgentContext.hs

-- | Create brand context for agent
brandContext :: CompleteBrand -> AgentBrandContext

-- | Format system prompt for specific agent role
formatSystemPrompt :: AgentBrandContext -> AgentRole -> Text
formatSystemPrompt ctx role = T.unlines
  [ "## Brand Voice Requirements"
  , ""
  , "You are writing for " <> abcBrandName ctx <> "."
  , ""
  , "### BE:"
  , abcVoiceBePrompt ctx
  , ""
  , "### NEVER BE:"
  , abcVoiceNeverBe ctx
  , ""
  , "Preferred terms: " <> T.intercalate ", " (V.toList (abcPreferredTerms ctx))
  , "Forbidden terms: " <> T.intercalate ", " (V.toList (abcForbiddenTerms ctx))
  ]
```

### 4.3 HYDROGEN ← COMPASS — PENDING

```purescript
-- hydrogen/src/Hydrogen/UI/Brand/Dashboard.purs

-- | Fetch brand from COMPASS API
fetchBrand :: UUID -> Aff (Either APIError CompleteBrand)

-- | Render brand visualization
renderBrand :: CompleteBrand -> Element Msg
renderBrand brand = 
  Compound.container
    [ BrandIdentity.view (brand.identity)
    , BrandPalette.view (brand.palette)
    , BrandTypography.view (brand.typography)
    , BrandVoice.view (brand.voice)
    , BrandLogo.view (brand.logo)
    ]
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 5. Proof Sharing

### 5.1 Lean4 Proof Locations

| Proof Domain | FOUNDRY | HYDROGEN | Shared |
|--------------|---------|----------|--------|
| **Co-effects** | `lean/Foundry/Continuity/` | `proofs/Continuity/` | Yes |
| **Sigil Protocol** | `lean/Foundry/Sigil/` | — | No |
| **Cornell Codecs** | `lean/Foundry/Cornell/` | — | No |
| **Brand Invariants** | `lean/Foundry/Brand/` | `proofs/Schema/Brand/` | Partial |
| **Typography** | `lean/Foundry/Brand/Typography.lean` | — | No |
| **Voice** | `lean/Foundry/Brand/Voice.lean` | — | No |

### 5.2 Proof Dependencies

```
foundry/lean/
├── Foundry/
│   ├── Pipeline.lean       (graded monads, co-effects) — COMPLETE
│   ├── Continuity/         (co-effect algebra — SHARED)
│   │   └── *.lean
│   ├── Cornell/            (wire format proofs) — COMPLETE
│   │   └── *.lean
│   ├── Sigil/              (binary protocol) — COMPLETE (18 theorems)
│   │   └── Sigil.lean
│   └── Brand/              (brand invariants)
│       ├── Typography.lean  ← ByteArray API needs update
│       ├── Voice.lean       ← ByteArray API needs update
│       └── Brand.lean       ← MISSING (blocked on Hydrogen)

hydrogen/proofs/
├── Continuity/             (SHARED with FOUNDRY)
│   └── *.lean
└── Schema/
    └── Brand/
        └── (to be created)
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 6. Build & Test Commands

### 6.1 FOUNDRY

```bash
cd /home/jpyxal/jpyxal/foundry

# Enter dev environment
nix develop

# Build all Haskell (4 packages)
cd haskell && cabal build all

# Run tests (expect 232 passing)
cd haskell && cabal test all

# Build Lean4 proofs
cd lean && lake build

# Run scraper server
cd scraper && npm install && npm run start

# Scrape a brand (requires scraper running)
cd haskell && cabal run foundry-scrape -- --url https://linear.app
```

### 6.2 HYDROGEN

```bash
cd /home/jpyxal/jpyxal/hydrogen

# Enter dev environment
nix develop

# Build PureScript
spago build

# Run tests
spago test

# Build Lean4 proofs
lake build

# Run development server
npm run dev
```

### 6.3 COMPASS

```bash
cd /home/jpyxal/jpyxal/COMPASS

# Enter dev environment
nix develop

# Build specific package
nix build .#compass-core -L
nix build .#compass-gateway -L
nix build .#compass-maestro -L

# Build all packages
for pkg in compass-core compass-ast compass-maestro compass-agents; do
  nix build .#$pkg -L
done

# Run PureScript frontend
cd apps/compass-ui && spago build

# Run tests
cd nix/haskell/compass-core && cabal test
```

### 6.4 Cross-Repository Verification

```bash
# Verify all repos build
cd /home/jpyxal/jpyxal

# FOUNDRY (232 tests)
(cd foundry && nix develop -c bash -c "cd haskell && cabal build all && cabal test all")

# HYDROGEN
(cd hydrogen && nix develop -c spago build)

# COMPASS
(cd COMPASS && nix build .#compass-core -L)

# Verify type alignment (future CI job)
# ./scripts/verify-type-alignment.sh
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 7. Migration Checklist

### 7.1 FOUNDRY Tasks

| Status | Task | Notes |
|--------|------|-------|
| `[x]` | Enable `foundry-scraper` in `cabal.project` | Working |
| `[x]` | Create `CompleteBrand` unified type | 18+ fields |
| `[x]` | Port most atoms from HYDROGEN | Layout, Imagery, Theme |
| `[ ]` | Port `UIElements.purs` to Haskell | 1 day effort |
| `[ ]` | Port `GraphicElements.purs` to Haskell | 1 day effort |
| `[x]` | Create `BrandOntology`, `BrandHierarchy` | Complete |
| `[x]` | Create `AgentContext` for MAESTRO | Complete |
| `[x]` | Create COMPASS export module | `ontologyToNDJSON` |
| `[ ]` | Fix Lean4 ByteArray API | 2 days effort |
| `[ ]` | Create `Brand.lean` compound proofs | 3 days effort |

### 7.2 HYDROGEN Tasks

| Status | Task | Notes |
|--------|------|-------|
| `[ ]` | Verify Schema alignment with FOUNDRY types | Pending |
| `[ ]` | Create brand dashboard components | Pending |
| `[ ]` | Create brand diff viewer | Pending |
| `[ ]` | Create export UI | Pending |

### 7.3 COMPASS Tasks

| Status | Task | Notes |
|--------|------|-------|
| `[ ]` | Add brand entity types to knowledge graph schema | Pending |
| `[ ]` | Create NDJSON import handler | Pending |
| `[ ]` | Create `AgentBrandContext` service | Pending |
| `[ ]` | Integrate with MAESTRO agent injection | Pending |
| `[ ]` | Add brand context gRPC endpoint | Pending |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

*Document updated: 2026-02-26*
*Status: FOUNDRY PIPELINE OPERATIONAL — 232 tests passing*

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                            // foundry // alignment
                                                              // straylight/2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
