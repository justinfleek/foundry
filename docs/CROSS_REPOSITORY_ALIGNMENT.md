# Cross-Repository Alignment Specification

> **Version**: 1.0.0  
> **Date**: 2026-02-26  
> **Repositories**: FOUNDRY, HYDROGEN, COMPASS

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
│  ├── foundry/          BRAND INGESTION ENGINE                                   │
│  │   ├── haskell/        Extraction pipeline, storage                           │
│  │   ├── lean/           Proofs, invariants                                     │
│  │   └── scraper/        Playwright, ZMQ                                        │
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
FOUNDRY CompleteBrand
├── completeBrandIdentity       : BrandIdentity
├── completeBrandPalette        : BrandPalette
├── completeBrandTypography     : BrandTypography
├── completeBrandSpacing        : BrandSpacing
├── completeBrandVoice          : BrandVoice
├── completeBrandLogo           : LogoSpecification
├── completeBrandGradient       : GradientSpecification
├── completeBrandLayout         : LayoutSpecification       ← MISSING
├── completeBrandUIElements     : UISpecification           ← MISSING
├── completeBrandGraphics       : GraphicElementsSpec       ← MISSING
├── completeBrandModes          : ModesSpecification        ← MISSING
├── completeBrandImagery        : ImagerySpecification      ← MISSING
├── completeBrandProvenance     : Provenance
├── completeBrandOntology       : BrandOntology             ← MISSING
├── completeBrandParent         : Maybe BrandIdentity       ← MISSING
└── completeBrandSharedAssets   : Maybe SharedBrandAssets   ← MISSING

HYDROGEN Brand.Brand
├── identity        : Identity
├── palette         : Palette
├── typography      : Typography
├── spacing         : Spacing
├── voice           : Voice
├── logo            : Logo.System                           ✅ EXISTS
├── theme           : Theme                                 ✅ EXISTS
├── tokens          : Token.System                          ✅ EXISTS
├── compound        : Compound.Types                        ✅ EXISTS
├── provenance      : Provenance
└── mission         : Mission

COMPASS BrandProfile (for MAESTRO)
├── brandId         : UUID
├── brandName       : Text
├── industry        : Text
├── toneDescription : Text
├── voiceBePrompt   : Text
├── voiceNeverBe    : Text
├── preferredTerms  : Vector Text
├── forbiddenTerms  : Vector Text
├── primaryColor    : Text (hex)
├── fontHeading     : Text
├── fontBody        : Text
└── customContext   : Map Text Text
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 2. Data Flow

### 2.1 Ingestion Flow

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  STAGE 1: SCRAPING (FOUNDRY)                                                    │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Location: foundry/scraper/                                                     │
│  Language: TypeScript (Playwright)                                              │
│  Output: ScrapeResult (HTML, CSS, fonts, images)                                │
│  Transport: ZMQ PUSH to tcp://localhost:5555                                    │
│                                                                                 │
│  Files:                                                                         │
│    scraper/src/scraper.ts          Main scraper logic                           │
│    scraper/src/extract.ts          DOM extraction                               │
│    scraper/src/zmq.ts              ZMQ publisher                                │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ ZMQ PUSH (ScrapeResult JSON)
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  STAGE 2: EXTRACTION (FOUNDRY)                                                  │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Location: foundry/haskell/foundry-extract/                                     │
│  Language: Haskell                                                              │
│  Input: ScrapeResult                                                            │
│  Output: CompleteBrand                                                          │
│                                                                                 │
│  Files:                                                                         │
│    src/Foundry/Extract/Color.hs         OKLCH extraction, clustering            │
│    src/Foundry/Extract/Typography.hs    Font stack, scale detection             │
│    src/Foundry/Extract/Spacing.hs       Grid inference                          │
│    src/Foundry/Extract/Voice.hs         Tone analysis (LLM-assisted)            │
│    src/Foundry/Extract/Logo.hs          Logo detection (PARTIAL)                │
│    src/Foundry/Extract/Compose.hs       Brand composition                       │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ CompleteBrand (Haskell)
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  STAGE 3: STORAGE (FOUNDRY)                                                     │
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
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ NDJSON over ZMQ PUSH
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  STAGE 4: KNOWLEDGE GRAPH (COMPASS)                                             │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Location: COMPASS/typed-compass/haskell/                                       │
│  Language: Haskell                                                              │
│                                                                                 │
│  Schema additions needed:                                                       │
│    - Entity types: brand, brand_voice, brand_palette, tone_attribute           │
│    - Relationship types: has_voice, has_palette, tone_is_descriptor            │
│                                                                                 │
│  Files (to create):                                                             │
│    src/Compass/Core/Brand/Import.hs     NDJSON consumer                         │
│    src/Compass/Core/Brand/Entity.hs     KG entity projection                    │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ gRPC / AgentBrandContext
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  STAGE 5: AGENT CONSUMPTION (COMPASS)                                           │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Location: COMPASS/nix/haskell/compass-maestro/                                 │
│  Language: Haskell                                                              │
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
│  STAGE 6: VISUALIZATION (HYDROGEN)                                              │
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

### 4.1 FOUNDRY → COMPASS

```haskell
-- foundry-core/src/Foundry/Core/Export/COMPASS.hs

-- | Export brand to COMPASS knowledge graph format
exportToCompass :: CompleteBrand -> Vector CompassEntity

-- | Entity projection
data CompassEntity = CompassEntity
  { entityType     :: !EntityType
  , entityId       :: !UUID
  , entityData     :: !Value  -- JSON
  , relationships  :: !(Vector Relationship)
  }

-- | Project CompleteBrand → KG entities
projectToEntities :: CompleteBrand -> Vector CompassEntity
projectToEntities brand = V.concat
  [ V.singleton (brandEntity brand)
  , V.map paletteEntity (paletteColors (completeBrandPalette brand))
  , V.map fontEntity (typographyFonts (completeBrandTypography brand))
  , V.singleton (voiceEntity (completeBrandVoice brand))
  , V.concatMap toneAttributeEntities (brandVoiceAttributes (completeBrandVoice brand))
  ]
```

### 4.2 COMPASS → MAESTRO

```haskell
-- COMPASS/nix/haskell/compass-maestro/src/Compass/Maestro/BrandContext.hs

-- | Fetch brand context for agent
fetchBrandContext :: UUID -> IO (Either BrandError AgentBrandContext)

-- | Inject into agent system prompt
injectBrandContext :: AgentBrandContext -> SystemPrompt -> SystemPrompt
injectBrandContext ctx prompt = prompt
  { promptSystem = T.unlines
      [ promptSystem prompt
      , ""
      , "## Brand Voice Requirements"
      , ""
      , "You are writing for " <> abcBrandName ctx <> "."
      , ""
      , abcVoiceBePrompt ctx
      , abcVoiceNeverBe ctx
      , ""
      , "Preferred terms: " <> T.intercalate ", " (V.toList (abcPreferredTerms ctx))
      , "Forbidden terms: " <> T.intercalate ", " (V.toList (abcForbiddenTerms ctx))
      ]
  }
```

### 4.3 HYDROGEN ← COMPASS

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
│   ├── Pipeline.lean       (graded monads, co-effects)
│   ├── Continuity/         (co-effect algebra — SHARED)
│   │   └── *.lean
│   ├── Cornell/            (wire format proofs)
│   │   └── *.lean
│   ├── Sigil/              (binary protocol)
│   │   └── Sigil.lean
│   └── Brand/              (brand invariants)
│       ├── Typography.lean  ← HAS SORRY
│       ├── Voice.lean       ← HAS SORRY
│       └── Brand.lean       ← MISSING

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

# Build all Haskell
cd haskell && cabal build all

# Run tests
cd haskell && cabal test all

# Build Lean4 proofs
cd lean && lake build

# Run scraper (requires Node)
cd scraper && npm install && npm run dev
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

# FOUNDRY
(cd foundry && nix develop -c bash -c "cd haskell && cabal build all")

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

- [ ] Enable `foundry-scraper` in `cabal.project`
- [ ] Create `CompleteBrand` unified type
- [ ] Port missing atoms from HYDROGEN (Layout, UIElements, Modes, etc.)
- [ ] Create `BrandOntology`, `BrandHierarchy`
- [ ] Create `AgentContext` for MAESTRO
- [ ] Create COMPASS export module
- [ ] Fix Lean4 sorries (Typography:212, Voice:166)
- [ ] Create `Brand.lean` compound proofs

### 7.2 HYDROGEN Tasks

- [ ] Verify Schema alignment with FOUNDRY types
- [ ] Create brand dashboard components
- [ ] Create brand diff viewer
- [ ] Create export UI

### 7.3 COMPASS Tasks

- [ ] Add brand entity types to knowledge graph schema
- [ ] Create NDJSON import handler
- [ ] Create `AgentBrandContext` service
- [ ] Integrate with MAESTRO agent injection
- [ ] Add brand context gRPC endpoint

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

*Document generated: 2026-02-26*
*Status: APPROVED FOR IMPLEMENTATION*

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                            // foundry // alignment
                                                              // straylight/2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
