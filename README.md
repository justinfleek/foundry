# FOUNDRY

**SMART Brand Ingestion Engine**

> Transform any website into a machine-readable brand specification with proven invariants.

```
URL  -->  Playwright  -->  ZMQ  -->  Haskell Extractors  -->  CompleteBrand  -->  COMPASS
          (scrape)              (Color, Type, Voice...)        (18+ fields)    (knowledge graph)
```

---

## What is FOUNDRY?

FOUNDRY is a **production-grade brand extraction pipeline** that:

1. **Scrapes** websites using Playwright in sandboxed environments
2. **Extracts** colors, typography, spacing, voice/tone from CSS/HTML/copy
3. **Composes** a typed `CompleteBrand` with 18+ semantic fields
4. **Exports** to COMPASS knowledge graph for AI agent consumption
5. **Proves** invariants in Lean4 (OKLCH bounds, scale monotonicity, etc.)

Built for [MAESTRO](https://github.com/straylight/compass) - a swarm of 64 AI agents that need pixel-perfect brand reproduction from pure data.

---

## Quick Start

### Prerequisites

- **Nix** (with flakes enabled) - handles all dependencies
- **Node.js 20+** - for TypeScript scraper
- **Chromium** - provided by Nix

### 1. Enter Development Environment

```bash
cd foundry
nix develop
```

This provides:
- GHC 9.12.2 with all Haskell dependencies
- Lean4 4.15.0 (via elan)
- PureScript 0.15.15 + Spago
- ZeroMQ, Playwright, DuckDB, PostgreSQL bindings

### 2. Build Everything

```bash
# Build Haskell packages
cd haskell && cabal build all

# Build TypeScript scraper
cd ../scraper && npm install && npm run build

# Build Lean4 proofs (optional)
cd ../lean && lake build
```

### 3. Run the Pipeline

**Terminal 1 - Start the Scraper Server:**

```bash
cd scraper

# Set Chromium path (Nix provides this)
export PLAYWRIGHT_CHROMIUM_PATH=$(which chromium)

# Start ZMQ server on port 5555
npm run start
```

**Terminal 2 - Scrape a Brand:**

```bash
cd haskell

# Scrape a website
cabal run foundry-scrape -- --url https://linear.app

# Or specify a custom endpoint
cabal run foundry-scrape -- --url https://coca-cola.com --endpoint tcp://127.0.0.1:5555
```

### 4. Run Tests

```bash
cd haskell && cabal test all
```

Expected output: **232 tests passing** across 4 packages.

---

## Architecture

```
foundry/
├── lean/                    # Lean4 - Proofs & Invariants
│   └── Foundry/
│       ├── Brand/           # Brand schema proofs
│       ├── Cornell/         # Wire format proofs (Git, HTTP/2, ZMTP, Protobuf)
│       ├── Pipeline/        # Graded monad definitions
│       └── Sigil/           # Binary protocol proofs
│
├── haskell/                 # Haskell - Backend Runtime
│   ├── foundry-core/        # Core types, graded monads, brand schemas
│   ├── foundry-extract/     # Brand extraction (color, type, spacing, voice)
│   ├── foundry-scraper/     # Playwright ZMQ client
│   └── foundry-storage/     # HAMT cache, DuckDB, PostgreSQL
│
├── scraper/                 # TypeScript - Playwright Scraper
│   └── src/
│       ├── scraper.ts       # Page scraping logic
│       ├── server.ts        # ZMQ ROUTER server
│       └── types.ts         # Protocol types (matches Haskell)
│
├── src/                     # PureScript - Brand Schemas
│   └── Brand/               # Hydrogen atom definitions
│
└── docs/                    # Documentation
    ├── SMART_BRAND_FRAMEWORK.md
    ├── BRAND_INGESTION_ARCHITECTURE.md
    └── TECHNICAL_SPECIFICATIONS.md
```

---

## The SMART Framework

FOUNDRY implements the **SMART Brand Framework** - a methodology for encoding brand guidelines into machine-readable specifications:

| Letter | Meaning | Implementation |
|--------|---------|----------------|
| **S** | Story-driven | Strategic layer: mission, values, personality, voice |
| **M** | Memorable | Consistent visual tokens: colors, typography, spacing |
| **A** | Agile | Adapts to context: light/dark modes, responsive breakpoints |
| **R** | Responsive | Scales correctly: type scales, spacing systems, grid |
| **T** | Targeted | AI-optimized: IS/NOT constraints, WCAG compliance |

### Two-Tier Architecture

**Strategic Layer** (extracted from copy, requires LLM assistance):
- Brand Overview, Mission, Values
- Voice & Tone (IS/NOT pairs)
- Taglines, Personality Traits

**Execution Layer** (extracted from CSS/HTML):
- Palette (OKLCH colors with semantic roles)
- Typography (font stacks, scales, weights)
- Spacing (base unit, scale ratio)
- Layout (grid, breakpoints, containers)
- Logo (variants, clear space, sizing)

---

## Core Types

### CompleteBrand (18+ fields)

The complete brand specification consumed by MAESTRO agents:

```haskell
data CompleteBrand = CompleteBrand
  { cbIdentity      :: !BrandIdentity      -- UUID5, domain, name
  , cbPalette       :: !ColorPalette       -- OKLCH colors, roles
  , cbTypography    :: !Typography         -- Fonts, scales, weights
  , cbSpacing       :: !Spacing            -- Base, ratio, scale
  , cbVoice         :: !BrandVoice         -- Tone, vocabulary, traits
  , cbOverview      :: !BrandOverview      -- Mission, values, story
  , cbStrategy      :: !BrandStrategy      -- Positioning, audience
  , cbTaglines      :: ![Tagline]          -- Primary, secondary
  , cbEditorial     :: !Editorial          -- Contact, social, legal
  , cbCustomers     :: ![CustomerPersona]  -- Target personas
  , cbLogo          :: !LogoSpecification  -- Variants, rules
  , cbLayout        :: !LayoutSystem       -- Grid, breakpoints
  , cbImagery       :: !ImageryGuidelines  -- Photography, illustration
  , cbMaterial      :: !MaterialSystem     -- Elevation, shadows
  , cbThemes        :: !ThemeSet           -- Light, dark, contrast
  , cbHierarchy     :: !(Maybe BrandHierarchy)  -- Parent/sub-brands
  , cbProvenance    :: !Provenance         -- SHA256, timestamps
  }
```

### BrandExtractionResult (from scraper)

Raw data extracted from websites before composition:

```haskell
data BrandExtractionResult = BrandExtractionResult
  { berColors     :: ![ExtractedColor]     -- All CSS colors found
  , berTypography :: !ExtractedTypography  -- Font faces, sizes
  , berSpacing    :: !ExtractedSpacing     -- Margin/padding values
  , berVoice      :: !ExtractedVoice       -- Text content analysis
  , berAssets     :: ![ExtractedAsset]     -- Images, SVGs, fonts
  }
```

---

## Extraction Pipeline

### Stage 1: Scrape (TypeScript + Playwright)

```typescript
// Captures:
// - All stylesheets (inline + external)
// - Computed styles on key elements
// - Text content for voice analysis
// - Asset URLs (images, fonts, SVGs)

const result = await scrapeBrand(page, url);
```

### Stage 2: Extract (Haskell)

```haskell
-- Color extraction: CSS parsing, OKLCH conversion, clustering
palette <- extractPalette cssRules

-- Typography extraction: font detection, scale inference
typography <- extractTypography fontFaces computedStyles

-- Spacing extraction: margin/padding analysis, ratio detection
spacing <- extractSpacing computedStyles

-- Voice extraction: NLP analysis, tone classification
voice <- extractVoice textBlocks
```

### Stage 3: Compose (Haskell)

```haskell
-- Combine extractions into CompleteBrand
completeBrand <- toCompleteBrand domain extractionResult

-- Generate intelligent defaults for strategic layer
-- (mission, values, taglines - require LLM for real data)
```

### Stage 4: Export (Haskell -> COMPASS)

```haskell
-- Convert to knowledge graph entities
ontology <- brandToOntology completeBrand

-- Export as newline-delimited JSON
ndjson <- ontologyToNDJSON ontology

-- Push to COMPASS via ZMQ
pushToCompass ndjson
```

---

## Usage Examples

### Extract Brand from URL

```bash
# Basic extraction
cabal run foundry-scrape -- --url https://linear.app

# Output includes:
# - Color palette (primary, secondary, accent, semantic)
# - Typography (font families, scale, weights)
# - Spacing system (base, ratio)
# - Voice analysis (tone, vocabulary)
```

### Programmatic Usage (Haskell)

```haskell
import Foundry.Extract (composeBrand)
import Foundry.Extract.Compose (toCompleteBrand)
import Foundry.Core.Brand.Ontology (brandToOntology, ontologyToNDJSON)

-- Extract and compose
extractionResult <- composeBrand scrapeResponse
completeBrand <- toCompleteBrand "example.com" extractionResult

-- Export to COMPASS
let ontology = brandToOntology completeBrand
let ndjson = ontologyToNDJSON ontology
```

### Use with MAESTRO Agents

```haskell
import Foundry.Core.Brand.AgentContext (brandContext, formatSystemPrompt)

-- Create agent context from brand
let ctx = brandContext completeBrand

-- Generate system prompt for agent
let prompt = formatSystemPrompt ctx agentRole

-- Agent now has:
-- - BE: (approved behaviors)
-- - NEVER BE: (forbidden behaviors)
-- - Color tokens, typography rules, voice constraints
```

---

## Test Brands

FOUNDRY has been validated against these production brands:

| Brand | Colors | Fonts | Assets | Status |
|-------|--------|-------|--------|--------|
| jbreenconsulting.com | 50+ | 4 | 50+ | Verified |
| linear.app | 20+ | 9 | 100+ | Verified |
| openrouter.ai | 15+ | 9 | 70+ | Verified |
| coca-cola.com | 30+ | 10 | 76+ | Verified |

---

## Lean4 Proofs

FOUNDRY proves critical invariants in Lean4:

### Brand Invariants
- **OKLCH bounds**: L in [0,1], C in [0,0.4], H in [0,360)
- **Typography scale**: Monotonically increasing sizes
- **Spacing ratio**: Greater than 1.0, typically golden ratio
- **Voice traits**: Non-empty, IS/NOT vocabulary disjoint

### Wire Format Proofs (Cornell)
- **Git pack format**: Roundtrip, deterministic parsing
- **HTTP/2 HPACK**: Header compression correctness
- **ZMTP**: ZeroMQ protocol state machines
- **Protobuf**: Varint encoding, field ordering

### Building Proofs

```bash
cd lean
lake build Foundry.Cornell.Proofs  # Wire formats
lake build Foundry.Sigil.Sigil     # Binary protocol (18 theorems)
lake build Foundry.Pipeline        # Graded monads
```

---

## Storage Architecture

FOUNDRY uses a 3-tier storage hierarchy:

```
┌─────────────────────────────────────────────────────────────────┐
│  L1: HAMT Cache (In-Memory)                                    │
│  - Hash Array Mapped Trie                                       │
│  - O(log32 n) lookups                                          │
│  - Brand data during active session                            │
├─────────────────────────────────────────────────────────────────┤
│  L2: DuckDB (Local)                                            │
│  - Columnar analytics                                          │
│  - Brand history, diffs                                        │
│  - Fast aggregations                                           │
├─────────────────────────────────────────────────────────────────┤
│  L3: PostgreSQL (Persistent)                                   │
│  - Source of truth                                             │
│  - Full brand catalog                                          │
│  - ACID guarantees                                             │
└─────────────────────────────────────────────────────────────────┘
```

---

## Security Model

### Sandboxing
- Playwright runs in **gVisor/Bubblewrap** containers
- No filesystem access outside designated paths
- Network restricted to target domains

### Determinism
- **UUID5** for all identifiers (reproducible from domain + content)
- No randomness (forbidden: `randomIO`, `UUID4`, `getCurrentTime` for non-provenance)
- SHA256 provenance for all extracted data

### Forbidden Patterns
See `CLAUDE.md` for complete list. Key prohibitions:
- No `undefined`, `error`, `panic` (bottoms)
- No `head`, `tail`, `!!` (partial functions)
- No `unsafePerformIO`, `unsafeCoerce` (escape hatches)

---

## Configuration

### Environment Variables

```bash
# Chromium path (required for scraper)
export PLAYWRIGHT_CHROMIUM_PATH=/path/to/chromium

# ZMQ endpoint (optional, default: tcp://127.0.0.1:5555)
export FOUNDRY_ZMQ_ENDPOINT=tcp://localhost:5555

# Log level (optional)
export FOUNDRY_LOG_LEVEL=debug
```

### Scraper Config

```haskell
data ScraperConfig = ScraperConfig
  { scEndpoint :: !Text           -- ZMQ endpoint
  , scTimeout  :: !Int            -- Request timeout (ms)
  , scRetries  :: !Int            -- Retry count
  }

defaultConfig :: ScraperConfig
defaultConfig = ScraperConfig
  { scEndpoint = "tcp://127.0.0.1:5555"
  , scTimeout  = 30000
  , scRetries  = 3
  }
```

---

## Development

### Adding a New Extractor

1. Create `haskell/foundry-extract/src/Foundry/Extract/NewExtractor.hs`
2. Implement `extract :: ScrapeResponse -> Either Error NewType`
3. Add to `composeBrand` in `Compose.hs`
4. Add tests in `test/Test/Foundry/Extract/NewExtractor.hs`
5. Update `foundry-extract.cabal`

### Adding a New Brand Field

1. Add field to `CompleteBrand` in `Complete.hs`
2. Add default builder in `Compose.hs`
3. Add to ontology export in `Ontology.hs`
4. Add Aeson instances for JSON serialization
5. Add tests

### Code Standards

- **500 lines max** per file
- **Explicit imports** (no `(..)` patterns)
- **StrictData** on all records
- **No stubs or TODOs** in committed code
- **No deletion** of "unused" code (it's incomplete, not unnecessary)

---

## Troubleshooting

### "Connection refused" on ZMQ

The TypeScript scraper server isn't running:

```bash
cd scraper && npm run start
```

### "Chromium not found"

Set the Playwright chromium path:

```bash
export PLAYWRIGHT_CHROMIUM_PATH=$(which chromium)
# Or from Nix store:
export PLAYWRIGHT_CHROMIUM_PATH=/nix/store/.../bin/chromium
```

### Tests failing with "libzmq not found"

Enter the Nix development shell:

```bash
nix develop
```

### Lean4 "unknown identifier" errors

Update Lean toolchain and rebuild mathlib:

```bash
elan update
cd lean && lake update && lake build
```

---

## Documentation

| Document | Description |
|----------|-------------|
| [SMART_BRAND_FRAMEWORK.md](docs/SMART_BRAND_FRAMEWORK.md) | Complete framework specification |
| [BRAND_INGESTION_ARCHITECTURE.md](docs/BRAND_INGESTION_ARCHITECTURE.md) | System architecture |
| [BRAND_SCHEMA.md](docs/BRAND_SCHEMA.md) | Schema documentation |
| [TECHNICAL_SPECIFICATIONS.md](docs/TECHNICAL_SPECIFICATIONS.md) | Type definitions, algorithms |
| [SIGIL_PROTOCOL.md](docs/SIGIL_PROTOCOL.md) | Binary protocol specification |
| [CLAUDE.md](CLAUDE.md) | AI assistant coding standards |

---

## Roadmap

### Completed
- [x] TypeScript Playwright scraper
- [x] ZMQ integration (TypeScript ROUTER <-> Haskell DEALER)
- [x] Color extraction (CSS parsing, OKLCH conversion, clustering)
- [x] Typography extraction (font detection, scale inference)
- [x] Spacing extraction (margin/padding analysis)
- [x] Voice extraction (NLP analysis, tone classification)
- [x] CompleteBrand composer (18+ fields)
- [x] COMPASS ontology export (NDJSON)
- [x] 232 passing tests

### In Progress
- [ ] UIElements extraction (buttons, inputs, depth)
- [ ] GraphicElements extraction (patterns, textures)
- [ ] Logo extraction (SVG analysis, variants)
- [ ] Layout extraction (grid detection)

### Planned
- [ ] LLM-assisted voice mining (IS/NOT pairs)
- [ ] Theme mode detection (light/dark stylesheets)
- [ ] Worker pool scaling (ZMQ DEALER/ROUTER)
- [ ] Prometheus metrics
- [ ] WebGPU brand renderer (via HYDROGEN)

---

## Related Projects

- **[HYDROGEN](https://github.com/straylight/hydrogen)** - PureScript UI framework with WebGPU rendering
- **[COMPASS](https://github.com/straylight/compass)** - Knowledge graph for MAESTRO AI agents
- **[MAESTRO](https://github.com/straylight/maestro)** - 64-agent AI swarm orchestration

---

## License

BSD-3-Clause

---

## Contributing

1. Read `CLAUDE.md` for coding standards
2. Ensure all tests pass: `cd haskell && cabal test all`
3. No TODOs, no stubs, no deletion of "unused" code
4. Explicit imports only

---

*Built by Straylight Software, 2026*
