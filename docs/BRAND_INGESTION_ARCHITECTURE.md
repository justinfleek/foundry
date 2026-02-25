━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                          // brand // ingestion // architecture
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "A brand is not a logo. A brand is a system — a coherent set of decisions
    that express a singular identity across every touchpoint."

                                                              — BRAND_SCHEMA.md

# BRAND INGESTION PIPELINE

## Purpose

Build a **brand ingestion pipeline** that scrapes websites and produces typed,
proven design language tokens. This is a real analysis engine that:

1. Scrapes a website (via Playwright in sandboxed gVisor/Bubblewrap)
2. Extracts colors, typography, spacing, voice/tone from CSS/HTML/copy
3. Produces a **Brand** compound type in the Hydrogen Schema with proven invariants
4. Stores brands in a 3-tier architecture: HAMT (L1 cache) → DuckDB (L2) → PostgreSQL (L3)

────────────────────────────────────────────────────────────────────────────────
                                                                 // table // of
                                                                     // contents
────────────────────────────────────────────────────────────────────────────────

1. System Overview
2. Dependency Graph (ADT)
3. Component Architecture
4. Lean4 Proof Requirements
5. Data Flow
6. Storage Architecture
7. Security Model
8. Implementation Phases
9. Open Questions

────────────────────────────────────────────────────────────────────────────────

════════════════════════════════════════════════════════════════════════════════
                                                         // 1 // system overview
════════════════════════════════════════════════════════════════════════════════

## 1. System Overview

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              INGESTION LAYER                                    │
│                                                                                 │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐             │
│  │   Playwright    │    │   SearXNG       │    │   Direct URL    │             │
│  │   (Sandboxed)   │    │   (Discovery)   │    │   (Manual)      │             │
│  └────────┬────────┘    └────────┬────────┘    └────────┬────────┘             │
│           │                      │                      │                       │
│           └──────────────────────┼──────────────────────┘                       │
│                                  ▼                                              │
│                    ┌─────────────────────────┐                                  │
│                    │  ZMQ Message Bus        │                                  │
│                    │  (Scrape Results)       │                                  │
│                    └────────────┬────────────┘                                  │
└─────────────────────────────────┼───────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              ANALYSIS LAYER (Haskell)                           │
│                                                                                 │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐             │
│  │  Color          │    │  Typography     │    │  Voice/Tone     │             │
│  │  Extractor      │    │  Extractor      │    │  Analyzer       │             │
│  └────────┬────────┘    └────────┬────────┘    └────────┬────────┘             │
│           │                      │                      │                       │
│  ┌────────┴────────┐    ┌────────┴────────┐    ┌────────┴────────┐             │
│  │  Spacing        │    │  Layout         │    │  Logo/Asset     │             │
│  │  Analyzer       │    │  Analyzer       │    │  Detector       │             │
│  └────────┬────────┘    └────────┬────────┘    └────────┬────────┘             │
│           │                      │                      │                       │
│           └──────────────────────┼──────────────────────┘                       │
│                                  ▼                                              │
│                    ┌─────────────────────────┐                                  │
│                    │  Brand Composer         │                                  │
│                    │  (Compound Type)        │                                  │
│                    └────────────┬────────────┘                                  │
└─────────────────────────────────┼───────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              PROOF LAYER (Lean4)                                │
│                                                                                 │
│  ┌─────────────────────────────────────────────────────────────────────────┐   │
│  │  Hydrogen.Schema.Brand.*                                                │   │
│  │                                                                         │   │
│  │  Identity.lean   — UUID5 determinism, domain validation                 │   │
│  │  Palette.lean    — OKLCH gamut bounds, semantic roles                   │   │
│  │  Typography.lean — FontWeight 100-900, scale monotonicity               │   │
│  │  Spacing.lean    — Base positive, ratio > 1                             │   │
│  │  Voice.lean      — Traits non-empty, vocabulary disjoint                │   │
│  │  Provenance.lean — SHA256 determinism, timestamp ordering               │   │
│  └─────────────────────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              STORAGE LAYER                                      │
│                                                                                 │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐             │
│  │  L1: HAMT       │───▶│  L2: DuckDB     │───▶│  L3: PostgreSQL │             │
│  │  (Hot Cache)    │    │  (Analytical)   │    │  (Durable)      │             │
│  │  ~1ms           │    │  ~10ms          │    │  ~100ms         │             │
│  └─────────────────┘    └─────────────────┘    └─────────────────┘             │
│                                                                                 │
│  Keys: UUID5(domain) — deterministic, content-addressed                         │
└─────────────────────────────────────────────────────────────────────────────────┘
```

════════════════════════════════════════════════════════════════════════════════
                                                    // 2 // dependency graph adt
════════════════════════════════════════════════════════════════════════════════

## 2. Dependency Graph (ADT)

### 2.1 Type Hierarchy

The Brand type is a compound composed of molecules, which are composed of atoms.
This follows the Hydrogen Schema atomic architecture.

```
                              ┌─────────────┐
                              │   Brand     │  ← Compound
                              └──────┬──────┘
                                     │
        ┌────────────┬───────────────┼───────────────┬────────────┐
        │            │               │               │            │
        ▼            ▼               ▼               ▼            ▼
   ┌─────────┐ ┌──────────┐  ┌────────────┐  ┌─────────┐  ┌────────────┐
   │Identity │ │ Palette  │  │Typography  │  │ Spacing │  │   Voice    │  ← Molecules
   └────┬────┘ └────┬─────┘  └─────┬──────┘  └────┬────┘  └─────┬──────┘
        │           │              │              │             │
        ▼           ▼              ▼              ▼             ▼
   ┌─────────┐ ┌─────────┐  ┌───────────┐  ┌──────────┐  ┌───────────┐
   │UUID5    │ │OKLCH    │  │FontWeight │  │SpacingPx │  │Tone       │
   │Domain   │ │Role     │  │FontFamily │  │Ratio     │  │Trait      │
   │Name     │ │Contrast │  │TypeScale  │  │Base      │  │Vocabulary │
   └─────────┘ └─────────┘  └───────────┘  └──────────┘  └───────────┘  ← Atoms
```

### 2.2 ADT Definitions (Lean4)

```lean
-- ATOMS (primitive bounded values)
structure UUID5 where bytes : ByteArray; len_eq : bytes.size = 16
structure Domain where value : String; valid : value.contains '.' ∧ value.length > 0
structure BrandName where value : String; bounded : 1 ≤ value.length ∧ value.length ≤ 256
structure OKLCH where L : Float; C : Float; H : Float; gamut : 0 ≤ L ∧ L ≤ 1 ∧ ...
structure FontWeight where val : Nat; bounded : 100 ≤ val ∧ val ≤ 900 ∧ val % 100 = 0
structure SpacingUnit where px : Float; positive : px > 0

-- MOLECULES (composed atoms with additional invariants)
structure Identity where
  uuid : UUID5
  domain : Domain
  name : BrandName
  deterministic : uuid = uuid5 domain.value name.value

structure Palette where
  colors : List (OKLCH × Role)
  has_primary : ∃ c, (c, Role.primary) ∈ colors
  roles_unique : ∀ c1 c2 r, (c1, r) ∈ colors → (c2, r) ∈ colors → c1 = c2

structure Typography where
  headingFamily : FontFamily
  bodyFamily : FontFamily
  scale : TypeScale
  monotonic : ∀ l1 l2, l1 < l2 → scale.sizeAt l1 < scale.sizeAt l2

structure Spacing where
  base : SpacingUnit
  ratio : Float
  ratio_gt_one : ratio > 1

structure Voice where
  tone : Tone
  traits : TraitSet
  vocabulary : Vocabulary
  traits_nonempty : traits.length > 0
  vocab_disjoint : ∀ t, t ∈ vocabulary.preferred → t ∉ vocabulary.prohibited

-- COMPOUND (complete brand with provenance)
structure Brand where
  identity : Identity
  palette : Palette
  typography : Typography
  spacing : Spacing
  voice : Voice
  provenance : Provenance
  -- Compound invariants
  palette_accessible : ∀ (fg bg : OKLCH), (fg, _) ∈ palette.colors → 
                       (bg, _) ∈ palette.colors → contrastRatio fg bg ≥ 4.5
```

### 2.3 Proof Dependencies

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                           PROOF DEPENDENCY GRAPH                             │
├──────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Mathlib.Tactic ──────────────────────────────────────────────────────────┐  │
│       │                                                                   │  │
│       ▼                                                                   │  │
│  Mathlib.Data.Real.Basic                                                  │  │
│       │                                                                   │  │
│       ├───────────────────┬──────────────────┬─────────────────┐          │  │
│       ▼                   ▼                  ▼                 ▼          │  │
│  Identity.lean      Palette.lean      Typography.lean    Spacing.lean    │  │
│  (UUID5 axioms)     (OKLCH bounds)    (Float pow axioms) (Float axioms)  │  │
│       │                   │                  │                 │          │  │
│       │                   │                  │                 │          │  │
│       └─────────────────┬─┴──────────────────┴─────────────────┘          │  │
│                         ▼                                                 │  │
│                   Voice.lean                                              │  │
│                   (List eraseDups)                                        │  │
│                         │                                                 │  │
│                         ▼                                                 │  │
│                   Provenance.lean                                         │  │
│                   (SHA256, Timestamps)                                    │  │
│                         │                                                 │  │
│                         ▼                                                 │  │
│                   Brand.lean (TO BE CREATED)                              │  │
│                   (Compound composition)                                  │  │
│                                                                           │  │
└───────────────────────────────────────────────────────────────────────────┘
```

════════════════════════════════════════════════════════════════════════════════
                                                 // 3 // component architecture
════════════════════════════════════════════════════════════════════════════════

## 3. Component Architecture

### 3.1 Package Structure

```
compass-brand/                          # New Haskell package
├── src/
│   ├── Compass/
│   │   └── Brand/
│   │       ├── Types.hs                # Core ADTs (generated from Lean4)
│   │       ├── Scraper/
│   │       │   ├── Playwright.hs       # ZMQ client to sandboxed scraper
│   │       │   └── Types.hs            # Scrape result types
│   │       ├── Extract/
│   │       │   ├── Color.hs            # CSS color extraction
│   │       │   ├── Typography.hs       # Font stack analysis
│   │       │   ├── Spacing.hs          # Spacing pattern detection
│   │       │   ├── Voice.hs            # NLP tone analysis
│   │       │   └── Layout.hs           # Grid/breakpoint detection
│   │       ├── Compose.hs              # Brand compound assembly
│   │       ├── Storage/
│   │       │   ├── HAMT.hs             # L1 in-memory cache
│   │       │   ├── DuckDB.hs           # L2 analytical queries
│   │       │   └── Postgres.hs         # L3 durable storage
│   │       └── Export/
│   │           ├── PureScript.hs       # Generate PS module
│   │           ├── CSS.hs              # Generate CSS variables
│   │           └── Figma.hs            # Generate Figma tokens
├── test/
│   ├── Hedgehog/                       # Property tests
│   └── Golden/                         # Golden tests against known brands
└── compass-brand.cabal

hydrogen/proofs/Hydrogen/Schema/Brand/  # Lean4 proofs (existing)
├── Identity.lean
├── Palette.lean
├── Typography.lean
├── Spacing.lean
├── Voice.lean
├── Provenance.lean
└── Brand.lean                          # TO BE CREATED: compound proofs

scraper/                                # Sandboxed scraper (thin JS)
├── src/
│   ├── index.ts                        # Playwright entry
│   ├── extract.ts                      # DOM extraction
│   └── zmq.ts                          # ZMQ publisher
├── sandbox/
│   ├── bubblewrap.sh                   # Bubblewrap wrapper
│   └── gvisor.nix                      # gVisor sandbox config
└── package.json
```

### 3.2 Haskell Package Dependencies

```
compass-brand
├── compass-core           # Event sourcing, CAS
├── zeromq4-haskell        # ZMQ messaging
├── duckdb-hs              # DuckDB bindings  
├── postgresql-simple      # PostgreSQL
├── megaparsec             # CSS parsing
├── text                   # Text processing
├── uuid                   # UUID5 generation
├── cryptonite             # SHA256
├── unordered-hamt         # HAMT implementation
├── hedgehog               # Property testing
└── haskemathesis          # Lean4 integration (optional)
```

### 3.3 Message Flow (ZMQ)

```
┌─────────────────┐          ┌─────────────────┐          ┌─────────────────┐
│  Scraper (JS)   │          │  ZMQ Broker     │          │  Analyzer (HS)  │
│  (Sandboxed)    │          │  (ROUTER/DEALER)│          │                 │
└────────┬────────┘          └────────┬────────┘          └────────┬────────┘
         │                            │                            │
         │  PUB: ScrapeResult         │                            │
         │ ─────────────────────────▶ │                            │
         │                            │  PUSH: ScrapeResult        │
         │                            │ ─────────────────────────▶ │
         │                            │                            │
         │                            │                   ┌────────┴────────┐
         │                            │                   │ Extract colors  │
         │                            │                   │ Extract fonts   │
         │                            │                   │ Extract spacing │
         │                            │                   │ Analyze voice   │
         │                            │                   └────────┬────────┘
         │                            │                            │
         │                            │  PUSH: Brand               │
         │                            │ ◀───────────────────────── │
         │                            │                            │
         │                            │  (Store to L1/L2/L3)       │
         │                            │                            │
```

### 3.4 Scrape Result Schema

```haskell
-- Sent from JS scraper to Haskell analyzer
data ScrapeResult = ScrapeResult
  { srUrl         :: !Text
  , srTimestamp   :: !UTCTime
  , srHtml        :: !Text
  , srCss         :: ![CSSSource]       -- Inline + external stylesheets
  , srComputed    :: ![ComputedStyle]   -- getComputedStyle for key elements
  , srFonts       :: ![FontFace]        -- @font-face declarations
  , srImages      :: ![ImageAsset]      -- Logo candidates
  , srMetadata    :: !PageMetadata      -- <title>, <meta>, Open Graph
  , srTextContent :: !Text              -- Visible text (for voice analysis)
  }

data CSSSource = CSSSource
  { cssOrigin  :: !CSSOrigin           -- Inline | External URL
  , cssContent :: !Text
  }

data ComputedStyle = ComputedStyle
  { csSelector    :: !Text             -- CSS selector
  , csProperties  :: !(Map Text Text)  -- property -> value
  }
```

════════════════════════════════════════════════════════════════════════════════
                                                // 4 // lean4 proof requirements
════════════════════════════════════════════════════════════════════════════════

## 4. Lean4 Proof Requirements

### 4.1 Current Status

| File             | Lines | Sorry | Axioms | Status      |
|------------------|-------|-------|--------|-------------|
| Identity.lean    | 344   | 0     | 4      | ✓ COMPLETE  |
| Palette.lean     | 463   | 0     | 0      | ✓ COMPLETE  |
| Typography.lean  | 499   | **1** | 5      | ✗ HAS SORRY |
| Spacing.lean     | 392   | 0     | 6      | ✓ COMPLETE  |
| Voice.lean       | 447   | **1** | 0      | ✗ HAS SORRY |
| Provenance.lean  | 395   | 0     | 3      | ✓ COMPLETE  |
| Brand.lean       | 0     | -     | -      | NOT CREATED |

### 4.2 Sorry #1: Typography.lean:212

**Location:** `Typography.lean`, line 212
**Theorem:** `TypeScale.monotonic`
**Statement:**
```lean
theorem monotonic (scale : TypeScale) (l1 l2 : Int) (h : l1 < l2) :
    (sizeAt scale l1).px < (sizeAt scale l2).px
```

**What needs proving:**
- `base * ratio^l1 < base * ratio^l2`
- Given: `ratio > 1`, `l1 < l2`, `base > 0`

**Proof strategy:**
1. The existing `pow_monotonic` axiom already states:
   ```lean
   axiom pow_monotonic : ∀ (r : Float) (a b : Float), r > 1 → a < b → 
     Float.pow r a < Float.pow r b
   ```
2. We need to apply `pow_monotonic` with `r = scale.ratio`, `a = l1`, `b = l2`
3. Then multiply both sides by `scale.base.px` (positive) preserving inequality
4. This requires `float_mul_pos_lt` or similar lemma

**Fix approach:**
```lean
theorem monotonic (scale : TypeScale) (l1 l2 : Int) (h : l1 < l2) :
    (sizeAt scale l1).px < (sizeAt scale l2).px := by
  simp only [sizeAt]
  have h_pow : Float.pow scale.ratio (Float.ofInt l1) < Float.pow scale.ratio (Float.ofInt l2) :=
    pow_monotonic scale.ratio (Float.ofInt l1) (Float.ofInt l2) scale.ratio_gt_one (by exact_mod_cast h)
  exact float_mul_pos_lt scale.base.positive h_pow
```

**New axiom needed:**
```lean
axiom float_mul_pos_lt : ∀ (c a b : Float), c > 0 → a < b → c * a < c * b
```

### 4.3 Sorry #2: Voice.lean:166

**Location:** `Voice.lean`, line 166
**Function:** `TraitSet.fromList`
**Statement:**
```lean
def fromList (ts : List Trait) (h : ts.length > 0) : TraitSet :=
  let deduped := ts.eraseDups
  ⟨deduped, by
    simp only [List.length_eraseDups]
    sorry, -- Requires List.eraseDups_length_pos_of_length_pos
   by simp⟩
```

**What needs proving:**
- `ts.eraseDups.length > 0` given `ts.length > 0`

**Proof strategy:**
1. `eraseDups` removes duplicates but preserves at least one element
2. For non-empty list, `eraseDups` is non-empty
3. This is a standard Mathlib lemma or can be proven directly

**Fix approach:**
```lean
theorem eraseDups_length_pos {α : Type*} [DecidableEq α] (l : List α) (h : l.length > 0) :
    l.eraseDups.length > 0 := by
  cases l with
  | nil => simp at h
  | cons x xs => 
    simp only [List.eraseDups_cons]
    split
    · -- x ∈ xs.eraseDups case: xs.eraseDups is non-empty
      assumption
    · -- x ∉ xs.eraseDups case: result has x at head
      simp only [List.length_cons]
      omega
```

**Then in fromList:**
```lean
def fromList (ts : List Trait) (h : ts.length > 0) : TraitSet :=
  let deduped := ts.eraseDups
  ⟨deduped, eraseDups_length_pos ts h, by simp⟩
```

### 4.4 Axiom Classification

**Justified Axioms (External Specifications):**

| Axiom | Justification | Source |
|-------|---------------|--------|
| `uuid5` | UUID5 generation per RFC 4122 | RFC 4122 Section 4.3 |
| `uuid5_deterministic` | UUID5 spec guarantees determinism | RFC 4122 |
| `uuid5_injective` | SHA-1 collision resistance | Cryptographic assumption |
| `sha256` | SHA256 per FIPS 180-4 | FIPS 180-4 |
| `sha256_deterministic` | SHA256 is a pure function | FIPS 180-4 |
| `sha256_injective` | Collision resistance | Cryptographic assumption |

**Research Axioms (Float Arithmetic):**

| Axiom | Status | Notes |
|-------|--------|-------|
| `float_pow_pos` | Research | IEEE 754 pow behavior |
| `float_pow_finite` | Research | Requires range analysis |
| `float_mul_pos` | Research | IEEE 754 multiply |
| `float_mul_finite` | Research | Requires range analysis |
| `pow_monotonic` | Research | Monotonicity of Float.pow |
| `float_mul_pos_lt` | NEEDED | Inequality preservation |

**Note:** Float axioms are "research axioms" because Lean4's `Float` is IEEE 754
which has edge cases (NaN, Inf, denormals). For our domain (positive reals,
finite values), these properties hold but aren't proven in Mathlib for `Float`.

### 4.5 Brand.lean Requirements (TO BE CREATED)

The compound `Brand` type needs proofs for:

1. **Composition validity:**
   - All molecules compose into valid compound
   - No conflicting invariants

2. **Accessibility guarantee:**
   - Primary/secondary contrast ≥ 4.5:1 (WCAG AA)
   - Text on background always readable

3. **Determinism:**
   - Same domain → same UUID5 → same Brand identity
   - Content-addressed by domain

4. **Serialization roundtrip:**
   - `deserialize (serialize brand) = brand`
   - Following Cornell Box pattern from libevring

**Proposed structure:**
```lean
structure Brand where
  identity : Identity
  palette : Palette  
  typography : Typography
  spacing : Spacing
  voice : Voice
  provenance : Provenance
  -- Compound invariants as proof fields (Cornell pattern)
  accessible : palette.meetsWCAG_AA
  deterministic : identity.uuid = uuid5 identity.domain.value identity.name.value
```

════════════════════════════════════════════════════════════════════════════════
                                                              // 5 // data flow
════════════════════════════════════════════════════════════════════════════════

## 5. Data Flow

### 5.1 Ingestion Pipeline

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│ STAGE 1: URL DISCOVERY                                                          │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Input: domain (e.g., "stripe.com")                                             │
│                                                                                 │
│  ┌─────────────┐     ┌─────────────┐     ┌─────────────┐                       │
│  │ SearXNG     │────▶│ Homepage    │────▶│ Subpages    │                       │
│  │ discovery   │     │ detection   │     │ /about      │                       │
│  └─────────────┘     └─────────────┘     │ /brand      │                       │
│                                          │ /press      │                       │
│                                          └─────────────┘                       │
│                                                                                 │
│  Output: List<URL> (homepage + brand-relevant pages)                            │
└─────────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│ STAGE 2: SANDBOXED SCRAPING                                                     │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  ┌─────────────────────────────────────────────────────────────────────────┐   │
│  │ gVisor/Bubblewrap Sandbox                                               │   │
│  │                                                                         │   │
│  │  ┌─────────────┐                                                        │   │
│  │  │ Playwright  │                                                        │   │
│  │  │ Chromium    │                                                        │   │
│  │  └──────┬──────┘                                                        │   │
│  │         │                                                               │   │
│  │         ▼                                                               │   │
│  │  ┌─────────────────────────────────────────────────────────────────┐    │   │
│  │  │ Extract:                                                        │    │   │
│  │  │  - document.styleSheets (all CSS)                               │    │   │
│  │  │  - getComputedStyle() on key elements                           │    │   │
│  │  │  - document.fonts (loaded fonts)                                │    │   │
│  │  │  - <img>, <svg> with logo heuristics                            │    │   │
│  │  │  - innerText (for voice analysis)                               │    │   │
│  │  │  - <meta> tags, Open Graph                                      │    │   │
│  │  └─────────────────────────────────────────────────────────────────┘    │   │
│  │                                                                         │   │
│  └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                 │
│  Output: ScrapeResult (HTML, CSS, computed styles, fonts, images, text)         │
│                                                                                 │
│  → ZMQ PUSH to Haskell analyzer                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│ STAGE 3: EXTRACTION (Haskell)                                                   │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐    │
│  │ Color         │  │ Typography    │  │ Spacing       │  │ Voice         │    │
│  │ Extractor     │  │ Extractor     │  │ Extractor     │  │ Analyzer      │    │
│  ├───────────────┤  ├───────────────┤  ├───────────────┤  ├───────────────┤    │
│  │ Parse CSS     │  │ Parse         │  │ Detect        │  │ NLP           │    │
│  │ color props   │  │ font-family   │  │ margin/pad    │  │ sentiment     │    │
│  │               │  │ font-size     │  │ patterns      │  │ tone          │    │
│  │ Cluster by    │  │ font-weight   │  │               │  │ formality     │    │
│  │ OKLCH         │  │               │  │ Detect grid   │  │               │    │
│  │               │  │ Detect scale  │  │ base unit     │  │ Extract       │    │
│  │ Assign roles  │  │ ratio         │  │               │  │ keywords      │    │
│  │ (frequency)   │  │               │  │ Compute       │  │               │    │
│  │               │  │ Map to        │  │ ratio         │  │ Classify      │    │
│  │ Verify        │  │ FontWeight    │  │               │  │ personality   │    │
│  │ contrast      │  │ enum          │  │               │  │ traits        │    │
│  └───────┬───────┘  └───────┬───────┘  └───────┬───────┘  └───────┬───────┘    │
│          │                  │                  │                  │            │
│          ▼                  ▼                  ▼                  ▼            │
│  ┌───────────────────────────────────────────────────────────────────────┐     │
│  │ Palette         Typography        Spacing           Voice            │     │
│  │ (molecule)      (molecule)        (molecule)        (molecule)       │     │
│  └───────────────────────────────────────────────────────────────────────┘     │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│ STAGE 4: COMPOSITION                                                            │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  ┌───────────────────────────────────────────────────────────────────────┐     │
│  │ Brand Composer                                                        │     │
│  ├───────────────────────────────────────────────────────────────────────┤     │
│  │                                                                       │     │
│  │  1. Generate Identity                                                 │     │
│  │     uuid = UUID5("hydrogen.brand", domain)                            │     │
│  │                                                                       │     │
│  │  2. Validate molecules                                                │     │
│  │     - Palette has primary? ✓                                          │     │
│  │     - Typography scale monotonic? ✓                                   │     │
│  │     - Spacing ratio > 1? ✓                                            │     │
│  │     - Voice traits non-empty? ✓                                       │     │
│  │                                                                       │     │
│  │  3. Verify compound invariants                                        │     │
│  │     - WCAG AA contrast? ✓                                             │     │
│  │     - Vocabulary disjoint? ✓                                          │     │
│  │                                                                       │     │
│  │  4. Compute provenance                                                │     │
│  │     hash = SHA256(serialize(brand))                                   │     │
│  │     timestamp = now()                                                 │     │
│  │                                                                       │     │
│  └───────────────────────────────────────────────────────────────────────┘     │
│                                                                                 │
│  Output: Brand (compound type with proof-carrying invariants)                   │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│ STAGE 5: STORAGE                                                                │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  ┌─────────────────────────────────────────────────────────────────────────┐   │
│  │                                                                         │   │
│  │  L1: HAMT (in-memory)                                                   │   │
│  │      Key: UUID5                                                         │   │
│  │      Value: Brand (serialized)                                          │   │
│  │      TTL: 1 hour                                                        │   │
│  │      ↓ evict                                                            │   │
│  │                                                                         │   │
│  │  L2: DuckDB (analytical)                                                │   │
│  │      Columnar storage                                                   │   │
│  │      Fast aggregation queries                                           │   │
│  │      "All brands using Inter font"                                      │   │
│  │      "Average primary color saturation"                                 │   │
│  │      ↓ persist                                                          │   │
│  │                                                                         │   │
│  │  L3: PostgreSQL (durable)                                               │   │
│  │      JSONB column for Brand                                             │   │
│  │      Full-text search on voice.vocabulary                               │   │
│  │      Foreign keys to user/org                                           │   │
│  │                                                                         │   │
│  └─────────────────────────────────────────────────────────────────────────┘   │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### 5.2 Graded Monad Effect Tracking

Each stage has tracked effects and co-effects:

```haskell
-- Effect grades (what the stage PRODUCES)
data Effect
  = Pure              -- No side effects
  | Network           -- Makes HTTP requests
  | FileSystem        -- Reads/writes files
  | Database          -- Database operations
  | Combined [Effect] -- Multiple effects

-- Co-effect grades (what the stage REQUIRES)
data CoEffect
  = NoRequirements
  | RequiresNetwork
  | RequiresSandbox
  | RequiresCredential Text
  | Combined [CoEffect]

-- Graded monad for pipeline stages
newtype Pipeline (eff :: Effect) (coeff :: CoEffect) a = Pipeline
  { runPipeline :: IO a }

-- Stage types with grades
discover   :: Pipeline 'Network 'RequiresNetwork [URL]
scrape     :: Pipeline 'Network 'RequiresSandbox ScrapeResult  
extract    :: Pipeline 'Pure 'NoRequirements [Molecule]
compose    :: Pipeline 'Pure 'NoRequirements Brand
store      :: Pipeline 'Database 'NoRequirements ()
```

### 5.3 Co-Effect Algebra Laws

The co-effect system must satisfy:

```
1. Idempotency:   satisfy (satisfy r) = satisfy r
2. Monotonicity:  if r₁ ⊆ r₂ then satisfied r₁ → satisfied r₂  
3. Associativity: (r₁ ⊗ r₂) ⊗ r₃ = r₁ ⊗ (r₂ ⊗ r₃)
4. Discharge:     CoEffect → DischargeProof → Bool
```

These laws are proven in Lean4 following the pattern from
`straylight/src/examples/lean-continuity/Continuity.lean`.

════════════════════════════════════════════════════════════════════════════════
                                                    // 6 // storage architecture
════════════════════════════════════════════════════════════════════════════════

## 6. Storage Architecture

### 6.1 Three-Tier Design

| Tier | Technology | Latency | Capacity | Purpose |
|------|------------|---------|----------|---------|
| L1   | HAMT       | ~1ms    | 10K brands | Hot cache for active queries |
| L2   | DuckDB     | ~10ms   | 1M brands | Analytical queries |
| L3   | PostgreSQL | ~100ms  | Unlimited | Durable storage, relationships |

### 6.2 Key Schema

All tiers use UUID5 as the primary key:

```haskell
-- Deterministic key generation
brandKey :: Domain -> UUID5
brandKey domain = uuid5 hydrogenNamespace (encodeUtf8 domain.value)
  where
    hydrogenNamespace = UUID5 "6ba7b810-9dad-11d1-80b4-00c04fd430c8"  -- DNS namespace
```

### 6.3 L1: HAMT (Hash Array Mapped Trie)

```haskell
-- In-memory persistent data structure
data BrandCache = BrandCache
  { bcHAMT    :: !(HAMT UUID5 CachedBrand)
  , bcTTL     :: !NominalDiffTime          -- Default 1 hour
  , bcMaxSize :: !Int                       -- Max entries before eviction
  }

data CachedBrand = CachedBrand
  { cbBrand     :: !Brand
  , cbCachedAt  :: !UTCTime
  , cbAccessCnt :: !Int                     -- LRU tracking
  }

-- O(log32 n) operations
lookup :: UUID5 -> BrandCache -> Maybe Brand
insert :: UUID5 -> Brand -> BrandCache -> BrandCache
evict  :: BrandCache -> BrandCache          -- Evict expired + LRU
```

### 6.4 L2: DuckDB (Analytical)

```sql
-- Columnar storage optimized for analytical queries
CREATE TABLE brands (
    uuid        UUID PRIMARY KEY,
    domain      TEXT NOT NULL,
    name        TEXT NOT NULL,
    
    -- Palette (flattened for columnar efficiency)
    primary_l   FLOAT,
    primary_c   FLOAT,
    primary_h   FLOAT,
    secondary_l FLOAT,
    secondary_c FLOAT,
    secondary_h FLOAT,
    
    -- Typography
    heading_font   TEXT,
    body_font      TEXT,
    scale_base     FLOAT,
    scale_ratio    FLOAT,
    
    -- Spacing
    spacing_base   FLOAT,
    spacing_ratio  FLOAT,
    
    -- Voice
    tone           TEXT,
    traits         TEXT[],
    
    -- Provenance
    content_hash   TEXT,
    scraped_at     TIMESTAMP,
    source_url     TEXT
);

-- Analytical queries
SELECT heading_font, COUNT(*) 
FROM brands 
GROUP BY heading_font 
ORDER BY COUNT(*) DESC;

SELECT AVG(primary_c) as avg_chroma
FROM brands
WHERE domain LIKE '%.tech';
```

### 6.5 L3: PostgreSQL (Durable)

```sql
-- Full JSONB storage with relationships
CREATE TABLE brands (
    uuid         UUID PRIMARY KEY,
    domain       TEXT NOT NULL UNIQUE,
    data         JSONB NOT NULL,             -- Full Brand as JSONB
    content_hash TEXT NOT NULL,
    created_at   TIMESTAMP DEFAULT NOW(),
    updated_at   TIMESTAMP DEFAULT NOW(),
    
    -- Relationships
    organization_id UUID REFERENCES organizations(id),
    created_by_id   UUID REFERENCES users(id)
);

-- Indexes for common queries
CREATE INDEX idx_brands_domain ON brands(domain);
CREATE INDEX idx_brands_org ON brands(organization_id);
CREATE INDEX idx_brands_hash ON brands(content_hash);
CREATE INDEX idx_brands_data_gin ON brands USING GIN(data);

-- Full-text search on voice vocabulary
CREATE INDEX idx_brands_vocabulary ON brands 
USING GIN(to_tsvector('english', data->'voice'->'vocabulary'->>'preferred'));
```

### 6.6 Cache Coherence

```haskell
-- Write-through with async L2/L3 persistence
storeBrand :: Brand -> Pipeline 'Database 'NoRequirements ()
storeBrand brand = do
    -- L1: Synchronous (fast)
    atomicModifyIORef' cacheRef (insert brand.identity.uuid brand)
    
    -- L2: Async batch write (every 100 brands or 10 seconds)
    enqueueDuckDB brand
    
    -- L3: Async persistent (immediate for durability)
    asyncWritePostgres brand

-- Read-through with fallback
loadBrand :: UUID5 -> Pipeline 'Database 'NoRequirements (Maybe Brand)
loadBrand uuid = do
    -- L1: Check cache first
    cached <- lookupCache uuid
    case cached of
        Just brand -> pure (Just brand)
        Nothing -> do
            -- L2: Check DuckDB
            fromDuck <- queryDuckDB uuid
            case fromDuck of
                Just brand -> do
                    insertCache uuid brand  -- Warm L1
                    pure (Just brand)
                Nothing -> do
                    -- L3: Check PostgreSQL
                    fromPg <- queryPostgres uuid
                    case fromPg of
                        Just brand -> do
                            insertCache uuid brand   -- Warm L1
                            insertDuckDB brand       -- Warm L2
                            pure (Just brand)
                        Nothing -> pure Nothing
```

════════════════════════════════════════════════════════════════════════════════
                                                          // 7 // security model
════════════════════════════════════════════════════════════════════════════════

## 7. Security Model

### 7.1 Sandbox Architecture

The scraper runs in a multi-layer sandbox:

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│ Layer 1: gVisor (sentry)                                                        │
│  - Intercepts all syscalls                                                      │
│  - No direct kernel access                                                      │
│  - Memory isolation                                                             │
│                                                                                 │
│  ┌─────────────────────────────────────────────────────────────────────────┐   │
│  │ Layer 2: Bubblewrap (bwrap)                                             │   │
│  │  - Network namespace (no outbound except allowed hosts)                 │   │
│  │  - Mount namespace (read-only root, tmpfs /tmp)                         │   │
│  │  - User namespace (unprivileged)                                        │   │
│  │  - Seccomp filter                                                       │   │
│  │                                                                         │   │
│  │  ┌─────────────────────────────────────────────────────────────────┐    │   │
│  │  │ Layer 3: Chromium sandbox                                       │    │   │
│  │  │  - Site isolation                                               │    │   │
│  │  │  - Process per origin                                           │    │   │
│  │  │  - No file:// access                                            │    │   │
│  │  │                                                                 │    │   │
│  │  │  ┌─────────────────────────────────────────────────────────┐    │    │   │
│  │  │  │ Playwright (headless)                                   │    │    │   │
│  │  │  │  - Single target URL                                    │    │    │   │
│  │  │  │  - No navigation to other domains                       │    │    │   │
│  │  │  │  - Timeout enforced                                     │    │    │   │
│  │  │  └─────────────────────────────────────────────────────────┘    │    │   │
│  │  └─────────────────────────────────────────────────────────────────┘    │   │
│  └─────────────────────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### 7.2 Network Policy

```yaml
# Allowed outbound from sandbox:
allowed_hosts:
  - "*.target-domain.com"     # Only the domain being scraped
  - "fonts.googleapis.com"     # Google Fonts (common)
  - "fonts.gstatic.com"        # Google Fonts CDN
  - "use.typekit.net"          # Adobe Fonts

blocked_protocols:
  - file://
  - chrome://
  - javascript:
  - data:                       # Except for small inline assets
```

### 7.3 Resource Limits

```nix
{
  scraper.limits = {
    maxMemoryMB = 512;           # Per scrape
    maxCpuSeconds = 30;          # Timeout
    maxNetworkBytes = 10485760;  # 10MB max download
    maxDiskBytes = 0;            # No disk writes
    maxProcesses = 10;           # Chromium needs several
  };
}
```

### 7.4 ZMQ Security

```haskell
-- CURVE encryption for ZMQ
data ZMQConfig = ZMQConfig
  { zmqServerPublicKey  :: !PublicKey   -- Haskell analyzer's public key
  , zmqServerSecretKey  :: !SecretKey   -- Haskell analyzer's secret key
  , zmqScraperPublicKey :: !PublicKey   -- Scraper's public key (registered)
  }

-- All messages are:
-- 1. Encrypted with CURVE (NaCl)
-- 2. Authenticated (only registered scrapers)
-- 3. Bounded in size (max 50MB)
```

════════════════════════════════════════════════════════════════════════════════
                                                  // 8 // implementation phases
════════════════════════════════════════════════════════════════════════════════

## 8. Implementation Phases

### Phase 0: Fix Existing Sorrys (IMMEDIATE)

| Task | File | Effort | Status |
|------|------|--------|--------|
| Fix `monotonic` sorry | Typography.lean:212 | 2h | PENDING |
| Fix `fromList` sorry | Voice.lean:166 | 1h | PENDING |
| Add `float_mul_pos_lt` axiom | Typography.lean | 30m | PENDING |
| Verify proofs compile | `lake build` | 15m | PENDING |

**Deliverable:** Zero sorry in Brand proofs

### Phase 1: Brand.lean Compound Type (1-2 days)

| Task | Effort | Dependencies |
|------|--------|--------------|
| Create Brand.lean structure | 2h | Phase 0 complete |
| Add compound invariants as proof fields | 3h | Cornell pattern study |
| Prove composition validity | 2h | All molecule proofs |
| Prove determinism (UUID5) | 1h | Identity.lean |
| Add serialization Box | 3h | Cornell Proofs.lean |

**Deliverable:** Brand.lean with zero sorry, following Cornell Box pattern

### Phase 2: compass-brand Haskell Package (3-5 days)

| Task | Effort | Dependencies |
|------|--------|--------------|
| Package scaffolding | 2h | - |
| Types.hs from Lean4 | 4h | Brand.lean complete |
| ZMQ client for scraper | 4h | - |
| Color extractor (CSS parsing) | 6h | - |
| Typography extractor | 4h | - |
| Spacing extractor | 3h | - |
| Voice analyzer (basic NLP) | 6h | - |
| Brand composer | 4h | All extractors |
| HAMT cache | 2h | - |
| DuckDB adapter | 4h | - |
| PostgreSQL adapter | 3h | - |
| Hedgehog property tests | 6h | All above |

**Deliverable:** Working Haskell package that composes brands

### Phase 3: Sandboxed Scraper (2-3 days)

| Task | Effort | Dependencies |
|------|--------|--------------|
| Playwright extraction script | 4h | - |
| ZMQ publisher | 2h | - |
| Bubblewrap wrapper | 3h | - |
| gVisor sandbox config | 4h | Nix expertise |
| Integration test with Haskell | 4h | Phase 2 |

**Deliverable:** Secure scraper communicating via ZMQ

### Phase 4: Graded Monad Proofs (2-3 days)

| Task | Effort | Dependencies |
|------|--------|--------------|
| Pipeline monad Lean4 definition | 4h | - |
| Effect algebra proofs | 4h | - |
| CoEffect algebra proofs | 4h | Continuity.lean pattern |
| Discharge proof structure | 3h | - |
| Haskell implementation | 4h | Proofs complete |

**Deliverable:** Proven graded monad for pipeline stages

### Phase 5: Integration & Testing (2-3 days)

| Task | Effort | Dependencies |
|------|--------|--------------|
| Golden tests (known brands) | 4h | Phases 2-3 |
| Property tests (Hedgehog) | 4h | Phase 2 |
| E2E test: URL → Brand | 4h | All phases |
| Performance benchmarks | 2h | - |
| Documentation | 3h | - |

**Deliverable:** Production-ready brand ingestion

### Total Estimated Effort

| Phase | Days | Cumulative |
|-------|------|------------|
| 0: Fix sorrys | 0.5 | 0.5 |
| 1: Brand.lean | 1.5 | 2 |
| 2: compass-brand | 4 | 6 |
| 3: Scraper | 2.5 | 8.5 |
| 4: Graded monads | 2.5 | 11 |
| 5: Integration | 2.5 | 13.5 |

**Total: ~14 days of focused work**

════════════════════════════════════════════════════════════════════════════════
                                                         // 9 // open questions
════════════════════════════════════════════════════════════════════════════════

## 9. Open Questions

### 9.1 Float Proofs

**Question:** Should we convert Float axioms to Real proofs?

**Context:** Lean4's `Float` is IEEE 754 with edge cases. Mathlib's `Real` has 
proven properties but doesn't represent actual runtime behavior.

**Options:**
1. Keep Float axioms, document IEEE 754 assumptions
2. Prove for Real, add runtime assertions that values are in safe range
3. Create a `BoundedFloat` type that excludes NaN/Inf by construction

**Recommendation:** Option 3 — create `BoundedFloat` that carries proof of
finiteness and bounds, similar to how `OKLCH` carries gamut proofs.

### 9.2 Voice Analysis Depth

**Question:** How sophisticated should voice/tone analysis be?

**Options:**
1. **Basic:** Keyword frequency, sentence length, formality heuristics
2. **Medium:** Pre-trained sentiment model (e.g., BERT fine-tuned)
3. **Advanced:** LLM-based analysis with structured output

**Recommendation:** Start with Option 1, design for Option 2/3 upgrade path.
Voice is subjective; basic heuristics may suffice for MVP.

### 9.3 Logo Detection

**Question:** Should we include logo detection in Phase 2?

**Context:** Logo detection requires image analysis (CV models). This adds
significant complexity.

**Options:**
1. Skip logos for now, focus on CSS-extractable data
2. Basic heuristics (largest image, "logo" in filename/alt)
3. CV model for logo detection (adds torch/onnx dependency)

**Recommendation:** Option 2 for MVP. Logos are important but heuristics
catch 80% of cases.

### 9.4 Incremental Scraping

**Question:** How to handle brand changes over time?

**Context:** Brands evolve. Same domain may have different brands over time.

**Options:**
1. UUID5 per domain (latest wins)
2. UUID5 per (domain, content_hash) — content-addressed versioning
3. UUID5 per domain, with version history table

**Recommendation:** Option 3. UUID5 identifies the brand, but we maintain
history for rollback and analysis.

### 9.5 PureScript Code Generation

**Question:** Should compass-brand generate PureScript modules?

**Context:** The extracted Brand should be usable in Hydrogen frontend.

**Options:**
1. Export JSON, import in PureScript
2. Generate PureScript module with typed Brand value
3. Use `verified-purescript` to generate from Lean4 proofs

**Recommendation:** Option 2 for MVP, migrate to Option 3 when
`verified-purescript` pipeline is mature.

────────────────────────────────────────────────────────────────────────────────
                                                                    // appendix
────────────────────────────────────────────────────────────────────────────────

## Appendix A: Reference Implementations

| Component | Reference | Location |
|-----------|-----------|----------|
| Cornell Box proofs | libevring | `/home/justin/libevring/lean/Cornell/Proofs.lean` |
| Graded monads | verified-purescript | `TypeClasses.lean` (via straylight-repos) |
| Co-effect algebra | continuity | `lean-continuity/Continuity.lean` |
| Color proofs | Hydrogen | `/home/justin/jpyxal/hydrogen/proofs/Hydrogen/Schema/Color/` |
| Existing Brand proofs | Hydrogen | `/home/justin/jpyxal/hydrogen/proofs/Hydrogen/Schema/Brand/` |
| CSS extraction | COMPASS toolbox | `/home/justin/jpyxal/COMPASS/toolbox/brand_ingestion/` |

## Appendix B: Key Files

```
# Proofs
hydrogen/proofs/Hydrogen/Schema/Brand/*.lean     # 6 files, 2 sorrys
hydrogen/proofs/Hydrogen/Schema/Color/*.lean     # Reference patterns
libevring/lean/Cornell/Proofs.lean               # Gold standard

# Documentation  
hydrogen/docs/BRAND_SCHEMA.md                    # Brand structure spec
hydrogen/docs/AGENT_EMBODIMENT.md                # Why this matters
hydrogen/docs/CONTINUITY_VISION.md               # Project vision

# Existing ingestion (Python, reference only)
COMPASS/toolbox/brand_ingestion/                 # PDF, Figma, Twitter, Instagram
```

## Appendix C: Axiom Inventory

| Axiom | File | Justification | Risk |
|-------|------|---------------|------|
| `uuid5` | Identity.lean | RFC 4122 | Low |
| `uuid5_deterministic` | Identity.lean | RFC 4122 | Low |
| `uuid5_injective` | Identity.lean | SHA-1 collision | Low |
| `sha256` | Provenance.lean | FIPS 180-4 | Low |
| `sha256_deterministic` | Provenance.lean | FIPS 180-4 | Low |
| `sha256_injective` | Provenance.lean | Collision resistance | Low |
| `float_pow_pos` | Spacing.lean | IEEE 754 | Medium |
| `float_pow_finite` | Spacing.lean | Range analysis | Medium |
| `float_mul_pos` | Spacing.lean | IEEE 754 | Medium |
| `float_mul_finite` | Spacing.lean | Range analysis | Medium |
| `pow_monotonic` | Typography.lean | IEEE 754 | Medium |
| `float_mul_pos_lt` | Typography.lean | **NEEDED** | Medium |

────────────────────────────────────────────────────────────────────────────────

                                                        — Claude Opus 4.5 // 2026-02-25
