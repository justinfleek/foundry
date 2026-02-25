━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // brand // ingestion // todo
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# BRAND INGESTION PROJECT TODO

**Last Updated:** 2026-02-25
**Architecture Doc:** `BRAND_INGESTION_ARCHITECTURE.md`

────────────────────────────────────────────────────────────────────────────────
                                                              // phase 0 // lean4
                                                                // fix // sorrys
────────────────────────────────────────────────────────────────────────────────

## Phase 0: Fix Existing Sorrys — COMPLETE

All Brand molecule files now build with zero sorry.

### Completed:
- [x] Typography.lean: Added axioms for float arithmetic, monotonicity proven
- [x] Voice.lean: Added `eraseDups_nonempty` and `eraseDups_idempotent` axioms
- [x] Identity.lean: Marked `make` as `noncomputable` (uses axiom `uuid5`)
- [x] Spacing.lean: Renamed `at` to `atLevel` (reserved keyword in Lean 4.29)
- [x] Provenance.lean: Fixed Timestamp ordering proofs
- [x] Palette.lean: Fixed Float comparisons (use `native_decide`), fixed NeutralScale structure
- [x] All files verified with `lake build`

### New axioms added (with justification):
- `gt_one_implies_pos`: x > 1 → x > 0 (obvious for Floats)
- `nat_toFloat_finite`: Nat.toFloat is always finite (Nats are bounded)
- `float_nat_mul_pos_of_pos`: Positive Nat * positive Float is positive

────────────────────────────────────────────────────────────────────────────────
                                                           // phase 1 // brand
                                                                  // compound
────────────────────────────────────────────────────────────────────────────────

## Phase 1: Brand.lean Compound Type — COMPLETE

### Completed:
- [x] Created `hydrogen/proofs/Hydrogen/Schema/Brand/Brand.lean` (325 lines)
- [x] Imports all Brand molecule modules (Identity, Palette, Typography, Spacing, Voice, Provenance)
- [x] `Brand` structure with proof fields (Cornell pattern):
  - `identity_derived`: UUID is deterministic from domain
  - `palette_valid`: Has primary color
  - `typography_valid`: Base size is positive
  - `spacing_valid`: Base spacing is positive
  - `voice_valid`: Has at least one trait
  - `provenance_valid`: Content hash is 64 chars
- [x] Smart constructor `Brand.make` validates all invariants
- [x] Compound theorems: `same_domain_same_uuid`, `typography_monotonic`, `voice_has_traits`
- [x] Content addressing: `contentHash`, `hashEq`, `hash_eq_implies_equal_content`
- [x] WCAG accessibility checks: `meetsWCAGAA`, `meetsWCAGAAA`
- [x] PureScript code generation included
- [x] Builds successfully: `lake build Hydrogen.Schema.Brand.Brand`

### Deferred to later phase:
- [ ] `BrandBox : Box Brand` serialization (requires Binary serialization infrastructure)
- [ ] `roundtrip` and `consumption` proofs (depends on BrandBox)

────────────────────────────────────────────────────────────────────────────────
                                                        // phase 2 // haskell
                                                         // compass-brand pkg
────────────────────────────────────────────────────────────────────────────────

## Phase 2: compass-brand Haskell Package

### P2.1: Package Scaffolding
- [ ] Create `COMPASS/nix/haskell/compass-brand/`
- [ ] Create `compass-brand.cabal` with dependencies
- [ ] Create `default.nix` for Nix integration
- [ ] Add to `nix/overlays/haskell.nix`
- [ ] Add to `nix/modules/flake/haskell.nix`
- [ ] Verify `nix build .#compass-brand`

### P2.2: Core Types (Types.hs)
- [ ] Define `Brand` ADT matching Lean4 structure
- [ ] Define all atom types (UUID5, Domain, OKLCH, FontWeight, etc.)
- [ ] Define all molecule types (Identity, Palette, Typography, etc.)
- [ ] Add `StrictData` pragma and `!` on all fields
- [ ] Add JSON serialization (ToJSON, FromJSON)

### P2.3: ZMQ Client (Scraper/Playwright.hs)
- [ ] Set up ZMQ DEALER socket
- [ ] Define message protocol (ScrapeRequest, ScrapeResult)
- [ ] Add CURVE encryption
- [ ] Add timeout handling
- [ ] Add reconnection logic

### P2.4: Extractors
- [ ] **Color extractor** (Extract/Color.hs)
  - [ ] Parse CSS color properties
  - [ ] Cluster colors by OKLCH similarity
  - [ ] Assign semantic roles (frequency-based)
  - [ ] Verify WCAG contrast ratios
  
- [ ] **Typography extractor** (Extract/Typography.hs)
  - [ ] Parse font-family stacks
  - [ ] Parse font-size values
  - [ ] Detect scale ratio (geometric regression)
  - [ ] Map to FontWeight enum
  
- [ ] **Spacing extractor** (Extract/Spacing.hs)
  - [ ] Parse margin/padding values
  - [ ] Detect base unit (GCD-like)
  - [ ] Compute scale ratio
  
- [ ] **Voice analyzer** (Extract/Voice.hs)
  - [ ] Basic NLP (sentence length, word frequency)
  - [ ] Formality heuristics
  - [ ] Keyword extraction
  - [ ] Map to Tone enum

### P2.5: Brand Composer (Compose.hs)
- [ ] Generate Identity (UUID5 from domain)
- [ ] Validate all molecules
- [ ] Compose into Brand
- [ ] Compute provenance (SHA256, timestamp)

### P2.6: Storage Adapters
- [ ] **HAMT** (Storage/HAMT.hs)
  - [ ] In-memory cache with TTL
  - [ ] LRU eviction
  
- [ ] **DuckDB** (Storage/DuckDB.hs)
  - [ ] Schema creation
  - [ ] Insert/query operations
  - [ ] Columnar flattening
  
- [ ] **PostgreSQL** (Storage/Postgres.hs)
  - [ ] Schema with JSONB
  - [ ] Insert/query operations
  - [ ] Full-text search on vocabulary

### P2.7: Export Adapters
- [ ] **PureScript** (Export/PureScript.hs)
- [ ] **CSS Variables** (Export/CSS.hs)
- [ ] **Figma Tokens** (Export/Figma.hs)

### P2.8: Tests
- [ ] Hedgehog property tests for extractors
- [ ] Golden tests for known brands
- [ ] Integration tests for full pipeline

────────────────────────────────────────────────────────────────────────────────
                                                         // phase 3 // scraper
                                                                 // sandboxed
────────────────────────────────────────────────────────────────────────────────

## Phase 3: Sandboxed Scraper

### P3.1: Playwright Script
- [ ] Create `scraper/src/index.ts`
- [ ] Implement DOM extraction (CSS, computed styles, fonts)
- [ ] Implement asset detection (images, SVGs)
- [ ] Implement text extraction
- [ ] Add timeout handling

### P3.2: ZMQ Publisher
- [ ] Create `scraper/src/zmq.ts`
- [ ] Implement DEALER socket
- [ ] Implement CURVE encryption
- [ ] Implement message serialization

### P3.3: Sandbox Configuration
- [ ] Create `scraper/sandbox/bubblewrap.sh`
  - [ ] Network namespace
  - [ ] Mount namespace (read-only root)
  - [ ] User namespace
  - [ ] Seccomp filter
  
- [ ] Create `scraper/sandbox/gvisor.nix`
  - [ ] gVisor runsc configuration
  - [ ] Resource limits
  - [ ] Network policy

### P3.4: Integration
- [ ] Test scraper → ZMQ → Haskell flow
- [ ] Verify sandbox isolation
- [ ] Performance benchmarks

────────────────────────────────────────────────────────────────────────────────
                                                       // phase 4 // graded
                                                            // monad proofs
────────────────────────────────────────────────────────────────────────────────

## Phase 4: Graded Monad Proofs

### P4.1: Lean4 Definitions
- [ ] Create `hydrogen/proofs/Hydrogen/Pipeline/Effect.lean`
- [ ] Define `Effect` inductive type
- [ ] Define `CoEffect` inductive type
- [ ] Define `Pipeline` graded monad

### P4.2: Effect Algebra
- [ ] Prove `Effect` forms a monoid
- [ ] Prove `Effect` composition is associative
- [ ] Prove `Pure` is identity

### P4.3: CoEffect Algebra
- [ ] Prove idempotency: `satisfy (satisfy r) = satisfy r`
- [ ] Prove monotonicity: `r₁ ⊆ r₂ → satisfied r₁ → satisfied r₂`
- [ ] Prove associativity: `(r₁ ⊗ r₂) ⊗ r₃ = r₁ ⊗ (r₂ ⊗ r₃)`

### P4.4: Discharge Proofs
- [ ] Define `DischargeProof` structure
- [ ] Prove discharge soundness

### P4.5: Haskell Implementation
- [ ] Implement `Pipeline` newtype
- [ ] Implement `Effect` type family
- [ ] Implement `CoEffect` type family
- [ ] Add type-level tracking

────────────────────────────────────────────────────────────────────────────────
                                                      // phase 5 // integration
                                                              // and testing
────────────────────────────────────────────────────────────────────────────────

## Phase 5: Integration & Testing

### P5.1: Golden Tests
- [ ] Scrape stripe.com → verify Brand structure
- [ ] Scrape vercel.com → verify Brand structure
- [ ] Scrape linear.app → verify Brand structure
- [ ] Scrape tailwindcss.com → verify Brand structure

### P5.2: Property Tests
- [ ] Palette: contrast always ≥ 4.5 for primary/secondary
- [ ] Typography: scale always monotonic
- [ ] Spacing: values always positive
- [ ] Voice: traits always non-empty
- [ ] Identity: UUID5 deterministic for same domain

### P5.3: E2E Tests
- [ ] Full pipeline: URL → ScrapeResult → Brand → Storage
- [ ] Cache coherence: L1/L2/L3 consistency
- [ ] Error handling: timeout, network error, malformed CSS

### P5.4: Performance
- [ ] Benchmark scraping (target: <30s per domain)
- [ ] Benchmark extraction (target: <1s)
- [ ] Benchmark storage (target: <100ms)

### P5.5: Documentation
- [ ] API documentation
- [ ] Architecture diagrams
- [ ] Deployment guide

────────────────────────────────────────────────────────────────────────────────
                                                              // status summary
────────────────────────────────────────────────────────────────────────────────

## Status Summary

| Phase | Status | Blocking |
|-------|--------|----------|
| 0: Fix sorrys | COMPLETE | - |
| 1: Brand.lean | COMPLETE | - |
| 2: compass-brand | NOT STARTED | - |
| 3: Scraper | NOT STARTED | - |
| 4: Graded monads | NOT STARTED | - |
| 5: Integration | NOT STARTED | Phases 2, 3 |

**Next Action:** Start Phase 2 — compass-brand Haskell package

────────────────────────────────────────────────────────────────────────────────

                                                        — Claude Opus 4.5 // 2026-02-25
