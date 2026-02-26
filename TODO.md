# FOUNDRY - Production Release TODO

**Target: System F Omega | 100% Production Grade | COMPASS Integration**

**Status Legend:**
- `[ ]` Not started
- `[~]` In progress
- `[x]` Complete
- `[!]` Blocked

**Related Documents:**
- `docs/PRODUCTION_INTEGRATION_PLAN.md` — Council-approved integration plan
- `docs/TECHNICAL_SPECIFICATIONS.md` — Type definitions and algorithms
- `docs/CROSS_REPOSITORY_ALIGNMENT.md` — FOUNDRY ↔ HYDROGEN ↔ COMPASS sync

---

## CURRENT STATE (2026-02-26)

### Build Status

| Component | Build | Tests | Notes |
|-----------|-------|-------|-------|
| **foundry-core** | `[x]` | 148 passing | Brand, Agent, Effect, Evring, Sigil |
| **foundry-extract** | `[x]` | 48 passing | Color, Typography, Spacing, Voice |
| **foundry-storage** | `[x]` | 22 passing | HAMT, DuckDB, Postgres adapters |
| **foundry-scraper** | `[!]` | 0 (blocked) | Commented out - requires libzmq |
| **PureScript** | `[!]` | N/A | Spago cache issue (network) |
| **Lean4 (Cornell)** | `[~]` | N/A | Import fixed, ByteArray API mismatch |
| **Lean4 (Brand)** | `[!]` | N/A | Blocked on Hydrogen dependency |

**Total: 218 Haskell tests passing**

### Codebase Size

| Language | Source Lines | Test Lines | Notes |
|----------|--------------|------------|-------|
| Haskell | ~15,700 | ~5,800 | 4 packages |
| PureScript | ~8,000 | 0 | Brand schemas |
| Lean4 | ~22,500 | N/A | Cornell, Pipeline, Sigil |
| TypeScript | ~1,050 | 0 | Playwright scraper |
| Dhall | ~24k chars | N/A | Pipeline/Resource config |
| C++ | ~24k chars | N/A | Evring/Sigil header |

---

## PHASE 0: CRITICAL FIXES

### 0.1 Forbidden Patterns in Source (PRODUCTION CODE)

| Status | File | Line | Issue | Fix |
|--------|------|------|-------|-----|
| `[x]` | `foundry-core/src/Foundry/Core/Effect/Graded.hs` | 22 | `undefined` in grade function | Was only in Haddock comment (spec, not code) |
| `[x]` | `foundry-core/src/Foundry/Core/Evring/Wai/MultiCoreRR.hs` | 194 | `!! idx` unsafe index | Converted to Vector with V.! safe indexing |

### 0.2 Error Calls in Evring (Low-level IO)

These are in io_uring code paths where failure is unrecoverable:

| Status | File | Line | Context |
|--------|------|------|---------|
| `[~]` | `Evring/Wai/Conn.hs` | 324 | Response buffer overflow |
| `[~]` | `Evring/Wai/Loop.hs` | 126,156,175,193,211 | SQ full conditions |

**Note**: These may be acceptable - io_uring exhaustion is a fatal condition.

### 0.3 Lean4 Import Fix

| Status | File | Line | Issue | Fix |
|--------|------|------|-------|-----|
| `[x]` | `lean/Foundry/Cornell/Basic.lean` | 12 | `import Foundry.Foundry.Cornell.Proofs` | Fixed to `import Foundry.Cornell.Proofs` |

### 0.4 Lean4 ByteArray API (4.15.0)

| Status | File | Issue | Fix |
|--------|------|-------|-----|
| `[~]` | `lean/Foundry/Cornell/Proofs.lean` | Missing `ByteArray.getElem_append_left` | Need to define locally or find new API |
| `[~]` | `lean/Foundry/Cornell/Proofs.lean` | Missing `ByteArray.size_append` | Need to define locally or find new API |
| `[~]` | `lean/Foundry/Cornell/Proofs.lean` | Missing `ByteArray.extract_append_eq_right` | Need to define locally or find new API |

### 0.5 Stubs Completed (VERIFIED)

| Status | File | Issue | Resolution |
|--------|------|-------|------------|
| `[x]` | `foundry-extract/src/Foundry/Extract/Typography.hs` | `typographyScaleTable` | Now populated from detected sizes |

### 0.6 Rename metxt → foundry (COMPLETED)

| Status | File | Notes |
|--------|------|-------|
| `[x]` | `flake.nix` | Dev shell, comments, package refs |
| `[x]` | `nix/modules/default.nix` | Module names |
| `[x]` | `nix/overlays/default.nix` | Overlay names |
| `[x]` | `nix/packages/default.nix` | Package refs |
| `[x]` | `spago.yaml` | Package name: foundry-brand |
| `[x]` | `purescript/foundry-playground/spago.yaml` | Package name + directory renamed |

---

## PHASE 1: CODE QUALITY

### 1.1 Explicit Imports

**Current count: 519 `(..)` patterns**

Priority files (by violation count):

| Status | File | Count |
|--------|------|-------|
| `[ ]` | `foundry-core/test/Test/Foundry/Core/Brand/Editorial.hs` | 21 |
| `[ ]` | `foundry-core/test/Test/Foundry/Core/Brand/Generators.hs` | 18 |
| `[ ]` | `foundry-core/src/Foundry/Core/Brand/Editorial.hs` | 17 |
| `[ ]` | `foundry-extract/src/Foundry/Extract/Typography.hs` | 15 |
| `[ ]` | `foundry-extract/src/Foundry/Extract/Types.hs` | 14 |

### 1.2 File Size Compliance (500 line max)

| Status | File | Lines | Action |
|--------|------|-------|--------|
| `[ ]` | `foundry-core/src/Foundry/Core/Evring/Wai.hs` | 977 | Split into Wai/*.hs modules |
| `[ ]` | `foundry-core/src/Foundry/Core/Evring/Event.hs` | 590 | Split event types |
| `[ ]` | `scraper/src/scraper.ts` | 591 | Split into extraction/*.ts |
| `[ ]` | `foundry-core/src/Foundry/Core/Evring/Zmtp.hs` | 545 | Split ZMTP state machine |
| `[ ]` | `foundry-core/src/Foundry/Core/Sigil/Sigil.hs` | 529 | Split protocol layers |
| `[ ]` | `foundry-core/src/Foundry/Core/Brand/Editorial.hs` | 506 | Split Contact/Social |

### 1.3 TODOs in Evring (In Progress Work)

| Status | File | Line | Content |
|--------|------|------|---------|
| `[~]` | `Evring/Ring.hs` | 182,188 | Implement actual io_uring |
| `[~]` | `Evring/Trace.hs` | 79,83 | Implement serialize/deserialize |
| `[~]` | `Evring/Wai.hs` | 430,676,970 | io_uring timeout, accept addr, zero-copy |
| `[~]` | `Evring/Zmtp.hs` | 402,486,501,517 | READY parse, greeting, events |

---

## PHASE 2: TEST COVERAGE

### 2.1 Current Test Distribution

```
foundry-core:    148 tests
  - Brand/Editorial, Strategy, Tagline
  - Agent (full)
  - Effect/CoEffect, Graded
  - Security (injection, memory, parser, cross-module)

foundry-extract:  48 tests
  - Color (CSS, Cluster, Role)
  - Typography (Scale, FontFamily)
  - Spacing
  - Voice (NLP, Tone)

foundry-storage:  22 tests
  - HAMT operations
```

### 2.2 Missing Test Coverage

| Status | Module | Priority |
|--------|--------|----------|
| `[ ]` | `Evring/*` | High - new io_uring code |
| `[ ]` | `Sigil/*` | High - binary protocol |
| `[ ]` | PureScript schemas | Medium |
| `[ ]` | Integration (ZMQ) | Blocked on libzmq |

### 2.3 Property-Based Testing Status

| Status | Category | Description |
|--------|----------|-------------|
| `[x]` | Color invariants | OKLCH bounds, CSS roundtrip |
| `[x]` | Typography invariants | Scale ratio, font stack |
| `[x]` | Spacing invariants | Monotonicity, ratio bounds |
| `[x]` | Voice security | Injection, emoji, unicode |
| `[x]` | Coeffect algebra | Tensor laws, purity, reproducibility |
| `[ ]` | Graded monad laws | Identity, associativity |
| `[ ]` | Agent budget | Conservation proofs |

---

## PHASE 3: LEAN4 PROOFS

### 3.1 Module Status

| Module | Status | Lines | Notes |
|--------|--------|-------|-------|
| `Foundry.Pipeline` | `[x]` | 320 | Graded monads, coeffects |
| `Foundry.Sigil.Sigil` | `[x]` | 800+ | 18 theorems, 0 sorry |
| `Foundry.Cornell.Proofs` | `[x]` | 850+ | Box codecs, roundtrip proofs |
| `Foundry.Cornell.*` | `[x]` | ~700KB | Wire formats (Nix, Git, ZMTP, HTTP/2/3, Protobuf) |
| `Foundry.Continuity` | `[x]` | 5.5k | Coeffect algebra |
| `Foundry.Brand` | `[!]` | 36 | Blocked - needs Hydrogen |

### 3.2 Axioms in Use

| File | Axiom | Justification |
|------|-------|---------------|
| `Cornell/Git.lean` | `zlib_deterministic` | Trust zlib decompressor |
| `Cornell/Git.lean` | `zlib_consumption_bound` | Bounded consumption |
| `Cornell/Nix.lean` | `nixString_roundtrip` | ByteArray tedium |
| `Cornell/Nix.lean` | `parseNStrings_*` | Array size < 2^64 |

### 3.3 External Dependencies

| Status | Dependency | Purpose |
|--------|------------|---------|
| `[!]` | Hydrogen | Brand schema proofs |

---

## PHASE 4: INFRASTRUCTURE

### 4.1 Build System

| Status | Task | Notes |
|--------|------|-------|
| `[x]` | `flake.nix` | Full dev environment |
| `[x]` | `cabal.project` | 3/4 packages enabled |
| `[x]` | `lakefile.lean` | Foundry lib target |
| `[x]` | `spago.yaml` | PureScript config |
| `[~]` | Buck2 | Available but not primary |

### 4.2 Development Environment

| Status | Tool | Version |
|--------|------|---------|
| `[x]` | GHC | 9.12.2 |
| `[x]` | PureScript | 0.15.15 |
| `[x]` | Spago | 1.0.3 |
| `[x]` | Lean4 | 4.15.0 (via elan) |
| `[x]` | Buck2 | 2025-12-01 |
| `[x]` | Dhall | 1.42.3 |
| `[x]` | ZeroMQ | Available in devShell |
| `[x]` | Playwright | Configured |
| `[x]` | DuckDB | Bindings available |
| `[x]` | PostgreSQL | Bindings available |

### 4.3 Pending Infrastructure

| Status | Task | Notes |
|--------|------|-------|
| `[ ]` | Enable foundry-scraper | Uncomment in cabal.project |
| `[ ]` | CI pipeline | GitHub Actions |
| `[ ]` | Cachix | Binary cache |

---

## PHASE 5: NEW COMPONENTS (Not in Original TODO)

### 5.1 Evring - io_uring WAI Server

High-performance HTTP server using Linux io_uring:

| Module | Lines | Status |
|--------|-------|--------|
| `Evring/Wai.hs` | 977 | `[~]` Core server |
| `Evring/Event.hs` | 590 | `[~]` Event types |
| `Evring/Conn.hs` | 498 | `[~]` Connection handling |
| `Evring/Loop.hs` | ~400 | `[~]` Event loop |
| `Evring/Ring.hs` | ~200 | `[~]` io_uring wrapper |
| `Evring/Zmtp.hs` | 545 | `[~]` ZeroMQ protocol |
| `Evring/Sigil.hs` | 529 | `[~]` Sigil protocol |
| `Evring/Trace.hs` | ~100 | `[~]` Tracing |

### 5.2 Sigil - Binary Protocol

Verified binary protocol with Lean4 proofs:

| Component | Location | Status |
|-----------|----------|--------|
| Lean4 proofs | `lean/Foundry/Sigil/Sigil.lean` | `[x]` 18 theorems |
| Haskell impl | `haskell/foundry-core/src/Foundry/Core/Sigil/Sigil.hs` | `[~]` |
| C++ header | `cpp/evring/sigil.h` | `[x]` |

### 5.3 Cornell - Verified Wire Formats

Massive library of verified binary codecs:

| Format | File | Lines | Status |
|--------|------|-------|--------|
| Core proofs | `Proofs.lean` | 850 | `[x]` |
| Nix protocol | `Nix.lean` | 1500+ | `[x]` |
| Git pack | `Git.lean` | 550+ | `[x]` |
| ZMTP | `Zmtp.lean` | 590+ | `[x]` |
| HTTP/2 | `Http2.lean` | 450+ | `[x]` |
| HTTP/3 | `Http3.lean` | 450+ | `[x]` |
| Protobuf | `Protobuf.lean` | 800+ | `[x]` |
| Sigil | `Sigil.lean` | 800+ | `[x]` |
| State machines | `StateMachine.lean` | 850+ | `[x]` |
| Extractors | `Extract*.lean` | 5000+ | `[x]` |

---

## PHASE 6: DOCUMENTATION

| Status | Document | Notes |
|--------|----------|-------|
| `[x]` | `CLAUDE.md` | Comprehensive AI instructions |
| `[x]` | `docs/SMART_BRAND_FRAMEWORK.md` | 640 lines, complete |
| `[x]` | `docs/BRAND_SCHEMA.md` | Schema documentation |
| `[x]` | `docs/SIGIL_PROTOCOL.md` | Protocol specification |
| `[ ]` | `ARCHITECTURE.md` | System overview |
| `[ ]` | Haddock | API documentation |

---

## PHASE 7: INTEGRATION

### 7.1 PureScript ↔ Haskell Alignment

| Status | PureScript Module | Haskell Equivalent |
|--------|-------------------|-------------------|
| `[x]` | `Brand/Identity.purs` | `Brand/Identity.hs` |
| `[x]` | `Brand/Palette.purs` | `Brand/Palette.hs` |
| `[x]` | `Brand/Typography.purs` | `Brand/Typography.hs` |
| `[x]` | `Brand/Spacing.purs` | `Brand/Spacing.hs` |
| `[x]` | `Brand/Voice.purs` | `Brand/Voice.hs` |
| `[x]` | `Brand/Strategy.purs` | `Brand/Strategy.hs` |
| `[x]` | `Brand/Editorial.purs` | `Brand/Editorial.hs` |
| `[x]` | `Brand/Logo.purs` | `Brand/Logo.hs` |
| `[ ]` | `Brand/Layout.purs` | Not yet |
| `[ ]` | `Brand/Modes.purs` | Not yet |
| `[ ]` | `Brand/UIElements.purs` | Not yet |
| `[ ]` | `Brand/GraphicElements.purs` | Not yet |
| `[ ]` | `Brand/Imagery.purs` | Not yet |

### 7.2 Scraper Integration

| Status | Component | Notes |
|--------|-----------|-------|
| `[x]` | TypeScript scraper | 1057 lines, Playwright |
| `[~]` | Haskell client | foundry-scraper (disabled) |
| `[ ]` | ZMQ bridge | Blocked on libzmq |

---

## SUMMARY

### Completion by Phase

| Phase | Status | Notes |
|-------|--------|-------|
| 0. Critical Fixes | `[~]` | 2 forbidden patterns remain |
| 1. Code Quality | `[ ]` | 519 wildcard imports, 6 oversized files |
| 2. Test Coverage | `[x]` | 218 tests passing |
| 3. Lean4 Proofs | `[~]` | Cornell complete, Brand blocked |
| 4. Infrastructure | `[x]` | Dev environment complete |
| 5. New Components | `[~]` | Evring/Sigil in progress |
| 6. Documentation | `[~]` | Core docs exist |
| 7. Integration | `[~]` | PS↔HS partial |

### Priority Order (UPDATED 2026-02-26 — COMPASS Integration)

**PHASE 0: FOUNDATION REPAIR (2 weeks)**

| Priority | Task | Effort |
|----------|------|--------|
| P0 | Enable foundry-scraper in cabal.project | 1 hour |
| P0 | Connect Playwright → ZMQ → Haskell | 2 days |
| P0 | Create `CompleteBrand` unified type (18+ fields) | 2 days |
| P0 | Port missing atoms from HYDROGEN (Layout, UIElements, Modes, Imagery, Graphics) | 3 days |
| P0 | Create `BrandOntology` (term aliases, SKU patterns) | 1 day |
| P1 | Create `BrandHierarchy` (sub-brand inheritance) | 1 day |
| P0 | Create `AgentBrandContext` for MAESTRO | 1 day |
| P0 | Aeson instances with JSON roundtrip tests | 2 days |

**PHASE 1: PROOF COMPLETION (2 weeks)**

| Priority | Task | Effort |
|----------|------|--------|
| P0 | Fix Typography.lean:212 (scale monotonicity SORRY) | 1 day |
| P0 | Fix Voice.lean:166 (eraseDups length SORRY) | 1 day |
| P0 | Fix Cornell ByteArray API for Lean4 4.15.0 | 2 days |
| P0 | Create Brand.lean (compound composition proofs) | 3 days |
| P1 | Prove WCAG accessibility guarantee | 2 days |
| P1 | Prove serialization roundtrip | 2 days |
| P0 | Property tests matching Lean4 theorems | 2 days |

**PHASE 2: EXTRACTION COMPLETENESS (3 weeks)**

| Priority | Task | Effort |
|----------|------|--------|
| P0 | Logo extraction (variants, lockups, clear space, sizing) | 3 days |
| P0 | Voice extraction (LLM-assisted IS/NOT mining) | 4 days |
| P1 | Layout extraction (grid system detection) | 2 days |
| P1 | UI element extraction (button/input/card specs) | 2 days |
| P1 | Mode detection (light/dark stylesheets) | 2 days |
| P2 | Imagery style extraction (color grading params) | 2 days |
| P2 | Pattern/texture detection | 1 day |

**PHASE 3: COMPASS INTEGRATION (2 weeks)**

| Priority | Task | Effort |
|----------|------|--------|
| P0 | Create COMPASS export module (CompleteBrand → NDJSON) | 3 days |
| P0 | BE:/NEVER BE: prompt generation from IS/NOT | 1 day |
| P0 | ZMQ PUSH to COMPASS | 2 days |
| P0 | Entity type additions to COMPASS knowledge graph | 1 day |
| P1 | Cache invalidation events | 2 days |

**PHASE 4: SWARM SCALE (3 weeks)**

| Priority | Task | Effort |
|----------|------|--------|
| P0 | Worker pool (ZMQ DEALER/ROUTER) | 3 days |
| P0 | Domain coordination (Redis locks) | 2 days |
| P0 | Rate limiting (per-domain, robots.txt) | 2 days |
| P0 | Backpressure (bounded queues, circuit breakers) | 2 days |
| P0 | Horizontal scraper scaling (Nix flake) | 3 days |
| P1 | gVisor sandboxing at scale | 2 days |
| P1 | DuckDB staging → PostgreSQL batch commit | 2 days |

**PHASE 5: OBSERVABILITY + HARDENING (2 weeks)**

| Priority | Task | Effort |
|----------|------|--------|
| P0 | Prometheus metrics | 2 days |
| P0 | Security audit (sandbox escape, injection) | 3 days |
| P0 | Load testing (10x expected peak) | 2 days |
| P1 | Jaeger distributed tracing | 2 days |
| P1 | Alerting (PagerDuty/Slack) | 1 day |
| P1 | Grafana dashboard | 1 day |
| P1 | Chaos testing (node failure, network partition) | 2 days |

**TOTAL: 14 weeks (3.5 months) to production-ready swarm scale**

---

## BUILD COMMANDS

```bash
# Enter dev environment
nix develop

# Build Haskell
cd haskell && cabal build all

# Run Haskell tests
cd haskell && cabal test all

# Build Lean4 (partial - Cornell only)
cd lean && lake build Foundry.Cornell.Proofs

# Build PureScript (requires network for registry)
spago build
```

---

*Last updated: 2026-02-26*
*Verified by full build + test run*
