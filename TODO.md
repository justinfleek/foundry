# FOUNDRY - Production Release TODO

**Target: System F Omega | 100% Production Grade**

**Status Legend:**
- `[ ]` Not started
- `[~]` In progress
- `[x]` Complete
- `[!]` Blocked

---

## PHASE 0: CRITICAL FIXES (MUST DO FIRST)

### 0.1 Remove Forbidden Patterns

| Status | File | Line | Issue | Fix |
|--------|------|------|-------|-----|
| `[ ]` | `foundry-storage/test/Test/Foundry/Storage/HAMT.hs` | 151 | Uses `undefined` | Use proper pattern matching or `error` with clear message |
| `[ ]` | `foundry-storage/bench/Main.hs` | 135 | Uses `Prelude.head` | Use `listToMaybe` or pattern match |
| `[ ]` | `foundry-extract/test/Test/Foundry/Extract/Color.hs` | 66 | Uses `!!` operator | Use safe indexing with bounds check |

### 0.2 Complete Stub Implementations

| Status | File | Line | Issue | Fix |
|--------|------|------|-------|-----|
| `[ ]` | `foundry-extract/src/Foundry/Extract/Typography.hs` | 134 | `typographyScaleTable = V.empty` TODO | Build scale table from detected font sizes |
| `[ ]` | `src/Brand/Provenance.purs` | 126-149 | Mock SHA256 implementation | Implement real SHA256 or FFI to Haskell |

### 0.3 Remove TODO Comments

| Status | File | Line | Content |
|--------|------|------|---------|
| `[ ]` | `flake.nix` | 94 | Re-enable sensenet integration |
| `[ ]` | `foundry-extract/src/Foundry/Extract/Typography.hs` | 134 | Build scale table |

---

## PHASE 1: CODE QUALITY (System F Omega Compliance)

### 1.1 Explicit Imports (371 `(..)` patterns to fix)

**Priority files (most violations):**

| Status | File | Count | Type |
|--------|------|-------|------|
| `[ ]` | `foundry-core/test/Test/Foundry/Core/Brand/Editorial.hs` | 21 | Imports |
| `[ ]` | `foundry-core/test/Test/Foundry/Core/Brand/Generators.hs` | 18 | Imports |
| `[ ]` | `foundry-core/src/Foundry/Core/Brand/Editorial.hs` | 17 | Exports |
| `[ ]` | `foundry-extract/src/Foundry/Extract/Typography.hs` | 15 | Imports |
| `[ ]` | `foundry-extract/src/Foundry/Extract/Types.hs` | 14 | Exports |
| `[ ]` | `foundry-extract/src/Foundry/Extract/Voice.hs` | 12 | Imports |
| `[ ]` | `foundry-core/src/Foundry/Core/Brand/Logo.hs` | 12 | Exports |
| `[ ]` | `foundry-extract/src/Foundry/Extract/Color.hs` | 11 | Imports |

**All modules requiring explicit imports:**

```
foundry-core/src/
[ ] Foundry/Core.hs
[ ] Foundry/Core/Agent.hs
[ ] Foundry/Core/Agent/Budget.hs
[ ] Foundry/Core/Agent/Context.hs
[ ] Foundry/Core/Agent/Permission.hs
[ ] Foundry/Core/Brand.hs
[ ] Foundry/Core/Brand/Color.hs
[ ] Foundry/Core/Brand/Customer.hs
[ ] Foundry/Core/Brand/Editorial.hs
[ ] Foundry/Core/Brand/Gradient.hs
[ ] Foundry/Core/Brand/Gradient/Rules.hs
[ ] Foundry/Core/Brand/Identity.hs
[ ] Foundry/Core/Brand/Logo.hs
[ ] Foundry/Core/Brand/Logo/Sizing.hs
[ ] Foundry/Core/Brand/Logo/Usage.hs
[ ] Foundry/Core/Brand/Overview.hs
[ ] Foundry/Core/Brand/Palette.hs
[ ] Foundry/Core/Brand/Provenance.hs
[ ] Foundry/Core/Brand/Spacing.hs
[ ] Foundry/Core/Brand/Strategy.hs
[ ] Foundry/Core/Brand/Tagline.hs
[ ] Foundry/Core/Brand/Typography.hs
[ ] Foundry/Core/Brand/Voice.hs
[ ] Foundry/Core/Effect.hs
[ ] Foundry/Core/Effect/CoEffect.hs
[ ] Foundry/Core/Effect/Graded.hs
[ ] Foundry/Core/Text.hs

foundry-extract/src/
[ ] Foundry/Extract.hs
[ ] Foundry/Extract/Color.hs
[ ] Foundry/Extract/Color/CSS.hs
[ ] Foundry/Extract/Color/Cluster.hs
[ ] Foundry/Extract/Color/Role.hs
[ ] Foundry/Extract/Compose.hs
[ ] Foundry/Extract/Spacing.hs
[ ] Foundry/Extract/Typography.hs
[ ] Foundry/Extract/Typography/FontFamily.hs
[ ] Foundry/Extract/Typography/Scale.hs
[ ] Foundry/Extract/Types.hs
[ ] Foundry/Extract/Voice.hs
[ ] Foundry/Extract/Voice/NLP.hs
[ ] Foundry/Extract/Voice/Tone.hs

foundry-storage/src/
[ ] Foundry/Storage.hs
[ ] Foundry/Storage/DuckDB.hs
[ ] Foundry/Storage/HAMT.hs
[ ] Foundry/Storage/Postgres.hs
[ ] Foundry/Storage/Types.hs

foundry-scraper/src/
[ ] Foundry/Scraper.hs
[ ] Foundry/Scraper/Client.hs
[ ] Foundry/Scraper/Config.hs
[ ] Foundry/Scraper/Protocol.hs

Test files:
[ ] All test files in foundry-core/test/
[ ] All test files in foundry-extract/test/
[ ] All test files in foundry-storage/test/
[ ] All test files in foundry-scraper/test/
```

### 1.2 File Size Compliance (500 line max)

| Status | File | Lines | Action |
|--------|------|-------|--------|
| `[ ]` | `foundry-core/test/Test/Foundry/Core/Brand/Generators.hs` | 809 | Split into Generators/*.hs modules |
| `[ ]` | `scraper/src/scraper.ts` | 591 | Split into scraper/extraction/*.ts |
| `[ ]` | `foundry-extract/test/Test/Foundry/Extract/Security.hs` | 569 | Split by category (Color, Typography, etc.) |
| `[ ]` | `foundry-core/src/Foundry/Core/Brand/Editorial.hs` | 506 | Split Contact/Social into submodules |

### 1.3 StrictData Compliance

| Status | Package | Action |
|--------|---------|--------|
| `[ ]` | foundry-core | Audit all record fields for `!` bang patterns |
| `[ ]` | foundry-extract | Audit all record fields for `!` bang patterns |
| `[ ]` | foundry-storage | Audit all record fields for `!` bang patterns |
| `[ ]` | foundry-scraper | Audit all record fields for `!` bang patterns |

---

## PHASE 2: TEST COVERAGE ("EVERYONE gets tested")

### 2.1 Haskell Module Tests

**foundry-core modules needing tests:**

| Status | Module | Test File |
|--------|--------|-----------|
| `[ ]` | `Brand/Overview.hs` | `Test/Foundry/Core/Brand/Overview.hs` |
| `[ ]` | `Brand/Customer.hs` | `Test/Foundry/Core/Brand/Customer.hs` |
| `[ ]` | `Brand/Typography.hs` | `Test/Foundry/Core/Brand/Typography.hs` |
| `[ ]` | `Brand/Color.hs` | `Test/Foundry/Core/Brand/Color.hs` |
| `[ ]` | `Brand/Identity.hs` | `Test/Foundry/Core/Brand/Identity.hs` |
| `[ ]` | `Brand/Gradient.hs` | `Test/Foundry/Core/Brand/Gradient.hs` |
| `[ ]` | `Brand/Gradient/Rules.hs` | `Test/Foundry/Core/Brand/Gradient/Rules.hs` |
| `[ ]` | `Brand/Voice.hs` | `Test/Foundry/Core/Brand/Voice.hs` |
| `[ ]` | `Brand/Palette.hs` | `Test/Foundry/Core/Brand/Palette.hs` |
| `[ ]` | `Brand/Logo.hs` | `Test/Foundry/Core/Brand/Logo.hs` |
| `[ ]` | `Brand/Logo/Usage.hs` | `Test/Foundry/Core/Brand/Logo/Usage.hs` |
| `[ ]` | `Brand/Logo/Sizing.hs` | `Test/Foundry/Core/Brand/Logo/Sizing.hs` |
| `[ ]` | `Brand/Spacing.hs` | `Test/Foundry/Core/Brand/Spacing.hs` |
| `[ ]` | `Brand/Provenance.hs` | `Test/Foundry/Core/Brand/Provenance.hs` |
| `[ ]` | `Agent/Context.hs` | `Test/Foundry/Core/Agent/Context.hs` |
| `[ ]` | `Agent/Permission.hs` | `Test/Foundry/Core/Agent/Permission.hs` |
| `[ ]` | `Agent/Budget.hs` | `Test/Foundry/Core/Agent/Budget.hs` |
| `[ ]` | `Effect/CoEffect.hs` | `Test/Foundry/Core/Effect/CoEffect.hs` |
| `[ ]` | `Effect/Graded.hs` | `Test/Foundry/Core/Effect/Graded.hs` |
| `[ ]` | `Text.hs` | `Test/Foundry/Core/Text.hs` |

**foundry-extract modules needing dedicated tests:**

| Status | Module | Test File |
|--------|--------|-----------|
| `[ ]` | `Color/Cluster.hs` | `Test/Foundry/Extract/Color/Cluster.hs` |
| `[ ]` | `Color/Role.hs` | `Test/Foundry/Extract/Color/Role.hs` |
| `[ ]` | `Color/CSS.hs` | `Test/Foundry/Extract/Color/CSS.hs` |
| `[ ]` | `Typography/FontFamily.hs` | `Test/Foundry/Extract/Typography/FontFamily.hs` |
| `[ ]` | `Typography/Scale.hs` | `Test/Foundry/Extract/Typography/Scale.hs` |
| `[ ]` | `Voice/NLP.hs` | `Test/Foundry/Extract/Voice/NLP.hs` |
| `[ ]` | `Voice/Tone.hs` | `Test/Foundry/Extract/Voice/Tone.hs` |

**foundry-storage modules needing tests:**

| Status | Module | Test File |
|--------|--------|-----------|
| `[ ]` | `Storage/DuckDB.hs` | `Test/Foundry/Storage/DuckDB.hs` |
| `[ ]` | `Storage/Postgres.hs` | `Test/Foundry/Storage/Postgres.hs` |
| `[ ]` | `Storage/Types.hs` | `Test/Foundry/Storage/Types.hs` |

**foundry-scraper modules needing tests:**

| Status | Module | Test File |
|--------|--------|-----------|
| `[ ]` | `Scraper/Config.hs` | `Test/Foundry/Scraper/Config.hs` |
| `[ ]` | `Scraper/Client.hs` | `Test/Foundry/Scraper/Client.hs` |

### 2.2 PureScript Tests (NONE EXIST)

| Status | Module | Test File |
|--------|--------|-----------|
| `[ ]` | `Brand/Brand.purs` | `test/Brand/Brand.purs` |
| `[ ]` | `Brand/Identity.purs` | `test/Brand/Identity.purs` |
| `[ ]` | `Brand/Palette.purs` | `test/Brand/Palette.purs` |
| `[ ]` | `Brand/Typography.purs` | `test/Brand/Typography.purs` |
| `[ ]` | `Brand/Spacing.purs` | `test/Brand/Spacing.purs` |
| `[ ]` | `Brand/Voice.purs` | `test/Brand/Voice.purs` |
| `[ ]` | `Brand/Strategy.purs` | `test/Brand/Strategy.purs` |
| `[ ]` | `Brand/Editorial.purs` | `test/Brand/Editorial.purs` |
| `[ ]` | `Brand/Logo.purs` | `test/Brand/Logo.purs` |
| `[ ]` | `Brand/Provenance.purs` | `test/Brand/Provenance.purs` |
| `[ ]` | `Brand/Layout.purs` | `test/Brand/Layout.purs` |
| `[ ]` | `Brand/Modes.purs` | `test/Brand/Modes.purs` |
| `[ ]` | `Brand/GraphicElements.purs` | `test/Brand/GraphicElements.purs` |
| `[ ]` | `Brand/UIElements.purs` | `test/Brand/UIElements.purs` |
| `[ ]` | `Brand/UIElements/Buttons.purs` | `test/Brand/UIElements/Buttons.purs` |
| `[ ]` | `Brand/UIElements/Accessibility.purs` | `test/Brand/UIElements/Accessibility.purs` |
| `[ ]` | `Brand/Strategy/Compound.purs` | `test/Brand/Strategy/Compound.purs` |
| `[ ]` | `Brand/Editorial/Contact.purs` | `test/Brand/Editorial/Contact.purs` |
| `[ ]` | `Brand/Editorial/Spelling.purs` | `test/Brand/Editorial/Spelling.purs` |
| `[ ]` | `Brand/Logo/Usage.purs` | `test/Brand/Logo/Usage.purs` |

### 2.3 Property-Based Testing

| Status | Category | Description |
|--------|----------|-------------|
| `[x]` | Color invariants | OKLCH lightness/chroma bounds, CSS parsing roundtrip |
| `[x]` | Typography invariants | Scale ratio positivity, font stack ordering |
| `[x]` | Spacing invariants | Scale monotonicity, ratio bounds |
| `[x]` | Voice security | Injection immunity, emoji handling |
| `[ ]` | Brand roundtrip | JSON encode/decode preserves equality |
| `[ ]` | Agent budget | Budget conservation under operations |
| `[ ]` | Permission lattice | Monotonicity, subset relations |
| `[ ]` | Graded monad laws | Left identity, right identity, associativity |
| `[ ]` | Coeffect algebra | Idempotency, monotonicity, associativity |

### 2.4 Integration Tests

| Status | Test | Description | Blocked By |
|--------|------|-------------|------------|
| `[!]` | Full pipeline | URL -> Brand extraction | libzmq, sandbox |
| `[!]` | Scraper ZMQ | Haskell client <-> TS server | libzmq |
| `[ ]` | HAMT persistence | Write -> Read consistency | None |
| `[ ]` | DuckDB storage | L2 cache operations | DuckDB bindings |
| `[ ]` | PostgreSQL storage | L3 persistence | PostgreSQL bindings |

### 2.5 Golden Tests

| Status | Brand | URL | Description |
|--------|-------|-----|-------------|
| `[ ]` | Stripe | stripe.com | Blue/purple palette, Inter font |
| `[ ]` | Vercel | vercel.com | Black/white minimal, Geist font |
| `[ ]` | Linear | linear.app | Purple gradient, custom typography |
| `[ ]` | Tailwind | tailwindcss.com | Multi-color palette, documentation brand |

### 2.6 Resilience Tests

| Status | Test | Description |
|--------|------|-------------|
| `[ ]` | Save/undo | State persistence and rollback |
| `[ ]` | Reload | Session recovery after crash |
| `[ ]` | Corruption recovery | Graceful handling of malformed data |
| `[ ]` | Timeout handling | Scraper timeout doesn't crash pipeline |
| `[ ]` | Memory bounds | Large brand extraction stays under limits |

---

## PHASE 3: LEAN4 PROOFS

### 3.1 External Dependencies

| Status | Dependency | Repository | Purpose |
|--------|------------|------------|---------|
| `[!]` | Hydrogen | github.com/straylight-software/hydrogen | Core brand proofs |
| `[!]` | Continuity | github.com/straylight-software/straylight | Coeffect algebra |

### 3.2 Axiom Justification

| Status | File | Line | Axiom | Justification Required |
|--------|------|------|-------|------------------------|
| `[ ]` | `lean/Foundry/Pipeline.lean` | 39 | `Hash` opaque type | Document content-addressing guarantee |
| `[ ]` | `lean/Foundry/Pipeline.lean` | 57 | `Coeffect.instDecidableEq` | Prove or provide computational witness |

### 3.3 Pipeline Proofs

| Status | Theorem | Description |
|--------|---------|-------------|
| `[ ]` | `pipeline_deterministic` | Same input -> same Brand output |
| `[ ]` | `extraction_total` | All valid URLs produce valid Brand |
| `[ ]` | `coeffect_preservation` | Pipeline respects coeffect constraints |
| `[ ]` | `budget_conservation` | Agent budget decreases monotonically |
| `[ ]` | `permission_monotonic` | Permissions can only decrease |

### 3.4 Brand Invariant Proofs

| Status | Theorem | Description |
|--------|---------|-------------|
| `[ ]` | `palette_nonempty` | Brand always has at least one color |
| `[ ]` | `color_valid_oklch` | All colors in valid OKLCH range |
| `[ ]` | `typography_scale_ordered` | Font sizes monotonically increase |
| `[ ]` | `spacing_scale_positive` | All spacing values > 0 |
| `[ ]` | `provenance_immutable` | Provenance hash never changes |

---

## PHASE 4: INFRASTRUCTURE

### 4.1 Build System

| Status | Task | Description |
|--------|------|-------------|
| `[x]` | `flake.nix` | Nix flake with all dependencies |
| `[x]` | `flake.lock` | Locked dependencies |
| `[~]` | sensenet integration | Buck2 build system (module API mismatch) |
| `[ ]` | CI pipeline | GitHub Actions for test/build/deploy |
| `[ ]` | Cachix | Binary cache for fast builds |

### 4.2 Development Environment

| Status | Task | Description |
|--------|------|-------------|
| `[x]` | `nix develop` | Working dev shell |
| `[x]` | ZeroMQ | libzmq available in devShell |
| `[x]` | Playwright | Browser automation configured |
| `[x]` | DuckDB | Database bindings available |
| `[x]` | PostgreSQL | Database bindings available |
| `[ ]` | foundry-scraper | Enable in cabal.project |

### 4.3 Sandboxing

| Status | Task | Description |
|--------|------|-------------|
| `[ ]` | `bubblewrap.sh` | Lightweight sandbox wrapper |
| `[ ]` | `gvisor.nix` | gVisor runsc configuration |
| `[ ]` | Playwright sandbox | Browser isolation policy |
| `[ ]` | Network policy | Whitelist allowed domains |

### 4.4 Observability

| Status | Task | Description |
|--------|------|-------------|
| `[ ]` | Structured logging | JSON logs with trace IDs |
| `[ ]` | Metrics | Prometheus-compatible metrics |
| `[ ]` | Tracing | OpenTelemetry spans |
| `[ ]` | Health checks | Liveness/readiness probes |

---

## PHASE 5: DOCUMENTATION

### 5.1 Architecture Documentation

| Status | Document | Description |
|--------|----------|-------------|
| `[x]` | `CLAUDE.md` | AI assistant instructions |
| `[ ]` | `ARCHITECTURE.md` | System architecture overview |
| `[ ]` | `SMART_BRAND_FRAMEWORK.md` | Brand schema documentation |
| `[ ]` | `COEFFECT_ALGEBRA.md` | Graded monad documentation |
| `[ ]` | `SECURITY_MODEL.md` | Sandbox and permission model |

### 5.2 API Documentation

| Status | Package | Description |
|--------|---------|-------------|
| `[ ]` | foundry-core | Haddock with examples |
| `[ ]` | foundry-extract | Haddock with examples |
| `[ ]` | foundry-storage | Haddock with examples |
| `[ ]` | foundry-scraper | Haddock with examples |
| `[ ]` | PureScript | Pursuit-style docs |

### 5.3 Module Annotations

Each module should have:
- Feature purpose and rationale
- Function contracts and behavior
- Dependencies (what this module requires)
- Dependents (what requires this module)

| Status | Package | Modules Annotated |
|--------|---------|-------------------|
| `[ ]` | foundry-core | 0/27 |
| `[ ]` | foundry-extract | 0/14 |
| `[ ]` | foundry-storage | 0/5 |
| `[ ]` | foundry-scraper | 0/4 |

---

## PHASE 6: SECURITY

### 6.1 Input Validation

| Status | Module | Validation |
|--------|--------|------------|
| `[x]` | Color/CSS.hs | RGB input sanitization |
| `[x]` | Typography/Scale.hs | Exponent bounds |
| `[x]` | Spacing.hs | Ratio clamping |
| `[ ]` | Voice.hs | XSS/injection prevention |
| `[ ]` | Scraper/Protocol.hs | URL validation |

### 6.2 Resource Limits

| Status | Resource | Limit |
|--------|----------|-------|
| `[ ]` | Memory | Max brand size |
| `[ ]` | Time | Extraction timeout |
| `[ ]` | Network | Rate limiting |
| `[ ]` | Storage | Quota per brand |

### 6.3 Cryptographic Security

| Status | Feature | Implementation |
|--------|---------|----------------|
| `[ ]` | SHA256 | Real implementation (not mock) |
| `[ ]` | UUID5 | Deterministic namespaced UUIDs |
| `[ ]` | Signatures | Brand provenance signing |

---

## PHASE 7: PERFORMANCE

### 7.1 Benchmarks

| Status | Benchmark | Target |
|--------|-----------|--------|
| `[x]` | HAMT insert | < 1ms |
| `[x]` | HAMT lookup | < 100us |
| `[ ]` | Brand serialization | < 10ms |
| `[ ]` | Color clustering | < 50ms |
| `[ ]` | Full extraction | < 5s |

### 7.2 Optimization

| Status | Optimization | Description |
|--------|--------------|-------------|
| `[ ]` | Lazy evaluation audit | Ensure no space leaks |
| `[ ]` | Strict fields | Bang patterns on hot paths |
| `[ ]` | Unboxing | Unbox numeric types |
| `[ ]` | Fusion | Vector/Text fusion |

---

## PHASE 8: DEPLOYMENT

### 8.1 Packaging

| Status | Format | Description |
|--------|--------|-------------|
| `[ ]` | Nix package | `nix build .#foundry` |
| `[ ]` | Docker image | OCI-compliant container |
| `[ ]` | Static binary | Fully static Haskell binary |

### 8.2 Configuration

| Status | Task | Description |
|--------|------|-------------|
| `[ ]` | Dhall config | Typed configuration schema |
| `[ ]` | Environment vars | 12-factor app compliance |
| `[ ]` | Secrets management | Vault/SOPS integration |

### 8.3 Monitoring

| Status | Task | Description |
|--------|------|-------------|
| `[ ]` | Grafana dashboards | Pre-built monitoring dashboards |
| `[ ]` | Alerting rules | Prometheus alertmanager rules |
| `[ ]` | Runbooks | Operational procedures |

---

## SUMMARY

### Counts by Phase

| Phase | Total | Complete | In Progress | Blocked |
|-------|-------|----------|-------------|---------|
| 0. Critical Fixes | 7 | 0 | 0 | 0 |
| 1. Code Quality | ~400 | 0 | 0 | 0 |
| 2. Test Coverage | ~80 | 10 | 0 | 2 |
| 3. Lean4 Proofs | 15 | 0 | 0 | 2 |
| 4. Infrastructure | 18 | 6 | 1 | 0 |
| 5. Documentation | 12 | 1 | 0 | 0 |
| 6. Security | 12 | 3 | 0 | 0 |
| 7. Performance | 10 | 2 | 0 | 0 |
| 8. Deployment | 9 | 0 | 0 | 0 |

### Priority Order

1. **PHASE 0**: Remove `undefined`, complete stubs - BLOCKS EVERYTHING
2. **PHASE 1.1**: Explicit imports - Code quality foundation
3. **PHASE 2**: Test coverage - Confidence for refactoring
4. **PHASE 4.2**: Enable foundry-scraper - Unblock integration tests
5. **PHASE 3**: Lean4 proofs - Mathematical guarantees
6. **PHASE 5**: Documentation - Maintainability
7. **PHASE 6-8**: Security, Performance, Deployment - Production readiness

---

## CURRENT TEST STATUS

```
foundry-core:    127 tests passing
foundry-extract:  48 tests passing
foundry-storage:  22 tests passing
foundry-scraper:   0 tests (blocked)
────────────────────────────────────
TOTAL:           197 tests passing
```

---

*Last updated: 2026-02-26*
*Target: System F Omega | Production Grade*
