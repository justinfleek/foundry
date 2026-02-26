━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                        // FOUNDRY
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# FOUNDRY - SMART Brand Ingestion Engine
# Lean4 CIC | Haskell Backend | PureScript Hydrogen | Graded Monads

## ABSOLUTE RULE #0: NEVER DISABLE WARNINGS

**DISABLING WARNINGS IS FORBIDDEN. NO EXCEPTIONS. EVER.**

## ABSOLUTE RULE #1: NEVER DELETE CODE TO FIX WARNINGS

**DELETING "UNUSED" CODE IS FORBIDDEN. NO EXCEPTIONS. EVER.**

```
❌ Deleting unused imports        -- FORBIDDEN
❌ Deleting unused functions      -- FORBIDDEN
❌ Deleting unused variables      -- FORBIDDEN
❌ Deleting "stub" code           -- FORBIDDEN
❌ Deleting incomplete code       -- FORBIDDEN
```

**WHY THIS IS LIFE OR DEATH:**

"Unused" code exists for a reason. It was written with intent. When you see an
"unused import" or "unused variable" warning:

1. **The code is INCOMPLETE** - Someone started work that wasn't finished
2. **The import IS needed** - Find WHERE it should be used and IMPLEMENT it
3. **Deleting is LAZY** - It hides incompleteness instead of completing work
4. **Deleting destroys value** - Code was paid for, deleting throws money away

**THE ONLY ACCEPTABLE RESPONSE TO AN "UNUSED" WARNING IS TO FIND AND IMPLEMENT
THE MISSING FUNCTIONALITY THAT USES IT.**

```
❌ {-# OPTIONS_GHC -Wno-* #-}     -- FORBIDDEN
❌ {-# OPTIONS_GHC -fno-warn-* #-} -- FORBIDDEN  
❌ -- hlint: ignore              -- FORBIDDEN
❌ # type: ignore                -- FORBIDDEN
❌ @SuppressWarnings             -- FORBIDDEN
❌ // eslint-disable             -- FORBIDDEN
❌ # noqa                        -- FORBIDDEN
❌ sorry                         -- FORBIDDEN (Lean4)
❌ axiom                         -- FORBIDDEN (Lean4)
❌ admit                         -- FORBIDDEN (Lean4)
```

---

## STRAYLIGHT STANDARDS

### Language Stack
- **Lean4 4.26+** - Calculus of Inductive Constructions, invariants defined FIRST
- **SciLean** - Scientific computing, floats, bezier curves (Lean4 library)
- **Haskell** - Backend, GHC 9.12, StrictData everywhere
- **PureScript Hydrogen** - Frontend framework, pure functional UI

### File Standards
- **500 lines maximum per file** - Leaders into secondary documents if needed
- **Explicit imports on EVERYTHING** - Norman Stansfield energy
- **AST edits on EVERYTHING** - No string manipulation of code
- **StrictData on EVERYTHING** - `!` bang patterns on all record fields
- **Modular compilation** - Every module compiles individually

### Type System Requirements
- **System F Omega** - Higher-kinded types, type-level programming
- **Co-effect algebra** - Track what computations REQUIRE from environment
- **Graded monads** - `Agent perms budget ctx a` parameterized capabilities
- **Linear types** - Resource accounting, budget conservation proofs

### Code Quality (NON-NEGOTIABLE)
- **ZERO stubs or TODOs** - If you write code, it must be COMPLETE
- **ZERO dummy code** - No placeholders, no "implement later"
- **ZERO escapes** - No unsafePerformIO, unsafeCoerce, undefined, error
- **ZERO forbidden patterns** - No `!!`, `Infinity`, `NaN`, `??`, `..`
- **UUID5 for determinism** - No randomness, reproducible identifiers

### Literate Programming
- Professional-grade annotations describing:
  - Feature purpose and rationale
  - Function contracts and behavior
  - Dependencies (what this module requires)
  - Dependents (what requires this module)
- Full scope/dependency graphs
- Complete system architecture
- Complete ontology/schemas

### FFI Policy
- **Allowed:** Imports/exports of code
- **Allowed:** Direct interaction with diffusion models
- **Allowed:** Python ML script interop
- **Forbidden:** Everything else - keep it pure

---

## REQUIRED DEPENDENCIES

| Dependency     | Purpose                                    |
| -------------- | ------------------------------------------ |
| ZeroMQ (ZMQ4)  | Message passing, agent communication       |
| SearXNG        | Privacy-respecting web search              |
| gVisor         | Container sandboxing, security isolation   |
| Playwright     | Browser automation, skill execution        |
| Hedgehog       | Property-based testing (Haskell)           |
| QuickCheck     | Property-based testing (Haskell)           |
| Haskemathesis  | Mathematical hypothesis testing            |
| Bubblewrap     | Sandboxing for skill execution             |
| Hydrogen       | PureScript frontend framework              |

---

## FORBIDDEN PATTERNS (ABSOLUTE - NO EXCEPTIONS)

### Forbidden Bottoms (NEVER - crashes at runtime)
```
❌ undefined        ❌ error "msg"      ❌ throw e
❌ panic            ❌ fail             ❌ fix id
❌ absurd           ❌ let x = x in x
❌ panic!           ❌ unreachable!
```

### Forbidden Partial Functions (NEVER - can crash)
```
❌ head             ❌ tail             ❌ init
❌ last             ❌ !! index         ❌ fromJust
❌ read             ❌ minimum          ❌ maximum
❌ foldr1           ❌ foldl1           ❌ cycle
```

### Forbidden Types (NEVER - non-deterministic/ambiguous)
```
❌ any/Any          ❌ unknown          ❌ Dynamic
❌ Void             ❌ null             ❌ None
❌ nil              ❌ Optional         ❌ Infinity
❌ NaN              ❌ -0               ❌ all
❌ Object           ❌ Function
```

### Forbidden Escape Hatches (NEVER - breaks guarantees)
```
❌ unsafePerformIO              ❌ unsafeCoerce
❌ unsafeDupablePerformIO       ❌ unsafeInterleaveIO
❌ unsafeFixIO                  ❌ accursedUnutterablePerformIO
❌ inlinePerformIO              ❌ unsafeIOToST
❌ unsafeSTToIO                 ❌ unsafeFreeze
❌ unsafeThaw                   ❌ unsafeRead
❌ unsafeWrite                  ❌ unsafeIndex
❌ unsafeAt                     ❌ castPtr
❌ castForeignPtr               ❌ trace/traceShow
❌ Debug.Trace.*
```

### Forbidden Randomness (NEVER - non-deterministic)
```
❌ randomIO          ❌ randomRIO         ❌ newStdGen
❌ getStdGen         ❌ getStdRandom      ❌ System.Random.*
❌ UUID4             ❌ generateUUID      ❌ getCurrentTime
❌ getPOSIXTime
```

---

## CO-EFFECT ALGEBRA LAWS (MUST HOLD)

```
✅ f(f(x)) = f(x)                    -- Idempotency
✅ S(x) >= S(y)                      -- Monotonicity
✅ (E₁ ∘ E₂) ∘ E₃ = E₁ ∘ (E₂ ∘ E₃)  -- Associativity
✅ ∀ mutation → Event                -- Provenance
```

## GRADED MONAD LAWS (MUST HOLD)

```
✅ return a >>= f  ≡  f a            -- Left identity
✅ m >>= return    ≡  m              -- Right identity
✅ (m >>= f) >>= g ≡  m >>= (λx → f x >>= g)  -- Associativity
```

---

## LEAN4 VERIFICATION REQUIREMENTS

1. **Invariants defined FIRST** - Before any implementation
2. **Logical justification** - Why is this invariant necessary?
3. **No sorry/axiom/admit** - Complete proofs only
4. **State machine verification** - All transitions proven
5. **Permission lattice proofs** - Monotonicity, subset relations
6. **Budget conservation proofs** - Linear resource accounting

---

## AI ASSISTANT RULES

### Hard Rules - NEVER VIOLATE

1. **Trace errors to root cause** - Never delete to fix
2. **ADD functionality, don't remove** - Swiss cheese holes mean incomplete work
3. **Ask before deletion** - 0.00001% chance code doesn't belong
4. **Read ENTIRE file before editing** - No partial reads
5. **One file at a time** - Read, edit, rebuild, verify, then move on
6. **Verify EVERY edit against the build** - Rebuild after each change
7. **AST edits only** - No string manipulation of code
8. **Explicit imports** - No `(..)` patterns ever

### The 0.00001% Rule

There is a slim chance code does not belong. In that case:
1. **ASK** before deletion
2. **Explain** why you think it doesn't belong
3. **Wait** for confirmation

It is FAR more likely that a session ended prematurely and there are still
things left to implement. Treat "unused" as "incomplete", not "unnecessary".

---

## PROJECT STRUCTURE

```
foundry/
├── lean/                    # Lean4 - CIC, proofs, invariants
│   ├── Foundry/
│   │   ├── Brand/           # SMART framework schemas
│   │   │   ├── Identity.lean
│   │   │   ├── Palette.lean
│   │   │   ├── Typography.lean
│   │   │   ├── Spacing.lean
│   │   │   ├── Voice.lean
│   │   │   ├── Strategy.lean
│   │   │   ├── Editorial.lean
│   │   │   └── Brand.lean   # Compound type
│   │   └── Pipeline/        # Ingestion pipeline proofs
│   │       └── Effect.lean  # Graded monad definitions
│   └── lakefile.lean
│
├── haskell/                 # Haskell - Backend runtime
│   ├── foundry-core/          # Core types, graded monads
│   ├── foundry-extract/       # Brand extraction (color, type, spacing)
│   ├── foundry-scraper/       # Playwright integration, ZMQ
│   └── foundry-storage/       # HAMT, DuckDB, PostgreSQL adapters
│
├── purescript/              # PureScript - Hydrogen frontend
│   └── foundry-ui/            # Brand ingestion dashboard
│
├── src/                     # PureScript Brand schemas (current)
│   └── Brand/
│
├── nix/                     # Nix - Deterministic builds
│   ├── flake.nix
│   ├── overlays/
│   └── modules/
│
└── docs/                    # Documentation
    ├── SMART_BRAND_FRAMEWORK.md
    ├── BRAND_INGESTION_ARCHITECTURE.md
    ├── BRAND_INGESTION_TODO.md
    └── BRAND_SCHEMA.md
```

---

## WALLET CONFIGURATION (X.509 / Coinbase Standard)

```yaml
wallet:
  chain: base                    # Primary: Base L2
  secondary_chain: solana        # Secondary: Solana
  spending_limit_usd: 0          # Human approves ALL initially
  auto_approve_below_usd: 0      # Raise as trust is earned
  daily_limit_usd: 50            # Even with human approval
  require_confirmation: true     # Double-confirm large transactions
```

---

## BUILD COMMANDS

```bash
# Lean4 proofs
cd lean && lake build

# Haskell packages
nix build .#foundry-core
nix build .#foundry-extract
nix build .#foundry-scraper

# PureScript frontend
cd purescript/foundry-ui && spago build

# Run full pipeline
nix run .#foundry-ingest -- --url https://example.com

# Full test suite
nix flake check
```

---

## REVENUE STREAMS (ORDERED BY RELIABILITY)

| Layer | Type        | Examples                           | Risk   |
| ----- | ----------- | ---------------------------------- | ------ |
| 1     | Foundation  | Skill sales, tips, education       | Low    |
| 2     | Steady      | Services, consulting, affiliate    | Low    |
| 3     | Growth      | Marketplace fees, subscriptions    | Medium |
| 4     | Speculative | Token launches, trading, NFTs      | High   |

**Priority:** Build Layer 1-2 first. Layer 3-4 only after proven revenue.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                              // foundry // claude
                                                              // straylight/2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
