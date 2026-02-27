# Foundry Constraint System Audit

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // constraint // audit
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

**Purpose**: Document where Foundry's constraint systems are incomplete or incorrect
**Date**: 2026-02-27
**Status**: IN PROGRESS

────────────────────────────────────────────────────────────────────────────────
                                                               // table // of // contents
────────────────────────────────────────────────────────────────────────────────

1. Executive Summary
2. Graded Monads — Budget/Permission Tracking Gap
3. Presburger Arithmetic — Proof Verification Gap
4. Integer Linear Programming — Multi-Agent Allocation Gap
5. Field Provenance — Completion Tracking Gap
6. Effect System — Scraper Purity Gap
7. Implementation Roadmap
8. References

────────────────────────────────────────────────────────────────────────────────
                                                         // 1 // executive // summary
────────────────────────────────────────────────────────────────────────────────

## 1. Executive Summary

### The Core Problem

Foundry claims to be a **mathematically rigorous** brand ingestion engine with:
- Graded monads for budget/permission tracking
- Presburger arithmetic for proof verification
- Integer Linear Programming for multi-agent resource allocation
- Field-level provenance for completion tracking
- Pure extraction with isolated effects

**Reality: Partial implementation with critical gaps.**

### Gap Assessment

| System | Claimed | Implemented | Gap |
|--------|---------|-------------|-----|
| Graded Monads | Budget conservation, permission monotonicity | Interface only, no instances | **90%** |
| Presburger Arithmetic | Layout proofs decidable | `native_decide` only, no `omega` | **80%** |
| Integer Linear Programming | Optimal multi-agent allocation | Not implemented | **100%** |
| Field Provenance | Track scraped vs inferred vs LLM | Types exist, not wired | **70%** |
| Effect System Purity | Pure extraction, isolated IO | TypeScript scraper exists | **50%** |

### Consequences

1. **Budget conservation is property-tested, not proven** — No Lean4 proof of spend ≤ limit
2. **Timestamp ordering can underflow** — DischargeProof.duration uses Nat subtraction without ordering proof
3. **Multi-agent coordination impossible** — Single-agent budget only, no ILP for allocation
4. **Field provenance not tracked** — Can't distinguish scraped from LLM-completed at runtime
5. **TypeScript in codebase** — 770 lines of JavaScript violates pure Straylight stack

### The Path Forward

| Track | Effort | Dependencies |
|-------|--------|--------------|
| Graded Monad Instances | 2 weeks | None |
| Presburger Proofs (omega) | 2 weeks | None |
| ILP Solver Integration | 3 weeks | glpk-hs |
| Field Provenance Wiring | 2 weeks | Source.hs (done) |
| Pure Haskell Scraper | 3 weeks | html-conduit |

**Total: 6-8 weeks** (tracks can parallelize)

────────────────────────────────────────────────────────────────────────────────
                                                              // 2 // graded // monads
────────────────────────────────────────────────────────────────────────────────

## 2. Graded Monads — Budget/Permission Tracking Gap

### 2.1 What We Claimed

From `CLAUDE.md`:
- `Agent perms budget ctx a` — Graded monad parameterized by capabilities
- Budget conservation proofs — Linear resource accounting
- Permission monotonicity — Permissions can only decrease

### 2.2 What Actually Exists

**Haskell Types (foundry-core):**
```haskell
-- src/Foundry/Core/Effect/Graded.hs (44 lines)
class (Monoid g) => Grade g where
  gradeCompose :: g -> g -> g

class (Monad m, Grade g) => GradedMonad g m | m -> g where
  getGrade :: m g
  withGrade :: g -> m a -> m a
```

**Status: INTERFACE ONLY. No instances.**

**Budget System:**
```haskell
-- src/Foundry/Core/Agent/Budget.hs
spendBudget :: Int -> Budget -> Maybe Budget
spendBudget amount budget
  | newSpent <= unBudgetLimit (budgetLimit budget) = Just ...
  | otherwise = Nothing
```

**Status: Runtime check only. No type-level tracking.**

### 2.3 The Gap

| Component | Theory | Implementation | Gap |
|-----------|--------|----------------|-----|
| `GradedMonad` typeclass | ✓ Defined | ✗ No instances | 100% |
| Budget at type level | Claimed | Runtime `Maybe` only | 100% |
| Permission monotonicity | Claimed | Not enforced | 100% |
| Budget conservation proof | Claimed | Property test only | 90% |

**What should exist:**
```haskell
-- Type-level budget tracking
newtype Agent (perms :: PermissionSet) (budget :: Nat) a = Agent (IO a)

-- Spending decreases budget at type level
spend :: forall n m a. (n <= m) => 
  Proxy n -> Agent perms m a -> Agent perms (m - n) a
```

### 2.4 Why This Matters

Without graded monads:
1. **Budget violations are runtime errors** — Should be compile-time impossible
2. **Permission escalation possible** — No type-level guarantee of monotonicity
3. **No compositional reasoning** — Can't prove `agent1 >> agent2` respects bounds

### 2.5 Files Affected

```
foundry-core/src/Foundry/Core/Effect/Graded.hs    -- Needs instances
foundry-core/src/Foundry/Core/Agent/Budget.hs     -- Needs type-level tracking
foundry-core/src/Foundry/Core/Agent/Permission.hs -- Needs monotonicity proof
lean/Foundry/Pipeline.lean                        -- Needs budget conservation theorem
```

────────────────────────────────────────────────────────────────────────────────
                                                     // 3 // presburger // arithmetic
────────────────────────────────────────────────────────────────────────────────

## 3. Presburger Arithmetic — Proof Verification Gap

### 3.1 What We Claimed

From `CLAUDE.md`:
- Invariants defined FIRST — Before any implementation
- Logical justification — Why is this invariant necessary?
- No sorry/axiom/admit — Complete proofs only

### 3.2 What Actually Exists

**Lean4 Proofs (lean/Foundry/Pipeline.lean):**
```lean
-- Uses native_decide for Boolean predicates
theorem pipeline_requires_network : pipelineCoeffects.requiresNetwork = true := by
  simp only [pipelineCoeffects, pipelineStages]
  native_decide

-- Axiom for DecidableEq (not proven)
@[instance] axiom Coeffect.instDecidableEq : DecidableEq Coeffect
```

**Status: Shallow proofs. No `omega` for arithmetic.**

### 3.3 What is Missing

**DischargeProof timestamp ordering:**
```lean
-- CURRENT: Can underflow
def duration (p : DischargeProof) : Nat :=
  p.endTime.nanos - p.startTime.nanos  -- BUG: No ordering proof

-- NEEDED: Prove ordering first
structure DischargeProof where
  startTime : Timestamp
  endTime : Timestamp
  ordered : startTime.nanos ≤ endTime.nanos  -- MISSING
```

**Budget conservation:**
```lean
-- NEEDED: Prove spending never exceeds limit
theorem budget_conservation (b : Budget) (amount : Nat) :
  spend amount b = some b' → b'.spent ≤ b.limit := by
  omega  -- NOT IMPLEMENTED
```

### 3.4 The Gap

| Component | Status | Issue |
|-----------|--------|-------|
| Coeffect algebra proofs | ✓ Structural | No arithmetic |
| Graded monad laws | ✓ Proven | Simplified, not full |
| Timestamp ordering | ✗ Missing | Can underflow |
| Budget conservation | ✗ Missing | Property test only |
| Permission monotonicity | ✗ Missing | No proof |
| `omega` tactic usage | ✗ Zero | All proofs avoid arithmetic |

### 3.5 Why This Matters

Presburger arithmetic is DECIDABLE. We should be able to:
1. **Automatically verify** budget constraints
2. **Prove** timestamp ordering at construction
3. **Decide** whether coefficient systems are satisfiable

Without `omega`:
- Arithmetic invariants are stated but not proven
- Runtime can violate "proven" properties
- Lean proofs don't connect to actual guarantees

### 3.6 Files Affected

```
lean/Foundry/Pipeline.lean           -- Add omega proofs
lean/Foundry/Budget.lean             -- NEW: Budget conservation
lean/Foundry/Timestamp.lean          -- NEW: Ordering invariants
```

────────────────────────────────────────────────────────────────────────────────
                                              // 4 // integer // linear // programming
────────────────────────────────────────────────────────────────────────────────

## 4. Integer Linear Programming — Multi-Agent Allocation Gap

### 4.1 What We Claimed

From `CLAUDE.md`:
- Linear types — Resource accounting, budget conservation proofs
- Co-effect algebra — Track what computations REQUIRE from environment

Implicit claim: At billion-agent scale, resources must be optimally allocated.

### 4.2 What Actually Exists

**Budget System (Single Agent):**
```haskell
-- foundry-core/src/Foundry/Core/Agent/Budget.hs
data Budget = Budget
  { budgetLimit :: !BudgetLimit
  , budgetSpent :: !Int
  }

spendBudget :: Int -> Budget -> Maybe Budget
```

**Status: Single-agent only. No multi-agent coordination.**

### 4.3 What is Missing

**Multi-Agent Budget Allocation Problem:**
```
Given:
  - N agents with capacities c_i
  - M tasks with costs t_j and values v_j
  - Global budget B

Find:
  - Assignment x_ij ∈ {0,1} (agent i does task j)

Maximize: Σ_ij v_j · x_ij            (total value)

Subject to:
  Σ_j t_j · x_ij ≤ c_i  ∀i          (agent capacity)
  Σ_i x_ij ≤ 1          ∀j          (task done once)
  Σ_ij t_j · x_ij ≤ B               (global budget)
```

**This is ILP. We have no solver.**

### 4.4 The Gap

| Component | Status | Issue |
|-----------|--------|-------|
| Single-agent budget | ✓ Implemented | Works |
| Multi-agent coordination | ✗ Missing | No allocation |
| Task assignment optimization | ✗ Missing | No ILP |
| Global budget constraint | ✗ Missing | Agents independent |
| Optimality proof | ✗ Missing | No solver |

### 4.5 Why This Matters

At billion-agent scale:
1. **Suboptimal allocation** — Greedy assignment wastes resources
2. **Coordination failures** — Agents may all choose same task
3. **Budget overruns** — No global constraint enforcement
4. **No fairness guarantees** — Some agents starve

### 4.6 How to Fix

**Option A: Integrate glpk-hs**
```haskell
-- Add to foundry-core.cabal
build-depends: glpk-hs >= 0.7

-- src/Foundry/Core/Agent/Allocation.hs
allocateTasks :: [Agent] -> [Task] -> Budget -> Either AllocationError Assignment
allocateTasks agents tasks globalBudget = 
  let problem = formulateILP agents tasks globalBudget
  in solveILP problem
```

**Option B: Integrate limp (pure Haskell)**
```haskell
-- Lighter weight, no C dependency
build-depends: limp >= 0.3
```

### 4.7 Files to Create

```
foundry-core/src/Foundry/Core/Agent/
├── Allocation.hs       -- ILP formulation
├── Solver.hs           -- glpk-hs or limp wrapper
└── Scheduling.hs       -- Task scheduling utilities
```

────────────────────────────────────────────────────────────────────────────────
                                                        // 5 // field // provenance
────────────────────────────────────────────────────────────────────────────────

## 5. Field Provenance — Completion Tracking Gap

### 5.1 What We Claimed

From conversation:
> "brands dont typically say what they are and arent, that is distilled from 
> my 25 yrs as a strategic brand consultant"

We need to distinguish:
- **Scraped** — Directly extracted from source
- **Inferred** — Computed from scraped data
- **LLM-Completed** — Filled by semantic analysis
- **Manual** — Human-provided
- **Default** — Placeholder requiring completion

### 5.2 What Actually Exists

**Source Types (just created 2026-02-27):**
```haskell
-- foundry-core/src/Foundry/Core/Brand/Source.hs
data Source
  = Scraped !ScrapedMeta
  | Inferred !InferredMeta
  | LLMCompleted !LLMMeta
  | Manual !ManualMeta
  | Default !DefaultMeta

data Sourced a = Sourced
  { sourcedValue  :: !a
  , sourcedSource :: !Source
  }
```

**Status: Types exist. Not wired to Brand types.**

**LLM Completion Prompts (just created 2026-02-27):**
```haskell
-- foundry-core/src/Foundry/Core/Brand/Completion.hs
voiceConstraintsPrompt :: PromptContext -> CompletionPrompt
brandValuesPrompt :: PromptContext -> CompletionPrompt
targetCustomerPrompt :: PromptContext -> CompletionPrompt
```

**Status: Prompts exist. No LLM integration.**

### 5.3 The Gap

| Component | Status | Issue |
|-----------|--------|-------|
| `Source` ADT | ✓ Complete | Works |
| `Sourced a` wrapper | ✓ Complete | Works |
| Brand types using `Sourced` | ✗ Not wired | All fields raw |
| Extractors emitting `Sourced` | ✗ Not wired | No metadata |
| LLM prompts | ✓ Designed | Not integrated |
| LLM API integration | ✗ Missing | No HTTP/ZMQ |
| JSON response parsing | ✗ Missing | No Aeson instances |

### 5.4 Current Brand Type (Not Provenance-Tracked)

```haskell
-- foundry-core/src/Foundry/Core/Brand/Voice.hs
data BrandVoice = BrandVoice
  { brandVoiceSummary    :: !VoiceSummary           -- Raw, no provenance
  , brandVoiceAttributes :: !(Vector ToneAttribute) -- Raw, no provenance
  , brandVoiceTone       :: !Tone                   -- Raw, no provenance
  , brandVoiceTraits     :: !TraitSet               -- Raw, no provenance
  , brandVoiceVocabulary :: !Vocabulary             -- Raw, no provenance
  }
```

### 5.5 What Should Exist

```haskell
data BrandVoice = BrandVoice
  { brandVoiceSummary    :: !(Sourced VoiceSummary)
  , brandVoiceAttributes :: !(Sourced (Vector ToneAttribute))
  , brandVoiceTone       :: !(Sourced Tone)
  , brandVoiceTraits     :: !(Sourced TraitSet)
  , brandVoiceVocabulary :: !(Sourced Vocabulary)
  }

-- Queries become possible:
needsCompletion :: BrandVoice -> Bool
needsCompletion v = 
  needsReview (brandVoiceSummary v) ||
  needsReview (brandVoiceAttributes v) ||
  ...

overallConfidence :: BrandVoice -> Double
overallConfidence v = 
  average [ confidence (brandVoiceSummary v)
          , confidence (brandVoiceAttributes v)
          , ...
          ]
```

### 5.6 Why This Matters

Without provenance:
1. **Can't flag incomplete brands** — Don't know what's missing
2. **Can't trigger LLM completion** — Don't know what needs inference
3. **No audit trail** — Can't explain where values came from
4. **No confidence scoring** — Treat all data as equally reliable

### 5.7 Files to Modify

```
foundry-core/src/Foundry/Core/Brand/Voice.hs      -- Add Sourced wrappers
foundry-core/src/Foundry/Core/Brand/Palette.hs    -- Add Sourced wrappers
foundry-core/src/Foundry/Core/Brand/Typography.hs -- Add Sourced wrappers
foundry-core/src/Foundry/Core/Brand/Spacing.hs    -- Add Sourced wrappers
foundry-core/src/Foundry/Core/Brand/Strategy.hs   -- Add Sourced wrappers
foundry-extract/src/Foundry/Extract/Color.hs      -- Emit Sourced
foundry-extract/src/Foundry/Extract/Typography.hs -- Emit Sourced
foundry-extract/src/Foundry/Extract/Voice.hs      -- Emit Sourced
```

────────────────────────────────────────────────────────────────────────────────
                                                            // 6 // effect // system
────────────────────────────────────────────────────────────────────────────────

## 6. Effect System — Scraper Purity Gap

### 6.1 The Architecture Vision

```
PURE DATA LAYER (Straylight Stack)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Lean4 CIC     → Proofs, invariants
Haskell       → Backend, extraction, composition
PureScript    → Translation layer to WebGPU
WebGPU        → Rendering (no DOM, no CSS, no JS)

LEGACY BOUNDARY (Ingestion/Export Only)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
TypeScript    → Scrape legacy websites
CSS Export    → Generate legacy stylesheets
JS Export     → Generate legacy code
```

**JavaScript exists only at boundaries.** Once data enters the pure layer, it's typed atoms, molecules, compounds forever.

### 6.2 What Actually Exists

**The Problem:**
```
scraper/
├── src/
│   ├── index.ts      (122 lines)
│   ├── scraper.ts    (592 lines)  ← LEGACY BOUNDARY
│   ├── server.ts     (166 lines)
│   └── types.ts      (181 lines)
└── Total: 770 lines of TypeScript
```

**This is the ONLY JavaScript in the codebase.** It exists because:
1. Playwright requires Node.js
2. Many websites require JS execution to render
3. Pure HTTP fetch misses dynamic content

### 6.3 The Gap

| Component | Pure Haskell | TypeScript | Issue |
|-----------|--------------|------------|-------|
| HTTP fetch | ✗ Missing | ✓ Exists | Could be pure |
| HTML parsing | ✗ Missing | ✓ Exists | Could be pure |
| CSS parsing | ✓ attoparsec | ✓ Exists | Haskell is better |
| JS execution | Impossible | ✓ Playwright | Requires sandbox |
| DOM extraction | ✗ Missing | ✓ Exists | Could be pure |

**The 80/20 split:**
- ~80% of brands can be scraped with pure HTTP + HTML parsing
- ~20% require JS execution (SPAs, dynamic content)

### 6.4 Why This Matters

At billion-agent scale, TypeScript scraper is a bottleneck:
1. **Node.js overhead** — V8 startup, GC pauses
2. **ZMQ serialization** — Haskell ↔ Node boundary crossing
3. **Non-determinism** — JS timing variations
4. **Security surface** — Node.js has larger attack surface than Haskell

**Pure data has none of these problems.**

### 6.5 The Solution Architecture

```
PRIMARY PATH (Pure Haskell - 80% of sites)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
http-conduit  → Fetch raw HTML/CSS
html-conduit  → Parse DOM structure  
attoparsec    → Parse CSS (already exists)
              → Extract into pure Brand types

FALLBACK PATH (Sandboxed Browser - 20% of sites)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
WebDriver     → Haskell controls browser via protocol
gVisor        → Browser runs in sandbox
              → Returns rendered HTML (no JS in Haskell)
              → Parse HTML same as primary path

PURE DATA (After Boundary)
━━━━━━━━━━━━━━━━━━━━━━━━━
Extracted values are Sourced atoms
Composition is pure Haskell
LLM completion is pure prompt templates
Output is pure typed Brand compound
```

### 6.6 Files to Create/Delete

**Create (Pure Haskell Scraper):**
```
foundry-extract/src/Foundry/Extract/
├── Fetch.hs           -- HTTP client (http-conduit)
├── HTML.hs            -- DOM parsing (html-conduit)
├── HTML/Selectors.hs  -- CSS selector matching
├── HTML/Computed.hs   -- Simulate computed styles
└── Scrape.hs          -- Unified scrape interface
```

**Delete (After Migration):**
```
scraper/                -- Entire directory
├── src/
│   ├── index.ts
│   ├── scraper.ts
│   ├── server.ts
│   └── types.ts
├── package.json
└── tsconfig.json
```

### 6.7 The WebDriver Fallback

For JS-heavy sites, use WebDriver protocol from Haskell:

```haskell
-- foundry-extract/src/Foundry/Extract/WebDriver.hs
scrapeWithBrowser :: URL -> IO ScrapeResult
scrapeWithBrowser url = do
  -- Connect to sandboxed browser via WebDriver protocol
  session <- newSession webDriverConfig
  
  -- Navigate and wait for JS
  navigateTo session url
  waitForNetworkIdle session
  
  -- Get rendered HTML (browser did the JS work)
  html <- getPageSource session
  
  -- Close session
  deleteSession session
  
  -- Parse HTML with pure Haskell (same as primary path)
  pure $ parseHTML html
```

**Key insight:** We never execute JS in Haskell. The browser (sandboxed) executes JS, we just retrieve the result as HTML.

### 6.8 Dependencies to Add

```cabal
-- foundry-extract.cabal
build-depends:
  , http-conduit  >= 2.3   && < 3    -- HTTP client
  , html-conduit  >= 1.3   && < 2    -- HTML parsing
  , xml-conduit   >= 1.9   && < 2    -- XML/HTML types
  , webdriver     >= 0.12  && < 1    -- Browser control (fallback)
```

────────────────────────────────────────────────────────────────────────────────
                                                   // 7 // implementation // roadmap
────────────────────────────────────────────────────────────────────────────────

## 7. Implementation Roadmap

### 7.1 Track Dependencies

```
     ┌──────────────┐     ┌──────────────┐     ┌──────────────┐
     │   Track 1    │     │   Track 2    │     │   Track 3    │
     │   Graded     │     │  Presburger  │     │     ILP      │
     │   Monads     │     │    Proofs    │     │   Solver     │
     └──────┬───────┘     └──────┬───────┘     └──────┬───────┘
            │                    │                    │
            └────────────────────┼────────────────────┘
                                 │
                                 ▼
     ┌──────────────┐     ┌──────────────────────────────────┐
     │   Track 4    │     │           Track 5                │
     │  Provenance  │────▶│      Pure Haskell Scraper        │
     │   Wiring     │     │  (Depends on types being ready)  │
     └──────────────┘     └──────────────────────────────────┘
                                 │
                                 ▼
                    ┌────────────────────────┐
                    │   Track 6              │
                    │   LLM Integration      │
                    │   (Needs provenance)   │
                    └────────────────────────┘
```

### 7.2 Track 1: Graded Monad Instances (2 weeks)

| Week | Deliverable | Files |
|------|-------------|-------|
| 1 | Budget as Grade, instances | `Foundry/Core/Effect/Graded.hs` |
| 2 | Permission tracking, tests | `Foundry/Core/Agent/Permission.hs` |

**Success Criteria:**
```haskell
-- This compiles and enforces budget at type level
example :: Agent '["read"] 100 Result
example = do
  a <- expensiveOp    -- Costs 50
  b <- cheapOp        -- Costs 10
  pure (a, b)         -- Total: 60, under budget
```

### 7.3 Track 2: Presburger Proofs (2 weeks)

| Week | Deliverable | Files |
|------|-------------|-------|
| 1 | Timestamp ordering, budget bounds | `lean/Foundry/Timestamp.lean`, `Budget.lean` |
| 2 | omega proofs, integration | `lean/Foundry/Pipeline.lean` |

**Success Criteria:**
```lean
-- This proves without sorry
theorem budget_conservation (b : Budget) (amount : Nat) :
  spend amount b = some b' → b'.spent ≤ b.limit := by omega
```

### 7.4 Track 3: ILP Solver (3 weeks)

| Week | Deliverable | Files |
|------|-------------|-------|
| 1 | Problem types, glpk-hs setup | `Foundry/Core/Agent/ILP.hs` |
| 2 | Allocation formulation | `Foundry/Core/Agent/Allocation.hs` |
| 3 | Solver integration, tests | Tests, benchmarks |

**Success Criteria:**
```haskell
-- This finds optimal assignment
result <- allocateTasks agents tasks globalBudget
case result of
  Optimal assignment -> -- Provably best allocation
  Infeasible -> -- Proof that no valid assignment exists
```

### 7.5 Track 4: Provenance Wiring (2 weeks)

| Week | Deliverable | Files |
|------|-------------|-------|
| 1 | Update Brand types | All `Brand/*.hs` modules |
| 2 | Update extractors | All `Extract/*.hs` modules |

**Success Criteria:**
```haskell
-- Every field tracks its source
brand <- extractBrand scrapeResult
confidence brand > 0.8  -- Aggregated from all fields
needsReview brand == False  -- No defaults remaining
```

### 7.6 Track 5: Pure Haskell Scraper (3 weeks)

| Week | Deliverable | Files |
|------|-------------|-------|
| 1 | HTTP + HTML parsing | `Extract/Fetch.hs`, `Extract/HTML.hs` |
| 2 | DOM extraction, CSS simulation | `Extract/HTML/Selectors.hs` |
| 3 | WebDriver fallback, delete TS | `Extract/WebDriver.hs`, delete `scraper/` |

**Success Criteria:**
```haskell
-- Pure Haskell ingestion, no TypeScript
result <- scrapeURL "https://stripe.com"
-- Returns ScrapeResult with Sourced fields
```

### 7.7 Track 6: LLM Integration (2 weeks)

| Week | Deliverable | Files |
|------|-------------|-------|
| 1 | HTTP client, response parsing | `Foundry/Core/Brand/LLM.hs` |
| 2 | IS/NOT inference, confidence | Integration with `Completion.hs` |

**Success Criteria:**
```haskell
-- LLM fills in what can't be scraped
incomplete <- extractBrand scrapeResult
complete <- completeWithLLM incomplete
-- IS/NOT constraints now populated
isLLMCompleted (brandVoiceAttributes complete) == True
```

### 7.8 Timeline

```
Week 1-2:  Tracks 1, 2, 3 in parallel
Week 3:    Track 3 continues, Track 4 starts
Week 4-5:  Track 4 completes, Track 5 starts
Week 6-7:  Track 5 completes, Track 6 starts
Week 8:    Buffer, documentation, integration tests
```

**Minimum timeline:** 6 weeks (aggressive)
**Recommended timeline:** 8 weeks (includes buffer)

### 7.9 Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| glpk-hs build issues | Medium | High | Use limp (pure Haskell) instead |
| WebDriver complexity | Medium | Medium | Keep TypeScript as fallback initially |
| LLM response parsing | Low | Medium | Strict JSON schema, validation |
| Type-level budget complexity | High | Medium | Start with runtime, upgrade later |

### 7.10 Success Metrics

After all tracks complete:

| Metric | Current | Target |
|--------|---------|--------|
| TypeScript lines | 770 | 0 |
| Lean proofs with sorry | Unknown | 0 |
| Fields with provenance | 0% | 100% |
| Budget conservation proven | No | Yes |
| ILP allocation | No | Yes |
| Test count | 197 | 300+ |

────────────────────────────────────────────────────────────────────────────────
                                                                 // 8 // references
────────────────────────────────────────────────────────────────────────────────

## 8. References

### 8.1 Graded Monads and Effect Systems

**Graded Monads (Original Theory)**
- Katsumata, S. "Parametric Effect Monads and Semantics of Effect Systems." POPL 2014.
- Defines graded monads as monads indexed by a monoid, foundation for budget tracking.

**Co-effect Systems**
- Petricek, Orchard, Mycroft. "Coeffects: A Calculus of Context-Dependent Computation." ICFP 2014.
- Tracks what computations REQUIRE from environment (dual to effects).

**Linear Types for Resource Tracking**
- Bernardy, Boespflug, Newton, Peyton Jones, Spiwack. "Linear Haskell." POPL 2018.
- Linear types for resource accounting, budget conservation proofs.

**NumFuzz — Sensitivity Analysis**
- Azevedo de Amorim, Gaboardi, Hsu, Katsumata, Cheung. "A Semantic Account of Metric Preservation." POPL 2017.
- Graded monads where grade tracks sensitivity/error bounds.

### 8.2 Presburger Arithmetic and Decision Procedures

**Original Decision Procedure**
- Presburger, M. "Über die Vollständigkeit eines gewissen Systems der Arithmetik ganzer Zahlen." 1929.
- Proves decidability of first-order theory of (ℕ, +).

**Cooper's Algorithm**
- Cooper, D. C. "Theorem Proving in Arithmetic without Multiplication." Machine Intelligence 7, 1972.
- Quantifier elimination, basis for omega tactic.

**Omega Test**
- Pugh, W. "The Omega Test: A Fast and Practical Integer Programming Algorithm for Dependence Analysis." 1991.
- Efficient Presburger decision procedure.

**Lean's omega Tactic**
- Lean 4 Mathlib documentation
- Implements Cooper's algorithm for automated integer arithmetic proofs.

### 8.3 Integer Linear Programming

**Simplex Method**
- Dantzig, G. B. "Linear Programming and Extensions." Princeton University Press, 1963.
- Foundation of LP solving.

**Branch and Bound**
- Land, A. H.; Doig, A. G. "An Automatic Method of Solving Discrete Programming Problems." Econometrica, 1960.
- Standard approach for converting LP solution to ILP.

**glpk-hs**
- Haskell bindings to GNU Linear Programming Kit
- https://hackage.haskell.org/package/glpk-hs

**limp**
- Pure Haskell linear programming library
- https://hackage.haskell.org/package/limp

### 8.4 Web Scraping and HTML Parsing

**http-conduit**
- Haskell HTTP client library
- https://hackage.haskell.org/package/http-conduit

**html-conduit**
- HTML parsing with conduit streaming
- https://hackage.haskell.org/package/html-conduit

**WebDriver Protocol**
- W3C WebDriver specification
- https://www.w3.org/TR/webdriver/

**Playwright**
- Browser automation library (current TypeScript scraper dependency)
- https://playwright.dev/

### 8.5 Brand Strategy and Design Systems

**SMART Framework**
- Internal documentation: `docs/SMART_BRAND_FRAMEWORK.md`
- Defines Identity, Palette, Typography, Spacing, Voice, Strategy, Editorial

**Design Token Standards**
- W3C Design Tokens Community Group
- https://design-tokens.github.io/community-group/format/

**Brand Consistency at Scale**
- Internal rationale for provenance tracking: scraped vs inferred vs LLM-completed

### 8.6 Haskell Libraries

**attoparsec**
- Fast binary and textual parsing
- https://hackage.haskell.org/package/attoparsec

**aeson**
- JSON parsing/encoding
- https://hackage.haskell.org/package/aeson

**hedgehog**
- Property-based testing
- https://hackage.haskell.org/package/hedgehog

**QuickCheck**
- Property-based testing (classic)
- https://hackage.haskell.org/package/QuickCheck

### 8.7 Lean 4 Resources

**Lean 4 Documentation**
- https://lean-lang.org/lean4/doc/

**Mathlib4**
- Mathematical library for Lean 4
- https://github.com/leanprover-community/mathlib4

**SciLean**
- Scientific computing in Lean 4
- https://github.com/lecopivo/SciLean

### 8.8 Internal Documentation

**Foundry Project**
- `CLAUDE.md` — Coding standards, forbidden patterns
- `TODO.md` — Master task list
- `docs/SMART_BRAND_FRAMEWORK.md` — Brand schema specification
- `docs/BRAND_INGESTION_ARCHITECTURE.md` — System architecture
- `docs/BRAND_SCHEMA.md` — Type definitions

**Source Files (created 2026-02-27)**
- `haskell/foundry-core/src/Foundry/Core/Brand/Source.hs` — Sourced wrapper, provenance ADT
- `haskell/foundry-core/src/Foundry/Core/Brand/Completion.hs` — LLM prompt templates

**Lean Proofs**
- `lean/Foundry/Pipeline.lean` — Coeffect algebra proofs
- `lean/Foundry/Effect.lean` — Graded monad definitions

### 8.9 Related Straylight Projects

**Hydrogen**
- PureScript UI framework with WebGPU rendering
- `docs/INTERNAL/CONSTRAINT_AUDIT.md` — Reference audit document format
- Shares graded monad and Presburger verification requirements

**Ecosystem Integration**
- ZeroMQ for agent communication
- DuckDB/PostgreSQL for storage
- gVisor for sandbox isolation

────────────────────────────────────────────────────────────────────────────────
                                                                   // end // of // audit
────────────────────────────────────────────────────────────────────────────────

**Document Status**: COMPLETE
**Date**: 2026-02-27
**Next Action**: Begin Track 1 (Graded Monad Instances) or Track 4 (Provenance Wiring)
