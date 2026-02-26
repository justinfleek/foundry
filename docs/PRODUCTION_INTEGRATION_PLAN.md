# FOUNDRY ↔ COMPASS ↔ HYDROGEN Production Integration Plan

> **Status**: COUNCIL APPROVED — 5 ROUNDS COMPLETE  
> **Version**: 1.0.0  
> **Date**: 2026-02-26  
> **Target**: Pixel-perfect brand reproduction at billion-token swarm scale

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Executive Summary

This document specifies the **BULLETPROOF** production plan for TOTAL brand ingestion across three repositories:

| Repository | Location | Role | Technology |
|------------|----------|------|------------|
| **FOUNDRY** | `/home/jpyxal/jpyxal/foundry` | Brand Ingestion Engine | Haskell, Lean4 proofs |
| **HYDROGEN** | `/home/jpyxal/jpyxal/hydrogen` | Frontend Schema & UI | PureScript, WebGPU/WebGL |
| **COMPASS** | `/home/jpyxal/jpyxal/COMPASS` | Marketing Automation Platform | Haskell, PostgreSQL, MAESTRO |

**Goal**: Enable TOTAL brand ingestion — every SKU, logo variant, font, color, spacing token, voice attribute — with:

- UUID5 determinism across all systems
- Full provenance tracking
- Co-effect algebra with graded monads
- Lean4 verified invariants (zero sorry, zero axiom)
- Pixel-perfect reproduction from Hydrogen atoms
- Swarm-scale operation (1B tokens, 1000 tok/s)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Table of Contents

1. [Current State Assessment](#1-current-state-assessment)
2. [Type Authority Architecture](#2-type-authority-architecture)
3. [Gap Analysis](#3-gap-analysis)
4. [Bottleneck Analysis](#4-bottleneck-analysis)
5. [Pixel-Perfect Reproduction Requirements](#5-pixel-perfect-reproduction-requirements)
6. [Production Roadmap](#6-production-roadmap)
7. [Cross-Repository Integration](#7-cross-repository-integration)
8. [Swarm Scale Architecture](#8-swarm-scale-architecture)
9. [Verification Requirements](#9-verification-requirements)
10. [Success Criteria](#10-success-criteria)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 1. Current State Assessment

### 1.1 FOUNDRY Status

| Component | Build | Tests | Notes |
|-----------|-------|-------|-------|
| **foundry-core** | ✅ | 148 passing | Brand, Agent, Effect, Evring, Sigil |
| **foundry-extract** | ✅ | 48 passing | Color, Typography, Spacing, Voice |
| **foundry-storage** | ✅ | 22 passing | HAMT, DuckDB, Postgres adapters |
| **foundry-scraper** | ❌ BLOCKED | 0 | Requires libzmq — DISABLED in cabal.project |
| **Lean4 (Cornell)** | ⚠️ PARTIAL | N/A | Import fixed, ByteArray API mismatch |
| **Lean4 (Brand)** | ❌ BLOCKED | N/A | Blocked on Hydrogen dependency |

**Codebase Size:**

| Language | Source Lines | Test Lines |
|----------|--------------|------------|
| Haskell | ~15,700 | ~5,800 |
| PureScript | ~8,000 | 0 |
| Lean4 | ~22,500 | N/A |
| TypeScript | ~1,050 | 0 |

### 1.2 HYDROGEN Status

| Component | Files | Status |
|-----------|-------|--------|
| **Schema Pillars** | 100+ | ✅ 12 pillars implemented |
| **Schema/Brand** | 37 | ✅ Complete atomic structure |
| **Schema/Color** | 3+ | ✅ OKLCH, Blend, Contrast |
| **Schema/Dimension** | 25+ | ✅ Complete spatial primitives |
| **Runtime/DOM** | ✅ | ✅ Browser target |
| **Runtime/WebGL** | ⚠️ | Partial |
| **Lean4 Proofs** | ⚠️ | In `proofs/` directory |

**The Schema is comprehensive:**

```
hydrogen/src/Hydrogen/Schema/
├── Audio/           (17 files) — Voice, Synthesis, Spatial
├── Brand/           (37 files) — Logo, Token, Theme, Voice, Identity
├── Color/           (3 files)  — Channel, Blend, Contrast
├── Dimension/       (25 files) — Point2D, Grid, Viewport, Breakpoint
├── Geometry.purs    — Primitives, transforms
├── Typography.purs  — Scale, weights, families
├── Motion.purs      — Temporal, easing
├── Elevation.purs   — Shadows, depth
├── Material.purs    — Fill, texture
├── Reactive/        (20 files) — States, validation
├── Gestural.purs    — Input patterns
├── Spatial.purs     — 3D, AR/VR
└── Bounded.purs     — Bounded primitives
```

### 1.3 COMPASS Status

| Component | Status | Notes |
|-----------|--------|-------|
| **14 Haskell packages** | ✅ ALL BUILD | compass-core, compass-agents, etc. |
| **MAESTRO** | ✅ | 5-layer pipeline, 64 agents |
| **typed-compass** | ✅ | Haskell + Lean + PureScript subdirs |
| **Authentication** | ✅ | Bcrypt, rate limiting, graded monads |
| **Knowledge Graph** | ⚠️ | Entity types exist, brand types MISSING |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 2. Type Authority Architecture

### 2.1 Resolved Type Hierarchy

**DECISION**: Three-layer architecture with Lean4 as CIC (Calculus of Inductive Constructions)

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  LAYER 0: Lean4 (CIC — Proof Layer)                                             │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  Location: foundry/lean/, hydrogen/proofs/                                      │
│                                                                                 │
│  Purpose: PROVE invariants — NOT define runtime types                           │
│                                                                                 │
│  Proves:                                                                        │
│    • traits_nonempty: ∀ voice, length(voice.traits) > 0                         │
│    • is_not_disjoint: ∀ attr, attr.is ∩ attr.not = ∅                            │
│    • palette_has_primary: ∃ color ∈ palette, color.role = Primary               │
│    • typography_monotonic: ∀ l1 l2, l1 < l2 → size(l1) < size(l2)               │
│    • spacing_ratio_gt_one: ∀ spacing, spacing.ratio > 1                         │
│    • uuid5_deterministic: ∀ domain, uuid5(domain) = uuid5(domain)               │
│    • coeffect_algebra: associativity, monotonicity, idempotency                 │
│    • serialization_roundtrip: decode(encode(x)) = x                             │
│                                                                                 │
│  ZERO sorry. ZERO axiom (except cryptographic primitives). ZERO admit.          │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ Extracted types / verified invariants
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  LAYER 1: Haskell (Backend — Runtime Layer)                                     │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  Location: foundry/haskell/, COMPASS/typed-compass/haskell/                     │
│                                                                                 │
│  Defines:                                                                       │
│    • Runtime types with StrictData (!bang patterns)                             │
│    • Graded monad implementation (Agent perms budget ctx a)                     │
│    • Co-effect algebra (discharge, tensor, satisfy)                             │
│    • Smart constructors enforcing Lean4-proven invariants                       │
│    • Extraction pipeline (Color, Typography, Spacing, Voice)                    │
│    • Storage adapters (HAMT L1, DuckDB L2, PostgreSQL L3)                       │
│    • ZMQ transport, NDJSON serialization                                        │
│    • COMPASS export projections                                                 │
│                                                                                 │
│  Exports: JSON Schema for frontend consumption                                  │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ JSON Schema / WebSocket / gRPC
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  LAYER 2: PureScript Hydrogen (Frontend — Display Layer)                        │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  Location: hydrogen/src/Hydrogen/                                               │
│                                                                                 │
│  Defines:                                                                       │
│    • 12-pillar Schema (atoms, molecules, compounds)                             │
│    • Element type (pure GPU instruction set as data)                            │
│    • Graded Element with Effect/CoEffect tracking                               │
│    • Target renderers (DOM, Canvas, WebGL, WebGPU)                              │
│    • Brand visualization components                                             │
│                                                                                 │
│  NO JavaScript except at boundaries. NO CSS except export.                      │
│  Everything is data. Same Element → same pixels. Always.                        │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### 2.2 Data Flow

```
  Coca-Cola Website
         │
         │ Playwright (sandboxed)
         ▼
┌─────────────────┐
│  ScrapeResult   │  Raw HTML, CSS, fonts, images, computed styles
└────────┬────────┘
         │
         │ ZMQ PUSH (foundry-scraper → foundry-extract)
         ▼
┌─────────────────┐
│  Extractors     │  Color, Typography, Spacing, Voice, Logo, Layout
│  (Haskell)      │
└────────┬────────┘
         │
         │ Smart constructors (Lean4 invariants enforced)
         ▼
┌─────────────────┐
│  CompleteBrand  │  Unified 18+ field compound type
│  (Haskell)      │
└────────┬────────┘
         │
         │ NDJSON over ZMQ PUSH
         ▼
┌─────────────────┐
│  COMPASS        │  Knowledge graph entities
│  (PostgreSQL)   │
└────────┬────────┘
         │
         │ gRPC / AgentBrandContext
         ▼
┌─────────────────┐
│  MAESTRO        │  64 AI agents with BE:/NEVER BE: prompts
│  (Haskell)      │
└────────┬────────┘
         │
         │ JSON over WebSocket
         ▼
┌─────────────────┐
│  Hydrogen UI    │  Brand dashboard, diff viewer, export
│  (PureScript)   │
└─────────────────┘
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 3. Gap Analysis

### 3.1 Critical Missing Components

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  FOUNDRY GAPS                                                                   │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  TYPES NOT IN HASKELL (exist in Hydrogen PureScript):                           │
│                                                                                 │
│  Layout System:                                                                 │
│    □ GridSystem (columns, gutters, margins, areas)                              │
│    □ Breakpoint (viewport triggers, media queries)                              │
│    □ SafeZone (content boundaries)                                              │
│    □ AspectRatio (locked proportions)                                           │
│                                                                                 │
│  UI Elements:                                                                   │
│    □ ButtonSpec (states, radii, shadows, lighting direction)                    │
│    □ InputSpec (focus rings, validation states)                                 │
│    □ CardSpec (elevation, padding ratios)                                       │
│    □ NeumorphicParams (light direction, depth, inner gradients)                 │
│                                                                                 │
│  Graphic Elements:                                                              │
│    □ Pattern (SVG-derived, tiling rules)                                        │
│    □ Texture (noise params, grain)                                              │
│    □ IconStyle (stroke width, corner radius)                                    │
│    □ IllustrationStyle (color, line weight, fill)                               │
│                                                                                 │
│  Modes:                                                                         │
│    □ ColorMode (light/dark/high-contrast)                                       │
│    □ TokenMapping (semantic → actual color resolution)                          │
│    □ ModeTransition (animation timing)                                          │
│                                                                                 │
│  Imagery:                                                                       │
│    □ PhotographyStyle (color grading params, 3-point lift/gamma/gain)           │
│    □ ImageCategory (approved content types)                                     │
│    □ CropRule (focal point, aspect locks)                                       │
│                                                                                 │
│  MISSING UNIFIED TYPES:                                                         │
│    □ CompleteBrand (18+ field unified type)                                     │
│    □ BrandOntology (term aliases, SKU patterns)                                 │
│    □ BrandHierarchy (sub-brand inheritance)                                     │
│    □ AgentBrandContext (MAESTRO consumption format)                             │
│                                                                                 │
│  MISSING PIPELINE:                                                              │
│    □ COMPASS export (projection to KG entities)                                 │
│    □ ZMQ bridge (scraper → Haskell)                                             │
│    □ NDJSON transport                                                           │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### 3.2 Lean4 Proof Gaps

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  LEAN4 PROOF STATUS                                                             │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  EXISTING (foundry/lean/):                                                      │
│    ✅ Foundry.Pipeline (320 lines) — Graded monads, coeffects                   │
│    ✅ Foundry.Sigil.Sigil (800+ lines) — 18 theorems, 0 sorry                   │
│    ✅ Foundry.Cornell.Proofs (850+ lines) — Box codecs, roundtrip               │
│    ✅ Foundry.Cornell.* (~700KB) — Wire formats                                 │
│    ✅ Foundry.Continuity (5.5k lines) — Coeffect algebra                        │
│                                                                                 │
│  INCOMPLETE:                                                                    │
│    ⚠️ Typography.lean:212 — SORRY (scale monotonicity)                          │
│    ⚠️ Voice.lean:166 — SORRY (eraseDups length preservation)                    │
│    ⚠️ Cornell/Proofs.lean — ByteArray API mismatch (Lean4 4.15.0)               │
│                                                                                 │
│  MISSING:                                                                       │
│    ❌ Brand.lean — Compound composition proofs                                  │
│    ❌ CompleteBrand serialization roundtrip                                     │
│    ❌ WCAG accessibility guarantee                                              │
│    ❌ Ontology term resolution correctness                                      │
│    ❌ Hierarchy inheritance preservation                                        │
│    ❌ Cache invalidation consistency                                            │
│                                                                                 │
│  AXIOMS IN USE (justified):                                                     │
│    • zlib_deterministic (Git.lean) — Trust zlib decompressor                    │
│    • zlib_consumption_bound (Git.lean) — Bounded consumption                    │
│    • nixString_roundtrip (Nix.lean) — ByteArray tedium                          │
│    • sha256_* — Cryptographic assumption                                        │
│    • uuid5_* — RFC 4122 Section 4.3                                             │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### 3.3 Scraper Pipeline Gaps

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  SCRAPER STATUS                                                                 │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  foundry-scraper: COMMENTED OUT in cabal.project                                │
│  Reason: Requires libzmq                                                        │
│                                                                                 │
│  scraper/src/scraper.ts: 1057 lines, NOT CONNECTED                              │
│    ✅ Playwright is configured                                                  │
│    ✅ ZMQ publisher exists                                                      │
│    ❌ No Haskell consumer                                                       │
│                                                                                 │
│  MISSING FOR PRODUCTION:                                                        │
│    ❌ URL Discovery (SearXNG integration)                                       │
│    ❌ Brand page heuristics (/about, /brand, /press)                            │
│    ❌ Sitemap parsing                                                           │
│    ❌ robots.txt compliance                                                     │
│    ❌ Rate limiting per domain                                                  │
│    ❌ Captcha handling (Cloudflare, etc.)                                       │
│    ❌ gVisor sandboxing at scale                                                │
│    ❌ Worker pool / horizontal scaling                                          │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### 3.4 Extraction Completeness

| Extractor | Status | Accuracy Target | Notes |
|-----------|--------|-----------------|-------|
| **Color** | ✅ COMPLETE | 95%+ | k-means clustering, OKLCH, role assignment |
| **Typography** | ✅ COMPLETE | 90%+ | Font family, scale detection, weights |
| **Spacing** | ✅ COMPLETE | 85%+ | Grid inference, base unit, ratio |
| **Voice** | ⚠️ PARTIAL | 70% | Needs LLM for IS/NOT mining |
| **Logo** | ⚠️ PARTIAL | 60% | Detection exists, variants/lockups NO |
| **Layout** | ❌ MISSING | — | Grid system, breakpoints, safe zones |
| **UI Elements** | ❌ MISSING | — | Button/input/card specs |
| **Graphic Elements** | ❌ MISSING | — | Patterns, textures, icons |
| **Modes** | ❌ MISSING | — | Light/dark detection |
| **Imagery** | ❌ MISSING | — | Photography style, color grading |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 4. Bottleneck Analysis

### 4.1 Swarm Scale Parameters

```
1B tokens ÷ 1000 tok/s = 1,000,000 seconds = 11.5 days continuous

Assuming average brand = 50KB extracted data:
  - 1B tokens ≈ 4GB raw text
  - ≈ 100,000 brand pages
  - ≈ 10,000 unique brands (10 pages each)
```

### 4.2 Identified Bottlenecks

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  BOTTLENECK 1: PLAYWRIGHT INSTANCES                                             │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Chromium: ~500MB RAM each                                                      │
│  100 concurrent: 50GB RAM                                                       │
│  Page load: 2-5s average                                                        │
│  Max throughput: 20-50 pages/second (single node)                               │
│                                                                                 │
│  SOLUTION:                                                                      │
│    □ Distribute across 20+ nodes                                                │
│    □ gVisor sandboxing per instance                                             │
│    □ ZMQ DEALER/ROUTER for load balancing                                       │
│    □ Connection pooling                                                         │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────────┐
│  BOTTLENECK 2: LLM VOICE EXTRACTION                                             │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Each page needs tone analysis                                                  │
│  LLM call: 200-500ms                                                            │
│  100,000 pages × 300ms = 8+ hours                                               │
│                                                                                 │
│  SOLUTION:                                                                      │
│    □ Batch processing (multiple pages per LLM call)                             │
│    □ Local models (Qwen3-TTS in COMPASS already)                                │
│    □ Caching by domain (same brand = same voice)                                │
│    □ Rule-based pre-filtering                                                   │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────────┐
│  BOTTLENECK 3: ZMQ MESSAGE BUS                                                  │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  DEALER/ROUTER: ~100K msg/s theoretical                                         │
│  With serialization overhead: ~10K msg/s realistic                              │
│                                                                                 │
│  SOLUTION:                                                                      │
│    □ Multiple brokers, sharding by domain hash                                  │
│    □ Binary protocol (Sigil) instead of JSON                                    │
│    □ Zero-copy transfers where possible                                         │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────────┐
│  BOTTLENECK 4: POSTGRESQL WRITES                                                │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  Bulk insert: 10K rows/second                                                   │
│  With indices: 2K rows/second                                                   │
│                                                                                 │
│  SOLUTION:                                                                      │
│    □ DuckDB staging → batch commit                                              │
│    □ Async commit mode                                                          │
│    □ Partitioning by brand UUID prefix                                          │
│    □ UNLOGGED tables for staging                                                │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────────┐
│  BOTTLENECK 5: LEAN4 PROOF CHECKING                                             │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  DO NOT DO THIS AT RUNTIME                                                      │
│                                                                                 │
│  Proofs are compile-time only.                                                  │
│  Runtime: smart constructors with O(1) validation.                              │
│                                                                                 │
│  Invariants proven once → enforced by construction forever.                     │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### 4.3 Missing Distributed Infrastructure

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  DISTRIBUTED INFRASTRUCTURE GAPS                                                │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  1. No Worker Pool                                                              │
│     □ Single process model                                                      │
│     □ No task distribution                                                      │
│     □ No failure recovery                                                       │
│                                                                                 │
│  2. No Coordination                                                             │
│     □ No domain locking (concurrent scrape same URL)                            │
│     □ No rate limit coordination across nodes                                   │
│     □ No progress tracking                                                      │
│                                                                                 │
│  3. No Backpressure                                                             │
│     □ Unbounded queues                                                          │
│     □ Memory exhaustion on spike                                                │
│     □ No circuit breakers                                                       │
│                                                                                 │
│  4. No Observability                                                            │
│     □ No metrics export                                                         │
│     □ No distributed tracing                                                    │
│     □ No alerting                                                               │
│                                                                                 │
│  NEEDED:                                                                        │
│     □ ZMQ DEALER/ROUTER topology                                                │
│     □ Redis for coordination / locks                                            │
│     □ Prometheus metrics                                                        │
│     □ Jaeger tracing                                                            │
│     □ Kubernetes operators OR Nix-based orchestration                           │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 5. Pixel-Perfect Reproduction Requirements

### 5.1 What "Pixel-Perfect in Data Form" Means

For Coca-Cola to be 100% reproducible from Hydrogen atoms:

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  COMPLETE DESIGN SYSTEM CAPTURE                                                 │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  IDENTITY (extractable):                                                        │
│    ✅ Name: "Coca-Cola"                                                         │
│    ✅ UUID5: deterministic from domain                                          │
│    ✅ Domain: coca-cola.com                                                     │
│                                                                                 │
│  PALETTE (extractable):                                                         │
│    ✅ Primary: #F40009 (Coca-Cola Red)                                          │
│    ✅ Secondary: #000000, #FFFFFF                                               │
│    ✅ OKLCH representation with gamut proofs                                    │
│    ✅ Contrast ratios verified (WCAG AA)                                        │
│                                                                                 │
│  TYPOGRAPHY (extractable):                                                      │
│    ✅ Spencerian Script (logo, locked)                                          │
│    ✅ TCCC Unity (headlines)                                                    │
│    ✅ Scale ratio, weights, line heights                                        │
│                                                                                 │
│  LOGO (partially extractable):                                                  │
│    ✅ Primary lockup detection                                                  │
│    ❌ Variant enumeration (horizontal, vertical, icon-only)                     │
│    ❌ Clear space rules (relative to "C" height)                                │
│    ❌ Minimum sizing per variant                                                │
│    ❌ Color variants (full color, white, black)                                 │
│    ❌ Background restrictions                                                   │
│    ❌ Common errors list                                                        │
│                                                                                 │
│  VOICE (partially extractable):                                                 │
│    ✅ IS/NOT constraints structure exists                                       │
│    ❌ Actual extraction from copy (needs LLM)                                   │
│    ❌ Vocabulary mining                                                         │
│    ❌ Tone classification                                                       │
│                                                                                 │
│  LAYOUT (not extractable yet):                                                  │
│    ❌ Grid system (columns, gutters)                                            │
│    ❌ Breakpoint definitions                                                    │
│    ❌ Safe zones                                                                │
│                                                                                 │
│  MISSING ENTIRELY:                                                              │
│    ❌ Motion (animation timing, easing curves)                                  │
│    ❌ Sound (sonic branding, audio signatures)                                  │
│    ❌ 3D (material properties, lighting)                                        │
│    ❌ AR/VR guidelines                                                          │
│    ❌ Packaging specifications                                                  │
│    ❌ Environmental/signage                                                     │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### 5.2 Hydrogen Atom Completeness

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  HYDROGEN ATOM/MOLECULE/COMPOUND COVERAGE                                       │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  ATOMS (primitives with bounds) — EXISTS IN HYDROGEN:                           │
│    ✅ Lightness, Chroma, Hue (OKLCH)                                            │
│    ✅ FontWeight (100-900)                                                      │
│    ✅ SpacingUnit (px, positive)                                                │
│    ✅ AnimationDuration (ms, positive)                                          │
│    ✅ EasingFunction (cubic-bezier params)                                      │
│    ✅ Opacity (0-1)                                                             │
│    ✅ BorderRadius (px or %)                                                    │
│    ✅ Angle (degrees, 0-360)                                                    │
│    ✅ AspectRatio (width:height)                                                │
│                                                                                 │
│  MOLECULES — EXISTS IN HYDROGEN:                                                │
│    ✅ OKLCH (L + C + H)                                                         │
│    ✅ TypeScale (base + ratio + levels)                                         │
│    ✅ Shadow (offset + blur + spread + color)                                   │
│    ✅ Border (width + style + color + radius)                                   │
│    ✅ Transition (property + duration + easing + delay)                         │
│    ✅ GradientStop (color + position)                                           │
│                                                                                 │
│  COMPOUNDS — EXISTS IN HYDROGEN:                                                │
│    ✅ BrandPalette, BrandTypography, BrandVoice                                 │
│    ✅ LogoSystem, LogoLockup, LogoVariants                                      │
│    ✅ Theme, TokenMapping                                                       │
│                                                                                 │
│  PROBLEM: These exist in PureScript but NOT in Haskell                          │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### 5.3 Extraction → Reproduction Pipeline

```
For pixel-perfect reproduction, we need:

1. EXTRACT from website → Hydrogen atoms
2. STORE as CompleteBrand (Haskell + PostgreSQL)
3. TRANSMIT to COMPASS knowledge graph
4. CONSUME by MAESTRO agents (AgentBrandContext)
5. RENDER via Hydrogen (PureScript → WebGPU)

Each step must preserve ALL information.
No lossy transformations.
Same UUID5 across all systems.
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 6. Production Roadmap

### 6.1 Phase 0: Foundation Repair (2 weeks)

**OBJECTIVE**: Single source of truth, working pipeline

**DELIVERABLES**:

| Task | Priority | Effort |
|------|----------|--------|
| Enable foundry-scraper in cabal.project | P0 | 1 hour |
| Connect Playwright → ZMQ → Haskell | P0 | 2 days |
| Port ALL Hydrogen Brand atoms to Haskell | P0 | 3 days |
| Create CompleteBrand unified type | P0 | 2 days |
| Create BrandOntology | P0 | 1 day |
| Create BrandHierarchy | P1 | 1 day |
| Aeson instances with roundtrip tests | P0 | 2 days |

**SUCCESS CRITERIA**:
```
✓ Single `cabal build all` builds everything
✓ scraper.ts can send to Haskell and get response
✓ All Hydrogen Brand types have Haskell equivalents
✓ CompleteBrand JSON roundtrip: decode(encode(x)) == x
```

### 6.2 Phase 1: Proof Completion (2 weeks)

**OBJECTIVE**: Zero sorries, full invariant coverage

**DELIVERABLES**:

| Task | Priority | Effort |
|------|----------|--------|
| Fix Typography.lean:212 (scale monotonicity) | P0 | 1 day |
| Fix Voice.lean:166 (eraseDups length) | P0 | 1 day |
| Fix Cornell ByteArray API for Lean4 4.15.0 | P0 | 2 days |
| Create Brand.lean (compound composition) | P0 | 3 days |
| Prove WCAG accessibility guarantee | P1 | 2 days |
| Prove serialization roundtrip | P1 | 2 days |
| Property tests matching Lean4 theorems | P0 | 2 days |

**SUCCESS CRITERIA**:
```
✓ `lake build` with zero sorry
✓ Lean4 types match Haskell exactly
✓ Hedgehog property tests pass for all invariants
```

### 6.3 Phase 2: Extraction Completeness (3 weeks)

**OBJECTIVE**: Extract ALL brand data, not just color/type/spacing

**DELIVERABLES**:

| Task | Priority | Effort |
|------|----------|--------|
| Logo extraction (variants, lockups, clear space) | P0 | 3 days |
| Voice extraction (LLM-assisted IS/NOT mining) | P0 | 4 days |
| Layout extraction (grid system detection) | P1 | 2 days |
| UI element extraction (button/input specs) | P1 | 2 days |
| Mode detection (light/dark stylesheets) | P1 | 2 days |
| Imagery style extraction | P2 | 2 days |
| Pattern/texture detection | P2 | 1 day |

**SUCCESS CRITERIA**:
```
✓ Extract 90%+ of Coca-Cola brand guide programmatically
✓ Human verification on 10 major brands
✓ Confidence scores on all extracted values
✓ 48+ additional tests passing
```

### 6.4 Phase 3: COMPASS Integration (2 weeks)

**OBJECTIVE**: Foundry → COMPASS pipeline working

**DELIVERABLES**:

| Task | Priority | Effort |
|------|----------|--------|
| COMPASS export (CompleteBrand → NDJSON entities) | P0 | 3 days |
| AgentBrandContext for MAESTRO | P0 | 2 days |
| BE:/NEVER BE: prompt generation | P0 | 1 day |
| ZMQ PUSH to COMPASS | P0 | 2 days |
| Entity type additions to COMPASS KG | P0 | 1 day |
| Cache invalidation events | P1 | 2 days |

**SUCCESS CRITERIA**:
```
✓ COMPASS receives and stores brand from Foundry
✓ MAESTRO can fetch AgentBrandContext <10ms
✓ Voice constraints generate valid LLM prompts
✓ Brand changes propagate to all caches <100ms
```

### 6.5 Phase 4: Swarm Scale (3 weeks)

**OBJECTIVE**: 1000 tok/s, 1B tokens, distributed

**DELIVERABLES**:

| Task | Priority | Effort |
|------|----------|--------|
| Worker pool (ZMQ DEALER/ROUTER) | P0 | 3 days |
| Domain coordination (Redis locks) | P0 | 2 days |
| Rate limiting (per-domain, robots.txt) | P0 | 2 days |
| Backpressure (bounded queues, circuit breakers) | P0 | 2 days |
| Horizontal scraper scaling (Nix flake) | P0 | 3 days |
| gVisor sandboxing at scale | P1 | 2 days |
| DuckDB staging → PostgreSQL batch commit | P1 | 2 days |

**SUCCESS CRITERIA**:
```
✓ 100 concurrent scrapers sustained
✓ 10K brands/hour throughput
✓ <1% failure rate
✓ Graceful degradation under load
```

### 6.6 Phase 5: Observability + Hardening (2 weeks)

**OBJECTIVE**: Production-grade reliability

**DELIVERABLES**:

| Task | Priority | Effort |
|------|----------|--------|
| Prometheus metrics | P0 | 2 days |
| Jaeger distributed tracing | P1 | 2 days |
| Alerting (PagerDuty/Slack) | P1 | 1 day |
| Grafana dashboard | P1 | 1 day |
| Security audit (sandbox escape, injection) | P0 | 3 days |
| Chaos testing (node failure, network partition) | P1 | 2 days |
| Load testing (10x expected peak) | P0 | 2 days |

**SUCCESS CRITERIA**:
```
✓ Mean time to detection <1 minute
✓ Mean time to recovery <5 minutes
✓ Zero security vulnerabilities
✓ 99.9% uptime SLA achievable
```

### 6.7 Gantt Overview

```
Week:   1  2  3  4  5  6  7  8  9 10 11 12 13 14
        ├──┴──┼──┴──┼──┴──┴──┼──┴──┼──┴──┴──┼──┴──┤
Phase 0 ████████
Phase 1          ████████
Phase 2                   ████████████
Phase 3                                ████████
Phase 4                                         ████████████
Phase 5                                                      ████████

TOTAL: 14 weeks (3.5 months) to production-ready swarm scale
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 7. Cross-Repository Integration

### 7.1 Type Synchronization

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  TYPE SYNC PROTOCOL                                                             │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  FOUNDRY (Haskell) types MUST match HYDROGEN (PureScript) types                 │
│                                                                                 │
│  Sync mechanism:                                                                │
│    1. Haskell defines canonical types (foundry-core)                            │
│    2. CI generates JSON Schema from Haskell                                     │
│    3. PureScript types validated against JSON Schema                            │
│    4. Lean4 proofs reference Haskell types                                      │
│                                                                                 │
│  On type change:                                                                │
│    1. Update Haskell type                                                       │
│    2. Update Lean4 proof (if invariants affected)                               │
│    3. Regenerate JSON Schema                                                    │
│    4. Update PureScript type (manual or codegen)                                │
│    5. CI validates roundtrip                                                    │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### 7.2 COMPASS Entity Mapping

```sql
-- Entity types to add to COMPASS knowledge graph
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'brand';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'brand_voice';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'brand_palette';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'brand_typography';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'brand_spacing';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'brand_logo';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'brand_mode';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'tone_attribute';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'color_oklch';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'font_family';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'gradient';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'pattern';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'layout_grid';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'ui_button';
ALTER TYPE entity_type ADD VALUE IF NOT EXISTS 'vocabulary_term';

-- Relationship types
ALTER TYPE relationship_type ADD VALUE IF NOT EXISTS 'has_voice';
ALTER TYPE relationship_type ADD VALUE IF NOT EXISTS 'has_palette';
ALTER TYPE relationship_type ADD VALUE IF NOT EXISTS 'has_typography';
ALTER TYPE relationship_type ADD VALUE IF NOT EXISTS 'has_tone_attribute';
ALTER TYPE relationship_type ADD VALUE IF NOT EXISTS 'tone_is_descriptor';
ALTER TYPE relationship_type ADD VALUE IF NOT EXISTS 'tone_not_descriptor';
ALTER TYPE relationship_type ADD VALUE IF NOT EXISTS 'inherits_from';
ALTER TYPE relationship_type ADD VALUE IF NOT EXISTS 'shares_asset';
```

### 7.3 MAESTRO AgentBrandContext

```haskell
-- foundry-core/src/Foundry/Core/Brand/AgentContext.hs

-- | Context provided to MAESTRO agents for brand-aware generation
data AgentBrandContext = AgentBrandContext
  { -- Identity
    abcBrandName        :: !Text
  , abcIndustry         :: !Text
  
    -- Voice (critical for LLM)
  , abcToneDescription  :: !Text
  , abcVoiceBePrompt    :: !Text       -- "BE: confident, clear, ..."
  , abcVoiceNeverBe     :: !Text       -- "NEVER BE: aggressive, ..."
  , abcPreferredTerms   :: !(Vector Text)
  , abcForbiddenTerms   :: !(Vector Text)
  
    -- Visual (for descriptions)
  , abcPrimaryColors    :: !(Vector Text)  -- Hex codes
  , abcFontHeading      :: !Text
  , abcFontBody         :: !Text
  
    -- Custom
  , abcCustomContext    :: !(Map Text Text)
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Generate BE:/NEVER BE: prompts from ToneAttribute
toVoicePrompt :: BrandVoice -> (Text, Text)
toVoicePrompt voice =
  let beList = concatMap (Set.toList . constraintIs . attributeConstraint) 
                         (V.toList (brandVoiceAttributes voice))
      neverList = concatMap (Set.toList . constraintNot . attributeConstraint)
                            (V.toList (brandVoiceAttributes voice))
  in ( "BE: " <> T.intercalate ", " (map unToneDescriptor beList)
     , "NEVER BE: " <> T.intercalate ", " (map unToneDescriptor neverList)
     )
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 8. Swarm Scale Architecture

### 8.1 Distributed Topology

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              SWARM ARCHITECTURE                                 │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  ┌───────────────────────────────────────────────────────────────────────────┐  │
│  │  ORCHESTRATION LAYER                                                      │  │
│  │                                                                           │  │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐                    │  │
│  │  │ Coordinator  │  │ Rate Limiter │  │ Progress     │                    │  │
│  │  │ (Redis)      │  │ (Redis)      │  │ Tracker      │                    │  │
│  │  └──────────────┘  └──────────────┘  └──────────────┘                    │  │
│  │                                                                           │  │
│  └───────────────────────────────────────────────────────────────────────────┘  │
│                                          │                                      │
│                                          │ ZMQ ROUTER                          │
│                                          ▼                                      │
│  ┌───────────────────────────────────────────────────────────────────────────┐  │
│  │  SCRAPING LAYER                                                           │  │
│  │                                                                           │  │
│  │  ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ... ┌────────┐             │  │
│  │  │ Worker │ │ Worker │ │ Worker │ │ Worker │     │ Worker │             │  │
│  │  │   1    │ │   2    │ │   3    │ │   4    │     │  100   │             │  │
│  │  │gVisor  │ │gVisor  │ │gVisor  │ │gVisor  │     │gVisor  │             │  │
│  │  │Playwrt │ │Playwrt │ │Playwrt │ │Playwrt │     │Playwrt │             │  │
│  │  └────────┘ └────────┘ └────────┘ └────────┘     └────────┘             │  │
│  │                                                                           │  │
│  └───────────────────────────────────────────────────────────────────────────┘  │
│                                          │                                      │
│                                          │ ZMQ PUSH                            │
│                                          ▼                                      │
│  ┌───────────────────────────────────────────────────────────────────────────┐  │
│  │  EXTRACTION LAYER                                                         │  │
│  │                                                                           │  │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐                    │  │
│  │  │ Extractor    │  │ Extractor    │  │ Extractor    │                    │  │
│  │  │ Pool 1       │  │ Pool 2       │  │ Pool 3       │                    │  │
│  │  │ (Haskell)    │  │ (Haskell)    │  │ (Haskell)    │                    │  │
│  │  └──────────────┘  └──────────────┘  └──────────────┘                    │  │
│  │                                                                           │  │
│  └───────────────────────────────────────────────────────────────────────────┘  │
│                                          │                                      │
│                                          │ NDJSON over ZMQ PUSH                │
│                                          ▼                                      │
│  ┌───────────────────────────────────────────────────────────────────────────┐  │
│  │  STORAGE LAYER                                                            │  │
│  │                                                                           │  │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐                    │  │
│  │  │ L1: HAMT     │─▶│ L2: DuckDB   │─▶│ L3: Postgres │                    │  │
│  │  │ (~1ms)       │  │ (~10ms)      │  │ (~100ms)     │                    │  │
│  │  └──────────────┘  └──────────────┘  └──────────────┘                    │  │
│  │                                                                           │  │
│  └───────────────────────────────────────────────────────────────────────────┘  │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### 8.2 Backpressure Strategy

```haskell
-- Bounded queue with backpressure
data BoundedQueue a = BoundedQueue
  { bqCapacity   :: !Int
  , bqHighWater  :: !Int  -- Slow down at this level
  , bqLowWater   :: !Int  -- Resume at this level
  , bqQueue      :: !(TBQueue a)
  , bqState      :: !(TVar QueueState)
  }

data QueueState
  = Flowing      -- Normal operation
  | Throttled    -- Slowing down
  | Blocked      -- Queue full, rejecting

-- Circuit breaker
data CircuitBreaker = CircuitBreaker
  { cbState          :: !(TVar CBState)
  , cbFailureCount   :: !(TVar Int)
  , cbFailureThreshold :: !Int
  , cbResetTimeout   :: !NominalDiffTime
  }

data CBState
  = Closed    -- Normal, allowing requests
  | Open      -- Tripped, rejecting requests
  | HalfOpen  -- Testing if service recovered
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 9. Verification Requirements

### 9.1 Lean4 Proofs Required

| Theorem | File | Status | Priority |
|---------|------|--------|----------|
| `TypeScale.monotonic` | Typography.lean | SORRY | P0 |
| `TraitSet.fromList_nonempty` | Voice.lean | SORRY | P0 |
| `ToneConstraint.disjoint` | Voice.lean | ✅ | — |
| `CompleteBrand.composition` | Brand.lean | MISSING | P0 |
| `CompleteBrand.roundtrip` | Brand.lean | MISSING | P0 |
| `BrandPalette.has_primary` | Palette.lean | ✅ | — |
| `BrandPalette.wcag_aa` | Palette.lean | MISSING | P1 |
| `Ontology.resolve_total` | Ontology.lean | MISSING | P1 |
| `Hierarchy.inherit_preserves` | Hierarchy.lean | MISSING | P1 |
| `Cache.invalidation_consistent` | Cache.lean | MISSING | P2 |

### 9.2 Property Tests Required

```haskell
-- Hedgehog property tests matching Lean4 theorems

-- Typography
prop_type_scale_monotonic :: Property
prop_type_scale_monotonic = property $ do
  scale <- forAll genTypeScale
  l1 <- forAll (Gen.int (Range.linear (-5) 10))
  l2 <- forAll (Gen.filter (> l1) (Gen.int (Range.linear (-5) 10)))
  assert $ sizeAt scale l1 < sizeAt scale l2

-- Voice
prop_tone_constraint_disjoint :: Property
prop_tone_constraint_disjoint = property $ do
  constraint <- forAll genToneConstraint
  assert $ Set.disjoint (constraintIs constraint) (constraintNot constraint)

prop_trait_set_nonempty :: Property
prop_trait_set_nonempty = property $ do
  traits <- forAll genTraitSet
  assert $ not (null (unTraitSet traits))

-- Serialization
prop_complete_brand_roundtrip :: Property
prop_complete_brand_roundtrip = property $ do
  brand <- forAll genCompleteBrand
  tripping brand encode decode

-- WCAG
prop_palette_contrast_aa :: Property
prop_palette_contrast_aa = property $ do
  palette <- forAll genBrandPalette
  let fg = primaryColor palette
      bg = backgroundColor palette
  assert $ contrastRatio fg bg >= 4.5
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 10. Success Criteria

### 10.1 Phase Completion Criteria

| Phase | Criteria | Verification |
|-------|----------|--------------|
| **Phase 0** | All Hydrogen Brand types in Haskell | `cabal build all` succeeds |
| **Phase 0** | Scraper → Haskell pipeline works | E2E test with coca-cola.com |
| **Phase 1** | Zero sorry in Lean4 | `lake build` succeeds |
| **Phase 1** | Property tests match theorems | `cabal test all` passes |
| **Phase 2** | 90%+ extraction accuracy | Human audit on 10 brands |
| **Phase 3** | COMPASS receives brands | Integration test |
| **Phase 3** | MAESTRO gets context <10ms | Benchmark |
| **Phase 4** | 100 concurrent scrapers | Load test |
| **Phase 4** | 10K brands/hour | Throughput test |
| **Phase 5** | 99.9% uptime | 7-day stability test |

### 10.2 Production Readiness Checklist

```
CORRECTNESS:
  □ Zero sorry in Lean4 proofs
  □ All property tests passing
  □ JSON roundtrip verified for all types
  □ UUID5 determinism verified cross-system

COMPLETENESS:
  □ All 12 Hydrogen pillars extractable
  □ CompleteBrand has 18+ fields
  □ COMPASS export covers all entity types
  □ AgentBrandContext serves all 64 agents

PERFORMANCE:
  □ Extraction <30s per URL
  □ Cache hit rate >95%
  □ MAESTRO context <10ms p99
  □ 10K brands/hour sustained

RELIABILITY:
  □ Circuit breakers on all external calls
  □ Backpressure prevents OOM
  □ Graceful degradation under load
  □ Zero data loss on crash

SECURITY:
  □ gVisor sandbox for all scrapers
  □ No prompt injection possible
  □ Input validation on all boundaries
  □ Rate limiting per client

OBSERVABILITY:
  □ Prometheus metrics exported
  □ Jaeger traces on all requests
  □ Alerts fire <1 minute
  □ Dashboards for all KPIs
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Appendix A: File Locations

### A.1 FOUNDRY Files

```
foundry/
├── haskell/
│   ├── foundry-core/src/Foundry/Core/
│   │   ├── Brand/
│   │   │   ├── Identity.hs        ✅ EXISTS
│   │   │   ├── Palette.hs         ✅ EXISTS
│   │   │   ├── Typography.hs      ✅ EXISTS
│   │   │   ├── Spacing.hs         ✅ EXISTS
│   │   │   ├── Voice.hs           ✅ EXISTS
│   │   │   ├── Logo.hs            ✅ EXISTS
│   │   │   ├── Gradient.hs        ✅ EXISTS
│   │   │   ├── Editorial.hs       ✅ EXISTS
│   │   │   ├── Strategy.hs        ✅ EXISTS
│   │   │   ├── Complete.hs        ❌ MISSING (CompleteBrand)
│   │   │   ├── Ontology.hs        ❌ MISSING
│   │   │   ├── Hierarchy.hs       ❌ MISSING
│   │   │   ├── AgentContext.hs    ❌ MISSING
│   │   │   ├── Layout.hs          ❌ MISSING
│   │   │   ├── UIElements.hs      ❌ MISSING
│   │   │   ├── Modes.hs           ❌ MISSING
│   │   │   └── Imagery.hs         ❌ MISSING
│   │   └── Export/
│   │       ├── COMPASS.hs         ❌ MISSING
│   │       └── NDJSON.hs          ❌ MISSING
│   └── foundry-extract/src/Foundry/Extract/
│       ├── Logo.hs                ⚠️ PARTIAL
│       ├── Layout.hs              ❌ MISSING
│       ├── UIElements.hs          ❌ MISSING
│       └── Modes.hs               ❌ MISSING
│
├── lean/Foundry/
│   ├── Brand.lean                 ❌ MISSING
│   ├── Brand/
│   │   ├── Typography.lean        ⚠️ HAS SORRY
│   │   └── Voice.lean             ⚠️ HAS SORRY
│   └── Cornell/
│       └── Proofs.lean            ⚠️ ByteArray API mismatch
│
└── scraper/
    └── src/scraper.ts             ✅ EXISTS (not connected)
```

### A.2 HYDROGEN Files

```
hydrogen/src/Hydrogen/Schema/
├── Brand/
│   ├── Brand.purs                 ✅ EXISTS
│   ├── Identity.purs              ✅ EXISTS
│   ├── Palette.purs               ✅ EXISTS
│   ├── Typography.purs            ✅ EXISTS
│   ├── Spacing.purs               ✅ EXISTS
│   ├── Voice.purs                 ✅ EXISTS
│   ├── Logo/                      ✅ EXISTS (10 files)
│   ├── Token/                     ✅ EXISTS (10 files)
│   ├── Theme.purs                 ✅ EXISTS
│   └── Compound/                  ✅ EXISTS (4 files)
│
├── Color/                         ✅ EXISTS
├── Dimension/                     ✅ EXISTS (25 files)
├── Typography.purs                ✅ EXISTS
├── Motion.purs                    ✅ EXISTS
├── Elevation.purs                 ✅ EXISTS
├── Material.purs                  ✅ EXISTS
└── Reactive/                      ✅ EXISTS (20 files)
```

### A.3 COMPASS Files

```
COMPASS/
├── typed-compass/
│   ├── haskell/                   ✅ EXISTS
│   ├── lean/                      ✅ EXISTS
│   └── purescript/                ✅ EXISTS
│
├── apps/
│   └── compass-ui/                ✅ EXISTS (194 PS files)
│
└── nix/haskell/
    └── (14 packages)              ✅ ALL BUILD
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Appendix B: Build Commands

```bash
# FOUNDRY
cd /home/jpyxal/jpyxal/foundry
nix develop
cd haskell && cabal build all
cd haskell && cabal test all
cd lean && lake build

# HYDROGEN
cd /home/jpyxal/jpyxal/hydrogen
nix develop
spago build
spago test
lake build  # Lean proofs

# COMPASS
cd /home/jpyxal/jpyxal/COMPASS
nix develop
nix build .#compass-core -L
nix build .#compass-gateway -L
cd apps/compass-ui && spago build
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

*Document generated: 2026-02-26*
*Council session: 5 rounds, unanimous*
*Status: APPROVED FOR IMPLEMENTATION*

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                              // foundry // council
                                                              // straylight/2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
