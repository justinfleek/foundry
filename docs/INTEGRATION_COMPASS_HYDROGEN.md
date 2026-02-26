# FOUNDRY ↔ HYDROGEN ↔ COMPASS Integration Specification

> **Status**: APPROVED FOR IMPLEMENTATION  
> **Version**: 1.0.0  
> **Date**: 2026-02-26  
> **Council Resolution**: 3 rounds, unanimous

---

## Executive Summary

This document specifies the complete integration architecture between three systems:

| System | Role | Technology |
|--------|------|------------|
| **FOUNDRY** | Brand Ingestion Engine | Haskell backend, Lean4 proofs |
| **HYDROGEN** | Frontend Schema & UI | PureScript, 12-pillar design system |
| **COMPASS** | Marketing Automation Platform | Haskell backend, PostgreSQL, MAESTRO orchestrator |

**Goal**: Enable TOTAL brand ingestion—every SKU, logo, font, color, spacing token, voice attribute—with UUID5 determinism, full provenance tracking, and seamless consumption by MAESTRO's 64 AI agents.

---

## Table of Contents

1. [Architecture Overview](#1-architecture-overview)
2. [Type Authority Hierarchy](#2-type-authority-hierarchy)
3. [Unified Data Model](#3-unified-data-model)
4. [Brand Customization Layer](#4-brand-customization-layer)
5. [Multi-Brand Hierarchies](#5-multi-brand-hierarchies)
6. [Integration Surfaces](#6-integration-surfaces)
7. [MAESTRO Agent Integration](#7-maestro-agent-integration)
8. [Storage Architecture](#8-storage-architecture)
9. [Cache & Invalidation Strategy](#9-cache--invalidation-strategy)
10. [Graded Monad Architecture](#10-graded-monad-architecture)
11. [Implementation Roadmap](#11-implementation-roadmap)
12. [Risk Analysis & Mitigations](#12-risk-analysis--mitigations)
13. [Appendix: Type Definitions](#appendix-type-definitions)

---

## 1. Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              FOUNDRY LAYER                                       │
│                         (Brand Ingestion Engine)                                 │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│   URL ──► Playwright ──► ScrapeResult ──► Extractors ──► CompleteBrand         │
│              │                               │                │                 │
│              │                               │                │                 │
│           [gVisor]                      [Graded Monad]    [Provenance]          │
│           sandbox                        permissions       tracking             │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                         │
                                         │ JSON Schema (canonical format)
                                         ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              HYDROGEN LAYER                                      │
│                      (Single Source of Truth for Types)                          │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│   PureScript Types ──► JSON Schema ──► Haskell Codegen ──► Lean4 Proofs        │
│        │                    │                │                   │              │
│        │                    │                │                   │              │
│   [12 Pillars]        [foundry/         [foundry-core/      [lean/              │
│   Brand Schema         schemas/]          Brand/*.hs]        Brand/*.lean]      │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                         │
                                         │ NDJSON over ZMQ / gRPC
                                         ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              COMPASS LAYER                                       │
│                      (Marketing Automation Platform)                             │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│   Knowledge Graph ◄── BrandExport ──► MAESTRO ──► 64 AI Agents                 │
│        │                                 │              │                       │
│        │                                 │              │                       │
│   [PostgreSQL]                    [5-Layer Router]  [BrandContext]              │
│   [DuckDB]                        [Agent Scoring]   [Voice Guardrails]          │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

---

## 2. Type Authority Hierarchy

**RESOLVED**: PureScript Hydrogen is the SINGLE SOURCE OF TRUTH for type definitions.

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  LAYER 0: Lean4 (Calculus of Inductive Constructions)                           │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  Purpose: PROVE invariants, NOT define runtime types                            │
│                                                                                 │
│  Proves:                                                                        │
│    • traits_nonempty: ∀ voice, length(voice.traits) > 0                         │
│    • is_not_disjoint: ∀ attr, attr.is ∩ attr.not = ∅                            │
│    • palette_has_primary: ∃ color ∈ palette, color.role = Primary               │
│    • typography_monotonic: ∀ l1 l2, l1 < l2 → size(l1) < size(l2)               │
│    • spacing_ratio_gt_one: ∀ spacing, spacing.ratio > 1                         │
│    • uuid5_deterministic: ∀ domain, uuid5(domain) = uuid5(domain)               │
│    • coeffect_algebra: associativity, monotonicity, idempotency                 │
│                                                                                 │
│  Does NOT prove (runtime responsibility):                                       │
│    • JSON serialization roundtrip                                               │
│    • PostgreSQL schema correctness                                              │
│    • LLM prompt generation correctness                                          │
└─────────────────────────────────────────────────────────────────────────────────┘
                                         │
                                         │ generates proof witnesses
                                         ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  LAYER 1: PureScript Hydrogen (SINGLE SOURCE OF TRUTH)                          │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  Location: hydrogen/src/Hydrogen/Schema/Brand/*.purs                            │
│                                                                                 │
│  Defines:                                                                       │
│    • 50+ Atoms (Lightness, Chroma, Hue, FontWeight, Tone, Trait, etc.)          │
│    • 25+ Molecules (OKLCH, TypeScale, TraitSet, VoiceAttribute, LogoLockup)     │
│    • 15+ Compounds (Brand, BrandPalette, LogoSystem, Theme, ColorSystem)        │
│    • Complete 12-pillar design system ontology                                  │
│                                                                                 │
│  Exports: JSON Schema 2020-12 via `spago run generate-schema`                   │
└─────────────────────────────────────────────────────────────────────────────────┘
                                         │
                                         │ JSON Schema codegen
                                         ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  LAYER 2: Haskell Foundry (Generated + Hand-written)                            │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  Location: foundry/haskell/foundry-core/src/Foundry/Core/Brand/*.hs             │
│                                                                                 │
│  Generated (from JSON Schema via TH splice):                                    │
│    • Layout.hs, UIElements.hs, GraphicElements.hs, Modes.hs, Imagery.hs         │
│    • All type definitions matching PureScript exactly                           │
│    • ToJSON/FromJSON instances                                                  │
│                                                                                 │
│  Hand-written (domain-specific logic):                                          │
│    • Extraction pipeline (foundry-extract)                                      │
│    • Storage adapters (foundry-storage)                                         │
│    • Graded monad implementation                                                │
│    • COMPASS projection functions                                               │
└─────────────────────────────────────────────────────────────────────────────────┘
                                         │
                                         │ projection (lossy but semantics-preserving)
                                         ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  LAYER 3: PostgreSQL COMPASS (Flattened Knowledge Graph)                        │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  Location: compass/migrations/*.sql                                             │
│                                                                                 │
│  Structure:                                                                     │
│    • entities table with 20+ entity_type values                                 │
│    • relationships table with 15+ relationship_type values                      │
│    • Denormalized for query performance                                         │
│    • BrandProfile for MAESTRO consumption                                       │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### Codegen Pipeline

**RESOLVED**: Option C — PureScript → JSON Schema → Haskell

```
src/Brand/*.purs
       │
       │ spago run generate-schema
       ▼
foundry/schemas/CompleteBrand.json
       │
       │  {
       │    "$schema": "https://json-schema.org/draft/2020-12/schema",
       │    "$id": "foundry://brand/CompleteBrand/1.0.0",
       │    "type": "object",
       │    "required": ["identity", "palette", ...],
       │    "properties": { ... }
       │  }
       │
       │ Haskell TH splice
       ▼
Foundry/Core/Brand/*.hs (generated)
       │
       │ CI validates round-trip
       ▼
decode (encode x) == Right x  ✓
```

**Rationale**: JSON Schema serves as a language-agnostic intermediate representation that enables:
- Haskell consumption via `aeson-schema` or custom TH
- Future TypeScript validators
- Documentation generation
- Schema validation at system boundaries

---

## 3. Unified Data Model

### CompleteBrand (18 Fields)

The `CompleteBrand` type satisfies all three system perspectives:

```haskell
-- foundry-core/src/Foundry/Core/Brand/Complete.hs

data CompleteBrand = CompleteBrand
  { -- STRATEGIC LAYER (The WHY) ─────────────────────────────────────────────
    completeBrandStrategy       :: !StrategicLayer
    -- Mission, vision, values, positioning, competitive context
    
  , completeBrandEditorial      :: !MasterStyleList
    -- Editorial rules, headline rules, punctuation, spelling region
  
    -- EXECUTION LAYER (The HOW) ─────────────────────────────────────────────
  , completeBrandIdentity       :: !BrandIdentity
    -- Name, domain, UUID5, one-line description
    
  , completeBrandPalette        :: !BrandPalette
    -- OKLCH colors with semantic roles (primary, secondary, accent, etc.)
    
  , completeBrandTypography     :: !BrandTypography
    -- Heading/body/mono families, type scale, weights
    
  , completeBrandSpacing        :: !BrandSpacing
    -- Geometric or linear spacing system
    
  , completeBrandVoice          :: !BrandVoice
    -- Tone, traits, vocabulary, IS/NOT constraints
    
  , completeBrandLogo           :: !LogoSpecification
    -- Lockups, variants, clear space, sizing rules, errors
    
  , completeBrandGradient       :: !GradientSpecification
    -- Linear, radial, conic gradients with stops
    
  , completeBrandLayout         :: !LayoutSpecification
    -- Grid systems, safe zones, breakpoints
    
  , completeBrandUIElements     :: !UISpecification
    -- Button, card, input, form specifications
    
  , completeBrandGraphics       :: !GraphicElementsSpecification
    -- Patterns, textures, icons, illustrations
    
  , completeBrandModes          :: !ModesSpecification
    -- Light/dark/contrast modes with token mappings
    
  , completeBrandImagery        :: !ImagerySpecification
    -- Photography style, illustration style, iconography
  
    -- META LAYER ────────────────────────────────────────────────────────────
  , completeBrandProvenance     :: !Provenance
    -- Source URL, timestamp, content hash, extractor version
  
    -- CUSTOMIZATION LAYER ───────────────────────────────────────────────────
  , completeBrandOntology       :: !BrandOntology
    -- Brand-specific naming, aliases, format patterns
    
  , completeBrandParent         :: !(Maybe BrandIdentity)
    -- Parent brand ID (if sub-brand)
    
  , completeBrandSharedAssets   :: !(Maybe SharedBrandAssets)
    -- Inherited assets from parent brand
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
```

### BrandVoice with IS/NOT Constraints

The `BrandVoice` type includes the critical IS/NOT pattern for AI guardrails:

```haskell
data BrandVoice = BrandVoice
  { brandVoiceSummary       :: !VoiceSummary
    -- Human-readable description of brand voice
    
  , brandVoiceToneAttrs     :: !(Vector ToneAttribute)
    -- IS/NOT constraint pairs for each tone dimension
    
  , brandVoiceLegacyTone    :: !Tone
    -- Coarse classification for backward compatibility
    
  , brandVoiceTraits        :: !TraitSet
    -- Personality adjectives (non-empty, proven in Lean4)
    
  , brandVoiceVocabulary    :: !Vocabulary
    -- Preferred and prohibited terms (disjoint sets)
  }

data ToneAttribute = ToneAttribute
  { toneAttrName            :: !Text
    -- e.g., "Authoritative", "Approachable", "Innovative"
    
  , toneAttrIs              :: !(Set ToneDescriptor)
    -- What the brand IS: "confident", "knowledgeable", "trusted"
    
  , toneAttrNot             :: !(Set ToneDescriptor)
    -- What the brand is NOT: "aggressive", "condescending", "aloof"
  }

-- INVARIANT (proven in Lean4): toneAttrIs ∩ toneAttrNot = ∅
```

---

## 4. Brand Customization Layer

### Problem Statement

Every brand has its own:
- **Naming conventions**: Nike says "swoosh", Apple says "bite mark", Target says "bullseye"
- **Database structures**: SKU formats, asset naming patterns
- **Internal ontology**: Sub-brands, product lines, regional variants

### Solution: BrandOntology

```haskell
-- foundry-core/src/Foundry/Core/Brand/Ontology.hs

data BrandOntology = BrandOntology
  { ontologyAliases         :: !(Map CanonicalTerm BrandAlias)
    -- Maps universal concepts to brand-specific terms
    -- e.g., "logo_icon" → "swoosh" (Nike)
    
  , ontologyProhibited      :: !(Set ProhibitedTerm)
    -- Terms this brand never uses
    
  , ontologyFormats         :: !BrandFormats
    -- SKU patterns, date formats, currency formats
  }

-- Universal concept → Brand-specific term mapping
data CanonicalTerm
  = CT_LogoIcon
  | CT_LogoWordmark
  | CT_PrimaryColor
  | CT_SecondaryColor
  | CT_HeadingFont
  | CT_BodyFont
  | CT_PrimaryLockup
  | CT_SecondaryLockup
  -- ... extensible
  deriving stock (Eq, Ord, Show, Enum, Bounded)

newtype BrandAlias = BrandAlias { unBrandAlias :: Text }
  deriving stock (Eq, Ord, Show)
  deriving newtype (ToJSON, FromJSON)

-- Resolution function
resolveTerm :: BrandOntology -> CanonicalTerm -> Text
resolveTerm ont term = 
  maybe (canonicalToDefault term) unBrandAlias 
        (Map.lookup term (ontologyAliases ont))

-- Reverse lookup
findCanonical :: BrandOntology -> Text -> Maybe CanonicalTerm
findCanonical ont alias =
  let inverted = Map.fromList 
        [(unBrandAlias v, k) | (k, v) <- Map.toList (ontologyAliases ont)]
  in Map.lookup alias inverted
```

### Brand Format Patterns

```haskell
data BrandFormats = BrandFormats
  { formatSKU               :: !SKUPattern
    -- e.g., Nike: "AA-######-###"
    -- e.g., Apple: "MXXX2LL/A"
    
  , formatAssetNaming       :: !AssetPattern
    -- e.g., "brand_logo_primary_rgb.svg"
    
  , formatColorNaming       :: !ColorPattern
    -- e.g., "Brand_P1", "Brand_S2"
    
  , formatDate              :: !DateFormat
    -- ISO 8601, US, EU, etc.
    
  , formatCurrency          :: !CurrencyFormat
    -- Symbol position, decimal separator
  }

data SKUPattern = SKUPattern
  { skuRegex                :: !Regex        -- Compiled pattern
  , skuTemplate             :: !Text         -- e.g., "AA-######-###"
  , skuGroups               :: !(Map Text GroupType)  -- Named capture groups
  }

-- Validation
validateSKU :: BrandFormats -> Text -> Either FormatError ValidatedSKU
validateSKU formats sku =
  case matchRegex (skuRegex (formatSKU formats)) sku of
    Just groups -> Right (ValidatedSKU sku groups)
    Nothing     -> Left (InvalidSKUFormat sku (skuTemplate (formatSKU formats)))
```

---

## 5. Multi-Brand Hierarchies

### Problem Statement

Large organizations have complex brand hierarchies:
- **Holding companies**: P&G, J&J, Unilever
- **Sub-brands**: Tide, Pampers, Neutrogena
- **Product lines**: Tide Pods, Tide Free & Gentle
- **Regional variants**: Tide US, Tide EU

### Solution: BrandHierarchy containing BrandOntology

```haskell
-- foundry-core/src/Foundry/Core/Brand/Hierarchy.hs

data BrandHierarchy = BrandHierarchy
  { hierarchyRoot           :: !Brand
    -- Top-level parent brand
    
  , hierarchySubBrands      :: !(Vector SubBrand)
    -- All child brands
    
  , hierarchyTree           :: !BrandTree
    -- Indexed tree structure for efficient traversal
    
  , hierarchySharedAssets   :: !SharedBrandAssets
    -- Assets inherited by all children
  }

data SubBrand = SubBrand
  { subBrandIdentity        :: !BrandIdentity
  , subBrandOntology        :: !BrandOntology    -- Child's own naming
  , subBrandOverrides       :: !BrandOverrides   -- What differs from parent
  , subBrandRelation        :: !BrandRelation    -- Relationship type
  }

data BrandRelation
  = ParentBrand             -- This brand owns sub-brands
  | SubBrand                -- Child of a parent brand
  | EndorsedBrand           -- "A brand by [Parent]" relationship
  | ProductLine             -- Sub-division within a brand
  | SKUVariant              -- Specific product variant
  | RegionalVariant         -- Geographic variant
  deriving stock (Eq, Ord, Show)

data SharedBrandAssets = SharedBrandAssets
  { sharedOntology          :: !BrandOntology    -- Corporate-wide naming
  , sharedVoice             :: !BrandVoice       -- Inherited voice constraints
  , sharedPalette           :: !BrandPalette     -- Core colors
  , sharedTypography        :: !BrandTypography  -- Fonts
  , sharedProhibitedVocab   :: !(Set Term)       -- Corporate-wide bans
  , sharedLegalDisclaimer   :: !Text             -- Required legal text
  }
```

### Inheritance Resolution

```haskell
-- Composition law: child overrides parent
resolveEffectiveBrand :: BrandHierarchy -> BrandId -> CompleteBrand
resolveEffectiveBrand hierarchy childId =
  let child = lookupBrand hierarchy childId
      parent = hierarchyRoot hierarchy
      shared = hierarchySharedAssets hierarchy
  in CompleteBrand
    { -- Child's identity (never inherited)
      completeBrandIdentity = subBrandIdentity child
      
      -- Merge ontology: child overrides parent
    , completeBrandOntology = mergeOntology 
        (sharedOntology shared) 
        (subBrandOntology child)
      
      -- Merge voice: child can add constraints, not remove
    , completeBrandVoice = mergeVoice
        (sharedVoice shared)
        (brandVoice (subBrandOverrides child))
      
      -- Palette: child can extend, not replace primary
    , completeBrandPalette = mergePalette
        (sharedPalette shared)
        (brandPalette (subBrandOverrides child))
      
      -- ... other fields ...
    }

-- Ontology merge: child aliases override parent aliases
mergeOntology :: BrandOntology -> BrandOntology -> BrandOntology
mergeOntology parent child = BrandOntology
  { ontologyAliases = Map.union (ontologyAliases child) (ontologyAliases parent)
  , ontologyProhibited = Set.union (ontologyProhibited child) (ontologyProhibited parent)
  , ontologyFormats = ontologyFormats child  -- Child fully overrides formats
  }
```

---

## 6. Integration Surfaces

### Surface 1: Foundry → Hydrogen (Type Alignment)

**Protocol**: JSON Schema as intermediate representation

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  PureScript (Source)                                                            │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  hydrogen/src/Hydrogen/Schema/Brand/Types.purs                                  │
│                                                                                 │
│  type CompleteBrand =                                                           │
│    { identity    :: BrandIdentity                                               │
│    , palette     :: BrandPalette                                                │
│    , typography  :: BrandTypography                                             │
│    , ...                                                                        │
│    }                                                                            │
└─────────────────────────────────────────────────────────────────────────────────┘
                              │
                              │ spago run generate-schema
                              ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  JSON Schema (Intermediate)                                                     │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  foundry/schemas/CompleteBrand.json                                             │
│                                                                                 │
│  {                                                                              │
│    "$schema": "https://json-schema.org/draft/2020-12/schema",                   │
│    "$id": "foundry://brand/CompleteBrand/1.0.0",                                │
│    "type": "object",                                                            │
│    "required": ["identity", "palette", "typography", ...],                      │
│    "properties": {                                                              │
│      "identity": { "$ref": "BrandIdentity.json" },                              │
│      "palette": { "$ref": "BrandPalette.json" },                                │
│      ...                                                                        │
│    }                                                                            │
│  }                                                                              │
└─────────────────────────────────────────────────────────────────────────────────┘
                              │
                              │ Haskell TH splice
                              ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  Haskell (Generated)                                                            │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  foundry/haskell/foundry-core/src/Foundry/Core/Brand/Generated.hs               │
│                                                                                 │
│  $(deriveFromSchema "foundry/schemas/CompleteBrand.json")                       │
│                                                                                 │
│  -- Generates:                                                                  │
│  data CompleteBrand = CompleteBrand                                             │
│    { completeBrandIdentity    :: !BrandIdentity                                 │
│    , completeBrandPalette     :: !BrandPalette                                  │
│    , completeBrandTypography  :: !BrandTypography                               │
│    , ...                                                                        │
│    } deriving stock (Show, Eq, Generic)                                         │
│      deriving anyclass (FromJSON, ToJSON)                                       │
└─────────────────────────────────────────────────────────────────────────────────┘
```

**Contract**:
- Schema version in `$id` MUST increment on breaking changes
- All Haskell fields use `!` strict annotation
- CI validates: `decode (encode x) == Right x` for all types
- Pre-commit hook regenerates schemas automatically

### Surface 2: Foundry → COMPASS (Data Export)

**Protocol**: NDJSON over ZMQ PUSH/PULL

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  Foundry Export Endpoint                                                        │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  ZMQ Socket: tcp://foundry:5555 (PUSH)                                          │
│                                                                                 │
│  Message Format (NDJSON):                                                       │
│  {"type":"brand","version":1,"payload":{<CompleteBrand JSON>}}                  │
│  {"type":"asset","version":1,"payload":{"hash":"sha256:...","url":"..."}}       │
│  {"type":"hierarchy","version":1,"payload":{"brandId":"...","path":[...]}}      │
│  {"type":"complete","version":1,"payload":{"brandCount":42,"assetCount":128}}   │
└─────────────────────────────────────────────────────────────────────────────────┘
                              │
                              │ ZMQ PUSH/PULL
                              ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  COMPASS Ingestion                                                              │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  ZMQ Socket: tcp://compass:5556 (PULL)                                          │
│                                                                                 │
│  Processing:                                                                    │
│  1. Parse NDJSON message                                                        │
│  2. Validate against JSON Schema                                                │
│  3. Project to knowledge graph entities                                         │
│  4. Insert into PostgreSQL                                                      │
│  5. Update materialized views                                                   │
│  6. Invalidate caches                                                           │
│                                                                                 │
│  Acknowledgment: {"status":"ok","imported":42}                                  │
│              or: {"status":"error","msg":"..."}                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

**Contract**:
- All messages include `version` field for forward compatibility
- `complete` message signals end of export batch
- COMPASS MUST ACK within 30s or Foundry retries
- Assets referenced by hash; COMPASS fetches via separate HTTP endpoint

### Surface 3: COMPASS → MAESTRO (Brand Context)

**Protocol**: gRPC with protobuf

```protobuf
// compass/proto/brand_context.proto

service BrandContextService {
  // Get full brand context for an agent
  rpc GetBrandContext(BrandContextRequest) returns (BrandContextResponse);
  
  // Stream brand updates in real-time
  rpc StreamBrandUpdates(BrandStreamRequest) returns (stream BrandUpdate);
  
  // Validate content against brand guidelines
  rpc ValidateContent(ContentValidationRequest) returns (ValidationResult);
}

message BrandContextRequest {
  string brand_id = 1;
  string agent_id = 2;
  repeated string required_fields = 3;  // Optional: subset of fields
}

message BrandContextResponse {
  AgentBrandContext context = 1;
  int64 version = 2;
  google.protobuf.Timestamp cached_at = 3;
}

message AgentBrandContext {
  // Identity
  string brand_name = 1;
  string industry = 2;
  
  // Voice (critical for LLM)
  string tone_description = 3;
  string voice_be_prompt = 4;       // "BE: confident, clear, ..."
  string voice_never_be_prompt = 5;  // "NEVER BE: aggressive, ..."
  repeated string vocabulary_preferred = 6;
  repeated string vocabulary_forbidden = 7;
  
  // Visual
  repeated string primary_colors_hex = 8;
  string font_heading = 9;
  string font_body = 10;
  
  // Custom
  map<string, string> custom_context = 11;
}

message ContentValidationRequest {
  string brand_id = 1;
  string content = 2;
  repeated string validation_rules = 3;  // Which rules to check
}

message ValidationResult {
  bool passed = 1;
  repeated Violation violations = 2;
}

message Violation {
  string rule = 1;
  string description = 2;
  string location = 3;  // Character offset or line number
  string suggestion = 4;
}
```

**Contract**:
- Response latency p99 < 10ms
- `version` enables MAESTRO to detect stale cache
- `StreamBrandUpdates` pushes invalidation events for hot-reload
- `ValidateContent` returns actionable feedback, not just pass/fail

### Surface 4: MAESTRO → Agents (Consumption)

**Protocol**: Injected context in agent system prompt

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  Agent System Prompt Template                                                   │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                 │
│  <system>                                                                       │
│  You are an AI assistant for {brand_name}.                                      │
│                                                                                 │
│  ## Brand Voice                                                                 │
│  {tone_description}                                                             │
│                                                                                 │
│  BE: {voice_be_prompt}                                                          │
│  NEVER BE: {voice_never_be_prompt}                                              │
│                                                                                 │
│  ## Vocabulary                                                                  │
│  Preferred terms: {vocabulary_preferred | join(", ")}                           │
│  Avoid these terms: {vocabulary_forbidden | join(", ")}                         │
│                                                                                 │
│  ## Brand Colors (for visual descriptions)                                      │
│  Primary: {primary_colors_hex[0]}                                               │
│  Secondary: {primary_colors_hex[1]}                                             │
│                                                                                 │
│  {custom_context | format_as_sections}                                          │
│  </system>                                                                      │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

**Contract**:
- Agent MUST NOT leak brand context in responses (no "As a {brand_name} assistant...")
- BE:/NEVER BE: are hard constraints, agents MUST comply
- Vocabulary forbidden list triggers response rewrite if violated
- Custom context sections formatted as markdown headers

---

## 7. MAESTRO Agent Integration

### Agent Scoring Formula

**RESOLVED**: Configurable weights with sensible defaults

```haskell
data AgentScoreWeights = AgentScoreWeights
  { industryWeight    :: !Double  -- default 0.30
  , toneWeight        :: !Double  -- default 0.40
  , vocabWeight       :: !Double  -- default 0.20
  , customFieldWeight :: !Double  -- default 0.10
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- INVARIANT: weights sum to 1.0 (enforced by smart constructor)
mkAgentScoreWeights 
  :: Double -> Double -> Double -> Double 
  -> Either WeightError AgentScoreWeights
mkAgentScoreWeights ind tone vocab custom
  | abs (ind + tone + vocab + custom - 1.0) > 0.001 = Left WeightsSumNot1
  | any (< 0) [ind, tone, vocab, custom] = Left NegativeWeight
  | otherwise = Right (AgentScoreWeights ind tone vocab custom)

-- Score computation
computeAgentScore :: AgentScoreWeights -> AgentMatch -> Double
computeAgentScore w m = 
    (industryWeight w    * industryBoost m)
  + (toneWeight w        * toneAlignment m)
  + (vocabWeight w       * vocabOverlap m)
  + (customFieldWeight w * customScore m)
```

**Rationale**:
- **Tone (0.40)**: Voice consistency is most noticeable to end users
- **Industry (0.30)**: Domain expertise matters for accuracy
- **Vocabulary (0.20)**: Catches terminology issues
- **Custom (0.10)**: Brand-specific scoring extensions

### IS/NOT → LLM Prompt Translation

```haskell
-- Convert ToneAttribute to LLM prompt format
toToneAttributeContext :: ToneAttribute -> ToneAttributeContext
toToneAttributeContext ToneAttribute{..} = ToneAttributeContext
  { tacName = toneAttrName
  , tacBePrompt = "BE: " <> T.intercalate ", " 
      (fmap unToneDescriptor $ toList toneAttrIs)
  , tacNeverBePrompt = "NEVER BE: " <> T.intercalate ", " 
      (fmap unToneDescriptor $ toList toneAttrNot)
  }

-- Full voice section for LLM system prompt
voiceSystemPrompt :: BrandContext -> Text
voiceSystemPrompt ctx = T.unlines
  [ "# BRAND VOICE REQUIREMENTS"
  , ""
  , "You are writing for " <> ctxBrandName ctx <> "."
  , ""
  , T.unlines $ V.toList $ V.map formatToneAttr (ctxToneAttributes ctx)
  , ""
  , "## VOCABULARY CONSTRAINTS"
  , "Preferred terms: " <> T.intercalate ", " (V.toList (ctxPreferredTerms ctx))
  , "Prohibited terms (NEVER USE): " <> T.intercalate ", " (V.toList (ctxProhibitedTerms ctx))
  ]

formatToneAttr :: ToneAttributeContext -> Text
formatToneAttr tac = T.unlines
  [ "## " <> tacName tac
  , tacBePrompt tac
  , tacNeverBePrompt tac
  ]
```

### Post-Generation Validation

```haskell
-- Two-layer enforcement for vocabulary
data ValidationResult
  = ValidationPassed
  | ValidationFailed !(Vector Violation)

-- Layer 1: Pre-generation (system prompt injection)
-- Layer 2: Post-generation (content validation)

validateContent :: BrandContext -> Text -> IO ValidationResult
validateContent ctx content = do
  let violations = mconcat
        [ checkProhibitedVocab (ctxProhibitedTerms ctx) content
        , checkToneConsistency (ctxToneAttributes ctx) content
        ]
  pure $ case V.null violations of
    True  -> ValidationPassed
    False -> ValidationFailed violations

checkProhibitedVocab :: Vector Text -> Text -> Vector Violation
checkProhibitedVocab prohibited content =
  let words = T.words (T.toLower content)
      found = V.filter (`elem` words) prohibited
  in V.map (\term -> Violation
    { violationRule = "prohibited_vocabulary"
    , violationDescription = "Content contains prohibited term: " <> term
    , violationSuggestion = "Remove or replace this term"
    }) found
```

---

## 8. Storage Architecture

### Hybrid Strategy: Normalized Storage, Denormalized Cache

**RESOLVED**: Normalized for writes, denormalized for reads

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  STORAGE LAYER (PostgreSQL + DuckDB)                                            │
│  ─────────────────────────────────────────────────────────────────────────────  │
│                                                                                 │
│  brands                                                                         │
│  ├── id              UUID PRIMARY KEY                                           │
│  ├── parent_id       UUID REFERENCES brands(id)                                 │
│  ├── version         INTEGER NOT NULL                                           │
│  ├── created_at      TIMESTAMPTZ NOT NULL                                       │
│  └── updated_at      TIMESTAMPTZ NOT NULL                                       │
│                                                                                 │
│  brand_fields                                                                   │
│  ├── brand_id        UUID REFERENCES brands(id)                                 │
│  ├── field_key       VARCHAR(255) NOT NULL                                      │
│  ├── field_value     JSONB NOT NULL                                             │
│  └── PRIMARY KEY (brand_id, field_key)                                          │
│                                                                                 │
│  assets                                                                         │
│  ├── hash            VARCHAR(64) PRIMARY KEY  -- SHA256                         │
│  ├── content_type    VARCHAR(100) NOT NULL                                      │
│  ├── size_bytes      BIGINT NOT NULL                                            │
│  └── blob            BYTEA NOT NULL                                             │
│                                                                                 │
│  brand_assets                                                                   │
│  ├── brand_id        UUID REFERENCES brands(id)                                 │
│  ├── asset_hash      VARCHAR(64) REFERENCES assets(hash)                        │
│  ├── role            VARCHAR(50) NOT NULL  -- logo_primary, font_heading, etc.  │
│  └── PRIMARY KEY (brand_id, asset_hash, role)                                   │
│                                                                                 │
│  → Assets stored ONCE, referenced by hash (content-addressed)                   │
│  → brand_fields enables sparse storage (not all brands have all fields)         │
│  → Inheritance computed at query time                                           │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                              │
                              │ materialization
                              ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  QUERY CACHE (HAMT in-memory + DuckDB materialized views)                       │
│  ─────────────────────────────────────────────────────────────────────────────  │
│                                                                                 │
│  complete_brands      -- Fully resolved CompleteBrand JSON                      │
│  agent_contexts       -- Pre-computed AgentBrandContext per agent               │
│  hierarchy_paths      -- brand_id → [ancestor_ids]                              │
│                                                                                 │
│  → Denormalized for O(1) agent access                                           │
│  → Invalidated on write (see Cache Strategy)                                    │
│  → HAMT provides immutable snapshots for concurrent reads                       │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### Entity Type Mapping (COMPASS Knowledge Graph)

```sql
-- New entity types for Hydrogen atoms/molecules
ALTER TYPE entity_type ADD VALUE 'brand';
ALTER TYPE entity_type ADD VALUE 'brand_voice';
ALTER TYPE entity_type ADD VALUE 'brand_palette';
ALTER TYPE entity_type ADD VALUE 'brand_typography';
ALTER TYPE entity_type ADD VALUE 'brand_spacing';
ALTER TYPE entity_type ADD VALUE 'brand_logo';
ALTER TYPE entity_type ADD VALUE 'brand_mode';
ALTER TYPE entity_type ADD VALUE 'tone_attribute';
ALTER TYPE entity_type ADD VALUE 'tone_descriptor';
ALTER TYPE entity_type ADD VALUE 'color_oklch';
ALTER TYPE entity_type ADD VALUE 'font_family';
ALTER TYPE entity_type ADD VALUE 'gradient';
ALTER TYPE entity_type ADD VALUE 'pattern';
ALTER TYPE entity_type ADD VALUE 'texture';
ALTER TYPE entity_type ADD VALUE 'layout_grid';
ALTER TYPE entity_type ADD VALUE 'ui_button';
ALTER TYPE entity_type ADD VALUE 'accessibility_rule';
ALTER TYPE entity_type ADD VALUE 'image_category';
ALTER TYPE entity_type ADD VALUE 'vocabulary_term';

-- New relationship types
ALTER TYPE relationship_type ADD VALUE 'has_voice';
ALTER TYPE relationship_type ADD VALUE 'has_palette';
ALTER TYPE relationship_type ADD VALUE 'has_typography';
ALTER TYPE relationship_type ADD VALUE 'has_tone_attribute';
ALTER TYPE relationship_type ADD VALUE 'tone_is_descriptor';
ALTER TYPE relationship_type ADD VALUE 'tone_not_descriptor';
ALTER TYPE relationship_type ADD VALUE 'has_primary_color';
ALTER TYPE relationship_type ADD VALUE 'has_secondary_color';
ALTER TYPE relationship_type ADD VALUE 'has_accent_color';
ALTER TYPE relationship_type ADD VALUE 'uses_font';
ALTER TYPE relationship_type ADD VALUE 'has_mode';
ALTER TYPE relationship_type ADD VALUE 'inherits_from';
ALTER TYPE relationship_type ADD VALUE 'shares_asset';
ALTER TYPE relationship_type ADD VALUE 'contains_pattern';
ALTER TYPE relationship_type ADD VALUE 'requires_accessibility';
```

---

## 9. Cache & Invalidation Strategy

### Strategy: Eager Invalidation, Lazy Recomputation

**RESOLVED**: Invalidate immediately, recompute on demand

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  Parent Brand v3 → v4 (palette changed)                                         │
└─────────────────────────────────────────────────────────────────────────────────┘
                              │
                              │ ZMQ broadcast to all nodes
                              ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  Invalidation Event                                                             │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  {                                                                              │
│    "brandId": "parent-uuid",                                                    │
│    "oldVersion": 3,                                                             │
│    "newVersion": 4,                                                             │
│    "changedFields": ["palette"],                                                │
│    "timestamp": "2026-02-26T12:00:00Z"                                          │
│  }                                                                              │
└─────────────────────────────────────────────────────────────────────────────────┘
                              │
                              │ propagate to children
                              ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  Sub-brand Cache Entries                                                        │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  "child-a"     → INVALIDATED (inherits palette)                                 │
│  "child-b"     → INVALIDATED (inherits palette)                                 │
│  "grandchild"  → INVALIDATED (inherits from child-a)                            │
└─────────────────────────────────────────────────────────────────────────────────┘
                              │
                              │ on next access
                              ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  Lazy Recomputation                                                             │
│  ─────────────────────────────────────────────────────────────────────────────  │
│  1. Load parent brand (v4)                                                      │
│  2. Inherit changed fields (palette)                                            │
│  3. Apply child overrides                                                       │
│  4. Compute new hash                                                            │
│  5. Store in cache with new version                                             │
│  6. Memoize intermediate results for siblings                                   │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### Three-Tier Cache

```haskell
data BrandCache = BrandCache
  { -- L1: Hot cache (in-memory, per-MAESTRO instance)
    -- Latency: <1ms
    -- TTL: 1 hour
    cacheL1           :: !(IORef (HAMT UUID CacheEntry))
    
    -- L2: Warm cache (Redis, shared across instances)
    -- Latency: <10ms
    -- TTL: 24 hours
  , cacheL2           :: !RedisConnection
    
    -- L3: Cold storage (PostgreSQL/DuckDB)
    -- Latency: <100ms
    -- TTL: Permanent
  , cacheL3           :: !DatabaseConnection
  
    -- Version tracking
  , cacheVersions     :: !(IORef (Map UUID ContentHash))
  }

data CacheEntry = CacheEntry
  { entryValue        :: !CompleteBrand
  , entryVersion      :: !ContentHash
  , entryParentVersion :: !(Maybe ContentHash)  -- For inheritance tracking
  , entryComputedAt   :: !UTCTime
  }

-- Cache lookup with fallback
lookupBrand :: BrandCache -> UUID -> IO (Maybe CompleteBrand)
lookupBrand cache brandId = do
  -- Try L1
  l1 <- readIORef (cacheL1 cache)
  case HAMT.lookup brandId l1 of
    Just entry -> pure (Just (entryValue entry))
    Nothing -> do
      -- Try L2
      l2Result <- Redis.get (cacheL2 cache) (brandCacheKey brandId)
      case l2Result of
        Just entry -> do
          -- Promote to L1
          modifyIORef' (cacheL1 cache) (HAMT.insert brandId entry)
          pure (Just (entryValue entry))
        Nothing -> do
          -- Load from L3 and populate caches
          l3Result <- loadFromDatabase (cacheL3 cache) brandId
          forM_ l3Result $ \brand -> do
            let entry = mkCacheEntry brand
            modifyIORef' (cacheL1 cache) (HAMT.insert brandId entry)
            Redis.set (cacheL2 cache) (brandCacheKey brandId) entry
          pure l3Result
```

---

## 10. Graded Monad Architecture

### Design: Lean4 Proves, Haskell Implements

**RESOLVED**: Separation of concerns between proof and runtime

```lean
-- lean/Foundry/Pipeline/Effect.lean

/-- Permission lattice for brand operations -/
inductive BrandPerm where
  | read      : BrandPerm
  | scrape    : BrandPerm
  | extract   : BrandPerm
  | store     : BrandPerm
  | mutate    : BrandPerm
  deriving DecidableEq, Repr

/-- Budget conservation theorem -/
theorem budget_conservation (op : BrandOp) (b : Budget) :
    cost op ≤ b → remaining (exec op b) = b - cost op := by
  intro h
  simp [exec, remaining]
  omega

/-- Permission monotonicity theorem -/
theorem permission_monotonic (p₁ p₂ : Set BrandPerm) :
    p₁ ⊆ p₂ → allowed p₁ ⊆ allowed p₂ := by
  intro h op hop
  exact h hop
```

```haskell
-- foundry-core/src/Foundry/Core/Effect.hs

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

-- | Permission set at type level
data BrandPerm
  = PermRead
  | PermScrape
  | PermExtract
  | PermStore
  | PermMutate
  deriving stock (Eq, Ord, Show)

-- | Type-level permission set
type family HasPerm (p :: BrandPerm) (perms :: [BrandPerm]) :: Constraint where
  HasPerm p (p ': _)  = ()
  HasPerm p (_ ': ps) = HasPerm p ps
  HasPerm p '[]       = TypeError ('Text "Missing permission: " ':<>: 'ShowType p)

-- | Graded brand agent monad
newtype BrandAgent (perms :: [BrandPerm]) (budget :: Nat) (ctx :: Type) a = BrandAgent
  { runBrandAgent :: ReaderT ctx (StateT Natural (ExceptT AgentError IO)) a
  }
  deriving newtype (Functor, Applicative, Monad, MonadIO)

-- | Extract colors (requires PermExtract)
extractColors 
  :: HasPerm 'PermExtract perms
  => RawHTML 
  -> BrandAgent perms budget ctx BrandPalette
extractColors html = BrandAgent $ do
  -- Implementation
  pure palette

-- | Store brand (requires PermStore)
storeBrand
  :: HasPerm 'PermStore perms
  => CompleteBrand
  -> BrandAgent perms budget ctx StorageKey
storeBrand brand = BrandAgent $ do
  -- Implementation
  pure key

-- | Budget-tracking operation
withBudget 
  :: KnownNat cost
  => BrandAgent perms budget ctx a 
  -> BrandAgent perms (budget - cost) ctx a
withBudget (BrandAgent action) = BrandAgent $ do
  remaining <- get
  let cost = natVal (Proxy @cost)
  when (remaining < cost) $
    throwError BudgetExhausted
  put (remaining - cost)
  action
```

---

## 11. Implementation Roadmap

```
═══════════════════════════════════════════════════════════════════════════════════
PHASE 0: FOUNDATION                                                    [Weeks 1-2]
═══════════════════════════════════════════════════════════════════════════════════

DELIVERABLES:
  □ PureScript Brand types finalized (18-field CompleteBrand)
  □ JSON Schema generation pipeline operational
  □ Lean4 lakefile compiles with invariant stubs
  □ Haskell foundry-core package with graded monad skeleton

DEPENDENCIES: None (bootstrap phase)

SUCCESS CRITERIA:
  ✓ `spago build` succeeds in hydrogen/
  ✓ `lake build` succeeds in foundry/lean/
  ✓ `cabal build all` succeeds in foundry/haskell/
  ✓ JSON Schema files generated in foundry/schemas/

───────────────────────────────────────────────────────────────────────────────────

═══════════════════════════════════════════════════════════════════════════════════
PHASE 1: CORE TYPES + PROOFS                                           [Weeks 3-5]
═══════════════════════════════════════════════════════════════════════════════════

DELIVERABLES:
  □ Complete Lean4 invariants for all 7 SMART components
  □ BrandHierarchy containing BrandOntology proven correct
  □ Permission lattice with subset/superset proofs
  □ Budget conservation theorem for all BrandOps
  □ Haskell TH splice consuming JSON Schema

DEPENDENCIES: Phase 0 complete

SUCCESS CRITERIA:
  ✓ Zero `sorry` in Lean4 codebase
  ✓ Haskell types auto-generated from schemas match PureScript
  ✓ Property tests pass: hierarchy, permissions, budget
  ✓ 100% of brand operations type-safe at compile time

───────────────────────────────────────────────────────────────────────────────────

═══════════════════════════════════════════════════════════════════════════════════
PHASE 2: EXTRACTION PIPELINE                                           [Weeks 6-8]
═══════════════════════════════════════════════════════════════════════════════════

DELIVERABLES:
  □ foundry-extract: color extraction (k-means clustering, perceptual grouping)
  □ foundry-extract: typography detection (font-family, weights, scale)
  □ foundry-extract: spacing grid inference (4px/8px/16px base)
  □ foundry-scraper: Playwright integration via ZMQ (gVisor sandboxed)
  □ Voice extraction stub (LLM integration point for Phase 4+)

DEPENDENCIES: Phase 1 complete, JSON Schema stable

SUCCESS CRITERIA:
  ✓ Extract palette from 10 test URLs with >90% accuracy
  ✓ Typography detection matches manual audit on 5 brands
  ✓ Spacing grid infers base unit correctly on 8/10 sites
  ✓ Pipeline runs end-to-end in <30s per URL

───────────────────────────────────────────────────────────────────────────────────

═══════════════════════════════════════════════════════════════════════════════════
PHASE 3: STORAGE + CACHING                                            [Weeks 9-11]
═══════════════════════════════════════════════════════════════════════════════════

DELIVERABLES:
  □ PostgreSQL schema for normalized brand storage
  □ DuckDB integration for analytics/materialized views
  □ HAMT-based in-memory cache with versioned entries
  □ ZMQ-based invalidation event bus
  □ Sub-brand inheritance resolution engine

DEPENDENCIES: Phase 2 complete (need data to store)

SUCCESS CRITERIA:
  ✓ Store/retrieve 1000 brands in <1s
  ✓ Cache hit rate >95% on read-heavy workload
  ✓ Invalidation propagates to all children in <100ms
  ✓ Zero stale reads under concurrent write load

───────────────────────────────────────────────────────────────────────────────────

═══════════════════════════════════════════════════════════════════════════════════
PHASE 4: AGENT INTEGRATION                                           [Weeks 12-14]
═══════════════════════════════════════════════════════════════════════════════════

DELIVERABLES:
  □ AgentBrandContext serialization format (protobuf)
  □ Agent scoring with configurable weights (0.3/0.4/0.2/0.1 defaults)
  □ BE:/NEVER BE: prompt generation from IS/NOT constraints
  □ MAESTRO gRPC integration endpoint
  □ Real-time brand context streaming via ZMQ

DEPENDENCIES: Phase 3 complete (need cache for fast access)

SUCCESS CRITERIA:
  ✓ Agent receives brand context in <10ms (p99)
  ✓ Scoring weights configurable via brand settings
  ✓ Generated prompts pass voice consistency tests
  ✓ MAESTRO can hot-swap brand context mid-conversation

───────────────────────────────────────────────────────────────────────────────────

═══════════════════════════════════════════════════════════════════════════════════
PHASE 5: HYDROGEN UI + POLISH                                        [Weeks 15-17]
═══════════════════════════════════════════════════════════════════════════════════

DELIVERABLES:
  □ Brand ingestion dashboard (Hydrogen/PureScript)
  □ Hierarchy visualization (tree view with inheritance indicators)
  □ Real-time extraction progress indicators
  □ Brand diff viewer (before/after comparison)
  □ Export to COMPASS format (one-click)

DEPENDENCIES: Phase 4 complete (need full pipeline to visualize)

SUCCESS CRITERIA:
  ✓ User can ingest brand from URL in <60s via UI
  ✓ Hierarchy displays up to 100 brands without lag
  ✓ Diff viewer highlights changed fields clearly
  ✓ COMPASS export validates against schema

───────────────────────────────────────────────────────────────────────────────────

═══════════════════════════════════════════════════════════════════════════════════
PHASE 6: HARDENING + LAUNCH                                          [Weeks 18-20]
═══════════════════════════════════════════════════════════════════════════════════

DELIVERABLES:
  □ Load testing: 10K concurrent brand lookups
  □ Security audit: sandboxing, input validation, prompt injection prevention
  □ Documentation: API reference, deployment guide, architecture diagrams
  □ Observability: metrics (Prometheus), tracing (Jaeger), alerting
  □ Production deployment via Nix flake

DEPENDENCIES: All previous phases complete

SUCCESS CRITERIA:
  ✓ p99 latency <50ms for brand lookup
  ✓ Zero security vulnerabilities in audit
  ✓ Documentation covers all public APIs
  ✓ Alerts fire within 1 minute of degradation
  ✓ Nix flake builds reproducibly on CI

═══════════════════════════════════════════════════════════════════════════════════
```

### Gantt Chart Overview

```
Week:   1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20
        ├──┴──┼──┴──┴──┼──┴──┴──┼──┴──┴──┼──┴──┴──┼──┴──┴──┤
Phase 0 ████████
Phase 1          ██████████████
Phase 2                         ██████████████
Phase 3                                        ██████████████
Phase 4                                                       ██████████████
Phase 5                                                                      ██████████████
Phase 6                                                                                     ██████████████
```

---

## 12. Risk Analysis & Mitigations

### Risk 1: JSON Schema Drift

| Aspect | Detail |
|--------|--------|
| **What could go wrong** | PureScript types evolve but JSON Schema isn't regenerated, causing Haskell types to diverge |
| **Likelihood** | Medium |
| **Impact** | High (silent type mismatches) |
| **Mitigation** | CI job: `spago run generate-schema && git diff --exit-code foundry/schemas/` fails build if schemas are stale |
| **Fallback** | Manual schema audit every sprint; type-level tests catch mismatches at compile time |

### Risk 2: Lean4 Proof Incompleteness

| Aspect | Detail |
|--------|--------|
| **What could go wrong** | Complex invariants resist proof completion, blocking Phase 1 |
| **Likelihood** | Medium |
| **Impact** | Medium (delays schedule) |
| **Mitigation** | Start with simplest invariants; pair Lean4 work with Haskell property tests; time-box difficult proofs (3 days max) |
| **Fallback** | Document unproven invariants with `-- UNPROVEN: <reason>` and track as tech debt |

### Risk 3: Extraction Accuracy

| Aspect | Detail |
|--------|--------|
| **What could go wrong** | Color extraction fails on complex gradients; typography detection misidentifies web fonts |
| **Likelihood** | High |
| **Impact** | Medium (requires manual correction) |
| **Mitigation** | Build test corpus of 50 diverse brand sites; human-in-the-loop verification; confidence scores on all extracted values |
| **Fallback** | Manual override UI in dashboard; extracted values are suggestions, not gospel |

### Risk 4: Cache Invalidation Race Conditions

| Aspect | Detail |
|--------|--------|
| **What could go wrong** | Concurrent writes + invalidations cause cache to serve stale data |
| **Likelihood** | Medium |
| **Impact** | High (incorrect brand data shown) |
| **Mitigation** | MVCC snapshots; write linearization via leader node; vector clocks for distributed deployments |
| **Fallback** | TTL-based expiration (24h) as safety net |

### Risk 5: Agent Context Injection Attacks

| Aspect | Detail |
|--------|--------|
| **What could go wrong** | Malicious brand data injects prompt instructions that override agent behavior |
| **Likelihood** | Low |
| **Impact** | Critical (security breach) |
| **Mitigation** | Sanitize all brand fields before injection; brand context in separate `<brand>` XML block; rate limit brand updates |
| **Fallback** | Content Security Policy for prompts; blocklist known attack patterns |

### Risk 6: Performance Under Load

| Aspect | Detail |
|--------|--------|
| **What could go wrong** | 10K concurrent brand lookups overwhelm cache, causing cascading failures |
| **Likelihood** | Low |
| **Impact** | High (service outage) |
| **Mitigation** | Load test with 2x expected peak; circuit breakers; graceful degradation (serve last-known-good cache) |
| **Fallback** | Horizontal scaling via read replicas; stateless workers behind load balancer |

### Risk 7: Scope Creep in Voice Extraction

| Aspect | Detail |
|--------|--------|
| **What could go wrong** | LLM-based voice extraction becomes unbounded research project |
| **Likelihood** | High |
| **Impact** | Medium (delays schedule) |
| **Mitigation** | Phase 2 delivers "voice extraction stub" with hardcoded templates + manual input; LLM integration is Phase 4+ |
| **Fallback** | Voice is fully manual for V1; extraction is V2 feature |

---

## Appendix: Type Definitions

### A.1 Complete Type Inventory

| Layer | Type | Lines | Status |
|-------|------|-------|--------|
| Atom | Lightness | 20 | ✅ Exists |
| Atom | Chroma | 20 | ✅ Exists |
| Atom | Hue | 20 | ✅ Exists |
| Atom | FontWeight | 30 | ✅ Exists |
| Atom | Tone | 25 | ✅ Exists |
| Atom | Trait | 40 | ✅ Exists |
| Atom | ToneDescriptor | 15 | ✅ Exists |
| Molecule | OKLCH | 50 | ✅ Exists |
| Molecule | TypeScale | 40 | ✅ Exists |
| Molecule | TraitSet | 30 | ✅ Exists |
| Molecule | ToneAttribute | 60 | ✅ Exists |
| Molecule | VoiceAttribute | 50 | ✅ Exists |
| Molecule | LogoLockup | 120 | ✅ Exists |
| Compound | BrandIdentity | 80 | ✅ Exists |
| Compound | BrandPalette | 100 | ✅ Exists |
| Compound | BrandTypography | 120 | ✅ Exists |
| Compound | BrandSpacing | 80 | ✅ Exists |
| Compound | BrandVoice | 150 | ✅ Exists |
| Compound | LogoSpecification | 200 | ✅ Exists |
| Compound | LayoutSpecification | 180 | ⚠️ PS only |
| Compound | UISpecification | 200 | ⚠️ PS only |
| Compound | GraphicElementsSpecification | 150 | ⚠️ PS only |
| Compound | ModesSpecification | 170 | ⚠️ PS only |
| Compound | ImagerySpecification | 140 | ⚠️ PS only |
| Compound | CompleteBrand | 100 | ⚠️ Needs extension |
| Custom | BrandOntology | 150 | ❌ Not started |
| Custom | BrandHierarchy | 200 | ❌ Not started |
| Custom | BrandFormats | 100 | ❌ Not started |

### A.2 Generated vs Hand-Written

| Module | Source | Generation Method |
|--------|--------|-------------------|
| Layout.hs | hydrogen/src/Brand/Layout.purs | TH from JSON Schema |
| UIElements.hs | hydrogen/src/Brand/UIElements.purs | TH from JSON Schema |
| GraphicElements.hs | hydrogen/src/Brand/GraphicElements.purs | TH from JSON Schema |
| Modes.hs | hydrogen/src/Brand/Modes.purs | TH from JSON Schema |
| Imagery.hs | hydrogen/src/Brand/Imagery.purs | TH from JSON Schema |
| Voice.hs (extension) | N/A | Hand-written (extends existing) |
| Ontology.hs | N/A | Hand-written (new concept) |
| Hierarchy.hs | N/A | Hand-written (new concept) |
| Projection.hs | N/A | Hand-written (COMPASS-specific) |
| Context.hs | N/A | Hand-written (MAESTRO-specific) |

### A.3 BrandContext for MAESTRO

```haskell
-- The flattened context MAESTRO agents receive
data BrandContext = BrandContext
  { -- Identity
    ctxBrandId            :: !UUID
  , ctxBrandName          :: !Text
  , ctxIndustry           :: !Text
  , ctxCategory           :: !Text
  
    -- Voice (critical for LLM consumption)
  , ctxVoiceSummary       :: !Text
  , ctxToneAttributes     :: !(Vector ToneAttributeContext)
  , ctxPreferredTerms     :: !(Vector Text)
  , ctxProhibitedTerms    :: !(Vector Text)
  
    -- Editorial
  , ctxEditorialRules     :: !EditorialContext
  
    -- Ontology (for terminology mapping)
  , ctxOntologyAliases    :: !(Map Text Text)
  
    -- Visual (for design agents)
  , ctxPrimaryColor       :: !Text  -- Hex code
  , ctxSecondaryColors    :: !(Vector Text)
  , ctxFontHeading        :: !Text
  , ctxFontBody           :: !Text
  
    -- Hierarchy
  , ctxParentBrandName    :: !(Maybe Text)
  , ctxInheritedVoice     :: !(Maybe BrandVoice)
  
    -- Scoring
  , ctxScoreWeights       :: !AgentScoreWeights
  
    -- Meta
  , ctxVersion            :: !ContentHash
  , ctxCachedAt           :: !UTCTime
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

data ToneAttributeContext = ToneAttributeContext
  { tacName               :: !Text
  , tacBePrompt           :: !Text   -- "BE: confident, clear, ..."
  , tacNeverBePrompt      :: !Text   -- "NEVER BE: aggressive, ..."
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
```

---

## Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2026-02-26 | Council | Initial release after 3-round planning session |

---

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // foundry // compass // hydrogen
                                                      // straylight/2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```
