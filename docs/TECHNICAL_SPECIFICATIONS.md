# FOUNDRY Technical Specifications

> **Version**: 1.0.0  
> **Date**: 2026-02-26  
> **Scope**: Type definitions, extraction algorithms, storage architecture

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Table of Contents

1. [Type Definitions](#1-type-definitions)
2. [Extraction Algorithms](#2-extraction-algorithms)
3. [Storage Architecture](#3-storage-architecture)
4. [Transport Protocols](#4-transport-protocols)
5. [Graded Monad Implementation](#5-graded-monad-implementation)
6. [Lean4 Proof Requirements](#6-lean4-proof-requirements)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 1. Type Definitions

### 1.1 CompleteBrand (Unified Type)

The `CompleteBrand` type is the canonical representation of a fully-ingested brand.
It satisfies all three system perspectives: FOUNDRY (extraction), HYDROGEN (display),
and COMPASS (knowledge graph).

```haskell
-- foundry-core/src/Foundry/Core/Brand/Complete.hs

{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Foundry.Core.Brand.Complete
  ( -- * Complete Brand Type
    CompleteBrand (..)
  , mkCompleteBrand
  
    -- * Validation
  , validateCompleteBrand
  , CompleteBrandError (..)
  ) where

-- | Complete brand specification — 18+ fields covering all SMART Framework pillars
data CompleteBrand = CompleteBrand
  { -- STRATEGIC LAYER (The WHY) ─────────────────────────────────────────────
    
    completeBrandStrategy       :: !StrategicLayer
    -- ^ Mission, vision, values, positioning, competitive context
    
  , completeBrandEditorial      :: !MasterStyleList
    -- ^ Editorial rules, headline rules, punctuation, spelling region
  
    -- EXECUTION LAYER (The HOW) ─────────────────────────────────────────────
    
  , completeBrandIdentity       :: !BrandIdentity
    -- ^ Name, domain, UUID5, one-line description
    
  , completeBrandPalette        :: !BrandPalette
    -- ^ OKLCH colors with semantic roles (primary, secondary, accent, etc.)
    
  , completeBrandTypography     :: !BrandTypography
    -- ^ Heading/body/mono families, type scale, weights
    
  , completeBrandSpacing        :: !BrandSpacing
    -- ^ Geometric or linear spacing system
    
  , completeBrandVoice          :: !BrandVoice
    -- ^ Tone, traits, vocabulary, IS/NOT constraints
    
  , completeBrandLogo           :: !LogoSpecification
    -- ^ Lockups, variants, clear space, sizing rules, errors
    
  , completeBrandGradient       :: !GradientSpecification
    -- ^ Linear, radial, conic gradients with stops
    
  , completeBrandLayout         :: !LayoutSpecification
    -- ^ Grid systems, safe zones, breakpoints
    
  , completeBrandUIElements     :: !UISpecification
    -- ^ Button, card, input, form specifications
    
  , completeBrandGraphics       :: !GraphicElementsSpecification
    -- ^ Patterns, textures, icons, illustrations
    
  , completeBrandModes          :: !ModesSpecification
    -- ^ Light/dark/contrast modes with token mappings
    
  , completeBrandImagery        :: !ImagerySpecification
    -- ^ Photography style, illustration style, iconography
  
    -- META LAYER ────────────────────────────────────────────────────────────
    
  , completeBrandProvenance     :: !Provenance
    -- ^ Source URL, timestamp, content hash, extractor version
  
    -- CUSTOMIZATION LAYER ───────────────────────────────────────────────────
    
  , completeBrandOntology       :: !BrandOntology
    -- ^ Brand-specific naming, aliases, format patterns
    
  , completeBrandParent         :: !(Maybe BrandIdentity)
    -- ^ Parent brand ID (if sub-brand)
    
  , completeBrandSharedAssets   :: !(Maybe SharedBrandAssets)
    -- ^ Inherited assets from parent brand
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
```

### 1.2 BrandOntology (Customization Layer)

```haskell
-- foundry-core/src/Foundry/Core/Brand/Ontology.hs

-- | Brand-specific naming conventions and format patterns
data BrandOntology = BrandOntology
  { ontologyAliases         :: !(Map CanonicalTerm BrandAlias)
    -- ^ Maps universal concepts to brand-specific terms
    -- e.g., "logo_icon" → "swoosh" (Nike)
    
  , ontologyProhibited      :: !(Set ProhibitedTerm)
    -- ^ Terms this brand never uses
    
  , ontologyFormats         :: !BrandFormats
    -- ^ SKU patterns, date formats, currency formats
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Universal concept identifiers
data CanonicalTerm
  = CT_LogoIcon
  | CT_LogoWordmark
  | CT_PrimaryColor
  | CT_SecondaryColor
  | CT_AccentColor
  | CT_NeutralColor
  | CT_HeadingFont
  | CT_BodyFont
  | CT_MonoFont
  | CT_PrimaryLockup
  | CT_HorizontalLockup
  | CT_VerticalLockup
  | CT_IconOnly
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Brand-specific term
newtype BrandAlias = BrandAlias { unBrandAlias :: Text }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Resolution: canonical → brand-specific
resolveTerm :: BrandOntology -> CanonicalTerm -> Text
resolveTerm ont term = 
  maybe (canonicalToDefault term) unBrandAlias 
        (Map.lookup term (ontologyAliases ont))

-- | Reverse lookup
findCanonical :: BrandOntology -> Text -> Maybe CanonicalTerm
findCanonical ont alias =
  let inverted = Map.fromList 
        [(unBrandAlias v, k) | (k, v) <- Map.toList (ontologyAliases ont)]
  in Map.lookup alias inverted
```

### 1.3 BrandHierarchy (Multi-Brand Support)

```haskell
-- foundry-core/src/Foundry/Core/Brand/Hierarchy.hs

-- | Complete brand hierarchy with inheritance
data BrandHierarchy = BrandHierarchy
  { hierarchyRoot           :: !CompleteBrand
    -- ^ Top-level parent brand
    
  , hierarchySubBrands      :: !(Vector SubBrand)
    -- ^ All child brands
    
  , hierarchyTree           :: !BrandTree
    -- ^ Indexed tree structure for efficient traversal
    
  , hierarchySharedAssets   :: !SharedBrandAssets
    -- ^ Assets inherited by all children
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Sub-brand with overrides
data SubBrand = SubBrand
  { subBrandIdentity        :: !BrandIdentity
  , subBrandOntology        :: !BrandOntology    -- Child's own naming
  , subBrandOverrides       :: !BrandOverrides   -- What differs from parent
  , subBrandRelation        :: !BrandRelation    -- Relationship type
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Relationship types
data BrandRelation
  = ParentBrand             -- This brand owns sub-brands
  | SubBrandOf              -- Child of a parent brand
  | EndorsedBrand           -- "A brand by [Parent]" relationship
  | ProductLine             -- Sub-division within a brand
  | SKUVariant              -- Specific product variant
  | RegionalVariant         -- Geographic variant
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Assets shared across hierarchy
data SharedBrandAssets = SharedBrandAssets
  { sharedOntology          :: !BrandOntology    -- Corporate-wide naming
  , sharedVoice             :: !BrandVoice       -- Inherited voice constraints
  , sharedPalette           :: !BrandPalette     -- Core colors
  , sharedTypography        :: !BrandTypography  -- Fonts
  , sharedProhibitedVocab   :: !(Set Text)       -- Corporate-wide bans
  , sharedLegalDisclaimer   :: !Text             -- Required legal text
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Resolve effective brand by applying inheritance
resolveEffectiveBrand :: BrandHierarchy -> BrandId -> CompleteBrand
resolveEffectiveBrand hierarchy childId =
  let child = lookupSubBrand hierarchy childId
      parent = hierarchyRoot hierarchy
      shared = hierarchySharedAssets hierarchy
  in applyInheritance shared parent (subBrandOverrides child)
```

### 1.4 AgentBrandContext (MAESTRO Consumption)

```haskell
-- foundry-core/src/Foundry/Core/Brand/AgentContext.hs

-- | Context provided to MAESTRO agents for brand-aware generation
-- This is the FORMAT that agents consume — optimized for LLM prompts
data AgentBrandContext = AgentBrandContext
  { -- Identity
    abcBrandName        :: !Text
  , abcBrandId          :: !UUID
  , abcIndustry         :: !Text
  , abcDomain           :: !Text
  
    -- Voice (critical for LLM)
  , abcToneDescription  :: !Text
    -- ^ Human-readable summary: "Professional, authoritative, approachable"
    
  , abcVoiceBePrompt    :: !Text
    -- ^ "BE: confident, knowledgeable, trusted, helpful, clear"
    
  , abcVoiceNeverBe     :: !Text
    -- ^ "NEVER BE: aggressive, condescending, pompous, aloof, jargon-heavy"
    
  , abcPreferredTerms   :: !(Vector Text)
    -- ^ Words to use
    
  , abcForbiddenTerms   :: !(Vector Text)
    -- ^ Words to NEVER use
  
    -- Visual (for descriptions)
  , abcPrimaryColorHex  :: !Text
  , abcSecondaryColors  :: !(Vector Text)
  , abcFontHeading      :: !Text
  , abcFontBody         :: !Text
  
    -- Constraints
  , abcTaglines         :: !(Vector Text)
    -- ^ Locked copy — never paraphrase
    
  , abcMission          :: !Text
    -- ^ Locked copy — never paraphrase
  
    -- Custom fields
  , abcCustomContext    :: !(Map Text Text)
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Project CompleteBrand → AgentBrandContext
toAgentContext :: CompleteBrand -> AgentBrandContext
toAgentContext brand = AgentBrandContext
  { abcBrandName = brandName (completeBrandIdentity brand)
  , abcBrandId = brandUUID (completeBrandIdentity brand)
  , abcIndustry = brandIndustry (completeBrandIdentity brand)
  , abcDomain = brandDomain (completeBrandIdentity brand)
  , abcToneDescription = voiceSummaryText (brandVoiceSummary (completeBrandVoice brand))
  , abcVoiceBePrompt = generateBePrompt (completeBrandVoice brand)
  , abcVoiceNeverBe = generateNeverBePrompt (completeBrandVoice brand)
  , abcPreferredTerms = vocabularyPreferred (brandVoiceVocabulary (completeBrandVoice brand))
  , abcForbiddenTerms = vocabularyAvoided (brandVoiceVocabulary (completeBrandVoice brand))
  , abcPrimaryColorHex = primaryColorHex (completeBrandPalette brand)
  , abcSecondaryColors = secondaryColorHexes (completeBrandPalette brand)
  , abcFontHeading = headingFontFamily (completeBrandTypography brand)
  , abcFontBody = bodyFontFamily (completeBrandTypography brand)
  , abcTaglines = taglineTexts (completeBrandEditorial brand)
  , abcMission = missionText (completeBrandStrategy brand)
  , abcCustomContext = Map.empty
  }

-- | Generate BE: prompt from IS constraints
generateBePrompt :: BrandVoice -> Text
generateBePrompt voice =
  let descriptors = concatMap (Set.toList . constraintIs . attributeConstraint)
                              (V.toList (brandVoiceAttributes voice))
  in "BE: " <> T.intercalate ", " (map unToneDescriptor descriptors)

-- | Generate NEVER BE: prompt from NOT constraints
generateNeverBePrompt :: BrandVoice -> Text
generateNeverBePrompt voice =
  let descriptors = concatMap (Set.toList . constraintNot . attributeConstraint)
                              (V.toList (brandVoiceAttributes voice))
  in "NEVER BE: " <> T.intercalate ", " (map unToneDescriptor descriptors)
```

### 1.5 Layout Specification

```haskell
-- foundry-core/src/Foundry/Core/Brand/Layout.hs

-- | Grid system specification
data LayoutSpecification = LayoutSpecification
  { layoutPrintGrid       :: !GridSystem
    -- ^ Print/portrait grid (e.g., 8 columns)
    
  , layoutDigitalGrid     :: !GridSystem
    -- ^ Digital/landscape grid (e.g., 16 columns)
    
  , layoutBreakpoints     :: !(Vector Breakpoint)
    -- ^ Responsive breakpoints
    
  , layoutSafeZones       :: !SafeZoneSpec
    -- ^ Content safe zones
    
  , layoutMargins         :: !MarginSpec
    -- ^ Page/screen margins
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Grid system definition
data GridSystem = GridSystem
  { gridColumns           :: !Natural
    -- ^ Number of columns (e.g., 8, 12, 16)
    
  , gridGutter            :: !SpacingUnit
    -- ^ Space between columns
    
  , gridMargin            :: !SpacingUnit
    -- ^ Outer margin
    
  , gridAreas             :: !(Maybe (Vector GridArea))
    -- ^ Named grid areas (optional)
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Breakpoint definition
data Breakpoint = Breakpoint
  { breakpointName        :: !Text
    -- ^ e.g., "mobile", "tablet", "desktop"
    
  , breakpointMinWidth    :: !(Maybe Pixel)
    -- ^ Min-width trigger
    
  , breakpointMaxWidth    :: !(Maybe Pixel)
    -- ^ Max-width trigger
    
  , breakpointColumns     :: !Natural
    -- ^ Grid columns at this breakpoint
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
```

### 1.6 UI Elements Specification

```haskell
-- foundry-core/src/Foundry/Core/Brand/UIElements.hs

-- | UI element specifications
data UISpecification = UISpecification
  { uiButtons             :: !ButtonSpec
  , uiInputs              :: !InputSpec
  , uiCards               :: !CardSpec
  , uiModals              :: !ModalSpec
  , uiNeumorphic          :: !(Maybe NeumorphicSpec)
    -- ^ Neumorphic params (if brand uses this style)
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Button specification
data ButtonSpec = ButtonSpec
  { buttonRadii           :: !CornerRadii
  , buttonPadding         :: !Inset
  , buttonElevation       :: !ElevationLevel
  , buttonStates          :: !InteractiveStates
  , buttonLightDirection  :: !Angle
    -- ^ For neumorphic: where highlight comes from
  , buttonInnerGradient   :: !(Maybe GradientSpec)
    -- ^ Internal gradient (often reversed from background)
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Interactive states
data InteractiveStates = InteractiveStates
  { stateDefault          :: !StateStyle
  , stateHover            :: !StateStyle
  , stateFocus            :: !StateStyle
  , stateActive           :: !StateStyle
  , stateDisabled         :: !StateStyle
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Neumorphic parameters
data NeumorphicSpec = NeumorphicSpec
  { neuLightDirection     :: !Angle
    -- ^ Where light comes from (e.g., 135° = top-left)
    
  , neuDepthScale         :: !DepthScale
    -- ^ How depth relates to element size/importance
    
  , neuLightShadowColor   :: !Color
  , neuDarkShadowColor    :: !Color
  
  , neuAccessibilityStroke :: !Bool
    -- ^ Whether to add thin stroke for vision accessibility
    
  , neuStrokeColor        :: !(Maybe Color)
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
```

### 1.7 Modes Specification

```haskell
-- foundry-core/src/Foundry/Core/Brand/Modes.hs

-- | Color mode specifications (light/dark/high-contrast)
data ModesSpecification = ModesSpecification
  { modesLight            :: !ModeDefinition
  , modesDark             :: !ModeDefinition
  , modesHighContrast     :: !(Maybe ModeDefinition)
  , modesColorBlind       :: !(Maybe ModeDefinition)
  , modesPriority         :: !ModePriority
    -- ^ Which mode is default
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Single mode definition
data ModeDefinition = ModeDefinition
  { modeName              :: !Text
  , modeTokenMapping      :: !(Map SemanticToken ActualColor)
    -- ^ semantic.primary → actual hex value
    
  , modeApprovedContexts  :: !(Vector Text)
    -- ^ When to use this mode
    
  , modeTransition        :: !ModeTransition
    -- ^ How to animate between modes
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Mode transition animation
data ModeTransition = ModeTransition
  { transitionDuration    :: !Milliseconds
  , transitionEasing      :: !EasingFunction
  , transitionProperties  :: !(Vector CSSProperty)
    -- ^ Which properties to animate
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 2. Extraction Algorithms

### 2.1 Color Extraction

```haskell
-- foundry-extract/src/Foundry/Extract/Color.hs

-- | Extract color palette from scraped CSS
extractPalette :: ScrapeResult -> Either ExtractionError ColorExtractionResult

-- Algorithm:
-- 1. Parse all CSS color values (hex, rgb, rgba, hsl, oklch)
-- 2. Convert to OKLCH color space
-- 3. K-means clustering to identify primary colors
-- 4. Frequency analysis for role assignment
-- 5. Contrast ratio verification (WCAG AA)
-- 6. Generate palette with semantic roles

data ColorExtractionConfig = ColorExtractionConfig
  { cecClusterCount       :: !Natural
    -- ^ Number of k-means clusters (default: 8)
    
  , cecMinFrequency       :: !Double
    -- ^ Minimum frequency threshold (default: 0.01)
    
  , cecContrastThreshold  :: !Double
    -- ^ WCAG contrast ratio (default: 4.5 for AA)
  }

-- | K-means clustering in OKLCH space
clusterColors :: Vector OKLCH -> Natural -> Vector (OKLCH, Double)
clusterColors colors k = 
  -- OKLCH is perceptually uniform, so Euclidean distance works
  let centroids = initializeCentroids colors k
      (finalCentroids, assignments) = iterateKMeans colors centroids
      frequencies = computeFrequencies assignments
  in V.zip finalCentroids frequencies

-- | Assign semantic roles based on frequency and position
assignRoles :: Vector (OKLCH, Double) -> BrandPalette
assignRoles clustered =
  let sorted = V.sortBy (comparing (Down . snd)) clustered
      primary = V.head sorted
      secondary = V.take 2 (V.tail sorted)
      accents = V.take 2 (V.drop 3 sorted)
      neutrals = V.filter isNeutral sorted
  in BrandPalette
       { palettePrimary = mkColorRole Primary (fst primary)
       , paletteSecondary = V.map (mkColorRole Secondary . fst) secondary
       , paletteAccent = V.map (mkColorRole Accent . fst) accents
       , paletteNeutral = V.map (mkColorRole Neutral . fst) neutrals
       }
```

### 2.2 Typography Extraction

```haskell
-- foundry-extract/src/Foundry/Extract/Typography.hs

-- | Extract typography from computed styles
extractTypography :: ScrapeResult -> Either ExtractionError TypographyExtractionResult

-- Algorithm:
-- 1. Parse font-family stacks from computed styles
-- 2. Identify heading fonts (h1-h6 elements)
-- 3. Identify body fonts (p, li, etc.)
-- 4. Extract font-size values
-- 5. Detect scale ratio (linear regression on sizes)
-- 6. Extract weights and line-heights

-- | Detect type scale ratio
detectScaleRatio :: Vector FontSize -> TypeScale
detectScaleRatio sizes =
  let logSizes = V.map (log . unFontSize) sizes
      -- Linear regression: log(size) = log(base) + level * log(ratio)
      (intercept, slope) = linearRegression (V.indexed logSizes)
      base = exp intercept
      ratio = exp slope
  in TypeScale
       { typeScaleBase = SpacingUnit base
       , typeScaleRatio = ratio
       }

-- | Extract font stack with fallbacks
extractFontStack :: Text -> FontStack
extractFontStack css =
  let families = T.splitOn "," css
      cleaned = map (T.strip . T.filter (/= '"') . T.filter (/= '\'')) families
  in FontStack
       { fontStackPrimary = V.head cleaned
       , fontStackFallbacks = V.fromList (tail cleaned)
       }
```

### 2.3 Voice Extraction (LLM-Assisted)

```haskell
-- foundry-extract/src/Foundry/Extract/Voice.hs

-- | Extract brand voice from text content
-- NOTE: This requires LLM assistance for IS/NOT constraint mining
extractVoice :: ScrapeResult -> VoiceExtractionResult

-- Algorithm:
-- 1. Extract visible text content
-- 2. Analyze formality (lexical analysis)
-- 3. Analyze sentiment (positive/negative/neutral)
-- 4. Extract frequently used terms (vocabulary)
-- 5. LLM: Generate IS/NOT constraints from copy analysis
-- 6. LLM: Classify personality traits

-- | Rule-based formality scoring
analyzeFormality :: Text -> FormalityScore
analyzeFormality text =
  let words = T.words (T.toLower text)
      -- Formal indicators
      formalWords = ["therefore", "consequently", "moreover", "regarding"]
      -- Informal indicators
      informalWords = ["gonna", "wanna", "kinda", "basically", "actually"]
      -- Contractions
      contractions = filter (T.isInfixOf "'") words
      
      formalCount = length (filter (`elem` formalWords) words)
      informalCount = length (filter (`elem` informalWords) words) 
                    + length contractions
      
      ratio = fromIntegral formalCount / max 1 (fromIntegral informalCount)
  in FormalityScore ratio

-- | LLM prompt for IS/NOT extraction
voiceAnalysisPrompt :: Text -> Text
voiceAnalysisPrompt brandCopy = T.unlines
  [ "Analyze this brand copy and extract tone attributes."
  , ""
  , "For each attribute, provide:"
  , "- Attribute name (e.g., Authoritative, Approachable)"
  , "- IS descriptors (what the brand IS)"
  , "- NOT descriptors (what the brand is NOT)"
  , ""
  , "Brand copy:"
  , brandCopy
  , ""
  , "Output format (JSON):"
  , "{"
  , "  \"attributes\": ["
  , "    {"
  , "      \"name\": \"Authoritative\","
  , "      \"is\": [\"knowledgeable\", \"trusted\", \"confident\"],"
  , "      \"not\": [\"aggressive\", \"pompous\", \"condescending\"]"
  , "    }"
  , "  ]"
  , "}"
  ]
```

### 2.4 Logo Extraction

```haskell
-- foundry-extract/src/Foundry/Extract/Logo.hs

-- | Extract logo specifications
extractLogo :: ScrapeResult -> Either ExtractionError LogoExtractionResult

-- Algorithm:
-- 1. Identify logo candidates (img, svg with logo heuristics)
-- 2. Detect primary lockup (largest, most prominent)
-- 3. Detect variants (different src attributes, same brand)
-- 4. Infer clear space from surrounding elements
-- 5. Extract minimum sizing from CSS

-- | Logo detection heuristics
isLogoCandidate :: Element -> Bool
isLogoCandidate elem =
  let classNames = elementClasses elem
      id = elementId elem
      alt = elementAlt elem
      src = elementSrc elem
  in any isLogoIndicator (classNames ++ [id] ++ maybeToList alt)
  || hasLogoInPath src

isLogoIndicator :: Text -> Bool
isLogoIndicator t =
  let lower = T.toLower t
  in any (`T.isInfixOf` lower) ["logo", "brand", "wordmark", "icon", "symbol"]

-- | Detect logo variants
detectVariants :: Vector Element -> Vector LogoVariant
detectVariants logos =
  let grouped = groupBy sameBaseName logos
      variants = concatMap classifyVariants grouped
  in V.fromList variants

classifyVariants :: Vector Element -> [LogoVariant]
classifyVariants elems =
  -- Heuristics based on filename patterns
  -- e.g., "logo-horizontal.svg", "logo-vertical.svg", "logo-icon.svg"
  map inferVariantType (V.toList elems)
```

### 2.5 Layout Extraction

```haskell
-- foundry-extract/src/Foundry/Extract/Layout.hs

-- | Extract layout/grid specifications
extractLayout :: ScrapeResult -> LayoutExtractionResult

-- Algorithm:
-- 1. Parse CSS grid definitions
-- 2. Parse flexbox patterns
-- 3. Detect common column counts
-- 4. Extract breakpoint media queries
-- 5. Infer gutter from gap properties

-- | Detect grid system from CSS
detectGridSystem :: Vector ComputedStyle -> Maybe GridSystem
detectGridSystem styles =
  let gridStyles = V.filter hasGridProperties styles
      columns = extractColumnCounts gridStyles
      mostCommon = mode columns
      gutters = extractGapValues gridStyles
  in if V.null gridStyles
     then Nothing
     else Just GridSystem
            { gridColumns = fromMaybe 12 mostCommon
            , gridGutter = averageGap gutters
            , gridMargin = SpacingUnit 0  -- Extracted separately
            , gridAreas = Nothing
            }

-- | Extract breakpoints from media queries
extractBreakpoints :: Text -> Vector Breakpoint
extractBreakpoints css =
  let queries = parseMediaQueries css
      breakpoints = map mediaQueryToBreakpoint queries
  in V.fromList (sortBy (comparing breakpointMinWidth) breakpoints)
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 3. Storage Architecture

### 3.1 Three-Tier Model

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│  L1: HAMT (In-Memory)                                                           │
│  ─────────────────────────────────────────────────────────────────────────────  │
│                                                                                 │
│  Latency: ~1ms                                                                  │
│  TTL: 1 hour                                                                    │
│  Capacity: 10,000 brands                                                        │
│                                                                                 │
│  Structure:                                                                     │
│    HAMT (UUID → CacheEntry)                                                     │
│    - Immutable snapshots for concurrent reads                                   │
│    - Copy-on-write updates                                                      │
│    - Content-addressed (SHA256 of serialized brand)                             │
│                                                                                 │
│  Use case: Hot path for MAESTRO agent lookups                                   │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ Eviction / Cache miss
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  L2: DuckDB (Analytical)                                                        │
│  ─────────────────────────────────────────────────────────────────────────────  │
│                                                                                 │
│  Latency: ~10ms                                                                 │
│  TTL: 24 hours                                                                  │
│  Capacity: 1,000,000 brands                                                     │
│                                                                                 │
│  Structure:                                                                     │
│    Columnar storage optimized for analytical queries:                           │
│    - "All brands using Inter font"                                              │
│    - "Average primary color saturation by industry"                             │
│    - "Brands with similar voice characteristics"                                │
│                                                                                 │
│  Schema:                                                                        │
│    brands (id, domain, name, industry, created_at)                              │
│    brand_colors (brand_id, role, l, c, h)                                       │
│    brand_fonts (brand_id, role, family, weight)                                 │
│    brand_voice (brand_id, tone, formality_score)                                │
│                                                                                 │
│  Use case: Analytics dashboard, similarity search                               │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
                                          │
                                          │ Persist / Cold storage
                                          ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│  L3: PostgreSQL (Durable)                                                       │
│  ─────────────────────────────────────────────────────────────────────────────  │
│                                                                                 │
│  Latency: ~100ms                                                                │
│  TTL: Permanent                                                                 │
│  Capacity: Unlimited                                                            │
│                                                                                 │
│  Structure:                                                                     │
│    Normalized + JSONB for flexibility:                                          │
│    - brands table (id, domain, version, jsonb_data)                             │
│    - brand_fields (brand_id, field_key, field_value JSONB)                      │
│    - assets (hash, content_type, blob)                                          │
│    - brand_assets (brand_id, asset_hash, role)                                  │
│                                                                                 │
│  Use case: Source of truth, backup, compliance                                  │
│                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### 3.2 Cache Invalidation

```haskell
-- foundry-storage/src/Foundry/Storage/Cache.hs

-- | Cache entry with version tracking
data CacheEntry = CacheEntry
  { entryValue          :: !CompleteBrand
  , entryVersion        :: !ContentHash
  , entryParentVersion  :: !(Maybe ContentHash)
    -- ^ For inheritance tracking
  , entryComputedAt     :: !UTCTime
  }

-- | Invalidation event (broadcast via ZMQ PUB)
data InvalidationEvent = InvalidationEvent
  { invBrandId          :: !UUID
  , invOldVersion       :: !ContentHash
  , invNewVersion       :: !ContentHash
  , invChangedFields    :: !(Vector Text)
  , invTimestamp        :: !UTCTime
  }

-- | Propagate invalidation through hierarchy
propagateInvalidation :: BrandHierarchy -> InvalidationEvent -> IO [InvalidationEvent]
propagateInvalidation hierarchy event = do
  let children = findChildren hierarchy (invBrandId event)
      inheritedFields = filter isInherited (invChangedFields event)
  
  if V.null inheritedFields
    then pure []  -- No inherited fields changed
    else do
      -- Generate invalidation events for all affected children
      forM children $ \child -> do
        newHash <- computeNewHash child
        pure InvalidationEvent
          { invBrandId = subBrandId child
          , invOldVersion = cachedVersion child
          , invNewVersion = newHash
          , invChangedFields = inheritedFields
          , invTimestamp = invTimestamp event
          }
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 4. Transport Protocols

### 4.1 NDJSON over ZMQ

```haskell
-- foundry-core/src/Foundry/Core/Transport/NDJSON.hs

-- | NDJSON message wrapper
data NDJSONMessage = NDJSONMessage
  { msgType     :: !MessageType
  , msgVersion  :: !Natural
  , msgPayload  :: !Value
  }

data MessageType
  = MsgBrand
  | MsgAsset
  | MsgHierarchy
  | MsgInvalidation
  | MsgComplete
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

-- | Encode brand for COMPASS export
encodeBrandMessage :: CompleteBrand -> ByteString
encodeBrandMessage brand = 
  let msg = NDJSONMessage MsgBrand 1 (toJSON brand)
  in encode msg <> "\n"

-- | ZMQ PUSH to COMPASS
pushToCompass :: ZMQ.Socket ZMQ.Push -> CompleteBrand -> IO ()
pushToCompass sock brand = do
  let msg = encodeBrandMessage brand
  ZMQ.send sock [] msg
```

### 4.2 Sigil Binary Protocol

For high-performance transport, Foundry uses the Sigil binary protocol
(verified in Lean4 with 18 theorems):

```haskell
-- foundry-core/src/Foundry/Core/Sigil/Sigil.hs

-- | Sigil frame structure (see lean/Foundry/Sigil/Sigil.lean for proofs)
data SigilFrame = SigilFrame
  { frameType     :: !Word8
  , frameFlags    :: !Word8
  , frameLength   :: !Word32
  , framePayload  :: !ByteString
  , frameChecksum :: !Word32
  }

-- | Encode CompleteBrand as Sigil frame
encodeSigil :: CompleteBrand -> SigilFrame
-- (Implementation follows Sigil protocol spec)
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 5. Graded Monad Implementation

### 5.1 Permission Lattice

```haskell
-- foundry-core/src/Foundry/Core/Effect/Graded.hs

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

-- | Permission set
data BrandPerm
  = PermRead      -- Read brand data
  | PermScrape    -- Scrape URLs
  | PermExtract   -- Run extractors
  | PermStore     -- Write to storage
  | PermMutate    -- Modify existing brands
  | PermExport    -- Export to COMPASS
  deriving stock (Eq, Ord, Show, Bounded, Enum)

-- | Type-level permission check
type family HasPerm (p :: BrandPerm) (perms :: [BrandPerm]) :: Constraint where
  HasPerm p (p ': _)  = ()
  HasPerm p (_ ': ps) = HasPerm p ps
  HasPerm p '[]       = TypeError ('Text "Missing permission: " ':<>: 'ShowType p)

-- | Graded monad
newtype BrandAgent (perms :: [BrandPerm]) (budget :: Nat) (ctx :: Type) a = BrandAgent
  { unBrandAgent :: ReaderT ctx (StateT Natural (ExceptT AgentError IO)) a
  }
  deriving newtype (Functor, Applicative, Monad, MonadIO)

-- | Require permission
requirePerm :: forall p perms budget ctx. HasPerm p perms => BrandAgent perms budget ctx ()
requirePerm = pure ()

-- | Example: scraping requires PermScrape
scrapeURL 
  :: HasPerm 'PermScrape perms
  => URL 
  -> BrandAgent perms budget ctx ScrapeResult
scrapeURL url = do
  requirePerm @'PermScrape
  -- Implementation
  pure undefined
```

### 5.2 Co-Effect Algebra

```haskell
-- foundry-core/src/Foundry/Core/Effect/CoEffect.hs

-- | Co-effects: what a computation REQUIRES from its environment
data CoEffect
  = CoNone            -- Requires nothing
  | CoNetwork         -- Requires network access
  | CoSandbox         -- Requires sandboxed environment
  | CoDatabase        -- Requires database connection
  | CoLLM             -- Requires LLM access
  | CoTensor [CoEffect]  -- Composition
  deriving stock (Eq, Show)

-- | Co-effect algebra laws (proven in Lean4)
-- 
-- Idempotency:   satisfy (satisfy r) = satisfy r
-- Monotonicity:  r₁ ⊆ r₂ → satisfied r₁ → satisfied r₂
-- Associativity: (r₁ ⊗ r₂) ⊗ r₃ = r₁ ⊗ (r₂ ⊗ r₃)

-- | Tensor (combine requirements)
tensor :: CoEffect -> CoEffect -> CoEffect
tensor CoNone r = r
tensor r CoNone = r
tensor (CoTensor rs1) (CoTensor rs2) = CoTensor (rs1 ++ rs2)
tensor (CoTensor rs) r = CoTensor (r : rs)
tensor r (CoTensor rs) = CoTensor (r : rs)
tensor r1 r2 = CoTensor [r1, r2]

-- | Discharge proof
data DischargeProof = DischargeProof
  { dpCoEffect    :: !CoEffect
  , dpEvidence    :: !Evidence
  , dpTimestamp   :: !UTCTime
  }

-- | Satisfy a co-effect
satisfy :: CoEffect -> DischargeProof -> Bool
satisfy CoNone _ = True
satisfy CoNetwork proof = hasNetworkAccess (dpEvidence proof)
satisfy CoSandbox proof = inSandbox (dpEvidence proof)
satisfy CoDatabase proof = hasDbConnection (dpEvidence proof)
satisfy CoLLM proof = hasLLMAccess (dpEvidence proof)
satisfy (CoTensor rs) proof = all (`satisfy` proof) rs
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## 6. Lean4 Proof Requirements

### 6.1 Typography Monotonicity (SORRY to fix)

```lean
-- lean/Foundry/Brand/Typography.lean

/-- Type scale computes size at level -/
def TypeScale.sizeAt (scale : TypeScale) (level : Int) : SpacingUnit :=
  ⟨scale.base.px * Float.pow scale.ratio (Float.ofInt level), by
    -- Proof that result is positive
    sorry⟩

/-- Type scale is monotonic: larger level → larger size -/
theorem TypeScale.monotonic (scale : TypeScale) (l1 l2 : Int) (h : l1 < l2) :
    (scale.sizeAt l1).px < (scale.sizeAt l2).px := by
  -- Current: sorry
  -- Fix: Apply pow_monotonic and float_mul_pos_lt
  simp only [sizeAt]
  have h_pow : Float.pow scale.ratio (Float.ofInt l1) < Float.pow scale.ratio (Float.ofInt l2) :=
    pow_monotonic scale.ratio (Float.ofInt l1) (Float.ofInt l2) scale.ratio_gt_one 
      (by exact_mod_cast h)
  exact float_mul_pos_lt scale.base.positive h_pow
```

### 6.2 Voice TraitSet Nonempty (SORRY to fix)

```lean
-- lean/Foundry/Brand/Voice.lean

/-- eraseDups preserves non-emptiness -/
theorem eraseDups_length_pos {α : Type*} [DecidableEq α] (l : List α) (h : l.length > 0) :
    l.eraseDups.length > 0 := by
  cases l with
  | nil => simp at h
  | cons x xs => 
    simp only [List.eraseDups_cons]
    split
    · -- x ∈ xs.eraseDups case
      assumption
    · -- x ∉ xs.eraseDups case
      simp only [List.length_cons]
      omega

/-- Create TraitSet from non-empty list -/
def TraitSet.fromList (ts : List Trait) (h : ts.length > 0) : TraitSet :=
  let deduped := ts.eraseDups
  ⟨deduped, eraseDups_length_pos ts h, by simp⟩
```

### 6.3 Brand Composition (to create)

```lean
-- lean/Foundry/Brand/Brand.lean

/-- Complete brand compound type -/
structure CompleteBrand where
  identity    : BrandIdentity
  palette     : BrandPalette
  typography  : BrandTypography
  spacing     : BrandSpacing
  voice       : BrandVoice
  provenance  : Provenance
  -- Compound invariants
  accessible  : palette.meetsWCAG_AA
  deterministic : identity.uuid = uuid5 identity.domain.value identity.name.value

/-- WCAG AA accessibility requirement -/
def BrandPalette.meetsWCAG_AA (p : BrandPalette) : Prop :=
  ∀ (fg bg : OKLCH), fg ∈ p.foregroundColors → bg ∈ p.backgroundColors →
    contrastRatio fg bg ≥ 4.5

/-- Serialization roundtrip -/
theorem CompleteBrand.roundtrip (brand : CompleteBrand) :
    decode (encode brand) = some brand := by
  -- Apply Cornell Box pattern
  sorry  -- TODO: Implement
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

*Document generated: 2026-02-26*
*Status: APPROVED FOR IMPLEMENTATION*

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                 // foundry // spec
                                                              // straylight/2026
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
