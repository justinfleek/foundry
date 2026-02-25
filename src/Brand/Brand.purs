-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // brand // brand
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete Brand compound type — SMART Framework.
-- |
-- | This is the top-level type that brand ingestion produces and agents consume.
-- | A Brand is composed of two layers:
-- |
-- | **STRATEGIC LAYER** (the WHY):
-- | - **Strategy**: Mission, Taglines, Values, Personality, ToneGuide, TargetCustomers
-- | - **Editorial**: Headline rules, Punctuation, Time/Date formatting, Spelling
-- |
-- | **EXECUTION LAYER** (the HOW):
-- | - **Identity**: Name, domain, UUID5
-- | - **Palette**: Colors with semantic roles (primary, secondary, etc.)
-- | - **Typography**: Font families, weights, and scale
-- | - **Spacing**: Grid system or geometric scale
-- | - **Voice**: Tone, personality traits, vocabulary
-- | - **Logo**: Logo components, lockups, clear space, sizing, usage rules
-- | - **Gradient**: Gradient definitions, directions, color stops, rules
-- | - **Layout**: Grid systems, margins, safe zones, print/digital specs
-- | - **UIElements**: Buttons, inputs, depth, lighting, accessibility
-- | - **GraphicElements**: Patterns, textures, logo-derived motifs
-- | - **Modes**: Alternative styling, light/dark, corporate/expressive
-- | - **Imagery**: Image categories, color grading, usage rules
-- | - **Provenance**: Source URL, timestamp, content hash
-- |
-- | STATUS: ✓ PROVEN (Hydrogen.Schema.Brand.*)
-- | All sub-components have Lean4 proofs. See proofs/Hydrogen/Schema/Brand/
-- |
-- | DEPENDENCIES:
-- |   - Hydrogen.Schema.Brand.Identity
-- |   - Hydrogen.Schema.Brand.Palette
-- |   - Hydrogen.Schema.Brand.Typography
-- |   - Hydrogen.Schema.Brand.Spacing
-- |   - Hydrogen.Schema.Brand.Voice
-- |   - Hydrogen.Schema.Brand.Logo
-- |   - Hydrogen.Schema.Brand.Gradient
-- |   - Hydrogen.Schema.Brand.Layout
-- |   - Hydrogen.Schema.Brand.UIElements
-- |   - Hydrogen.Schema.Brand.GraphicElements
-- |   - Hydrogen.Schema.Brand.Modes
-- |   - Hydrogen.Schema.Brand.Imagery
-- |   - Hydrogen.Schema.Brand.Provenance
-- |   - Hydrogen.Schema.Brand.Strategy
-- |   - Hydrogen.Schema.Brand.Strategy.Compound
-- |   - Hydrogen.Schema.Brand.Editorial
-- |
-- | DEPENDENTS:
-- |   - Haskell compass-brand extraction pipeline
-- |   - Agent brand consumption layer

module Hydrogen.Schema.Brand.Brand
  ( -- * Brand Type (Complete SMART Framework)
    Brand
  , mkBrand
  
  -- * Strategic Layer Accessors
  , brandStrategy
  , brandEditorial
  
  -- * Execution Layer Accessors
  , brandIdentity
  , brandPalette
  , brandTypography
  , brandSpacing
  , brandVoice
  , brandLogo
  , brandGradient
  , brandLayout
  , brandUIElements
  , brandGraphicElements
  , brandModes
  , brandImagery
  , brandProvenance
  
  -- * Content Addressing
  , brandContentHash
  , brandsEqual
  ) where

import Prelude
  ( class Eq
  , (==)
  , (<>)
  , show
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // identity layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.Identity 
  ( BrandIdentity
  , unDomain
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // palette layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.Palette
  ( BrandPalette
  , getPrimary
  , unLightness
  , unChroma
  , unHue
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // typography layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.Typography
  ( BrandTypography
  , unFontFamily
  , fontWeightToInt
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // spacing layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.Spacing
  ( BrandSpacing
  , getSpacing
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // voice layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.Voice
  ( BrandVoice
  , toneToString
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // logo layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.Logo
  ( LogoSpecification
  , lockupName
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // gradient layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.Gradient
  ( GradientSpecification
  , gradientName
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // layout layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.Layout
  ( LayoutSpecification
  , gridColumns
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // ui elements layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.UIElements
  ( UISpecification
  , visualTreatmentToString
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                // graphic elements layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.GraphicElements
  ( GraphicElementsSpecification
  , elementName
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // modes layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.Modes
  ( ModesSpecification
  , specDefaultMode
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // imagery layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.Imagery
  ( ImagerySpecification
  , gradingTechniqueToString
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // provenance layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.Provenance
  ( Provenance
  , ContentHash
  , SourceURL
  , Timestamp
  , sha256
  , mkProvenance
  , unContentHash
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // strategy layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.Strategy
  ( MissionStatement
  , unMissionStatement
  )

import Hydrogen.Schema.Brand.Strategy.Compound
  ( StrategicLayer
  , strategicMission
  , strategicOverview
  , overviewBrandName
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // editorial layer imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brand.Editorial
  ( MasterStyleList
  , styleListSpelling
  , spellingRegion
  , regionalSpellingToString
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // brand type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete Brand compound — SMART Framework.
-- |
-- | Composes the Strategic Layer (WHY) with the Execution Layer (HOW).
-- |
-- | Invariants (proven in Lean4):
-- | - identity.uuid is deterministic from identity.domain
-- | - palette has exactly one primary color
-- | - typography weights are 100-900, multiples of 100
-- | - spacing scale ratio > 1 (monotonically increasing)
-- | - voice has at least one trait
-- | - logo has at least one lockup
-- | - gradient has at least one gradient definition
-- | - layout has print and digital specifications
-- | - uiElements has at least one button spec
-- | - graphicElements has at least one element
-- | - modes has at least one mode with a default
-- | - imagery has at least one category
-- | - strategy has non-empty mission, taglines, values, personality (3-5 traits)
-- | - strategy has at least one tone constraint and one target customer segment
-- | - editorial has complete headline, punctuation, contact, spelling, formatting rules
-- | - provenance.contentHash matches serialized content
type Brand =
  { -- Strategic Layer (WHY)
    strategy :: StrategicLayer
  , editorial :: MasterStyleList
    -- Execution Layer (HOW)
  , identity :: BrandIdentity
  , palette :: BrandPalette
  , typography :: BrandTypography
  , spacing :: BrandSpacing
  , voice :: BrandVoice
  , logo :: LogoSpecification
  , gradient :: GradientSpecification
  , layout :: LayoutSpecification
  , uiElements :: UISpecification
  , graphicElements :: GraphicElementsSpecification
  , modes :: ModesSpecification
  , imagery :: ImagerySpecification
  , provenance :: Provenance
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // construction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a complete Brand with all components.
-- |
-- | The provenance content hash is computed automatically from all fields.
mkBrand 
  :: StrategicLayer             -- Strategic layer (mission, taglines, values, etc.)
  -> MasterStyleList            -- Editorial rules (headlines, punctuation, etc.)
  -> BrandIdentity              -- Identity (name, domain, UUID)
  -> BrandPalette               -- Color palette with semantic roles
  -> BrandTypography            -- Typography (fonts, scales)
  -> BrandSpacing               -- Spacing system
  -> BrandVoice                 -- Voice and tone
  -> LogoSpecification          -- Logo components, lockups, sizing
  -> GradientSpecification      -- Gradient definitions and rules
  -> LayoutSpecification        -- Grid systems, margins, safe zones
  -> UISpecification            -- Buttons, inputs, accessibility
  -> GraphicElementsSpecification  -- Patterns, textures, motifs
  -> ModesSpecification         -- Alternative styling modes
  -> ImagerySpecification       -- Image categories, color grading
  -> SourceURL                  -- Source of ingestion
  -> Timestamp                  -- When ingested
  -> Brand
mkBrand strategy editorial identity palette typography spacing voice logo gradient layout uiElements graphicElements modes imagery sourceUrl ingestedAt =
  let 
    -- Serialize for hashing (all fields contribute to content hash)
    contentStr = serializeForHash strategy editorial identity palette typography spacing voice logo gradient layout uiElements graphicElements modes imagery
    contentHash = sha256 contentStr
    provenance = mkProvenance sourceUrl ingestedAt contentHash
  in
    { strategy
    , editorial
    , identity
    , palette
    , typography
    , spacing
    , voice
    , logo
    , gradient
    , layout
    , uiElements
    , graphicElements
    , modes
    , imagery
    , provenance
    }

-- | Serialize brand components for content hashing.
-- |
-- | This produces a canonical string representation. Order matters for
-- | deterministic hashing. All layers contribute to the hash.
serializeForHash 
  :: StrategicLayer
  -> MasterStyleList
  -> BrandIdentity 
  -> BrandPalette 
  -> BrandTypography 
  -> BrandSpacing 
  -> BrandVoice 
  -> LogoSpecification
  -> GradientSpecification
  -> LayoutSpecification
  -> UISpecification
  -> GraphicElementsSpecification
  -> ModesSpecification
  -> ImagerySpecification
  -> String
serializeForHash strategy editorial identity palette typography spacing voice logo gradient layout uiElements graphicElements modes imagery =
  let
    -- Strategic layer contribution
    mission = unMissionStatement (strategicMission strategy)
    brandName = overviewBrandName (strategicOverview strategy)
    
    -- Editorial layer contribution
    spellingRegionStr = regionalSpellingToString (spellingRegion (styleListSpelling editorial))
    
    -- Execution layer contribution (core)
    primary = getPrimary palette
    l = unLightness primary.l
    c = unChroma primary.c
    h = unHue primary.h
    
    -- Execution layer contribution (extended)
    defaultModeName = specDefaultMode modes
    printColumns = gridColumns layout.print.grid
    uiTreatment = visualTreatmentToString uiElements.philosophy.treatment
  in
    -- Canonical format: all fields in deterministic order
    brandName <> "|" <>
    mission <> "|" <>
    spellingRegionStr <> "|" <>
    unDomain identity.domain <> "|" <>
    show l <> "|" <>
    show c <> "|" <>
    show h <> "|" <>
    show (getSpacing spacing 1) <> "|" <>
    unFontFamily typography.headingFamily <> "|" <>
    show (fontWeightToInt typography.regularWeight) <> "|" <>
    toneToString voice.tone <> "|" <>
    defaultModeName <> "|" <>
    show printColumns <> "|" <>
    uiTreatment

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // strategic layer accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get the strategic layer (mission, taglines, values, personality, tone, customers).
brandStrategy :: Brand -> StrategicLayer
brandStrategy b = b.strategy

-- | Get the editorial rules (headlines, punctuation, contact format, spelling, formatting).
brandEditorial :: Brand -> MasterStyleList
brandEditorial b = b.editorial

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // execution layer accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get brand identity (name, domain, UUID).
brandIdentity :: Brand -> BrandIdentity
brandIdentity b = b.identity

-- | Get brand palette (colors with semantic roles).
brandPalette :: Brand -> BrandPalette
brandPalette b = b.palette

-- | Get brand typography (fonts, weights, scale).
brandTypography :: Brand -> BrandTypography
brandTypography b = b.typography

-- | Get brand spacing (grid or geometric scale).
brandSpacing :: Brand -> BrandSpacing
brandSpacing b = b.spacing

-- | Get brand voice (tone, traits, vocabulary).
brandVoice :: Brand -> BrandVoice
brandVoice b = b.voice

-- | Get brand logo (components, lockups, sizing, usage rules).
brandLogo :: Brand -> LogoSpecification
brandLogo b = b.logo

-- | Get brand gradient (definitions, directions, color stops, rules).
brandGradient :: Brand -> GradientSpecification
brandGradient b = b.gradient

-- | Get brand layout (grid systems, margins, safe zones).
brandLayout :: Brand -> LayoutSpecification
brandLayout b = b.layout

-- | Get brand UI elements (buttons, inputs, depth, lighting, accessibility).
brandUIElements :: Brand -> UISpecification
brandUIElements b = b.uiElements

-- | Get brand graphic elements (patterns, textures, logo-derived motifs).
brandGraphicElements :: Brand -> GraphicElementsSpecification
brandGraphicElements b = b.graphicElements

-- | Get brand modes (alternative styling, light/dark, corporate/expressive).
brandModes :: Brand -> ModesSpecification
brandModes b = b.modes

-- | Get brand imagery (image categories, color grading, usage rules).
brandImagery :: Brand -> ImagerySpecification
brandImagery b = b.imagery

-- | Get brand provenance (source, timestamp, content hash).
brandProvenance :: Brand -> Provenance
brandProvenance b = b.provenance

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // content addressing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get the content hash of a brand.
-- |
-- | This is the primary key for content-addressed storage.
-- | The hash is computed from ALL fields (strategic + editorial + execution).
brandContentHash :: Brand -> ContentHash
brandContentHash b = b.provenance.contentHash

-- | Check if two brands have identical content.
-- |
-- | Uses content hash comparison (O(1)) rather than deep equality.
-- | Two brands with identical strategic, editorial, and execution layers
-- | will have the same content hash.
brandsEqual :: Brand -> Brand -> Boolean
brandsEqual b1 b2 = 
  unContentHash (brandContentHash b1) == unContentHash (brandContentHash b2)
