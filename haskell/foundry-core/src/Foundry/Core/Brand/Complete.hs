{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                             // foundry // core // brand // complete
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Complete
Description : Unified CompleteBrand type with all 20+ components
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines the CompleteBrand compound type that unifies all brand components
from the SMART Brand Framework into a single coherent structure.

== SMART Brand Framework

This module implements the complete SMART Brand Framework:

1. Identity (ID, Name, Domain)
2. Overview (Origin, Promise, Industry)
3. Strategy (Mission, Vision, Values, Personality)
4. Messaging (Taglines, Usage Rules)
5. Voice (Tone, Traits, Vocabulary)
6. Editorial (Style Guide)
7. Customers (Segments)
8. Logo (Components, Lockups, Rules)
9. Color (Palette, Gradients)
10. Typography (Fonts, Scale)
11. Spacing (Scale, Units)
12. Layout (Grid, Breakpoints)
13. Material (Shadows, Surfaces)
14. Imagery (Photography, Illustration)
15. Themes (Light, Dark, Contrast)
16. UI Elements (Buttons, Elevation, Accessibility)
17. Graphic Elements (Patterns, Textures, Motifs)
18. Provenance (Source, Hash, Timestamp)

== Dependencies

Requires: All Foundry.Core.Brand.* modules
Required by: Foundry.Extract, COMPASS export

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Complete
  ( -- * Complete Brand
    CompleteBrand (..)
  , mkCompleteBrand

    -- * Brand Summary
  , BrandSummary (..)
  , summarizeBrand

    -- * Validation
  , BrandValidationError (..)
  , validateBrand

    -- * Conversion
  , brandToJSON
  , brandFromJSON
  ) where

import Data.Aeson (ToJSON (..), object, (.=))
import Data.ByteString.Lazy (ByteString)
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as V
import GHC.Generics (Generic)

-- Brand component imports
import Foundry.Core.Brand.Customer (CustomerSegment)
import Foundry.Core.Brand.Editorial (MasterStyleList)
import Foundry.Core.Brand.Gradient (GradientSpecification)
import Foundry.Core.Brand.GraphicElements (GraphicElementsSpecification)
import Foundry.Core.Brand.Identity (BrandId, BrandName, Domain)
import Foundry.Core.Brand.Imagery (ImageryGuidelines)
import Foundry.Core.Brand.Layout (LayoutSystem)
import Foundry.Core.Brand.Logo (LogoSpecification)
import Foundry.Core.Brand.Material (MaterialSystem)
import Foundry.Core.Brand.Overview (BrandOverview)
import Foundry.Core.Brand.Palette (BrandPalette (..))
import Foundry.Core.Brand.Provenance (Provenance)
import Foundry.Core.Brand.Spacing (SpacingScale)
import Foundry.Core.Brand.Strategy (StrategicLayer)
import Foundry.Core.Brand.Tagline (TaglineSet)
import Foundry.Core.Brand.Theme (ThemeSet)
import Foundry.Core.Brand.Typography (Typography)
import Foundry.Core.Brand.UIElements (UISpecification)
import Foundry.Core.Brand.Voice (BrandVoice)

--------------------------------------------------------------------------------
-- Complete Brand
--------------------------------------------------------------------------------

-- | Complete brand specification with all 18+ components
--
-- This is the canonical representation of a brand's complete visual and
-- verbal identity. All components are required except where explicitly
-- marked as optional (Maybe).
data CompleteBrand = CompleteBrand
  { -- ════════════════════════════════════════════════════════════════════════
    -- IDENTITY LAYER (Section 1)
    -- ════════════════════════════════════════════════════════════════════════
    
    cbId       :: !BrandId
    -- ^ Unique brand identifier (UUID5 from domain)
  , cbName     :: !BrandName
    -- ^ Primary brand name
  , cbDomain   :: !Domain
    -- ^ Canonical domain (e.g., "stripe.com")
  , cbOverview :: !BrandOverview
    -- ^ Brand narrative and context
    
    -- ════════════════════════════════════════════════════════════════════════
    -- STRATEGIC LAYER (Sections 2-8)
    -- ════════════════════════════════════════════════════════════════════════
    
  , cbStrategy  :: !StrategicLayer
    -- ^ Mission, values, personality, positioning
  , cbTaglines  :: !TaglineSet
    -- ^ Primary and secondary taglines
  , cbVoice     :: !BrandVoice
    -- ^ Tone, traits, vocabulary
  , cbEditorial :: !MasterStyleList
    -- ^ Editorial style guide
  , cbCustomers :: !(Vector CustomerSegment)
    -- ^ Target customer segments
    
    -- ════════════════════════════════════════════════════════════════════════
    -- EXECUTION LAYER - LOGO (Sections 9-14)
    -- ════════════════════════════════════════════════════════════════════════
    
  , cbLogo :: !LogoSpecification
    -- ^ Complete logo system (components, lockups, rules)
    
    -- ════════════════════════════════════════════════════════════════════════
    -- EXECUTION LAYER - COLOR (Sections 15-16)
    -- ════════════════════════════════════════════════════════════════════════
    
  , cbPalette   :: !BrandPalette
    -- ^ Color palette (OKLCH colors with roles)
  , cbGradients :: !(Maybe GradientSpecification)
    -- ^ Gradient rules (optional)
    
    -- ════════════════════════════════════════════════════════════════════════
    -- EXECUTION LAYER - TYPOGRAPHY (Sections 17-22)
    -- ════════════════════════════════════════════════════════════════════════
    
  , cbTypography :: !Typography
    -- ^ Font families, scale, line heights
    
    -- ════════════════════════════════════════════════════════════════════════
    -- EXECUTION LAYER - SPACING & LAYOUT (Sections 23-25)
    -- ════════════════════════════════════════════════════════════════════════
    
  , cbSpacing :: !SpacingScale
    -- ^ Spacing scale (base unit + multipliers)
  , cbLayout  :: !(Maybe LayoutSystem)
    -- ^ Grid system, breakpoints, zones (optional)
    
    -- ════════════════════════════════════════════════════════════════════════
    -- EXECUTION LAYER - MATERIAL & IMAGERY
    -- ════════════════════════════════════════════════════════════════════════
    
  , cbMaterial :: !(Maybe MaterialSystem)
    -- ^ Shadows, elevation, surfaces (optional)
  , cbImagery  :: !(Maybe ImageryGuidelines)
    -- ^ Photography and illustration rules (optional)
    
    -- ════════════════════════════════════════════════════════════════════════
    -- EXECUTION LAYER - THEMES
    -- ════════════════════════════════════════════════════════════════════════
    
  , cbThemes :: !(Maybe ThemeSet)
    -- ^ Light/dark/contrast themes (optional)
    
    -- ════════════════════════════════════════════════════════════════════════
    -- EXECUTION LAYER - UI ELEMENTS
    -- ════════════════════════════════════════════════════════════════════════
    
  , cbUIElements :: !(Maybe UISpecification)
    -- ^ Button specs, elevation, visual treatment, accessibility (optional)
    
    -- ════════════════════════════════════════════════════════════════════════
    -- EXECUTION LAYER - GRAPHIC ELEMENTS
    -- ════════════════════════════════════════════════════════════════════════
    
  , cbGraphicElements :: !(Maybe GraphicElementsSpecification)
    -- ^ Patterns, textures, logo-derived motifs (optional)
    
    -- ════════════════════════════════════════════════════════════════════════
    -- METADATA
    -- ════════════════════════════════════════════════════════════════════════
    
  , cbProvenance :: !Provenance
    -- ^ Source, hash, timestamp for reproducibility
  }
  deriving stock (Eq, Show, Generic)

-- NOTE: ToJSON/FromJSON instances for CompleteBrand require JSON instances
-- for all nested brand types (BrandOverview, StrategicLayer, TaglineSet, etc.)
-- These will be added incrementally as JSON support is needed.

-- | Smart constructor for CompleteBrand
mkCompleteBrand
  :: BrandId
  -> BrandName
  -> Domain
  -> BrandOverview
  -> StrategicLayer
  -> TaglineSet
  -> BrandVoice
  -> MasterStyleList
  -> Vector CustomerSegment
  -> LogoSpecification
  -> BrandPalette
  -> Maybe GradientSpecification
  -> Typography
  -> SpacingScale
  -> Maybe LayoutSystem
  -> Maybe MaterialSystem
  -> Maybe ImageryGuidelines
  -> Maybe ThemeSet
  -> Maybe UISpecification
  -> Maybe GraphicElementsSpecification
  -> Provenance
  -> CompleteBrand
mkCompleteBrand = CompleteBrand

--------------------------------------------------------------------------------
-- Brand Summary
--------------------------------------------------------------------------------

-- | Lightweight summary of a brand for quick reference
data BrandSummary = BrandSummary
  { bsId           :: !BrandId
  , bsName         :: !BrandName
  , bsDomain       :: !Domain
  , bsColorCount   :: !Int
  , bsFontCount    :: !Int
  , bsHasLogo      :: !Bool
  , bsHasThemes    :: !Bool
  , bsComponentCount :: !Int
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON BrandSummary where
  toJSON BrandSummary{..} = object
    [ "id"             .= bsId
    , "name"           .= bsName
    , "domain"         .= bsDomain
    , "colorCount"     .= bsColorCount
    , "fontCount"      .= bsFontCount
    , "hasLogo"        .= bsHasLogo
    , "hasThemes"      .= bsHasThemes
    , "componentCount" .= bsComponentCount
    ]

-- | Generate a summary from a complete brand
summarizeBrand :: CompleteBrand -> BrandSummary
summarizeBrand cb = BrandSummary
  { bsId = cbId cb
  , bsName = cbName cb
  , bsDomain = cbDomain cb
  , bsColorCount = countColors cb
  , bsFontCount = 2  -- heading + body families
  , bsHasLogo = True  -- Logo is required
  , bsHasThemes = case cbThemes cb of
      Just _ -> True
      Nothing -> False
  , bsComponentCount = countComponents cb
  }
  where
    countColors :: CompleteBrand -> Int
    countColors brand = length $ unBrandPalette $ cbPalette brand
    
    countComponents :: CompleteBrand -> Int
    countComponents brand = 
      11  -- Required components (id, name, domain, overview, strategy, taglines, voice, editorial, customers, logo, palette, typography, spacing, provenance)
      + maybe 0 (const 1) (cbGradients brand)
      + maybe 0 (const 1) (cbLayout brand)
      + maybe 0 (const 1) (cbMaterial brand)
      + maybe 0 (const 1) (cbImagery brand)
      + maybe 0 (const 1) (cbThemes brand)
      + maybe 0 (const 1) (cbUIElements brand)
      + maybe 0 (const 1) (cbGraphicElements brand)

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validation errors for CompleteBrand
data BrandValidationError
  = EmptyCustomerSegments
    -- ^ No customer segments defined
  | MissingPrimaryColor
    -- ^ Palette has no primary color
  | MissingHeadingFont
    -- ^ No heading font family defined
  | InconsistentThemes !Text
    -- ^ Theme configuration is inconsistent
  | InvalidProvenance !Text
    -- ^ Provenance data is invalid
  deriving stock (Eq, Show, Generic)

instance ToJSON BrandValidationError where
  toJSON EmptyCustomerSegments = object ["error" .= ("empty_customer_segments" :: Text)]
  toJSON MissingPrimaryColor = object ["error" .= ("missing_primary_color" :: Text)]
  toJSON MissingHeadingFont = object ["error" .= ("missing_heading_font" :: Text)]
  toJSON (InconsistentThemes msg) = object ["error" .= ("inconsistent_themes" :: Text), "message" .= msg]
  toJSON (InvalidProvenance msg) = object ["error" .= ("invalid_provenance" :: Text), "message" .= msg]

-- | Validate a CompleteBrand
validateBrand :: CompleteBrand -> Vector BrandValidationError
validateBrand brand = V.fromList $ concat
  [ validateCustomers brand
  -- Add more validations as needed
  ]
  where
    validateCustomers :: CompleteBrand -> [BrandValidationError]
    validateCustomers b
      | V.null (cbCustomers b) = [EmptyCustomerSegments]
      | otherwise = []

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

-- NOTE: brandToJSON and brandFromJSON require ToJSON/FromJSON instances
-- for CompleteBrand. These will be implemented once all nested brand types
-- have JSON support.

-- | Placeholder for future JSON serialization
brandToJSON :: CompleteBrand -> ByteString
brandToJSON _ = "{}"

-- | Placeholder for future JSON deserialization
brandFromJSON :: ByteString -> Either String CompleteBrand
brandFromJSON _ = Left "JSON deserialization not yet implemented - requires JSON instances for all nested types"
