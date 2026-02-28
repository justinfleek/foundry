{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                         // foundry // core // brand // uielements
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.UIElements
Description : UI Elements specification (buttons, inputs, depth, lighting, accessibility)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

SMART Framework UI Elements Layer: Buttons, inputs, depth, lighting,
and accessibility specifications.

Interactive components that make up the brand's digital product experience.
This module captures the design philosophy and specific rules for buttons,
icons, inputs, and other interface elements.

== SMART Framework

  S - Story-driven: UI philosophy reflects brand personality
  M - Memorable: Consistent visual treatment creates recognition
  A - Agile: Adapts to different contexts (CTA, secondary, disabled)
  R - Responsive: Depth/elevation scales with importance
  T - Targeted: Accessibility ensures inclusive experience

== Dependencies

Requires: vector, text, aeson
Required by: Foundry.Core.Brand.Complete

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.UIElements
  ( -- * Visual Treatment Style
    VisualTreatment (..)
  , visualTreatmentToText
  , parseVisualTreatment

    -- * UI Philosophy
  , UIPhilosophy (..)
  , mkUIPhilosophy

    -- * Lighting Direction
  , LightingDirection (..)
  , lightingDirectionToText
  , parseLightingDirection

    -- * UI Element Rules
  , UIElementRules (..)
  , mkUIElementRules

    -- * Complete UI Specification
  , UISpecification (..)
  , mkUISpecification
  , defaultUISpecification

    -- * Re-exports from sub-modules
  , module Foundry.Core.Brand.UIElements.Buttons
  , module Foundry.Core.Brand.UIElements.Accessibility
  ) where

import Data.Aeson
  ( FromJSON (..)
  , ToJSON (..)
  , object
  , withObject
  , withText
  , (.:)
  , (.=)
  )
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V
import GHC.Generics (Generic)

import Foundry.Core.Brand.UIElements.Accessibility
import Foundry.Core.Brand.UIElements.Buttons

--------------------------------------------------------------------------------
-- Visual Treatment
--------------------------------------------------------------------------------

-- | Visual treatment style for UI elements.
data VisualTreatment
  = Neumorphic     -- ^ Soft shadows, raised/inset appearance
  | Flat           -- ^ No shadows, minimal depth
  | Glassmorphic   -- ^ Frosted glass, blur effects
  | Skeuomorphic   -- ^ Realistic textures, 3D appearance
  | Material       -- ^ Material Design shadows/elevation
  | Outlined       -- ^ Border-focused, minimal fill
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

-- | Convert visual treatment to text.
visualTreatmentToText :: VisualTreatment -> Text
visualTreatmentToText Neumorphic   = "neumorphic"
visualTreatmentToText Flat         = "flat"
visualTreatmentToText Glassmorphic = "glassmorphic"
visualTreatmentToText Skeuomorphic = "skeuomorphic"
visualTreatmentToText Material     = "material"
visualTreatmentToText Outlined     = "outlined"

-- | Parse visual treatment from text.
parseVisualTreatment :: Text -> Maybe VisualTreatment
parseVisualTreatment t = case T.toLower t of
  "neumorphic"      -> Just Neumorphic
  "neumorphism"     -> Just Neumorphic
  "soft-ui"         -> Just Neumorphic
  "flat"            -> Just Flat
  "flat-ui"         -> Just Flat
  "glassmorphic"    -> Just Glassmorphic
  "glassmorphism"   -> Just Glassmorphic
  "glass"           -> Just Glassmorphic
  "skeuomorphic"    -> Just Skeuomorphic
  "skeuomorphism"   -> Just Skeuomorphic
  "material"        -> Just Material
  "material-design" -> Just Material
  "outlined"        -> Just Outlined
  "outline"         -> Just Outlined
  _                 -> Nothing

instance ToJSON VisualTreatment where
  toJSON = toJSON . visualTreatmentToText

instance FromJSON VisualTreatment where
  parseJSON = withText "VisualTreatment" $ \t ->
    case parseVisualTreatment t of
      Just vt -> pure vt
      Nothing -> fail $ "Invalid visual treatment: " <> T.unpack t

--------------------------------------------------------------------------------
-- UI Philosophy
--------------------------------------------------------------------------------

-- | UI design philosophy describing the overall approach to interface design.
data UIPhilosophy = UIPhilosophy
  { upTreatment     :: !VisualTreatment
    -- ^ The visual treatment style
  , upNegativeSpace :: !Text
    -- ^ How whitespace is used
  , upEffectsUsage  :: !Text
    -- ^ Guidelines for decorative effects
  }
  deriving stock (Eq, Show, Generic)

-- | Create UI philosophy with validation.
mkUIPhilosophy :: VisualTreatment -> Text -> Text -> Maybe UIPhilosophy
mkUIPhilosophy treatment negSpace effects
  | T.length negSpace >= 1
  , T.length effects >= 1
  = Just UIPhilosophy
      { upTreatment     = treatment
      , upNegativeSpace = negSpace
      , upEffectsUsage  = effects
      }
  | otherwise = Nothing

instance ToJSON UIPhilosophy where
  toJSON UIPhilosophy{..} = object
    [ "treatment"     .= upTreatment
    , "negativeSpace" .= upNegativeSpace
    , "effectsUsage"  .= upEffectsUsage
    ]

instance FromJSON UIPhilosophy where
  parseJSON = withObject "UIPhilosophy" $ \o -> do
    upTreatment     <- o .: "treatment"
    upNegativeSpace <- o .: "negativeSpace"
    upEffectsUsage  <- o .: "effectsUsage"
    pure UIPhilosophy{..}

--------------------------------------------------------------------------------
-- Lighting Direction
--------------------------------------------------------------------------------

-- | Lighting direction for shadows and highlights.
data LightingDirection
  = LightFromTop       -- ^ Light source above
  | LightFromTopLeft   -- ^ Light source top-left (most common)
  | LightFromTopRight  -- ^ Light source top-right
  | LightFromLeft      -- ^ Light source left
  | LightFromRight     -- ^ Light source right
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

-- | Convert lighting direction to text.
lightingDirectionToText :: LightingDirection -> Text
lightingDirectionToText LightFromTop      = "top"
lightingDirectionToText LightFromTopLeft  = "top-left"
lightingDirectionToText LightFromTopRight = "top-right"
lightingDirectionToText LightFromLeft     = "left"
lightingDirectionToText LightFromRight    = "right"

-- | Parse lighting direction from text.
parseLightingDirection :: Text -> Maybe LightingDirection
parseLightingDirection t = case T.toLower t of
  "top"       -> Just LightFromTop
  "above"     -> Just LightFromTop
  "top-left"  -> Just LightFromTopLeft
  "topleft"   -> Just LightFromTopLeft
  "top-right" -> Just LightFromTopRight
  "topright"  -> Just LightFromTopRight
  "left"      -> Just LightFromLeft
  "right"     -> Just LightFromRight
  _           -> Nothing

instance ToJSON LightingDirection where
  toJSON = toJSON . lightingDirectionToText

instance FromJSON LightingDirection where
  parseJSON = withText "LightingDirection" $ \t ->
    case parseLightingDirection t of
      Just ld -> pure ld
      Nothing -> fail $ "Invalid lighting direction: " <> T.unpack t

--------------------------------------------------------------------------------
-- UI Element Rules
--------------------------------------------------------------------------------

-- | UI element rules defining how elements relate to each other.
data UIElementRules = UIElementRules
  { uerBackgroundContext    :: !Text
    -- ^ How elements relate to background
  , uerLightingDirection    :: !LightingDirection
    -- ^ Lighting direction for shadows
  , uerInternalGradient     :: !Text
    -- ^ Internal gradient direction for elements
  , uerAccessibilityStroke  :: !Bool
    -- ^ Whether stroke is required for accessibility
  , uerMinContrastRatio     :: !Double
    -- ^ Minimum contrast ratio (WCAG)
  }
  deriving stock (Eq, Show, Generic)

-- | Create UI element rules with validation.
mkUIElementRules
  :: Text              -- ^ Background context
  -> LightingDirection -- ^ Lighting direction
  -> Text              -- ^ Internal gradient
  -> Bool              -- ^ Accessibility stroke required
  -> Double            -- ^ Minimum contrast ratio
  -> Maybe UIElementRules
mkUIElementRules bgContext lighting intGrad accStroke contrast
  | T.length bgContext >= 1
  , T.length intGrad >= 1
  , contrast > 0
  = Just UIElementRules
      { uerBackgroundContext   = bgContext
      , uerLightingDirection   = lighting
      , uerInternalGradient    = intGrad
      , uerAccessibilityStroke = accStroke
      , uerMinContrastRatio    = contrast
      }
  | otherwise = Nothing

instance ToJSON UIElementRules where
  toJSON UIElementRules{..} = object
    [ "backgroundContext"   .= uerBackgroundContext
    , "lightingDirection"   .= uerLightingDirection
    , "internalGradient"    .= uerInternalGradient
    , "accessibilityStroke" .= uerAccessibilityStroke
    , "minContrastRatio"    .= uerMinContrastRatio
    ]

instance FromJSON UIElementRules where
  parseJSON = withObject "UIElementRules" $ \o -> do
    uerBackgroundContext   <- o .: "backgroundContext"
    uerLightingDirection   <- o .: "lightingDirection"
    uerInternalGradient    <- o .: "internalGradient"
    uerAccessibilityStroke <- o .: "accessibilityStroke"
    uerMinContrastRatio    <- o .: "minContrastRatio"
    pure UIElementRules{..}

--------------------------------------------------------------------------------
-- Complete UI Specification
--------------------------------------------------------------------------------

-- | Complete UI specification for a brand.
data UISpecification = UISpecification
  { uisPhilosophy         :: !UIPhilosophy
    -- ^ Overall design philosophy
  , uisElementRules       :: !UIElementRules
    -- ^ Element interaction rules
  , uisButtonSpecs        :: !(Vector ButtonSpec)
    -- ^ Button specifications (primary, secondary, etc.)
  , uisAccessibilityRules :: !(Vector AccessibilityRule)
    -- ^ Accessibility requirements
  }
  deriving stock (Eq, Show, Generic)

-- | Create UI specification with validation.
mkUISpecification
  :: UIPhilosophy
  -> UIElementRules
  -> Vector ButtonSpec
  -> Vector AccessibilityRule
  -> Maybe UISpecification
mkUISpecification philosophy rules buttons accessibility
  | V.length buttons >= 1
  = Just UISpecification
      { uisPhilosophy         = philosophy
      , uisElementRules       = rules
      , uisButtonSpecs        = buttons
      , uisAccessibilityRules = accessibility
      }
  | otherwise = Nothing

-- | Default UI specification for brands without explicit UI specs.
defaultUISpecification :: UISpecification
defaultUISpecification = UISpecification
  { uisPhilosophy = UIPhilosophy
      { upTreatment     = Flat
      , upNegativeSpace = "Generous whitespace, breathing room around elements"
      , upEffectsUsage  = "Minimal decorative effects, focus on content"
      }
  , uisElementRules = UIElementRules
      { uerBackgroundContext   = "Elements should stand out from background"
      , uerLightingDirection   = LightFromTopLeft
      , uerInternalGradient    = "none"
      , uerAccessibilityStroke = True
      , uerMinContrastRatio    = 4.5  -- WCAG AA
      }
  , uisButtonSpecs = V.singleton ButtonSpec
      { bsVariant         = ButtonPrimary
      , bsElevation       = ElevationSpec ElevationFlat 0 0
      , bsBorderRadius    = 4
      , bsPaddingH        = 16
      , bsPaddingV        = 8
      , bsBackgroundColor = "#0066CC"
      , bsTextColor       = "#FFFFFF"
      }
  , uisAccessibilityRules = V.fromList
      [ AccessibilityRule MinContrastRatio "4.5:1" "WCAG AA standard for normal text"
      , AccessibilityRule TouchTargetSize "44px" "Minimum touch target size"
      , AccessibilityRule FocusIndicator "visible" "Focus must be visible for keyboard navigation"
      ]
  }

instance ToJSON UISpecification where
  toJSON UISpecification{..} = object
    [ "philosophy"         .= uisPhilosophy
    , "elementRules"       .= uisElementRules
    , "buttonSpecs"        .= uisButtonSpecs
    , "accessibilityRules" .= uisAccessibilityRules
    ]

instance FromJSON UISpecification where
  parseJSON = withObject "UISpecification" $ \o -> do
    uisPhilosophy         <- o .: "philosophy"
    uisElementRules       <- o .: "elementRules"
    uisButtonSpecs        <- o .: "buttonSpecs"
    uisAccessibilityRules <- o .: "accessibilityRules"
    pure UISpecification{..}
