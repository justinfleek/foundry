-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // brand // uielements
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SMART Framework UI Elements Layer: Buttons, inputs, depth, lighting,
-- | and accessibility specifications.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | Interactive components that make up the brand's digital product experience.
-- | This module captures the design philosophy and specific rules for buttons,
-- | icons, inputs, and other interface elements.
-- |
-- | SMART FRAMEWORK:
-- |   S - Story-driven: UI philosophy reflects brand personality
-- |   M - Memorable: Consistent visual treatment creates recognition
-- |   A - Agile: Adapts to different contexts (CTA, secondary, disabled)
-- |   R - Responsive: Depth/elevation scales with importance
-- |   T - Targeted: Accessibility ensures inclusive experience
-- |
-- | DEPENDENCIES:
-- |   - Hydrogen.Schema.Brand.UIElements.Buttons
-- |   - Hydrogen.Schema.Brand.UIElements.Accessibility
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Brand (compound Brand type)

module Hydrogen.Schema.Brand.UIElements
  ( -- * Visual Treatment Style
    VisualTreatment
      ( Neumorphic
      , Flat
      , Glassmorphic
      , Skeuomorphic
      , Material
      , Outlined
      )
  , visualTreatmentToString
  , parseVisualTreatment
  
  -- * UI Philosophy
  , UIPhilosophy
  , mkUIPhilosophy
  , philosophyTreatment
  , philosophyNegativeSpace
  , philosophyEffectsUsage
  
  -- * Lighting Direction
  , LightingDirection
      ( LightFromTop
      , LightFromTopLeft
      , LightFromTopRight
      , LightFromLeft
      , LightFromRight
      )
  , lightingDirectionToString
  , parseLightingDirection
  
  -- * Re-exports from UIElements.Buttons
  , module Hydrogen.Schema.Brand.UIElements.Buttons
  
  -- * Re-exports from UIElements.Accessibility
  , module Hydrogen.Schema.Brand.UIElements.Accessibility
  
  -- * UI Element Rules
  , UIElementRules
  , mkUIElementRules
  , rulesBackgroundContext
  , rulesLightingDirection
  , rulesInternalGradient
  , rulesAccessibilityStroke
  , rulesMinContrastRatio
  
  -- * Complete UI Specification
  , UISpecification
  , mkUISpecification
  , uiPhilosophy
  , uiElementRules
  , uiButtonSpecs
  , uiAccessibilityRules
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>=)
  , (>)
  , (&&)
  , (<>)
  , show
  , compare
  )

import Data.Array (length) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, toLower) as String

import Hydrogen.Schema.Brand.UIElements.Buttons
  ( ElevationLevel
      ( ElevationFlat
      , ElevationRaised
      , ElevationFloating
      , ElevationOverlay
      )
  , elevationLevelToString
  , parseElevationLevel
  , ElevationSpec
  , mkElevationSpec
  , elevationLevel
  , elevationShadowBlur
  , elevationShadowOffset
  , ButtonState
      ( ButtonDefault
      , ButtonHover
      , ButtonActive
      , ButtonFocused
      , ButtonDisabled
      )
  , buttonStateToString
  , ButtonVariant
      ( ButtonPrimary
      , ButtonSecondary
      , ButtonTertiary
      , ButtonGhost
      , ButtonDestructive
      )
  , buttonVariantToString
  , ButtonSpec
  , mkButtonSpec
  , buttonVariant
  , buttonElevation
  , buttonBorderRadius
  , buttonPaddingHorizontal
  , buttonPaddingVertical
  , buttonBackgroundColor
  , buttonTextColor
  )

import Hydrogen.Schema.Brand.UIElements.Accessibility
  ( AccessibilityRequirement
      ( MinContrastRatio
      , StrokeRequired
      , FocusIndicator
      , TouchTargetSize
      , ReducedMotion
      )
  , accessibilityRequirementToString
  , AccessibilityRule
  , mkAccessibilityRule
  , accessibilityType
  , accessibilityValue
  , accessibilityDescription
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // visual treatment
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Visual treatment style for UI elements.
data VisualTreatment
  = Neumorphic     -- Soft shadows, raised/inset appearance
  | Flat           -- No shadows, minimal depth
  | Glassmorphic   -- Frosted glass, blur effects
  | Skeuomorphic   -- Realistic textures, 3D appearance
  | Material       -- Material Design shadows/elevation
  | Outlined       -- Border-focused, minimal fill

derive instance eqVisualTreatment :: Eq VisualTreatment

instance ordVisualTreatment :: Ord VisualTreatment where
  compare v1 v2 = compare (treatmentToInt v1) (treatmentToInt v2)
    where
      treatmentToInt :: VisualTreatment -> Int
      treatmentToInt Neumorphic = 0
      treatmentToInt Flat = 1
      treatmentToInt Glassmorphic = 2
      treatmentToInt Skeuomorphic = 3
      treatmentToInt Material = 4
      treatmentToInt Outlined = 5

instance showVisualTreatment :: Show VisualTreatment where
  show = visualTreatmentToString

-- | Convert visual treatment to string.
visualTreatmentToString :: VisualTreatment -> String
visualTreatmentToString Neumorphic = "neumorphic"
visualTreatmentToString Flat = "flat"
visualTreatmentToString Glassmorphic = "glassmorphic"
visualTreatmentToString Skeuomorphic = "skeuomorphic"
visualTreatmentToString Material = "material"
visualTreatmentToString Outlined = "outlined"

-- | Parse visual treatment from string.
parseVisualTreatment :: String -> Maybe VisualTreatment
parseVisualTreatment s = case String.toLower s of
  "neumorphic" -> Just Neumorphic
  "neumorphism" -> Just Neumorphic
  "soft-ui" -> Just Neumorphic
  "flat" -> Just Flat
  "flat-ui" -> Just Flat
  "glassmorphic" -> Just Glassmorphic
  "glassmorphism" -> Just Glassmorphic
  "glass" -> Just Glassmorphic
  "skeuomorphic" -> Just Skeuomorphic
  "skeuomorphism" -> Just Skeuomorphic
  "material" -> Just Material
  "material-design" -> Just Material
  "outlined" -> Just Outlined
  "outline" -> Just Outlined
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // ui philosophy
-- ═══════════════════════════════════════════════════════════════════════════════

-- | UI design philosophy.
type UIPhilosophy =
  { treatment :: VisualTreatment
  , negativeSpace :: String       -- How whitespace is used
  , effectsUsage :: String        -- Guidelines for decorative effects
  }

-- | Create UI philosophy.
mkUIPhilosophy :: VisualTreatment -> String -> String -> Maybe UIPhilosophy
mkUIPhilosophy treatment negSpace effects =
  if String.length negSpace >= 1 && String.length effects >= 1
    then Just
      { treatment: treatment
      , negativeSpace: negSpace
      , effectsUsage: effects
      }
    else Nothing

-- | Get visual treatment.
philosophyTreatment :: UIPhilosophy -> VisualTreatment
philosophyTreatment up = up.treatment

-- | Get negative space guidance.
philosophyNegativeSpace :: UIPhilosophy -> String
philosophyNegativeSpace up = up.negativeSpace

-- | Get effects usage guidance.
philosophyEffectsUsage :: UIPhilosophy -> String
philosophyEffectsUsage up = up.effectsUsage

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // lighting direction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Lighting direction for shadows and highlights.
data LightingDirection
  = LightFromTop        -- Light source above
  | LightFromTopLeft    -- Light source top-left
  | LightFromTopRight   -- Light source top-right
  | LightFromLeft       -- Light source left
  | LightFromRight      -- Light source right

derive instance eqLightingDirection :: Eq LightingDirection

instance ordLightingDirection :: Ord LightingDirection where
  compare l1 l2 = compare (lightToInt l1) (lightToInt l2)
    where
      lightToInt :: LightingDirection -> Int
      lightToInt LightFromTop = 0
      lightToInt LightFromTopLeft = 1
      lightToInt LightFromTopRight = 2
      lightToInt LightFromLeft = 3
      lightToInt LightFromRight = 4

instance showLightingDirection :: Show LightingDirection where
  show = lightingDirectionToString

-- | Convert lighting direction to string.
lightingDirectionToString :: LightingDirection -> String
lightingDirectionToString LightFromTop = "top"
lightingDirectionToString LightFromTopLeft = "top-left"
lightingDirectionToString LightFromTopRight = "top-right"
lightingDirectionToString LightFromLeft = "left"
lightingDirectionToString LightFromRight = "right"

-- | Parse lighting direction from string.
parseLightingDirection :: String -> Maybe LightingDirection
parseLightingDirection s = case String.toLower s of
  "top" -> Just LightFromTop
  "above" -> Just LightFromTop
  "top-left" -> Just LightFromTopLeft
  "topleft" -> Just LightFromTopLeft
  "top-right" -> Just LightFromTopRight
  "topright" -> Just LightFromTopRight
  "left" -> Just LightFromLeft
  "right" -> Just LightFromRight
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // ui element rules
-- ═══════════════════════════════════════════════════════════════════════════════

-- | UI element rules.
type UIElementRules =
  { backgroundContext :: String      -- How elements relate to background
  , lightingDir :: LightingDirection
  , internalGradient :: String       -- Internal gradient direction
  , accessibilityStroke :: Boolean   -- Whether stroke is required
  , minContrast :: Number            -- Minimum contrast ratio
  }

-- | Create UI element rules.
mkUIElementRules
  :: String
  -> LightingDirection
  -> String
  -> Boolean
  -> Number
  -> Maybe UIElementRules
mkUIElementRules bgContext lighting intGrad accStroke contrast =
  if String.length bgContext >= 1 && String.length intGrad >= 1 && contrast > 0.0
    then Just
      { backgroundContext: bgContext
      , lightingDir: lighting
      , internalGradient: intGrad
      , accessibilityStroke: accStroke
      , minContrast: contrast
      }
    else Nothing

-- | Get background context.
rulesBackgroundContext :: UIElementRules -> String
rulesBackgroundContext uer = uer.backgroundContext

-- | Get lighting direction.
rulesLightingDirection :: UIElementRules -> LightingDirection
rulesLightingDirection uer = uer.lightingDir

-- | Get internal gradient direction.
rulesInternalGradient :: UIElementRules -> String
rulesInternalGradient uer = uer.internalGradient

-- | Check if accessibility stroke required.
rulesAccessibilityStroke :: UIElementRules -> Boolean
rulesAccessibilityStroke uer = uer.accessibilityStroke

-- | Get minimum contrast ratio.
rulesMinContrastRatio :: UIElementRules -> Number
rulesMinContrastRatio uer = uer.minContrast

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // ui specification
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete UI specification for a brand.
type UISpecification =
  { philosophy :: UIPhilosophy
  , elementRules :: UIElementRules
  , buttonSpecs :: Array ButtonSpec
  , accessibilityRules :: Array AccessibilityRule
  }

-- | Create UI specification.
mkUISpecification
  :: UIPhilosophy
  -> UIElementRules
  -> Array ButtonSpec
  -> Array AccessibilityRule
  -> Maybe UISpecification
mkUISpecification philosophy rules buttons accessibility =
  if Array.length buttons >= 1
    then Just
      { philosophy: philosophy
      , elementRules: rules
      , buttonSpecs: buttons
      , accessibilityRules: accessibility
      }
    else Nothing

-- | Get UI philosophy.
uiPhilosophy :: UISpecification -> UIPhilosophy
uiPhilosophy us = us.philosophy

-- | Get element rules.
uiElementRules :: UISpecification -> UIElementRules
uiElementRules us = us.elementRules

-- | Get button specs.
uiButtonSpecs :: UISpecification -> Array ButtonSpec
uiButtonSpecs us = us.buttonSpecs

-- | Get accessibility rules.
uiAccessibilityRules :: UISpecification -> Array AccessibilityRule
uiAccessibilityRules us = us.accessibilityRules
