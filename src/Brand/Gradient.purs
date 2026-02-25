-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // brand // gradient
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SMART Framework Gradient Layer: Gradient definitions, directions,
-- | color stops, and usage rules.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | Gradients add depth and visual interest to brand compositions.
-- | This module captures approved gradient combinations, direction rules,
-- | and common errors to avoid.
-- |
-- | SMART FRAMEWORK:
-- |   S - Story-driven: Gradients reinforce brand color narrative
-- |   M - Memorable: Consistent gradient direction creates recognition
-- |   A - Agile: Exception rules for UI elements (buttons, icons)
-- |   R - Responsive: Resolution rules prevent banding
-- |   T - Targeted: Minimum contrast ratios ensure accessibility
-- |
-- | DEPENDENCIES:
-- |   - Hydrogen.Schema.Brand.Gradient.Rules
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Brand (compound Brand type)

module Hydrogen.Schema.Brand.Gradient
  ( -- * Re-exports from Gradient.Rules
    module Hydrogen.Schema.Brand.Gradient.Rules
  
  -- * Color Stop
  , ColorStop
  , mkColorStop
  , stopColorName
  , stopColorHex
  , stopPosition
  
  -- * Gradient Definition
  , GradientDefinition
  , mkGradientDefinition
  , gradientName
  , gradientDirection
  , gradientTopColor
  , gradientBottomColor
  , gradientStops
  
  -- * Gradient Rules
  , GradientRules
  , mkGradientRules
  , defaultDirection
  , minimumContrast
  , antiBandingNotes
  , gradientExceptions
  , gradientErrors
  
  -- * Complete Gradient Specification
  , GradientSpecification
  , mkGradientSpecification
  , specGradients
  , specRules
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>=)
  , (>)
  , (&&)
  , (<=)
  , (<>)
  , show
  , compare
  )

import Data.Array (length) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length) as String

import Hydrogen.Schema.Brand.Gradient.Rules
  ( GradientDirection
      ( ToTop
      , ToBottom
      , ToLeft
      , ToRight
      , ToTopLeft
      , ToTopRight
      , ToBottomLeft
      , ToBottomRight
      )
  , gradientDirectionToString
  , gradientDirectionToDegrees
  , parseGradientDirection
  , GradientExceptionContext
      ( UIButtons
      , UIIcons
      , UICards
      , Backgrounds
      , Overlays
      )
  , exceptionContextToString
  , parseExceptionContext
  , GradientException
  , mkGradientException
  , exceptionContext
  , exceptionDirection
  , exceptionNotes
  , GradientErrorType
      ( TintCombination
      , OpacityReduction
      , UnapprovedGradient
      , EdgeTreatment
      , DirectionReversal
      , UnapprovedAngle
      , MultipleColors
      , InsufficientContrast
      )
  , gradientErrorTypeToString
  , GradientError
  , mkGradientError
  , gradientErrorType
  , gradientErrorDescription
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // color stop
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A color stop in a gradient.
type ColorStop =
  { colorName :: String    -- Brand color name (e.g., "Brand_P1")
  , colorHex :: String     -- Hex value
  , position :: Number     -- Position 0.0 to 1.0
  }

-- | Create color stop.
mkColorStop :: String -> String -> Number -> Maybe ColorStop
mkColorStop name hex pos =
  if String.length name >= 1 
     && String.length hex >= 4 
     && pos >= 0.0 
     && pos <= 1.0
    then Just { colorName: name, colorHex: hex, position: pos }
    else Nothing

-- | Get color name.
stopColorName :: ColorStop -> String
stopColorName cs = cs.colorName

-- | Get color hex.
stopColorHex :: ColorStop -> String
stopColorHex cs = cs.colorHex

-- | Get position.
stopPosition :: ColorStop -> Number
stopPosition cs = cs.position

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // gradient definition
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A gradient definition.
type GradientDefinition =
  { name :: String                   -- Gradient identifier
  , direction :: GradientDirection
  , topColor :: ColorStop            -- Lighter color (at start)
  , bottomColor :: ColorStop         -- Darker color (at end)
  , stops :: Array ColorStop         -- All stops for complex gradients
  }

-- | Create gradient definition.
mkGradientDefinition
  :: String
  -> GradientDirection
  -> ColorStop
  -> ColorStop
  -> Maybe GradientDefinition
mkGradientDefinition name dir top bottom =
  if String.length name >= 1
    then Just
      { name: name
      , direction: dir
      , topColor: top
      , bottomColor: bottom
      , stops: [top, bottom]
      }
    else Nothing

-- | Get gradient name.
gradientName :: GradientDefinition -> String
gradientName gd = gd.name

-- | Get gradient direction.
gradientDirection :: GradientDefinition -> GradientDirection
gradientDirection gd = gd.direction

-- | Get top (light) color.
gradientTopColor :: GradientDefinition -> ColorStop
gradientTopColor gd = gd.topColor

-- | Get bottom (dark) color.
gradientBottomColor :: GradientDefinition -> ColorStop
gradientBottomColor gd = gd.bottomColor

-- | Get all color stops.
gradientStops :: GradientDefinition -> Array ColorStop
gradientStops gd = gd.stops

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // gradient rules
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Global gradient rules.
type GradientRules =
  { defaultDir :: GradientDirection    -- Default direction for all gradients
  , minContrast :: Number              -- Minimum contrast ratio (e.g., 4.5)
  , antiBanding :: String              -- Anti-banding guidance
  , exceptions :: Array GradientException
  , errors :: Array GradientError
  }

-- | Create gradient rules.
mkGradientRules
  :: GradientDirection
  -> Number
  -> String
  -> Array GradientException
  -> Array GradientError
  -> Maybe GradientRules
mkGradientRules dir contrast antibanding exceptions errors =
  if contrast > 0.0 && String.length antibanding >= 1
    then Just
      { defaultDir: dir
      , minContrast: contrast
      , antiBanding: antibanding
      , exceptions: exceptions
      , errors: errors
      }
    else Nothing

-- | Get default direction.
defaultDirection :: GradientRules -> GradientDirection
defaultDirection gr = gr.defaultDir

-- | Get minimum contrast.
minimumContrast :: GradientRules -> Number
minimumContrast gr = gr.minContrast

-- | Get anti-banding notes.
antiBandingNotes :: GradientRules -> String
antiBandingNotes gr = gr.antiBanding

-- | Get exceptions.
gradientExceptions :: GradientRules -> Array GradientException
gradientExceptions gr = gr.exceptions

-- | Get errors.
gradientErrors :: GradientRules -> Array GradientError
gradientErrors gr = gr.errors

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // gradient specification
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete gradient specification for a brand.
type GradientSpecification =
  { gradients :: Array GradientDefinition
  , rules :: GradientRules
  }

-- | Create gradient specification.
mkGradientSpecification
  :: Array GradientDefinition
  -> GradientRules
  -> Maybe GradientSpecification
mkGradientSpecification grads rules =
  if Array.length grads >= 1
    then Just { gradients: grads, rules: rules }
    else Nothing

-- | Get all gradient definitions.
specGradients :: GradientSpecification -> Array GradientDefinition
specGradients gs = gs.gradients

-- | Get gradient rules.
specRules :: GradientSpecification -> GradientRules
specRules gs = gs.rules
