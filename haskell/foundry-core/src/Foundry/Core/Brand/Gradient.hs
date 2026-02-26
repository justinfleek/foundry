{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // foundry // brand/gradient
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Gradient
Description : SMART Framework Gradient Layer (Section 16)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Gradient specifications following the SMART Brand Ingestion Framework.

== SMART Framework Section 16: Gradients

From the framework:
- Direction: The approved angle and flow direction (e.g., -90°, lighter on top)
- Two-stop only: Do not use multiple colors in a single gradient
- Resolution: High enough to avoid banding
- Anti-Banding: Do not use Noise/Grain to mask banding

== AI Ingestion Priority #5

"Gradient Direction + Stop Colors — Two data points per gradient (top color,
bottom color) plus a global direction rule. Simple, enforceable."

== Invariants

* Angle ∈ [0, 360)
* Stop positions ∈ [0, 1]
* Exactly two stops per gradient (SMART mandates two-stop only)
* Contrast ratio ≥ 4.5:1 for accessibility

DEPENDENCIES:
  - Foundry.Core.Brand.Palette (for color references)

DEPENDENTS:
  - Foundry.Core.Brand (compound Brand type)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Gradient
  ( -- * Gradient Direction
    GradientAngle (..)
  , mkGradientAngle
  , angleToCSS
  
    -- * Gradient Stops
  , GradientStop (..)
  , mkGradientStop
  
    -- * Two-Stop Gradient (SMART mandated)
  , TwoStopGradient (..)
  , mkTwoStopGradient
  , gradientToCSS
  
    -- * Gradient Errors (DO NOT rules)
  , GradientError (..)
  , gradientErrorToText
  
    -- * Complete Gradient Specification
  , GradientSpecification (..)
  , mkGradientSpecification
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V

--------------------------------------------------------------------------------
-- Gradient Direction
--------------------------------------------------------------------------------

-- | Gradient angle in degrees (0-360, CSS convention)
-- 
-- CSS Convention:
--   0°   = to top (bottom to top)
--   90°  = to right (left to right)
--   180° = to bottom (top to bottom)
--   270° = to left (right to left)
newtype GradientAngle = GradientAngle {unGradientAngle :: Double}
  deriving stock (Eq, Ord, Show)

-- | Create gradient angle with validation
mkGradientAngle :: Double -> Maybe GradientAngle
mkGradientAngle deg
  | deg >= 0 && deg < 360 = Just (GradientAngle deg)
  | otherwise = Nothing

-- | Convert angle to CSS string
angleToCSS :: GradientAngle -> Text
angleToCSS (GradientAngle deg) = T.pack (show deg) <> "deg"

--------------------------------------------------------------------------------
-- Gradient Stops
--------------------------------------------------------------------------------

-- | A gradient color stop (color + position)
data GradientStop = GradientStop
  { stopColor    :: !Text    -- ^ Hex color (e.g., "#8e43f0")
  , stopPosition :: !Double  -- ^ Position 0.0 (start) to 1.0 (end)
  }
  deriving stock (Eq, Show)

-- | Create gradient stop with validation
mkGradientStop :: Text -> Double -> Maybe GradientStop
mkGradientStop color pos
  | T.length color >= 4  -- At least "#rgb"
  , pos >= 0 && pos <= 1 = Just GradientStop
      { stopColor = color
      , stopPosition = pos
      }
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Two-Stop Gradient (SMART Framework mandates two-stop only)
--------------------------------------------------------------------------------

-- | A two-stop gradient (SMART Framework: "Do not use multiple colors in a 
-- single gradient (two-stop only)")
--
-- From SMART Framework AI Ingestion Priority #5:
-- "Two data points per gradient (top color, bottom color) plus a global 
-- direction rule. Simple, enforceable."
data TwoStopGradient = TwoStopGradient
  { gradientName      :: !Text          -- ^ e.g., "Primary Gradient"
  , gradientAngle     :: !GradientAngle -- ^ Direction
  , gradientLightStop :: !GradientStop  -- ^ Lighter color (typically top/start)
  , gradientDarkStop  :: !GradientStop  -- ^ Darker color (typically bottom/end)
  }
  deriving stock (Eq, Show)

-- | Create two-stop gradient with validation
mkTwoStopGradient
  :: Text          -- ^ Name
  -> GradientAngle -- ^ Angle
  -> GradientStop  -- ^ Light stop
  -> GradientStop  -- ^ Dark stop
  -> Maybe TwoStopGradient
mkTwoStopGradient name angle light dark
  | T.length name >= 1
  , stopPosition light < stopPosition dark  -- Light must come before dark
    = Just TwoStopGradient
        { gradientName = name
        , gradientAngle = angle
        , gradientLightStop = light
        , gradientDarkStop = dark
        }
  | otherwise = Nothing

-- | Convert gradient to CSS linear-gradient string
gradientToCSS :: TwoStopGradient -> Text
gradientToCSS g = T.concat
  [ "linear-gradient("
  , angleToCSS (gradientAngle g)
  , ", "
  , stopColor (gradientLightStop g)
  , " "
  , T.pack (show (stopPosition (gradientLightStop g) * 100)) <> "%"
  , ", "
  , stopColor (gradientDarkStop g)
  , " "
  , T.pack (show (stopPosition (gradientDarkStop g) * 100)) <> "%"
  , ")"
  ]

--------------------------------------------------------------------------------
-- Gradient Errors (DO NOT rules from SMART Framework)
--------------------------------------------------------------------------------

-- | Gradient error categories from SMART Framework Section 16
--
-- "Gradient Common Errors:
--   - Do not combine tints or lower gradient opacity
--   - Do not use unapproved gradients
--   - Do not apply treatments (vignettes, glows) to gradient edges
--   - Do not reverse gradient direction (unless in approved exception contexts)
--   - Do not use unapproved angles
--   - Do not use multiple colors in a single gradient (two-stop only)
--   - Maintain minimum contrast ratio (e.g., 4.5:1)"
data GradientError
  = CombinedTints           -- ^ Don't combine tints or lower opacity
  | UnapprovedGradient      -- ^ Only use approved gradients
  | EdgeTreatment           -- ^ No vignettes, glows on edges
  | ReversedDirection       -- ^ Don't reverse unless approved
  | UnapprovedAngle         -- ^ Only use approved angles
  | MultipleStops           -- ^ Two-stop only
  | InsufficientContrast    -- ^ Below 4.5:1 ratio
  | BandingVisible          -- ^ Resolution too low
  | NoiseMasking            -- ^ Don't use noise/grain to hide banding
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | Convert gradient error to human-readable text
gradientErrorToText :: GradientError -> Text
gradientErrorToText CombinedTints = "Do not combine tints or lower gradient opacity"
gradientErrorToText UnapprovedGradient = "Do not use unapproved gradients"
gradientErrorToText EdgeTreatment = "Do not apply treatments (vignettes, glows) to gradient edges"
gradientErrorToText ReversedDirection = "Do not reverse gradient direction unless approved"
gradientErrorToText UnapprovedAngle = "Do not use unapproved angles"
gradientErrorToText MultipleStops = "Do not use multiple colors in a single gradient (two-stop only)"
gradientErrorToText InsufficientContrast = "Maintain minimum contrast ratio (4.5:1)"
gradientErrorToText BandingVisible = "Use high enough resolution to avoid banding"
gradientErrorToText NoiseMasking = "Do not use Noise/Grain to mask banding"

--------------------------------------------------------------------------------
-- Complete Gradient Specification
--------------------------------------------------------------------------------

-- | Complete gradient specification for a brand
data GradientSpecification = GradientSpecification
  { gradientDefaultAngle   :: !GradientAngle          -- ^ Default direction for all gradients
  , gradientApproved       :: !(Vector TwoStopGradient) -- ^ Approved gradient combinations
  , gradientExceptionRules :: !(Vector Text)          -- ^ Contexts where rules may differ
  , gradientMinContrast    :: !Double                 -- ^ Minimum contrast ratio (default 4.5)
  }
  deriving stock (Eq, Show)

-- | Create gradient specification with validation
mkGradientSpecification
  :: GradientAngle
  -> Vector TwoStopGradient
  -> Vector Text
  -> Double
  -> Maybe GradientSpecification
mkGradientSpecification angle approved exceptions contrast
  | V.length approved >= 1  -- Must have at least one approved gradient
  , contrast >= 1.0         -- Contrast must be positive
    = Just GradientSpecification
        { gradientDefaultAngle = angle
        , gradientApproved = approved
        , gradientExceptionRules = exceptions
        , gradientMinContrast = contrast
        }
  | otherwise = Nothing
