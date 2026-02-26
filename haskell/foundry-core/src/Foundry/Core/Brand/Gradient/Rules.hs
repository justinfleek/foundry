{- |
Module      : Foundry.Core.Brand.Gradient.Rules
Description : Gradient directions, exceptions, and error types
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Gradient directions, exception contexts, and error types.
Mirrors Hydrogen.Schema.Brand.Gradient.Rules from PureScript.

DEPENDENCIES:
  - None (foundational module)

DEPENDENTS:
  - Foundry.Core.Brand.Gradient (main gradient module)
-}
module Foundry.Core.Brand.Gradient.Rules
  ( -- * Gradient Direction
    GradientDirection (..)
  , gradientDirectionToText
  , gradientDirectionToDegrees
  , parseGradientDirection
  
    -- * Gradient Exception
  , GradientExceptionContext (..)
  , exceptionContextToText
  , parseExceptionContext
  
  , GradientException (..)
  , mkGradientException
  
    -- * Gradient Error
  , GradientErrorType (..)
  , gradientErrorTypeToText
  
  , GradientError (..)
  , mkGradientError
  ) where

import Data.Text (Text)
import Data.Text qualified as T

-- | Gradient direction.
data GradientDirection
  = ToTop           -- ^ 0° (bottom to top)
  | ToBottom        -- ^ 180° (top to bottom)
  | ToLeft          -- ^ 270° (right to left)
  | ToRight         -- ^ 90° (left to right)
  | ToTopLeft       -- ^ 315° (bottom-right to top-left)
  | ToTopRight      -- ^ 45° (bottom-left to top-right)
  | ToBottomLeft    -- ^ 225° (top-right to bottom-left)
  | ToBottomRight   -- ^ 135° (top-left to bottom-right)
  deriving stock (Eq, Ord, Show)

-- | Convert gradient direction to text.
gradientDirectionToText :: GradientDirection -> Text
gradientDirectionToText ToTop = "to-top"
gradientDirectionToText ToBottom = "to-bottom"
gradientDirectionToText ToLeft = "to-left"
gradientDirectionToText ToRight = "to-right"
gradientDirectionToText ToTopLeft = "to-top-left"
gradientDirectionToText ToTopRight = "to-top-right"
gradientDirectionToText ToBottomLeft = "to-bottom-left"
gradientDirectionToText ToBottomRight = "to-bottom-right"

-- | Convert gradient direction to CSS degrees.
gradientDirectionToDegrees :: GradientDirection -> Int
gradientDirectionToDegrees ToTop = 0
gradientDirectionToDegrees ToBottom = 180
gradientDirectionToDegrees ToLeft = 270
gradientDirectionToDegrees ToRight = 90
gradientDirectionToDegrees ToTopLeft = 315
gradientDirectionToDegrees ToTopRight = 45
gradientDirectionToDegrees ToBottomLeft = 225
gradientDirectionToDegrees ToBottomRight = 135

-- | Parse gradient direction from text.
parseGradientDirection :: Text -> Maybe GradientDirection
parseGradientDirection s = case T.toLower s of
  "to-top"          -> Just ToTop
  "to top"          -> Just ToTop
  "0deg"            -> Just ToTop
  "to-bottom"       -> Just ToBottom
  "to bottom"       -> Just ToBottom
  "180deg"          -> Just ToBottom
  "to-left"         -> Just ToLeft
  "to left"         -> Just ToLeft
  "270deg"          -> Just ToLeft
  "to-right"        -> Just ToRight
  "to right"        -> Just ToRight
  "90deg"           -> Just ToRight
  "to-top-left"     -> Just ToTopLeft
  "to top left"     -> Just ToTopLeft
  "315deg"          -> Just ToTopLeft
  "to-top-right"    -> Just ToTopRight
  "to top right"    -> Just ToTopRight
  "45deg"           -> Just ToTopRight
  "to-bottom-left"  -> Just ToBottomLeft
  "to bottom left"  -> Just ToBottomLeft
  "225deg"          -> Just ToBottomLeft
  "to-bottom-right" -> Just ToBottomRight
  "to bottom right" -> Just ToBottomRight
  "135deg"          -> Just ToBottomRight
  _                 -> Nothing

-- | Context where gradient rules differ.
data GradientExceptionContext
  = UIButtons      -- ^ Buttons use reversed gradient
  | UIIcons        -- ^ Icons use reversed gradient
  | UICards        -- ^ Cards may have different direction
  | Backgrounds    -- ^ Background gradients
  | Overlays       -- ^ Overlay effects
  deriving stock (Eq, Ord, Show)

-- | Convert exception context to text.
exceptionContextToText :: GradientExceptionContext -> Text
exceptionContextToText UIButtons = "ui-buttons"
exceptionContextToText UIIcons = "ui-icons"
exceptionContextToText UICards = "ui-cards"
exceptionContextToText Backgrounds = "backgrounds"
exceptionContextToText Overlays = "overlays"

-- | Parse exception context from text.
parseExceptionContext :: Text -> Maybe GradientExceptionContext
parseExceptionContext s = case T.toLower s of
  "ui-buttons"  -> Just UIButtons
  "buttons"     -> Just UIButtons
  "ui-icons"    -> Just UIIcons
  "icons"       -> Just UIIcons
  "ui-cards"    -> Just UICards
  "cards"       -> Just UICards
  "backgrounds" -> Just Backgrounds
  "background"  -> Just Backgrounds
  "overlays"    -> Just Overlays
  "overlay"     -> Just Overlays
  _             -> Nothing

-- | A gradient exception rule.
data GradientException = GradientException
  { exceptionContext   :: !GradientExceptionContext  -- ^ Context for this exception
  , exceptionDirection :: !GradientDirection         -- ^ Override direction
  , exceptionNotes     :: !Text                      -- ^ Explanation
  }
  deriving stock (Eq, Show)

-- | Create gradient exception (always succeeds, no validation needed).
mkGradientException
  :: GradientExceptionContext
  -> GradientDirection
  -> Text
  -> GradientException
mkGradientException ctx dir notes = GradientException
  { exceptionContext = ctx
  , exceptionDirection = dir
  , exceptionNotes = notes
  }

-- | Type of gradient error.
data GradientErrorType
  = TintCombination        -- ^ Combining tints incorrectly
  | OpacityReduction       -- ^ Lowering gradient opacity
  | UnapprovedGradient     -- ^ Using non-approved gradient
  | EdgeTreatment          -- ^ Adding vignettes, glows to edges
  | DirectionReversal      -- ^ Reversing direction incorrectly
  | UnapprovedAngle        -- ^ Using non-approved angle
  | MultipleColors         -- ^ Using more than two stops
  | InsufficientContrast   -- ^ Contrast ratio too low
  deriving stock (Eq, Ord, Show)

-- | Convert gradient error type to text.
gradientErrorTypeToText :: GradientErrorType -> Text
gradientErrorTypeToText TintCombination = "tint-combination"
gradientErrorTypeToText OpacityReduction = "opacity-reduction"
gradientErrorTypeToText UnapprovedGradient = "unapproved-gradient"
gradientErrorTypeToText EdgeTreatment = "edge-treatment"
gradientErrorTypeToText DirectionReversal = "direction-reversal"
gradientErrorTypeToText UnapprovedAngle = "unapproved-angle"
gradientErrorTypeToText MultipleColors = "multiple-colors"
gradientErrorTypeToText InsufficientContrast = "insufficient-contrast"

-- | A gradient error (DO NOT rule).
data GradientError = GradientError
  { gradientErrorType        :: !GradientErrorType  -- ^ Type of error
  , gradientErrorDescription :: !Text               -- ^ What not to do
  }
  deriving stock (Eq, Show)

-- | Create gradient error with validation.
mkGradientError :: GradientErrorType -> Text -> Maybe GradientError
mkGradientError errType desc
  | T.length desc >= 1 = Just GradientError
      { gradientErrorType = errType
      , gradientErrorDescription = desc
      }
  | otherwise = Nothing
