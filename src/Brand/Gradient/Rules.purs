-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // brand // gradient // rules
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gradient exceptions, errors, and rules.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | DEPENDENCIES:
-- |   - None (foundational module)
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Gradient (main gradient module)

module Hydrogen.Schema.Brand.Gradient.Rules
  ( -- * Gradient Direction (re-export for rules)
    GradientDirection
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
  
  -- * Gradient Exception
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
  
  -- * Gradient Error
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
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>=)
  , show
  , compare
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, toLower) as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // gradient direction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Gradient direction.
data GradientDirection
  = ToTop           -- 0° (bottom to top)
  | ToBottom        -- 180° (top to bottom)
  | ToLeft          -- 270° (right to left)
  | ToRight         -- 90° (left to right)
  | ToTopLeft       -- 315° (bottom-right to top-left)
  | ToTopRight      -- 45° (bottom-left to top-right)
  | ToBottomLeft    -- 225° (top-right to bottom-left)
  | ToBottomRight   -- 135° (top-left to bottom-right)

derive instance eqGradientDirection :: Eq GradientDirection

instance ordGradientDirection :: Ord GradientDirection where
  compare d1 d2 = compare (dirToInt d1) (dirToInt d2)
    where
      dirToInt :: GradientDirection -> Int
      dirToInt ToTop = 0
      dirToInt ToBottom = 1
      dirToInt ToLeft = 2
      dirToInt ToRight = 3
      dirToInt ToTopLeft = 4
      dirToInt ToTopRight = 5
      dirToInt ToBottomLeft = 6
      dirToInt ToBottomRight = 7

instance showGradientDirection :: Show GradientDirection where
  show = gradientDirectionToString

-- | Convert gradient direction to string.
gradientDirectionToString :: GradientDirection -> String
gradientDirectionToString ToTop = "to-top"
gradientDirectionToString ToBottom = "to-bottom"
gradientDirectionToString ToLeft = "to-left"
gradientDirectionToString ToRight = "to-right"
gradientDirectionToString ToTopLeft = "to-top-left"
gradientDirectionToString ToTopRight = "to-top-right"
gradientDirectionToString ToBottomLeft = "to-bottom-left"
gradientDirectionToString ToBottomRight = "to-bottom-right"

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

-- | Parse gradient direction from string.
parseGradientDirection :: String -> Maybe GradientDirection
parseGradientDirection s = case String.toLower s of
  "to-top" -> Just ToTop
  "to top" -> Just ToTop
  "0deg" -> Just ToTop
  "to-bottom" -> Just ToBottom
  "to bottom" -> Just ToBottom
  "180deg" -> Just ToBottom
  "-90deg" -> Just ToBottom
  "to-left" -> Just ToLeft
  "to left" -> Just ToLeft
  "270deg" -> Just ToLeft
  "to-right" -> Just ToRight
  "to right" -> Just ToRight
  "90deg" -> Just ToRight
  "to-top-left" -> Just ToTopLeft
  "to top left" -> Just ToTopLeft
  "315deg" -> Just ToTopLeft
  "to-top-right" -> Just ToTopRight
  "to top right" -> Just ToTopRight
  "45deg" -> Just ToTopRight
  "to-bottom-left" -> Just ToBottomLeft
  "to bottom left" -> Just ToBottomLeft
  "225deg" -> Just ToBottomLeft
  "to-bottom-right" -> Just ToBottomRight
  "to bottom right" -> Just ToBottomRight
  "135deg" -> Just ToBottomRight
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // gradient exception
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Context where gradient rules differ.
data GradientExceptionContext
  = UIButtons      -- Buttons use reversed gradient
  | UIIcons        -- Icons use reversed gradient
  | UICards        -- Cards may have different direction
  | Backgrounds    -- Background gradients
  | Overlays       -- Overlay effects

derive instance eqGradientExceptionContext :: Eq GradientExceptionContext

instance ordGradientExceptionContext :: Ord GradientExceptionContext where
  compare e1 e2 = compare (excToInt e1) (excToInt e2)
    where
      excToInt :: GradientExceptionContext -> Int
      excToInt UIButtons = 0
      excToInt UIIcons = 1
      excToInt UICards = 2
      excToInt Backgrounds = 3
      excToInt Overlays = 4

instance showGradientExceptionContext :: Show GradientExceptionContext where
  show = exceptionContextToString

-- | Convert exception context to string.
exceptionContextToString :: GradientExceptionContext -> String
exceptionContextToString UIButtons = "ui-buttons"
exceptionContextToString UIIcons = "ui-icons"
exceptionContextToString UICards = "ui-cards"
exceptionContextToString Backgrounds = "backgrounds"
exceptionContextToString Overlays = "overlays"

-- | Parse exception context from string.
parseExceptionContext :: String -> Maybe GradientExceptionContext
parseExceptionContext s = case String.toLower s of
  "ui-buttons" -> Just UIButtons
  "buttons" -> Just UIButtons
  "ui-icons" -> Just UIIcons
  "icons" -> Just UIIcons
  "ui-cards" -> Just UICards
  "cards" -> Just UICards
  "backgrounds" -> Just Backgrounds
  "background" -> Just Backgrounds
  "overlays" -> Just Overlays
  "overlay" -> Just Overlays
  _ -> Nothing

-- | A gradient exception rule.
type GradientException =
  { context :: GradientExceptionContext
  , direction :: GradientDirection   -- Override direction for this context
  , notes :: String                  -- Explanation
  }

-- | Create gradient exception.
mkGradientException
  :: GradientExceptionContext
  -> GradientDirection
  -> String
  -> GradientException
mkGradientException ctx dir notes =
  { context: ctx
  , direction: dir
  , notes: notes
  }

-- | Get exception context.
exceptionContext :: GradientException -> GradientExceptionContext
exceptionContext ge = ge.context

-- | Get exception direction.
exceptionDirection :: GradientException -> GradientDirection
exceptionDirection ge = ge.direction

-- | Get exception notes.
exceptionNotes :: GradientException -> String
exceptionNotes ge = ge.notes

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // gradient error
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Type of gradient error.
data GradientErrorType
  = TintCombination        -- Combining tints incorrectly
  | OpacityReduction       -- Lowering gradient opacity
  | UnapprovedGradient     -- Using non-approved gradient
  | EdgeTreatment          -- Adding vignettes, glows to edges
  | DirectionReversal      -- Reversing direction incorrectly
  | UnapprovedAngle        -- Using non-approved angle
  | MultipleColors         -- Using more than two stops
  | InsufficientContrast   -- Contrast ratio too low

derive instance eqGradientErrorType :: Eq GradientErrorType

instance ordGradientErrorType :: Ord GradientErrorType where
  compare t1 t2 = compare (typeToInt t1) (typeToInt t2)
    where
      typeToInt :: GradientErrorType -> Int
      typeToInt TintCombination = 0
      typeToInt OpacityReduction = 1
      typeToInt UnapprovedGradient = 2
      typeToInt EdgeTreatment = 3
      typeToInt DirectionReversal = 4
      typeToInt UnapprovedAngle = 5
      typeToInt MultipleColors = 6
      typeToInt InsufficientContrast = 7

instance showGradientErrorType :: Show GradientErrorType where
  show = gradientErrorTypeToString

-- | Convert gradient error type to string.
gradientErrorTypeToString :: GradientErrorType -> String
gradientErrorTypeToString TintCombination = "tint-combination"
gradientErrorTypeToString OpacityReduction = "opacity-reduction"
gradientErrorTypeToString UnapprovedGradient = "unapproved-gradient"
gradientErrorTypeToString EdgeTreatment = "edge-treatment"
gradientErrorTypeToString DirectionReversal = "direction-reversal"
gradientErrorTypeToString UnapprovedAngle = "unapproved-angle"
gradientErrorTypeToString MultipleColors = "multiple-colors"
gradientErrorTypeToString InsufficientContrast = "insufficient-contrast"

-- | A gradient error (DO NOT rule).
type GradientError =
  { errorType :: GradientErrorType
  , description :: String
  }

-- | Create gradient error.
mkGradientError :: GradientErrorType -> String -> Maybe GradientError
mkGradientError errType desc =
  if String.length desc >= 1
    then Just { errorType: errType, description: desc }
    else Nothing

-- | Get error type.
gradientErrorType :: GradientError -> GradientErrorType
gradientErrorType ge = ge.errorType

-- | Get error description.
gradientErrorDescription :: GradientError -> String
gradientErrorDescription ge = ge.description
