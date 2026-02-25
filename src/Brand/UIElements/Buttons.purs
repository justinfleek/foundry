-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // brand // uielements // buttons
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Button specifications: states, variants, and button specs.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | DEPENDENCIES:
-- |   - None (foundational module)
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.UIElements (main UI elements module)

module Hydrogen.Schema.Brand.UIElements.Buttons
  ( -- * Elevation Level
    ElevationLevel
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
  
  -- * Button State
  , ButtonState
      ( ButtonDefault
      , ButtonHover
      , ButtonActive
      , ButtonFocused
      , ButtonDisabled
      )
  , buttonStateToString
  
  -- * Button Variant
  , ButtonVariant
      ( ButtonPrimary
      , ButtonSecondary
      , ButtonTertiary
      , ButtonGhost
      , ButtonDestructive
      )
  , buttonVariantToString
  
  -- * Button Specification
  , ButtonSpec
  , mkButtonSpec
  , buttonVariant
  , buttonElevation
  , buttonBorderRadius
  , buttonPaddingHorizontal
  , buttonPaddingVertical
  , buttonBackgroundColor
  , buttonTextColor
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>=)
  , (&&)
  , show
  , compare
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, toLower) as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // elevation level
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Elevation level for depth perception.
data ElevationLevel
  = ElevationFlat       -- No elevation (0dp)
  | ElevationRaised     -- Slight elevation (2-4dp)
  | ElevationFloating   -- Moderate elevation (6-8dp)
  | ElevationOverlay    -- High elevation (12-24dp)

derive instance eqElevationLevel :: Eq ElevationLevel

instance ordElevationLevel :: Ord ElevationLevel where
  compare e1 e2 = compare (elevToInt e1) (elevToInt e2)
    where
      elevToInt :: ElevationLevel -> Int
      elevToInt ElevationFlat = 0
      elevToInt ElevationRaised = 1
      elevToInt ElevationFloating = 2
      elevToInt ElevationOverlay = 3

instance showElevationLevel :: Show ElevationLevel where
  show = elevationLevelToString

-- | Convert elevation level to string.
elevationLevelToString :: ElevationLevel -> String
elevationLevelToString ElevationFlat = "flat"
elevationLevelToString ElevationRaised = "raised"
elevationLevelToString ElevationFloating = "floating"
elevationLevelToString ElevationOverlay = "overlay"

-- | Parse elevation level from string.
parseElevationLevel :: String -> Maybe ElevationLevel
parseElevationLevel s = case String.toLower s of
  "flat" -> Just ElevationFlat
  "none" -> Just ElevationFlat
  "0" -> Just ElevationFlat
  "raised" -> Just ElevationRaised
  "low" -> Just ElevationRaised
  "floating" -> Just ElevationFloating
  "medium" -> Just ElevationFloating
  "overlay" -> Just ElevationOverlay
  "high" -> Just ElevationOverlay
  _ -> Nothing

-- | Elevation specification with shadow values.
type ElevationSpec =
  { level :: ElevationLevel
  , shadowBlur :: Number        -- Shadow blur radius (px)
  , shadowOffset :: Number      -- Shadow Y offset (px)
  }

-- | Create elevation spec.
mkElevationSpec :: ElevationLevel -> Number -> Number -> Maybe ElevationSpec
mkElevationSpec level blur offset =
  if blur >= 0.0
    then Just { level: level, shadowBlur: blur, shadowOffset: offset }
    else Nothing

-- | Get elevation level.
elevationLevel :: ElevationSpec -> ElevationLevel
elevationLevel es = es.level

-- | Get shadow blur.
elevationShadowBlur :: ElevationSpec -> Number
elevationShadowBlur es = es.shadowBlur

-- | Get shadow offset.
elevationShadowOffset :: ElevationSpec -> Number
elevationShadowOffset es = es.shadowOffset

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // button state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Button interaction state.
data ButtonState
  = ButtonDefault
  | ButtonHover
  | ButtonActive
  | ButtonFocused
  | ButtonDisabled

derive instance eqButtonState :: Eq ButtonState

instance ordButtonState :: Ord ButtonState where
  compare s1 s2 = compare (stateToInt s1) (stateToInt s2)
    where
      stateToInt :: ButtonState -> Int
      stateToInt ButtonDefault = 0
      stateToInt ButtonHover = 1
      stateToInt ButtonActive = 2
      stateToInt ButtonFocused = 3
      stateToInt ButtonDisabled = 4

instance showButtonState :: Show ButtonState where
  show = buttonStateToString

-- | Convert button state to string.
buttonStateToString :: ButtonState -> String
buttonStateToString ButtonDefault = "default"
buttonStateToString ButtonHover = "hover"
buttonStateToString ButtonActive = "active"
buttonStateToString ButtonFocused = "focused"
buttonStateToString ButtonDisabled = "disabled"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // button variant
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Button variant type.
data ButtonVariant
  = ButtonPrimary       -- Main CTA
  | ButtonSecondary     -- Secondary action
  | ButtonTertiary      -- Tertiary/low-emphasis
  | ButtonGhost         -- Text-only, no background
  | ButtonDestructive   -- Destructive action (delete, etc.)

derive instance eqButtonVariant :: Eq ButtonVariant

instance ordButtonVariant :: Ord ButtonVariant where
  compare v1 v2 = compare (variantToInt v1) (variantToInt v2)
    where
      variantToInt :: ButtonVariant -> Int
      variantToInt ButtonPrimary = 0
      variantToInt ButtonSecondary = 1
      variantToInt ButtonTertiary = 2
      variantToInt ButtonGhost = 3
      variantToInt ButtonDestructive = 4

instance showButtonVariant :: Show ButtonVariant where
  show = buttonVariantToString

-- | Convert button variant to string.
buttonVariantToString :: ButtonVariant -> String
buttonVariantToString ButtonPrimary = "primary"
buttonVariantToString ButtonSecondary = "secondary"
buttonVariantToString ButtonTertiary = "tertiary"
buttonVariantToString ButtonGhost = "ghost"
buttonVariantToString ButtonDestructive = "destructive"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // button specification
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Button specification.
type ButtonSpec =
  { variant :: ButtonVariant
  , elevation :: ElevationSpec
  , borderRadius :: Number        -- Border radius (px)
  , paddingH :: Number            -- Horizontal padding
  , paddingV :: Number            -- Vertical padding
  , backgroundColor :: String     -- Hex color
  , textColor :: String           -- Hex color
  }

-- | Create button spec.
mkButtonSpec
  :: ButtonVariant
  -> ElevationSpec
  -> Number
  -> Number
  -> Number
  -> String
  -> String
  -> Maybe ButtonSpec
mkButtonSpec variant elev radius padH padV bgColor txtColor =
  if radius >= 0.0 
     && padH >= 0.0 
     && padV >= 0.0
     && String.length bgColor >= 4
     && String.length txtColor >= 4
    then Just
      { variant: variant
      , elevation: elev
      , borderRadius: radius
      , paddingH: padH
      , paddingV: padV
      , backgroundColor: bgColor
      , textColor: txtColor
      }
    else Nothing

-- | Get button variant.
buttonVariant :: ButtonSpec -> ButtonVariant
buttonVariant bs = bs.variant

-- | Get elevation.
buttonElevation :: ButtonSpec -> ElevationSpec
buttonElevation bs = bs.elevation

-- | Get border radius.
buttonBorderRadius :: ButtonSpec -> Number
buttonBorderRadius bs = bs.borderRadius

-- | Get horizontal padding.
buttonPaddingHorizontal :: ButtonSpec -> Number
buttonPaddingHorizontal bs = bs.paddingH

-- | Get vertical padding.
buttonPaddingVertical :: ButtonSpec -> Number
buttonPaddingVertical bs = bs.paddingV

-- | Get background color.
buttonBackgroundColor :: ButtonSpec -> String
buttonBackgroundColor bs = bs.backgroundColor

-- | Get text color.
buttonTextColor :: ButtonSpec -> String
buttonTextColor bs = bs.textColor
