{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                     // foundry // core // brand // uielements // buttons
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.UIElements.Buttons
Description : Button specifications: states, variants, elevation specs
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines button-related types including elevation levels, button states,
button variants, and complete button specifications.

== SMART Brand Framework Section

Buttons are the primary interactive components that express brand personality
through visual treatment (neumorphic, flat, material, etc.)

== Dependencies

Requires: text, aeson
Required by: Foundry.Core.Brand.UIElements

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.UIElements.Buttons
  ( -- * Elevation Level
    ElevationLevel (..)
  , elevationLevelToText
  , parseElevationLevel

    -- * Elevation Spec
  , ElevationSpec (..)
  , mkElevationSpec

    -- * Button State
  , ButtonState (..)
  , buttonStateToText
  , parseButtonState

    -- * Button Variant
  , ButtonVariant (..)
  , buttonVariantToText
  , parseButtonVariant

    -- * Button Specification
  , ButtonSpec (..)
  , mkButtonSpec
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
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Elevation Level
--------------------------------------------------------------------------------

-- | Elevation level for depth perception.
data ElevationLevel
  = ElevationFlat       -- ^ No elevation (0dp)
  | ElevationRaised     -- ^ Slight elevation (2-4dp)
  | ElevationFloating   -- ^ Moderate elevation (6-8dp)
  | ElevationOverlay    -- ^ High elevation (12-24dp)
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

-- | Convert elevation level to text.
elevationLevelToText :: ElevationLevel -> Text
elevationLevelToText ElevationFlat     = "flat"
elevationLevelToText ElevationRaised   = "raised"
elevationLevelToText ElevationFloating = "floating"
elevationLevelToText ElevationOverlay  = "overlay"

-- | Parse elevation level from text.
parseElevationLevel :: Text -> Maybe ElevationLevel
parseElevationLevel t = case T.toLower t of
  "flat"     -> Just ElevationFlat
  "none"     -> Just ElevationFlat
  "0"        -> Just ElevationFlat
  "raised"   -> Just ElevationRaised
  "low"      -> Just ElevationRaised
  "floating" -> Just ElevationFloating
  "medium"   -> Just ElevationFloating
  "overlay"  -> Just ElevationOverlay
  "high"     -> Just ElevationOverlay
  _          -> Nothing

instance ToJSON ElevationLevel where
  toJSON = toJSON . elevationLevelToText

instance FromJSON ElevationLevel where
  parseJSON = withText "ElevationLevel" $ \t ->
    case parseElevationLevel t of
      Just lvl -> pure lvl
      Nothing  -> fail $ "Invalid elevation level: " <> T.unpack t

--------------------------------------------------------------------------------
-- Elevation Spec
--------------------------------------------------------------------------------

-- | Elevation specification with shadow values.
data ElevationSpec = ElevationSpec
  { esLevel        :: !ElevationLevel
    -- ^ The elevation level
  , esShadowBlur   :: !Double
    -- ^ Shadow blur radius in pixels
  , esShadowOffset :: !Double
    -- ^ Shadow Y offset in pixels
  }
  deriving stock (Eq, Show, Generic)

-- | Create elevation spec with validation.
mkElevationSpec :: ElevationLevel -> Double -> Double -> Maybe ElevationSpec
mkElevationSpec level blur offset
  | blur >= 0 = Just ElevationSpec
      { esLevel        = level
      , esShadowBlur   = blur
      , esShadowOffset = offset
      }
  | otherwise = Nothing

instance ToJSON ElevationSpec where
  toJSON ElevationSpec{..} = object
    [ "level"        .= esLevel
    , "shadowBlur"   .= esShadowBlur
    , "shadowOffset" .= esShadowOffset
    ]

instance FromJSON ElevationSpec where
  parseJSON = withObject "ElevationSpec" $ \o -> do
    esLevel        <- o .: "level"
    esShadowBlur   <- o .: "shadowBlur"
    esShadowOffset <- o .: "shadowOffset"
    pure ElevationSpec{..}

--------------------------------------------------------------------------------
-- Button State
--------------------------------------------------------------------------------

-- | Button interaction state.
data ButtonState
  = ButtonDefault   -- ^ Normal resting state
  | ButtonHover     -- ^ Mouse hover state
  | ButtonActive    -- ^ Being pressed
  | ButtonFocused   -- ^ Keyboard focus
  | ButtonDisabled  -- ^ Disabled/inactive
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

-- | Convert button state to text.
buttonStateToText :: ButtonState -> Text
buttonStateToText ButtonDefault  = "default"
buttonStateToText ButtonHover    = "hover"
buttonStateToText ButtonActive   = "active"
buttonStateToText ButtonFocused  = "focused"
buttonStateToText ButtonDisabled = "disabled"

-- | Parse button state from text.
parseButtonState :: Text -> Maybe ButtonState
parseButtonState t = case T.toLower t of
  "default"  -> Just ButtonDefault
  "normal"   -> Just ButtonDefault
  "hover"    -> Just ButtonHover
  "active"   -> Just ButtonActive
  "pressed"  -> Just ButtonActive
  "focused"  -> Just ButtonFocused
  "focus"    -> Just ButtonFocused
  "disabled" -> Just ButtonDisabled
  "inactive" -> Just ButtonDisabled
  _          -> Nothing

instance ToJSON ButtonState where
  toJSON = toJSON . buttonStateToText

instance FromJSON ButtonState where
  parseJSON = withText "ButtonState" $ \t ->
    case parseButtonState t of
      Just st -> pure st
      Nothing -> fail $ "Invalid button state: " <> T.unpack t

--------------------------------------------------------------------------------
-- Button Variant
--------------------------------------------------------------------------------

-- | Button variant type.
data ButtonVariant
  = ButtonPrimary      -- ^ Main CTA button
  | ButtonSecondary    -- ^ Secondary action button
  | ButtonTertiary     -- ^ Tertiary/low-emphasis button
  | ButtonGhost        -- ^ Text-only, no background
  | ButtonDestructive  -- ^ Destructive action (delete, etc.)
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

-- | Convert button variant to text.
buttonVariantToText :: ButtonVariant -> Text
buttonVariantToText ButtonPrimary     = "primary"
buttonVariantToText ButtonSecondary   = "secondary"
buttonVariantToText ButtonTertiary    = "tertiary"
buttonVariantToText ButtonGhost       = "ghost"
buttonVariantToText ButtonDestructive = "destructive"

-- | Parse button variant from text.
parseButtonVariant :: Text -> Maybe ButtonVariant
parseButtonVariant t = case T.toLower t of
  "primary"     -> Just ButtonPrimary
  "cta"         -> Just ButtonPrimary
  "secondary"   -> Just ButtonSecondary
  "tertiary"    -> Just ButtonTertiary
  "ghost"       -> Just ButtonGhost
  "text"        -> Just ButtonGhost
  "destructive" -> Just ButtonDestructive
  "danger"      -> Just ButtonDestructive
  "delete"      -> Just ButtonDestructive
  _             -> Nothing

instance ToJSON ButtonVariant where
  toJSON = toJSON . buttonVariantToText

instance FromJSON ButtonVariant where
  parseJSON = withText "ButtonVariant" $ \t ->
    case parseButtonVariant t of
      Just v  -> pure v
      Nothing -> fail $ "Invalid button variant: " <> T.unpack t

--------------------------------------------------------------------------------
-- Button Specification
--------------------------------------------------------------------------------

-- | Complete button specification.
data ButtonSpec = ButtonSpec
  { bsVariant         :: !ButtonVariant
    -- ^ The button variant (primary, secondary, etc.)
  , bsElevation       :: !ElevationSpec
    -- ^ Elevation/shadow specification
  , bsBorderRadius    :: !Double
    -- ^ Border radius in pixels
  , bsPaddingH        :: !Double
    -- ^ Horizontal padding in pixels
  , bsPaddingV        :: !Double
    -- ^ Vertical padding in pixels
  , bsBackgroundColor :: !Text
    -- ^ Background color (hex)
  , bsTextColor       :: !Text
    -- ^ Text color (hex)
  }
  deriving stock (Eq, Show, Generic)

-- | Create button spec with validation.
mkButtonSpec
  :: ButtonVariant
  -> ElevationSpec
  -> Double          -- ^ Border radius
  -> Double          -- ^ Horizontal padding
  -> Double          -- ^ Vertical padding
  -> Text            -- ^ Background color
  -> Text            -- ^ Text color
  -> Maybe ButtonSpec
mkButtonSpec variant elev radius padH padV bgColor txtColor
  | radius >= 0
  , padH >= 0
  , padV >= 0
  , T.length bgColor >= 4
  , T.length txtColor >= 4
  = Just ButtonSpec
      { bsVariant         = variant
      , bsElevation       = elev
      , bsBorderRadius    = radius
      , bsPaddingH        = padH
      , bsPaddingV        = padV
      , bsBackgroundColor = bgColor
      , bsTextColor       = txtColor
      }
  | otherwise = Nothing

instance ToJSON ButtonSpec where
  toJSON ButtonSpec{..} = object
    [ "variant"         .= bsVariant
    , "elevation"       .= bsElevation
    , "borderRadius"    .= bsBorderRadius
    , "paddingH"        .= bsPaddingH
    , "paddingV"        .= bsPaddingV
    , "backgroundColor" .= bsBackgroundColor
    , "textColor"       .= bsTextColor
    ]

instance FromJSON ButtonSpec where
  parseJSON = withObject "ButtonSpec" $ \o -> do
    bsVariant         <- o .: "variant"
    bsElevation       <- o .: "elevation"
    bsBorderRadius    <- o .: "borderRadius"
    bsPaddingH        <- o .: "paddingH"
    bsPaddingV        <- o .: "paddingV"
    bsBackgroundColor <- o .: "backgroundColor"
    bsTextColor       <- o .: "textColor"
    pure ButtonSpec{..}
