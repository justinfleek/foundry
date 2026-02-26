{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // foundry // core // brand // theme
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Theme
Description : Theme mode definitions (light/dark/contrast)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines theme modes and their associated token configurations for
supporting light mode, dark mode, high contrast, and custom themes.

== SMART Brand Framework Section

This module implements theming support for brand applications,
ensuring consistent appearance across different viewing contexts.

== Dependencies

Requires: vector, text, aeson
Required by: Foundry.Core.Brand.Complete

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Theme
  ( -- * Theme Mode
    ThemeMode (..)
  , themeModeToText
  , textToThemeMode

    -- * Theme Preference
  , ThemePreference (..)
  , preferenceToMode

    -- * Color Adaptation
  , ColorAdaptation (..)
  , mkColorAdaptation

    -- * Theme Definition
  , ThemeName (..)
  , mkThemeName
  , themeNameToText
  , ThemeDescription (..)
  , mkThemeDescription
  , Theme (..)
  , mkTheme

    -- * Theme Set
  , ThemeSet (..)
  , mkThemeSet
  , getTheme
  , allThemes
  ) where

import Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, withText, (.:), (.:?), (.=))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V
import GHC.Generics (Generic)

import Foundry.Core.Brand.Palette (OKLCH)

--------------------------------------------------------------------------------
-- Theme Mode
--------------------------------------------------------------------------------

-- | Available theme modes
data ThemeMode
  = ThemeModeLight
    -- ^ Standard light theme
  | ThemeModeDark
    -- ^ Dark theme for low-light environments
  | ThemeModeContrast
    -- ^ High contrast for accessibility
  | ThemeModeAuto
    -- ^ Follow system preference
  | ThemeModeCustom !Text
    -- ^ Custom named theme
  deriving stock (Eq, Ord, Show, Generic)

instance ToJSON ThemeMode where
  toJSON ThemeModeLight = "light"
  toJSON ThemeModeDark = "dark"
  toJSON ThemeModeContrast = "contrast"
  toJSON ThemeModeAuto = "auto"
  toJSON (ThemeModeCustom name) = toJSON $ "custom:" <> name

instance FromJSON ThemeMode where
  parseJSON = withText "ThemeMode" $ \t ->
    pure $ textToThemeMode t

-- | Convert theme mode to text
themeModeToText :: ThemeMode -> Text
themeModeToText ThemeModeLight = "light"
themeModeToText ThemeModeDark = "dark"
themeModeToText ThemeModeContrast = "contrast"
themeModeToText ThemeModeAuto = "auto"
themeModeToText (ThemeModeCustom name) = "custom:" <> name

-- | Parse theme mode from text
textToThemeMode :: Text -> ThemeMode
textToThemeMode "light" = ThemeModeLight
textToThemeMode "dark" = ThemeModeDark
textToThemeMode "contrast" = ThemeModeContrast
textToThemeMode "auto" = ThemeModeAuto
textToThemeMode t
  | "custom:" `T.isPrefixOf` t = ThemeModeCustom (T.drop 7 t)
  | otherwise = ThemeModeCustom t

--------------------------------------------------------------------------------
-- Theme Preference
--------------------------------------------------------------------------------

-- | User's theme preference
data ThemePreference
  = PreferLight
    -- ^ Always use light theme
  | PreferDark
    -- ^ Always use dark theme
  | PreferSystem
    -- ^ Follow OS/browser preference
  | PreferContrast
    -- ^ Always use high contrast
  deriving stock (Eq, Show, Generic)

instance ToJSON ThemePreference where
  toJSON PreferLight = "light"
  toJSON PreferDark = "dark"
  toJSON PreferSystem = "system"
  toJSON PreferContrast = "contrast"

instance FromJSON ThemePreference where
  parseJSON = withText "ThemePreference" $ \case
    "light" -> pure PreferLight
    "dark" -> pure PreferDark
    "system" -> pure PreferSystem
    "contrast" -> pure PreferContrast
    _ -> pure PreferSystem

-- | Resolve preference to concrete mode (for non-system)
preferenceToMode :: ThemePreference -> Maybe ThemeMode
preferenceToMode PreferLight = Just ThemeModeLight
preferenceToMode PreferDark = Just ThemeModeDark
preferenceToMode PreferContrast = Just ThemeModeContrast
preferenceToMode PreferSystem = Nothing

--------------------------------------------------------------------------------
-- Color Adaptation
--------------------------------------------------------------------------------

-- | How colors adapt between themes
data ColorAdaptation = ColorAdaptation
  { caLightColor :: !OKLCH
    -- ^ Color in light mode
  , caDarkColor  :: !OKLCH
    -- ^ Color in dark mode
  , caContrast   :: !(Maybe OKLCH)
    -- ^ Optional high-contrast override
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ColorAdaptation where
  toJSON ColorAdaptation{..} = object
    [ "light"    .= caLightColor
    , "dark"     .= caDarkColor
    , "contrast" .= caContrast
    ]

instance FromJSON ColorAdaptation where
  parseJSON = withObject "ColorAdaptation" $ \v -> ColorAdaptation
    <$> v .: "light"
    <*> v .: "dark"
    <*> v .:? "contrast"

-- | Smart constructor
mkColorAdaptation :: OKLCH -> OKLCH -> Maybe OKLCH -> ColorAdaptation
mkColorAdaptation = ColorAdaptation

--------------------------------------------------------------------------------
-- Theme Definition
--------------------------------------------------------------------------------

-- | Theme name
newtype ThemeName = ThemeName Text
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor
mkThemeName :: Text -> Maybe ThemeName
mkThemeName t
  | T.null (T.strip t) = Nothing
  | otherwise = Just $ ThemeName (T.strip t)

-- | Extract text
themeNameToText :: ThemeName -> Text
themeNameToText (ThemeName t) = t

-- | Theme description
newtype ThemeDescription = ThemeDescription Text
  deriving stock (Eq, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor
mkThemeDescription :: Text -> ThemeDescription
mkThemeDescription = ThemeDescription . T.strip

-- | A complete theme definition
data Theme = Theme
  { themeName        :: !ThemeName
    -- ^ Unique theme name
  , themeDescription :: !ThemeDescription
    -- ^ Human-readable description
  , themeMode        :: !ThemeMode
    -- ^ Which mode this theme represents
  , themeBackground  :: !OKLCH
    -- ^ Primary background color
  , themeForeground  :: !OKLCH
    -- ^ Primary text color
  , themeAccent      :: !OKLCH
    -- ^ Accent/brand color for this theme
  , themeMuted       :: !OKLCH
    -- ^ Muted/secondary text color
  , themeBorder      :: !OKLCH
    -- ^ Default border color
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON Theme where
  toJSON Theme{..} = object
    [ "name"        .= themeName
    , "description" .= themeDescription
    , "mode"        .= themeMode
    , "background"  .= themeBackground
    , "foreground"  .= themeForeground
    , "accent"      .= themeAccent
    , "muted"       .= themeMuted
    , "border"      .= themeBorder
    ]

instance FromJSON Theme where
  parseJSON = withObject "Theme" $ \v -> Theme
    <$> v .: "name"
    <*> v .: "description"
    <*> v .: "mode"
    <*> v .: "background"
    <*> v .: "foreground"
    <*> v .: "accent"
    <*> v .: "muted"
    <*> v .: "border"

-- | Smart constructor
mkTheme 
  :: ThemeName 
  -> ThemeDescription 
  -> ThemeMode 
  -> OKLCH  -- ^ background
  -> OKLCH  -- ^ foreground
  -> OKLCH  -- ^ accent
  -> OKLCH  -- ^ muted
  -> OKLCH  -- ^ border
  -> Theme
mkTheme = Theme

--------------------------------------------------------------------------------
-- Theme Set
--------------------------------------------------------------------------------

-- | Complete set of themes for a brand
data ThemeSet = ThemeSet
  { tsLight    :: !Theme
    -- ^ Light mode theme (required)
  , tsDark     :: !Theme
    -- ^ Dark mode theme (required)
  , tsContrast :: !(Maybe Theme)
    -- ^ High contrast theme (optional)
  , tsCustom   :: !(Vector Theme)
    -- ^ Additional custom themes
  , tsDefault  :: !ThemeMode
    -- ^ Default theme mode
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ThemeSet where
  toJSON ThemeSet{..} = object
    [ "light"    .= tsLight
    , "dark"     .= tsDark
    , "contrast" .= tsContrast
    , "custom"   .= tsCustom
    , "default"  .= tsDefault
    ]

instance FromJSON ThemeSet where
  parseJSON = withObject "ThemeSet" $ \v -> ThemeSet
    <$> v .: "light"
    <*> v .: "dark"
    <*> v .:? "contrast"
    <*> v .: "custom"
    <*> v .: "default"

-- | Smart constructor
mkThemeSet :: Theme -> Theme -> Maybe Theme -> Vector Theme -> ThemeMode -> ThemeSet
mkThemeSet = ThemeSet

-- | Get theme by mode
getTheme :: ThemeSet -> ThemeMode -> Maybe Theme
getTheme ts ThemeModeLight = Just $ tsLight ts
getTheme ts ThemeModeDark = Just $ tsDark ts
getTheme ts ThemeModeContrast = tsContrast ts
getTheme ts ThemeModeAuto = Just $ tsLight ts  -- Default to light
getTheme ts (ThemeModeCustom name) = 
  V.find (\t -> themeNameToText (themeName t) == name) (tsCustom ts)

-- | Get all themes as a vector
allThemes :: ThemeSet -> Vector Theme
allThemes ts = 
  V.singleton (tsLight ts) 
  <> V.singleton (tsDark ts) 
  <> maybe V.empty V.singleton (tsContrast ts)
  <> tsCustom ts
