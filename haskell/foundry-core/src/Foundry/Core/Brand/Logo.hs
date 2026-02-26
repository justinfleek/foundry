{- |
Module      : Foundry.Core.Brand.Logo
Description : SMART Framework Logo Layer
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Logo components, lockups, clear space, minimum sizing, usage rules, and errors.
Mirrors Hydrogen.Schema.Brand.Logo from PureScript.

SMART FRAMEWORK:
  S - Story-driven: Icon symbolism connects to brand values/mission
  M - Memorable: Lockups define recognizable arrangements
  A - Agile: Multiple lockups for different contexts
  R - Responsive: Minimum sizing ensures legibility
  T - Targeted: Clear space rules prevent cluttered presentation

DEPENDENCIES:
  - Foundry.Core.Brand.Logo.Sizing
  - Foundry.Core.Brand.Logo.Usage

DEPENDENTS:
  - Foundry.Core.Brand (compound Brand type)
-}
module Foundry.Core.Brand.Logo
  ( -- * Logo Components
    LogoComponent (..)
  , logoComponentToText
  
  , LogoIcon (..)
  , mkLogoIcon
  
  , LogoWordmark (..)
  , mkLogoWordmark
  
    -- * Lockup Orientation
  , LockupOrientation (..)
  , orientationToText
  , parseOrientation
  
    -- * Color Variant
  , ColorVariant (..)
  , colorVariantToText
  , parseColorVariant
  
    -- * Logo Lockup
  , LogoLockup (..)
  , mkLogoLockup
  
    -- * Re-exports from Logo.Sizing
  , module Foundry.Core.Brand.Logo.Sizing
  
    -- * Re-exports from Logo.Usage
  , module Foundry.Core.Brand.Logo.Usage
  
    -- * Complete Logo Specification
  , LogoSpecification (..)
  , mkLogoSpecification
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V

import Foundry.Core.Brand.Logo.Sizing
  ( ClearSpaceRule (..)
  , mkClearSpaceRule
  , MinimumSize (..)
  , mkMinimumSize
  , LockupSizing (..)
  , mkLockupSizing
  )

import Foundry.Core.Brand.Logo.Usage
  ( UsageContext (..)
  , usageContextToText
  , parseUsageContext
  , LogoUsageRule (..)
  , mkLogoUsageRule
  , LogoErrorCategory (..)
  , errorCategoryToText
  , LogoError (..)
  , mkLogoError
  )

-- | Type of logo component.
data LogoComponent
  = IconComponent       -- ^ Symbol/icon element
  | WordmarkComponent   -- ^ Typographic brand name
  | TaglineComponent    -- ^ Optional tagline element
  deriving stock (Eq, Ord, Show)

-- | Convert logo component to text.
logoComponentToText :: LogoComponent -> Text
logoComponentToText IconComponent = "icon"
logoComponentToText WordmarkComponent = "wordmark"
logoComponentToText TaglineComponent = "tagline"

-- | Logo icon/symbol element.
data LogoIcon = LogoIcon
  { iconDescription :: !Text  -- ^ Visual description of the icon
  , iconSymbolism   :: !Text  -- ^ Narrative meaning behind the icon
  }
  deriving stock (Eq, Show)

-- | Create logo icon with validation.
mkLogoIcon :: Text -> Text -> Maybe LogoIcon
mkLogoIcon desc symbolism
  | T.length desc >= 1 && T.length symbolism >= 1 =
      Just LogoIcon
        { iconDescription = desc
        , iconSymbolism = symbolism
        }
  | otherwise = Nothing

-- | Logo wordmark (typographic brand name).
data LogoWordmark = LogoWordmark
  { wordmarkText       :: !Text  -- ^ The brand name text
  , wordmarkTypography :: !Text  -- ^ Typography treatment description
  }
  deriving stock (Eq, Show)

-- | Create logo wordmark with validation.
mkLogoWordmark :: Text -> Text -> Maybe LogoWordmark
mkLogoWordmark text typo
  | T.length text >= 1 && T.length typo >= 1 =
      Just LogoWordmark
        { wordmarkText = text
        , wordmarkTypography = typo
        }
  | otherwise = Nothing

-- | Lockup orientation.
data LockupOrientation
  = Horizontal  -- ^ Side by side
  | Vertical    -- ^ Stacked vertically
  | Square      -- ^ Square proportion
  | Stacked     -- ^ Multi-row arrangement
  deriving stock (Eq, Ord, Show)

-- | Convert orientation to text.
orientationToText :: LockupOrientation -> Text
orientationToText Horizontal = "horizontal"
orientationToText Vertical = "vertical"
orientationToText Square = "square"
orientationToText Stacked = "stacked"

-- | Parse orientation from text.
parseOrientation :: Text -> Maybe LockupOrientation
parseOrientation s = case T.toLower s of
  "horizontal" -> Just Horizontal
  "vertical"   -> Just Vertical
  "square"     -> Just Square
  "stacked"    -> Just Stacked
  _            -> Nothing

-- | Color variant for logo lockups.
data ColorVariant
  = FullColor    -- ^ Full brand colors
  | BlackWhite   -- ^ Pure black and white
  | Reversed     -- ^ Inverted for dark backgrounds
  | Monochrome   -- ^ Single brand color
  | Grayscale    -- ^ Grayscale rendering
  deriving stock (Eq, Ord, Show)

-- | Convert color variant to text.
colorVariantToText :: ColorVariant -> Text
colorVariantToText FullColor = "full-color"
colorVariantToText BlackWhite = "black-white"
colorVariantToText Reversed = "reversed"
colorVariantToText Monochrome = "monochrome"
colorVariantToText Grayscale = "grayscale"

-- | Parse color variant from text.
parseColorVariant :: Text -> Maybe ColorVariant
parseColorVariant s = case T.toLower s of
  "full-color"      -> Just FullColor
  "full color"      -> Just FullColor
  "color"           -> Just FullColor
  "black-white"     -> Just BlackWhite
  "black and white" -> Just BlackWhite
  "bw"              -> Just BlackWhite
  "reversed"        -> Just Reversed
  "reverse"         -> Just Reversed
  "inverted"        -> Just Reversed
  "monochrome"      -> Just Monochrome
  "mono"            -> Just Monochrome
  "grayscale"       -> Just Grayscale
  "greyscale"       -> Just Grayscale
  "gray"            -> Just Grayscale
  _                 -> Nothing

-- | A logo lockup defines an approved arrangement of logo components.
data LogoLockup = LogoLockup
  { lockupName                :: !Text                    -- ^ e.g., "Primary", "Horizontal"
  , lockupComponents          :: !(Vector LogoComponent)  -- ^ Which components are included
  , lockupOrientation         :: !LockupOrientation       -- ^ Arrangement
  , lockupUseCases            :: !(Vector Text)           -- ^ e.g., "letterheads", "email signatures"
  , lockupColorVariants       :: !(Vector ColorVariant)   -- ^ Available color treatments
  , lockupApprovedBackgrounds :: !(Vector Text)           -- ^ Approved background colors (hex)
  }
  deriving stock (Eq, Show)

-- | Create logo lockup with validation.
mkLogoLockup
  :: Text                    -- ^ Name
  -> Vector LogoComponent    -- ^ Components
  -> LockupOrientation       -- ^ Orientation
  -> Vector Text             -- ^ Use cases
  -> Vector ColorVariant     -- ^ Color variants
  -> Vector Text             -- ^ Approved backgrounds
  -> Maybe LogoLockup
mkLogoLockup name comps orient uses variants backgrounds
  | T.length name >= 1 && V.length comps >= 1 =
      Just LogoLockup
        { lockupName = name
        , lockupComponents = comps
        , lockupOrientation = orient
        , lockupUseCases = uses
        , lockupColorVariants = variants
        , lockupApprovedBackgrounds = backgrounds
        }
  | otherwise = Nothing

-- | Complete logo specification for a brand.
data LogoSpecification = LogoSpecification
  { logoIcon       :: !LogoIcon                 -- ^ Icon/symbol
  , logoWordmark   :: !LogoWordmark             -- ^ Wordmark
  , logoLockups    :: !(Vector LogoLockup)      -- ^ Approved lockups
  , logoClearSpace :: !ClearSpaceRule           -- ^ Clear space requirements
  , logoSizing     :: !(Vector LockupSizing)    -- ^ Sizing rules per lockup
  , logoUsageRules :: !(Vector LogoUsageRule)   -- ^ Usage rules per context
  , logoErrors     :: !(Vector LogoError)       -- ^ DO NOT rules
  }
  deriving stock (Eq, Show)

-- | Create logo specification with validation.
mkLogoSpecification
  :: LogoIcon
  -> LogoWordmark
  -> Vector LogoLockup
  -> ClearSpaceRule
  -> Vector LockupSizing
  -> Vector LogoUsageRule
  -> Vector LogoError
  -> Maybe LogoSpecification
mkLogoSpecification icon wm lockups cs sizing rules errors
  | V.length lockups >= 1 =
      Just LogoSpecification
        { logoIcon = icon
        , logoWordmark = wm
        , logoLockups = lockups
        , logoClearSpace = cs
        , logoSizing = sizing
        , logoUsageRules = rules
        , logoErrors = errors
        }
  | otherwise = Nothing
