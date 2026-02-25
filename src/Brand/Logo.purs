-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // brand // logo
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SMART Framework Logo Layer: Logo components, lockups, clear space,
-- | minimum sizing, usage rules, and common errors.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | The logo is the primary visual identifier of the brand. This module
-- | captures its components, lockups, sizing constraints, and usage rules.
-- |
-- | SMART FRAMEWORK:
-- |   S - Story-driven: Icon symbolism connects to brand values/mission
-- |   M - Memorable: Lockups define recognizable arrangements
-- |   A - Agile: Multiple lockups for different contexts
-- |   R - Responsive: Minimum sizing ensures legibility
-- |   T - Targeted: Clear space rules prevent cluttered presentation
-- |
-- | DEPENDENCIES:
-- |   - Hydrogen.Schema.Brand.Logo.Usage
-- |   - Hydrogen.Schema.Brand.Logo.Sizing
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Brand (compound Brand type)

module Hydrogen.Schema.Brand.Logo
  ( -- * Logo Components
    LogoComponent
      ( IconComponent
      , WordmarkComponent
      , TaglineComponent
      )
  , logoComponentToString
  
  , LogoIcon
  , mkLogoIcon
  , iconDescription
  , iconSymbolism
  
  , LogoWordmark
  , mkLogoWordmark
  , wordmarkText
  , wordmarkTypography
  
  -- * Lockup Orientation
  , LockupOrientation
      ( Horizontal
      , Vertical
      , Square
      , Stacked
      )
  , orientationToString
  , parseOrientation
  
  -- * Color Variant
  , ColorVariant
      ( FullColor
      , BlackWhite
      , Reversed
      , Monochrome
      , Grayscale
      )
  , colorVariantToString
  , parseColorVariant
  
  -- * Logo Lockup
  , LogoLockup
  , mkLogoLockup
  , lockupName
  , lockupComponents
  , lockupOrientation
  , lockupUseCases
  , lockupColorVariants
  , lockupApprovedBackgrounds
  
  -- * Re-exports from Logo.Sizing
  , module Hydrogen.Schema.Brand.Logo.Sizing
  
  -- * Re-exports from Logo.Usage
  , module Hydrogen.Schema.Brand.Logo.Usage
  
  -- * Complete Logo Specification
  , LogoSpecification
  , mkLogoSpecification
  , logoIcon
  , logoWordmark
  , logoLockups
  , logoClearSpace
  , logoSizing
  , logoUsageRules
  , logoErrors
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>=)
  , (&&)
  , (<>)
  , show
  , compare
  )

import Data.Array (length) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, toLower) as String

import Hydrogen.Schema.Brand.Logo.Sizing
  ( ClearSpaceRule
  , mkClearSpaceRule
  , clearSpaceReference
  , clearSpaceMultiplier
  , clearSpaceDescription
  , MinimumSize
  , mkMinimumSize
  , minSizePrintInches
  , minSizeDigitalWidth
  , minSizeDigitalHeight
  , LockupSizing
  , mkLockupSizing
  , lockupSizingName
  , lockupSizingMinPrint
  , lockupSizingMinDigital
  )

import Hydrogen.Schema.Brand.Logo.Usage
  ( UsageContext
      ( UsageFirstPage
      , UsageSubsequentPages
      , UsageWatermark
      , UsageSocialMedia
      , UsageAppIcon
      , UsageEmail
      , UsageStationery
      )
  , usageContextToString
  , parseUsageContext
  , LogoUsageRule
  , mkLogoUsageRule
  , usageRuleContext
  , usageRuleLockup
  , usageRuleAlignment
  , usageRuleNotes
  , LogoErrorCategory
      ( ContrastError
      , ColorError
      , DistortionError
      , LayoutError
      )
  , errorCategoryToString
  , LogoError
  , mkLogoError
  , errorCategory
  , errorDescription
  , errorSeverity
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // logo components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Type of logo component.
data LogoComponent
  = IconComponent       -- Symbol/icon element
  | WordmarkComponent   -- Typographic brand name
  | TaglineComponent    -- Optional tagline element

derive instance eqLogoComponent :: Eq LogoComponent

instance ordLogoComponent :: Ord LogoComponent where
  compare c1 c2 = compare (compToInt c1) (compToInt c2)
    where
      compToInt :: LogoComponent -> Int
      compToInt IconComponent = 0
      compToInt WordmarkComponent = 1
      compToInt TaglineComponent = 2

instance showLogoComponent :: Show LogoComponent where
  show = logoComponentToString

-- | Convert logo component to string.
logoComponentToString :: LogoComponent -> String
logoComponentToString IconComponent = "icon"
logoComponentToString WordmarkComponent = "wordmark"
logoComponentToString TaglineComponent = "tagline"

-- | Logo icon/symbol element.
type LogoIcon =
  { description :: String   -- Visual description of the icon
  , symbolism :: String     -- Narrative meaning behind the icon
  }

-- | Create logo icon.
mkLogoIcon :: String -> String -> Maybe LogoIcon
mkLogoIcon desc symbolism =
  if String.length desc >= 1 && String.length symbolism >= 1
    then Just { description: desc, symbolism: symbolism }
    else Nothing

-- | Get icon description.
iconDescription :: LogoIcon -> String
iconDescription li = li.description

-- | Get icon symbolism.
iconSymbolism :: LogoIcon -> String
iconSymbolism li = li.symbolism

-- | Logo wordmark (typographic brand name).
type LogoWordmark =
  { text :: String           -- The brand name text
  , typography :: String     -- Typography treatment description
  }

-- | Create logo wordmark.
mkLogoWordmark :: String -> String -> Maybe LogoWordmark
mkLogoWordmark text typo =
  if String.length text >= 1 && String.length typo >= 1
    then Just { text: text, typography: typo }
    else Nothing

-- | Get wordmark text.
wordmarkText :: LogoWordmark -> String
wordmarkText lw = lw.text

-- | Get wordmark typography.
wordmarkTypography :: LogoWordmark -> String
wordmarkTypography lw = lw.typography

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // lockup orientation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Lockup orientation.
data LockupOrientation
  = Horizontal   -- Side by side
  | Vertical     -- Stacked vertically
  | Square       -- Square proportion
  | Stacked      -- Multi-row arrangement

derive instance eqLockupOrientation :: Eq LockupOrientation

instance ordLockupOrientation :: Ord LockupOrientation where
  compare o1 o2 = compare (orientToInt o1) (orientToInt o2)
    where
      orientToInt :: LockupOrientation -> Int
      orientToInt Horizontal = 0
      orientToInt Vertical = 1
      orientToInt Square = 2
      orientToInt Stacked = 3

instance showLockupOrientation :: Show LockupOrientation where
  show = orientationToString

-- | Convert orientation to string.
orientationToString :: LockupOrientation -> String
orientationToString Horizontal = "horizontal"
orientationToString Vertical = "vertical"
orientationToString Square = "square"
orientationToString Stacked = "stacked"

-- | Parse orientation from string.
parseOrientation :: String -> Maybe LockupOrientation
parseOrientation s = case String.toLower s of
  "horizontal" -> Just Horizontal
  "vertical" -> Just Vertical
  "square" -> Just Square
  "stacked" -> Just Stacked
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // color variant
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Color variant for logo lockups.
data ColorVariant
  = FullColor     -- Full brand colors
  | BlackWhite    -- Pure black and white
  | Reversed      -- Inverted for dark backgrounds
  | Monochrome    -- Single brand color
  | Grayscale     -- Grayscale rendering

derive instance eqColorVariant :: Eq ColorVariant

instance ordColorVariant :: Ord ColorVariant where
  compare v1 v2 = compare (variantToInt v1) (variantToInt v2)
    where
      variantToInt :: ColorVariant -> Int
      variantToInt FullColor = 0
      variantToInt BlackWhite = 1
      variantToInt Reversed = 2
      variantToInt Monochrome = 3
      variantToInt Grayscale = 4

instance showColorVariant :: Show ColorVariant where
  show = colorVariantToString

-- | Convert color variant to string.
colorVariantToString :: ColorVariant -> String
colorVariantToString FullColor = "full-color"
colorVariantToString BlackWhite = "black-white"
colorVariantToString Reversed = "reversed"
colorVariantToString Monochrome = "monochrome"
colorVariantToString Grayscale = "grayscale"

-- | Parse color variant from string.
parseColorVariant :: String -> Maybe ColorVariant
parseColorVariant s = case String.toLower s of
  "full-color" -> Just FullColor
  "full color" -> Just FullColor
  "color" -> Just FullColor
  "black-white" -> Just BlackWhite
  "black and white" -> Just BlackWhite
  "bw" -> Just BlackWhite
  "reversed" -> Just Reversed
  "reverse" -> Just Reversed
  "inverted" -> Just Reversed
  "monochrome" -> Just Monochrome
  "mono" -> Just Monochrome
  "grayscale" -> Just Grayscale
  "greyscale" -> Just Grayscale
  "gray" -> Just Grayscale
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // logo lockup
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A logo lockup defines an approved arrangement of logo components.
type LogoLockup =
  { name :: String                          -- e.g., "Primary", "Horizontal"
  , components :: Array LogoComponent       -- Which components are included
  , orientation :: LockupOrientation
  , useCases :: Array String                -- e.g., "letterheads", "email signatures"
  , colorVariants :: Array ColorVariant     -- Available color treatments
  , approvedBackgrounds :: Array String     -- Approved background colors (hex)
  }

-- | Create logo lockup.
mkLogoLockup
  :: String
  -> Array LogoComponent
  -> LockupOrientation
  -> Array String
  -> Array ColorVariant
  -> Array String
  -> Maybe LogoLockup
mkLogoLockup name comps orient uses variants backgrounds =
  if String.length name >= 1 && Array.length comps >= 1
    then Just
      { name: name
      , components: comps
      , orientation: orient
      , useCases: uses
      , colorVariants: variants
      , approvedBackgrounds: backgrounds
      }
    else Nothing

-- | Get lockup name.
lockupName :: LogoLockup -> String
lockupName ll = ll.name

-- | Get lockup components.
lockupComponents :: LogoLockup -> Array LogoComponent
lockupComponents ll = ll.components

-- | Get lockup orientation.
lockupOrientation :: LogoLockup -> LockupOrientation
lockupOrientation ll = ll.orientation

-- | Get lockup use cases.
lockupUseCases :: LogoLockup -> Array String
lockupUseCases ll = ll.useCases

-- | Get color variants.
lockupColorVariants :: LogoLockup -> Array ColorVariant
lockupColorVariants ll = ll.colorVariants

-- | Get approved backgrounds.
lockupApprovedBackgrounds :: LogoLockup -> Array String
lockupApprovedBackgrounds ll = ll.approvedBackgrounds

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // logo specification
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete logo specification for a brand.
type LogoSpecification =
  { icon :: LogoIcon
  , wordmark :: LogoWordmark
  , lockups :: Array LogoLockup
  , clearSpace :: ClearSpaceRule
  , sizing :: Array LockupSizing
  , usageRules :: Array LogoUsageRule
  , errors :: Array LogoError
  }

-- | Create logo specification.
mkLogoSpecification
  :: LogoIcon
  -> LogoWordmark
  -> Array LogoLockup
  -> ClearSpaceRule
  -> Array LockupSizing
  -> Array LogoUsageRule
  -> Array LogoError
  -> Maybe LogoSpecification
mkLogoSpecification icon wm lockups cs sizing rules errors =
  if Array.length lockups >= 1
    then Just
      { icon: icon
      , wordmark: wm
      , lockups: lockups
      , clearSpace: cs
      , sizing: sizing
      , usageRules: rules
      , errors: errors
      }
    else Nothing

-- | Get logo icon.
logoIcon :: LogoSpecification -> LogoIcon
logoIcon ls = ls.icon

-- | Get logo wordmark.
logoWordmark :: LogoSpecification -> LogoWordmark
logoWordmark ls = ls.wordmark

-- | Get logo lockups.
logoLockups :: LogoSpecification -> Array LogoLockup
logoLockups ls = ls.lockups

-- | Get clear space rule.
logoClearSpace :: LogoSpecification -> ClearSpaceRule
logoClearSpace ls = ls.clearSpace

-- | Get sizing rules.
logoSizing :: LogoSpecification -> Array LockupSizing
logoSizing ls = ls.sizing

-- | Get usage rules.
logoUsageRules :: LogoSpecification -> Array LogoUsageRule
logoUsageRules ls = ls.usageRules

-- | Get error rules (DO NOT list).
logoErrors :: LogoSpecification -> Array LogoError
logoErrors ls = ls.errors
