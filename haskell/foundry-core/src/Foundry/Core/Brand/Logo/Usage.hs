{- |
Module      : Foundry.Core.Brand.Logo.Usage
Description : Logo usage context, rules, and error types
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Logo usage contexts, usage rules, error categories, and error types.
Mirrors Hydrogen.Schema.Brand.Logo.Usage from PureScript.

DEPENDENCIES:
  - None (foundational module)

DEPENDENTS:
  - Foundry.Core.Brand.Logo (main logo module)
-}
module Foundry.Core.Brand.Logo.Usage
  ( -- * Usage Context
    UsageContext (..)
  , usageContextToText
  , parseUsageContext
  
    -- * Logo Usage Rule
  , LogoUsageRule (..)
  , mkLogoUsageRule
  
    -- * Logo Error Category
  , LogoErrorCategory (..)
  , errorCategoryToText
  
    -- * Logo Error
  , LogoError (..)
  , mkLogoError
  ) where

import Data.Text (Text)
import Data.Text qualified as T

-- | Context in which logo is used.
data UsageContext
  = UsageFirstPage        -- ^ First page of documents
  | UsageSubsequentPages  -- ^ Subsequent document pages
  | UsageWatermark        -- ^ Background watermark
  | UsageSocialMedia      -- ^ Social media profiles
  | UsageAppIcon          -- ^ Application icon
  | UsageEmail            -- ^ Email signatures
  | UsageStationery       -- ^ Business cards, letterheads
  deriving stock (Eq, Ord, Show)

-- | Convert usage context to text.
usageContextToText :: UsageContext -> Text
usageContextToText UsageFirstPage = "first-page"
usageContextToText UsageSubsequentPages = "subsequent-pages"
usageContextToText UsageWatermark = "watermark"
usageContextToText UsageSocialMedia = "social-media"
usageContextToText UsageAppIcon = "app-icon"
usageContextToText UsageEmail = "email"
usageContextToText UsageStationery = "stationery"

-- | Parse usage context from text.
parseUsageContext :: Text -> Maybe UsageContext
parseUsageContext s = case T.toLower s of
  "first-page"        -> Just UsageFirstPage
  "first page"        -> Just UsageFirstPage
  "subsequent-pages"  -> Just UsageSubsequentPages
  "subsequent pages"  -> Just UsageSubsequentPages
  "watermark"         -> Just UsageWatermark
  "social-media"      -> Just UsageSocialMedia
  "social media"      -> Just UsageSocialMedia
  "social"            -> Just UsageSocialMedia
  "app-icon"          -> Just UsageAppIcon
  "app icon"          -> Just UsageAppIcon
  "icon"              -> Just UsageAppIcon
  "email"             -> Just UsageEmail
  "stationery"        -> Just UsageStationery
  _                   -> Nothing

-- | A specific logo usage rule.
data LogoUsageRule = LogoUsageRule
  { usageRuleContext   :: !UsageContext  -- ^ Context for this rule
  , usageRuleLockup    :: !Text          -- ^ Which lockup to use
  , usageRuleAlignment :: !Text          -- ^ Alignment instruction
  , usageRuleNotes     :: !Text          -- ^ Additional notes
  }
  deriving stock (Eq, Show)

-- | Create logo usage rule with validation.
mkLogoUsageRule
  :: UsageContext
  -> Text   -- ^ Lockup name
  -> Text   -- ^ Alignment
  -> Text   -- ^ Notes
  -> Maybe LogoUsageRule
mkLogoUsageRule ctx lockup align notes
  | T.length lockup >= 1 =
      Just LogoUsageRule
        { usageRuleContext = ctx
        , usageRuleLockup = lockup
        , usageRuleAlignment = align
        , usageRuleNotes = notes
        }
  | otherwise = Nothing

-- | Category of logo error.
data LogoErrorCategory
  = ContrastError     -- ^ Insufficient contrast
  | ColorError        -- ^ Wrong colors used
  | DistortionError   -- ^ Stretched, skewed, cropped
  | LayoutError       -- ^ Component relationships broken
  deriving stock (Eq, Ord, Show)

-- | Convert error category to text.
errorCategoryToText :: LogoErrorCategory -> Text
errorCategoryToText ContrastError = "contrast"
errorCategoryToText ColorError = "color"
errorCategoryToText DistortionError = "distortion"
errorCategoryToText LayoutError = "layout"

-- | A logo error (DO NOT rule).
data LogoError = LogoError
  { logoErrorCategory    :: !LogoErrorCategory  -- ^ Type of error
  , logoErrorDescription :: !Text               -- ^ What not to do
  , logoErrorSeverity    :: !Text               -- ^ "critical", "major", "minor"
  }
  deriving stock (Eq, Show)

-- | Create logo error with validation.
mkLogoError
  :: LogoErrorCategory
  -> Text  -- ^ Description
  -> Text  -- ^ Severity
  -> Maybe LogoError
mkLogoError cat desc sev
  | T.length desc >= 1 && T.length sev >= 1 =
      Just LogoError
        { logoErrorCategory = cat
        , logoErrorDescription = desc
        , logoErrorSeverity = sev
        }
  | otherwise = Nothing
