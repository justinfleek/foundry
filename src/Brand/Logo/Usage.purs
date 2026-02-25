-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // brand // logo // usage
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Logo usage context, usage rules, error categories, and error types.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | This module contains:
-- | - UsageContext: Where logo is used (first page, social media, etc.)
-- | - LogoUsageRule: Rules for specific contexts
-- | - LogoErrorCategory: Types of logo errors
-- | - LogoError: DO NOT rules
-- |
-- | DEPENDENCIES:
-- |   - None (foundational module)
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Logo (main logo module)

module Hydrogen.Schema.Brand.Logo.Usage
  ( -- * Usage Context
    UsageContext
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
  
  -- * Logo Usage Rule
  , LogoUsageRule
  , mkLogoUsageRule
  , usageRuleContext
  , usageRuleLockup
  , usageRuleAlignment
  , usageRuleNotes
  
  -- * Logo Error Category
  , LogoErrorCategory
      ( ContrastError
      , ColorError
      , DistortionError
      , LayoutError
      )
  , errorCategoryToString
  
  -- * Logo Error
  , LogoError
  , mkLogoError
  , errorCategory
  , errorDescription
  , errorSeverity
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

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, toLower) as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // usage context
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Context in which logo is used.
data UsageContext
  = UsageFirstPage        -- First page of documents
  | UsageSubsequentPages  -- Subsequent document pages
  | UsageWatermark        -- Background watermark
  | UsageSocialMedia      -- Social media profiles
  | UsageAppIcon          -- Application icon
  | UsageEmail            -- Email signatures
  | UsageStationery       -- Business cards, letterheads

derive instance eqUsageContext :: Eq UsageContext

instance ordUsageContext :: Ord UsageContext where
  compare u1 u2 = compare (usageToInt u1) (usageToInt u2)
    where
      usageToInt :: UsageContext -> Int
      usageToInt UsageFirstPage = 0
      usageToInt UsageSubsequentPages = 1
      usageToInt UsageWatermark = 2
      usageToInt UsageSocialMedia = 3
      usageToInt UsageAppIcon = 4
      usageToInt UsageEmail = 5
      usageToInt UsageStationery = 6

instance showUsageContext :: Show UsageContext where
  show = usageContextToString

-- | Convert usage context to string.
usageContextToString :: UsageContext -> String
usageContextToString UsageFirstPage = "first-page"
usageContextToString UsageSubsequentPages = "subsequent-pages"
usageContextToString UsageWatermark = "watermark"
usageContextToString UsageSocialMedia = "social-media"
usageContextToString UsageAppIcon = "app-icon"
usageContextToString UsageEmail = "email"
usageContextToString UsageStationery = "stationery"

-- | Parse usage context from string.
parseUsageContext :: String -> Maybe UsageContext
parseUsageContext s = case String.toLower s of
  "first-page" -> Just UsageFirstPage
  "first page" -> Just UsageFirstPage
  "subsequent-pages" -> Just UsageSubsequentPages
  "subsequent pages" -> Just UsageSubsequentPages
  "watermark" -> Just UsageWatermark
  "social-media" -> Just UsageSocialMedia
  "social media" -> Just UsageSocialMedia
  "social" -> Just UsageSocialMedia
  "app-icon" -> Just UsageAppIcon
  "app icon" -> Just UsageAppIcon
  "icon" -> Just UsageAppIcon
  "email" -> Just UsageEmail
  "stationery" -> Just UsageStationery
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // logo usage rule
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A specific logo usage rule.
type LogoUsageRule =
  { context :: UsageContext
  , lockupName :: String      -- Which lockup to use
  , alignment :: String       -- Alignment instruction
  , notes :: String           -- Additional notes
  }

-- | Create logo usage rule.
mkLogoUsageRule
  :: UsageContext
  -> String
  -> String
  -> String
  -> Maybe LogoUsageRule
mkLogoUsageRule ctx lockup align notes =
  if String.length lockup >= 1
    then Just
      { context: ctx
      , lockupName: lockup
      , alignment: align
      , notes: notes
      }
    else Nothing

-- | Get usage context.
usageRuleContext :: LogoUsageRule -> UsageContext
usageRuleContext lur = lur.context

-- | Get lockup name.
usageRuleLockup :: LogoUsageRule -> String
usageRuleLockup lur = lur.lockupName

-- | Get alignment.
usageRuleAlignment :: LogoUsageRule -> String
usageRuleAlignment lur = lur.alignment

-- | Get notes.
usageRuleNotes :: LogoUsageRule -> String
usageRuleNotes lur = lur.notes

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // logo error category
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Category of logo error.
data LogoErrorCategory
  = ContrastError     -- Insufficient contrast
  | ColorError        -- Wrong colors used
  | DistortionError   -- Stretched, skewed, cropped
  | LayoutError       -- Component relationships broken

derive instance eqLogoErrorCategory :: Eq LogoErrorCategory

instance ordLogoErrorCategory :: Ord LogoErrorCategory where
  compare e1 e2 = compare (errToInt e1) (errToInt e2)
    where
      errToInt :: LogoErrorCategory -> Int
      errToInt ContrastError = 0
      errToInt ColorError = 1
      errToInt DistortionError = 2
      errToInt LayoutError = 3

instance showLogoErrorCategory :: Show LogoErrorCategory where
  show = errorCategoryToString

-- | Convert error category to string.
errorCategoryToString :: LogoErrorCategory -> String
errorCategoryToString ContrastError = "contrast"
errorCategoryToString ColorError = "color"
errorCategoryToString DistortionError = "distortion"
errorCategoryToString LayoutError = "layout"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // logo error
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A logo error (DO NOT rule).
type LogoError =
  { category :: LogoErrorCategory
  , description :: String       -- What not to do
  , severity :: String          -- "critical", "major", "minor"
  }

-- | Create logo error.
mkLogoError :: LogoErrorCategory -> String -> String -> Maybe LogoError
mkLogoError cat desc sev =
  if String.length desc >= 1 && String.length sev >= 1
    then Just
      { category: cat
      , description: desc
      , severity: sev
      }
    else Nothing

-- | Get error category.
errorCategory :: LogoError -> LogoErrorCategory
errorCategory le = le.category

-- | Get error description.
errorDescription :: LogoError -> String
errorDescription le = le.description

-- | Get error severity.
errorSeverity :: LogoError -> String
errorSeverity le = le.severity
