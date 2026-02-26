{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // foundry // brand/editorial
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Editorial
Description : SMART Framework Section 7 - Master Style List
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Editorial and copy rules that apply across all written content. This module
encodes the Master Style List from the SMART Brand Ingestion Framework.

== SMART Framework Alignment

  S - Story-driven: Editorial rules reflect brand personality in text
  M - Memorable: Consistent style creates recognizable voice
  A - Agile: Rules adapt to headlines, body, lists, etc.
  R - Responsive: Format rules work across mediums
  T - Targeted: Language complexity calibrates to audience

== Categories (per Section 7)

  1. Headlines - Conciseness, punctuation, case style, font/weight
  2. Punctuation - List punctuation, hyphenation, exclamation limits, Oxford comma
  3. Contact & Times - Phone format, time format, date notation
  4. Spelling - Regional preferences, commonly confused words
  5. Formatting - Default alignment, capitalization rules

== Dependencies

  - Data.Text
  - Data.Vector

== Dependents

  - Foundry.Core.Brand (compound Brand type)
  - Foundry.Core.Brand.Strategy (StrategicLayer)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Editorial
  ( -- * Headline Style
    HeadlineCaseStyle (..)
  , caseStyleToText
  , parseCaseStyle
  
  , HeadlinePunctuation (..)
  , headlinePunctuationToText
  
  , HeadlineStyle (..)
  , mkHeadlineStyle
  
    -- * Punctuation Rules
  , ListPunctuation (..)
  , listPunctuationToText
  
  , OxfordComma (..)
  , oxfordCommaToText
  
  , HyphenationPolicy (..)
  , hyphenationToText
  
  , ExclamationLimit (..)
  , mkExclamationLimit
  
  , PunctuationRules (..)
  , mkPunctuationRules
  
    -- * Contact & Time Formats
  , PhoneFormat (..)
  , mkPhoneFormat
  
  , TimeFormat (..)
  , timeFormatToText
  
  , TimeRangeNotation (..)
  , timeRangeToText
  
  , MidnightNoon (..)
  , midnightNoonToText
  
  , DayAbbreviation (..)
  , dayAbbrevToText
  
  , ContactTimeRules (..)
  , mkContactTimeRules
  
    -- * Spelling Conventions
  , RegionalSpelling (..)
  , regionalSpellingToText
  
  , ConfusedWord (..)
  , mkConfusedWord
  
  , SpellingConventions (..)
  , mkSpellingConventions
  
    -- * Text Formatting
  , TextAlignment (..)
  , textAlignmentToText
  
  , CapitalizationRule (..)
  , capitalizationToText
  
  , FormattingRules (..)
  , mkFormattingRules
  
    -- * Complete Master Style List
  , MasterStyleList (..)
  , mkMasterStyleList
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Word (Word8)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // headline style
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Headline case style.
data HeadlineCaseStyle
  = TitleCase      -- ^ Each Word Capitalized
  | SentenceCase   -- ^ Only first word capitalized
  | AllCaps        -- ^ ALL CAPS
  | SmallCaps      -- ^ sᴍᴀʟʟ ᴄᴀᴘs (typographic treatment)
  deriving stock (Eq, Ord, Show)

-- | Convert case style to text.
caseStyleToText :: HeadlineCaseStyle -> Text
caseStyleToText TitleCase = "title-case"
caseStyleToText SentenceCase = "sentence-case"
caseStyleToText AllCaps = "all-caps"
caseStyleToText SmallCaps = "small-caps"

-- | Parse case style from text.
parseCaseStyle :: Text -> Maybe HeadlineCaseStyle
parseCaseStyle s = case T.toLower (T.strip s) of
  "title-case"    -> Just TitleCase
  "title case"    -> Just TitleCase
  "title"         -> Just TitleCase
  "sentence-case" -> Just SentenceCase
  "sentence case" -> Just SentenceCase
  "sentence"      -> Just SentenceCase
  "all-caps"      -> Just AllCaps
  "allcaps"       -> Just AllCaps
  "uppercase"     -> Just AllCaps
  "small-caps"    -> Just SmallCaps
  "smallcaps"     -> Just SmallCaps
  _               -> Nothing

-- | Headline punctuation preferences.
data HeadlinePunctuation
  = AmpersandPreferred   -- ^ Use "&" instead of "and"
  | AndPreferred         -- ^ Use "and" instead of "&"
  | AmpersandAllowed     -- ^ Both acceptable
  | NoPeriods            -- ^ No periods at end of headlines
  | NoColons             -- ^ No colons in headlines
  deriving stock (Eq, Ord, Show)

-- | Convert headline punctuation to text.
headlinePunctuationToText :: HeadlinePunctuation -> Text
headlinePunctuationToText AmpersandPreferred = "prefer-ampersand"
headlinePunctuationToText AndPreferred = "prefer-and"
headlinePunctuationToText AmpersandAllowed = "ampersand-allowed"
headlinePunctuationToText NoPeriods = "no-periods"
headlinePunctuationToText NoColons = "no-colons"

-- | Complete headline style specification.
data HeadlineStyle = HeadlineStyle
  { headlineCaseStyle    :: !HeadlineCaseStyle         -- ^ Case treatment
  , headlinePunctuation  :: !(Vector HeadlinePunctuation) -- ^ Punctuation rules
  , headlineMaxLength    :: !(Maybe Word8)             -- ^ Maximum character count
  , headlineConciseness  :: !Text                      -- ^ Conciseness guidance
  }
  deriving stock (Eq, Show)

-- | Create headline style with validation.
mkHeadlineStyle 
  :: HeadlineCaseStyle 
  -> Vector HeadlinePunctuation 
  -> Maybe Word8 
  -> Text 
  -> HeadlineStyle
mkHeadlineStyle caseStyle punc maxLen concise = HeadlineStyle
  { headlineCaseStyle = caseStyle
  , headlinePunctuation = punc
  , headlineMaxLength = maxLen
  , headlineConciseness = concise
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // punctuation rules
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | List item punctuation style.
data ListPunctuation
  = PeriodsOnAll         -- ^ Period at end of every list item
  | PeriodsOnFinal       -- ^ Period only on final item
  | NoListPeriods        -- ^ No periods on list items
  | PeriodsOnSentences   -- ^ Periods only when item is a full sentence
  deriving stock (Eq, Ord, Show)

-- | Convert list punctuation to text.
listPunctuationToText :: ListPunctuation -> Text
listPunctuationToText PeriodsOnAll = "periods-on-all"
listPunctuationToText PeriodsOnFinal = "periods-on-final"
listPunctuationToText NoListPeriods = "no-periods"
listPunctuationToText PeriodsOnSentences = "periods-on-sentences"

-- | Oxford comma usage.
data OxfordComma
  = OxfordAlways   -- ^ Always use: "red, white, and blue"
  | OxfordNever    -- ^ Never use: "red, white and blue"
  | OxfordOptional -- ^ Contextual usage allowed
  deriving stock (Eq, Ord, Show)

-- | Convert Oxford comma to text.
oxfordCommaToText :: OxfordComma -> Text
oxfordCommaToText OxfordAlways = "always"
oxfordCommaToText OxfordNever = "never"
oxfordCommaToText OxfordOptional = "optional"

-- | Hyphenation policy.
data HyphenationPolicy
  = HyphenateCompounds   -- ^ Hyphenate compound modifiers
  | MinimalHyphenation   -- ^ Only where required for clarity
  | NoHyphenation        -- ^ Avoid hyphens where possible
  | StyleGuideHyphens    -- ^ Follow external style guide (AP, Chicago, etc.)
  deriving stock (Eq, Ord, Show)

-- | Convert hyphenation policy to text.
hyphenationToText :: HyphenationPolicy -> Text
hyphenationToText HyphenateCompounds = "compound-modifiers"
hyphenationToText MinimalHyphenation = "minimal"
hyphenationToText NoHyphenation = "avoid"
hyphenationToText StyleGuideHyphens = "style-guide"

-- | Exclamation point limit per content piece.
--
-- Many brand guides limit exclamation points to prevent overly casual tone.
-- Common limits: 0 (never), 1 (per page/section), unlimited (no restriction).
newtype ExclamationLimit = ExclamationLimit { unExclamationLimit :: Word8 }
  deriving stock (Eq, Ord, Show)

-- | Create exclamation limit. 0 means "never use exclamation points".
mkExclamationLimit :: Word8 -> ExclamationLimit
mkExclamationLimit = ExclamationLimit

-- | Complete punctuation rules.
data PunctuationRules = PunctuationRules
  { punctListStyle       :: !ListPunctuation   -- ^ List item punctuation
  , punctOxfordComma     :: !OxfordComma       -- ^ Serial comma usage
  , punctHyphenation     :: !HyphenationPolicy -- ^ Hyphen policy
  , punctExclamationMax  :: !ExclamationLimit  -- ^ Max exclamation points
  }
  deriving stock (Eq, Show)

-- | Create punctuation rules.
mkPunctuationRules 
  :: ListPunctuation 
  -> OxfordComma 
  -> HyphenationPolicy 
  -> ExclamationLimit 
  -> PunctuationRules
mkPunctuationRules listP ox hyph excl = PunctuationRules
  { punctListStyle = listP
  , punctOxfordComma = ox
  , punctHyphenation = hyph
  , punctExclamationMax = excl
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // contact & times
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Phone number format template.
--
-- Uses 'X' as placeholder for digits. Examples:
--   "XXX-XXX-XXXX"     -- US with hyphens
--   "(XXX) XXX-XXXX"   -- US with parentheses  
--   "+X XXX XXX XXXX"  -- International
newtype PhoneFormat = PhoneFormat { unPhoneFormat :: Text }
  deriving stock (Eq, Ord, Show)

-- | Create phone format with validation.
mkPhoneFormat :: Text -> Maybe PhoneFormat
mkPhoneFormat t
  | T.null t = Nothing
  | T.any (== 'X') t = Just (PhoneFormat t)
  | otherwise = Nothing  -- Must contain at least one X placeholder

-- | Time format preference.
data TimeFormat
  = TwelveHour      -- ^ 3:00 PM
  | TwentyFourHour  -- ^ 15:00
  deriving stock (Eq, Ord, Show)

-- | Convert time format to text.
timeFormatToText :: TimeFormat -> Text
timeFormatToText TwelveHour = "12-hour"
timeFormatToText TwentyFourHour = "24-hour"

-- | Time range notation.
data TimeRangeNotation
  = EnDash         -- ^ 9:00 AM–5:00 PM (en-dash)
  | Hyphen         -- ^ 9:00 AM-5:00 PM (hyphen)
  | ToWord         -- ^ 9:00 AM to 5:00 PM (word)
  deriving stock (Eq, Ord, Show)

-- | Convert time range notation to text.
timeRangeToText :: TimeRangeNotation -> Text
timeRangeToText EnDash = "en-dash"
timeRangeToText Hyphen = "hyphen"
timeRangeToText ToWord = "to-word"

-- | Midnight/noon representation.
data MidnightNoon
  = TwelveAMPM       -- ^ 12:00 AM / 12:00 PM
  | MidnightNoonWord -- ^ "midnight" / "noon"
  | TwentyFourStyle  -- ^ 00:00 / 12:00
  deriving stock (Eq, Ord, Show)

-- | Convert midnight/noon style to text.
midnightNoonToText :: MidnightNoon -> Text
midnightNoonToText TwelveAMPM = "12-am-pm"
midnightNoonToText MidnightNoonWord = "words"
midnightNoonToText TwentyFourStyle = "24-hour"

-- | Day name abbreviation policy.
data DayAbbreviation
  = NeverAbbreviate  -- ^ Always spell out: "Monday"
  | ThreeLetters     -- ^ Three letters: "Mon"
  | TwoLetters       -- ^ Two letters: "Mo"
  | ContextualAbbrev -- ^ Abbreviate only when space-constrained
  deriving stock (Eq, Ord, Show)

-- | Convert day abbreviation policy to text.
dayAbbrevToText :: DayAbbreviation -> Text
dayAbbrevToText NeverAbbreviate = "never"
dayAbbrevToText ThreeLetters = "three-letter"
dayAbbrevToText TwoLetters = "two-letter"
dayAbbrevToText ContextualAbbrev = "contextual"

-- | Complete contact and time rules.
data ContactTimeRules = ContactTimeRules
  { contactPhoneFormat  :: !PhoneFormat        -- ^ Phone number format
  , contactTimeFormat   :: !TimeFormat         -- ^ 12 or 24 hour
  , contactTimeRange    :: !TimeRangeNotation  -- ^ Range separator
  , contactMidnightNoon :: !MidnightNoon       -- ^ Midnight/noon style
  , contactDayAbbrev    :: !DayAbbreviation    -- ^ Day abbreviation policy
  }
  deriving stock (Eq, Show)

-- | Create contact/time rules.
mkContactTimeRules 
  :: PhoneFormat 
  -> TimeFormat 
  -> TimeRangeNotation 
  -> MidnightNoon 
  -> DayAbbreviation 
  -> ContactTimeRules
mkContactTimeRules phone time range mn day = ContactTimeRules
  { contactPhoneFormat = phone
  , contactTimeFormat = time
  , contactTimeRange = range
  , contactMidnightNoon = mn
  , contactDayAbbrev = day
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // spelling conventions
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Regional spelling preference.
data RegionalSpelling
  = AmericanEnglish  -- ^ color, organize, center
  | BritishEnglish   -- ^ colour, organise, centre
  | CanadianEnglish  -- ^ colour, organize, centre (hybrid)
  | AustralianEnglish -- ^ colour, organise, centre
  deriving stock (Eq, Ord, Show)

-- | Convert regional spelling to text.
regionalSpellingToText :: RegionalSpelling -> Text
regionalSpellingToText AmericanEnglish = "en-US"
regionalSpellingToText BritishEnglish = "en-GB"
regionalSpellingToText CanadianEnglish = "en-CA"
regionalSpellingToText AustralianEnglish = "en-AU"

-- | Commonly confused word pair with preferred usage.
data ConfusedWord = ConfusedWord
  { confusedIncorrect :: !Text  -- ^ The incorrect/discouraged form
  , confusedCorrect   :: !Text  -- ^ The correct/preferred form
  , confusedContext   :: !Text  -- ^ When to apply this rule
  }
  deriving stock (Eq, Show)

-- | Create confused word rule with validation.
mkConfusedWord :: Text -> Text -> Text -> Maybe ConfusedWord
mkConfusedWord incorrect correct context
  | T.null incorrect = Nothing
  | T.null correct = Nothing
  | otherwise = Just ConfusedWord
      { confusedIncorrect = incorrect
      , confusedCorrect = correct
      , confusedContext = context
      }

-- | Complete spelling conventions.
data SpellingConventions = SpellingConventions
  { spellingRegion   :: !RegionalSpelling      -- ^ Regional variant
  , spellingConfused :: !(Vector ConfusedWord) -- ^ Common errors to avoid
  }
  deriving stock (Eq, Show)

-- | Create spelling conventions.
mkSpellingConventions :: RegionalSpelling -> Vector ConfusedWord -> SpellingConventions
mkSpellingConventions region confused = SpellingConventions
  { spellingRegion = region
  , spellingConfused = confused
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // formatting rules
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Default text alignment.
data TextAlignment
  = AlignLeft     -- ^ Left-aligned (most common)
  | AlignCenter   -- ^ Center-aligned
  | AlignRight    -- ^ Right-aligned
  | AlignJustify  -- ^ Justified (full width)
  deriving stock (Eq, Ord, Show)

-- | Convert text alignment to text.
textAlignmentToText :: TextAlignment -> Text
textAlignmentToText AlignLeft = "left"
textAlignmentToText AlignCenter = "center"
textAlignmentToText AlignRight = "right"
textAlignmentToText AlignJustify = "justify"

-- | Capitalization rules for specific contexts.
data CapitalizationRule
  = CapBrandNames      -- ^ Brand names are always capitalized as specified
  | CapProductNames    -- ^ Product names follow brand capitalization
  | CapAcronyms        -- ^ Acronyms follow specific rules
  | CapCamelCase       -- ^ camelCase allowed for technical terms
  | CapNoAllCaps       -- ^ NEVER use all caps except where specified
  deriving stock (Eq, Ord, Show)

-- | Convert capitalization rule to text.
capitalizationToText :: CapitalizationRule -> Text
capitalizationToText CapBrandNames = "brand-names"
capitalizationToText CapProductNames = "product-names"
capitalizationToText CapAcronyms = "acronyms"
capitalizationToText CapCamelCase = "camel-case-allowed"
capitalizationToText CapNoAllCaps = "no-all-caps"

-- | Complete formatting rules.
data FormattingRules = FormattingRules
  { formatAlignment      :: !TextAlignment              -- ^ Default alignment
  , formatCapitalization :: !(Vector CapitalizationRule) -- ^ Cap rules
  }
  deriving stock (Eq, Show)

-- | Create formatting rules.
mkFormattingRules :: TextAlignment -> Vector CapitalizationRule -> FormattingRules
mkFormattingRules align caps = FormattingRules
  { formatAlignment = align
  , formatCapitalization = caps
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // master style list
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete Master Style List - the editorial style guide for a brand.
--
-- Per SMART Framework Section 7, this encompasses all editorial rules that
-- ensure consistent voice and formatting across all written content.
data MasterStyleList = MasterStyleList
  { styleHeadlines    :: !HeadlineStyle        -- ^ Headline formatting
  , stylePunctuation  :: !PunctuationRules     -- ^ Punctuation rules
  , styleContactTime  :: !ContactTimeRules     -- ^ Contact/time formatting
  , styleSpelling     :: !SpellingConventions  -- ^ Spelling preferences
  , styleFormatting   :: !FormattingRules      -- ^ General formatting
  }
  deriving stock (Eq, Show)

-- | Create a complete master style list.
mkMasterStyleList 
  :: HeadlineStyle 
  -> PunctuationRules 
  -> ContactTimeRules 
  -> SpellingConventions 
  -> FormattingRules 
  -> MasterStyleList
mkMasterStyleList headlines punct contact spell fmt = MasterStyleList
  { styleHeadlines = headlines
  , stylePunctuation = punct
  , styleContactTime = contact
  , styleSpelling = spell
  , styleFormatting = fmt
  }
