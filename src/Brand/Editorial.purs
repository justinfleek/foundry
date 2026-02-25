-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // brand // editorial
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SMART Framework Editorial Layer: Master Style List for copy and content.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | This module captures editorial and copy rules that apply across all written
-- | content: headlines, punctuation, contact information, spelling, and formatting.
-- |
-- | SMART FRAMEWORK:
-- |   S - Story-driven: Headlines capture brand voice in minimal words
-- |   M - Memorable: Consistent punctuation creates recognizable style
-- |   A - Agile: Rules flex across contexts while maintaining consistency
-- |   R - Responsive: Formatting adapts to medium (print/digital)
-- |   T - Targeted: Spelling conventions match audience expectations
-- |
-- | DEPENDENCIES:
-- |   - Hydrogen.Schema.Brand.Editorial.Contact
-- |   - Hydrogen.Schema.Brand.Editorial.Spelling
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Brand (compound Brand type)

module Hydrogen.Schema.Brand.Editorial
  ( -- * Case Style
    CaseStyle
      ( TitleCase
      , SentenceCase
      , UpperCase
      , LowerCase
      )
  , caseStyleToString
  , parseCaseStyle
  
  -- * Headline Rules
  , HeadlineRules
  , mkHeadlineRules
  , headlineCaseStyle
  , headlineMaxWords
  , headlinePreferAmpersand
  , headlineFontWeight
  , headlineKerning
  
  -- * Punctuation Rules
  , PunctuationRules
  , mkPunctuationRules
  , useOxfordComma
  , listItemPeriods
  , maxExclamationPoints
  , hyphenationPolicy
  
  -- * Re-exports from Editorial.Contact
  , module Hydrogen.Schema.Brand.Editorial.Contact
  
  -- * Re-exports from Editorial.Spelling
  , module Hydrogen.Schema.Brand.Editorial.Spelling
  
  -- * Master Style List (Complete)
  , MasterStyleList
  , mkMasterStyleList
  , styleListHeadlines
  , styleListPunctuation
  , styleListContactFormat
  , styleListSpelling
  , styleListFormatting
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>=)
  , (<=)
  , (&&)
  , (<>)
  , show
  , compare
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, toLower) as String

import Hydrogen.Schema.Brand.Editorial.Contact
  ( PhoneFormat
      ( PhoneHyphens
      , PhoneDots
      , PhoneSpaces
      , PhoneParensArea
      )
  , phoneFormatToString
  , parsePhoneFormat
  , HourFormat
      ( Hour12
      , Hour24
      )
  , hourFormatToString
  , parseHourFormat
  , TimeFormat
  , mkTimeFormat
  , timeHourFormat
  , timeAmPmSpaced
  , timeRangeSeparator
  , timeMidnightConvention
  , timeNoonConvention
  , ContactFormatRules
  , mkContactFormatRules
  , contactPhoneFormat
  , contactTimeFormat
  , contactAbbreviateDays
  )

import Hydrogen.Schema.Brand.Editorial.Spelling
  ( RegionalSpelling
      ( AmericanEnglish
      , BritishEnglish
      , CanadianEnglish
      , AustralianEnglish
      )
  , regionalSpellingToString
  , parseRegionalSpelling
  , SpellingConventions
  , mkSpellingConventions
  , spellingRegion
  , spellingExceptions
  , spellingConfusedWords
  , TextAlignment
      ( AlignLeft
      , AlignCenter
      , AlignRight
      , AlignJustify
      )
  , textAlignmentToString
  , parseTextAlignment
  , FormattingRules
  , mkFormattingRules
  , formattingDefaultAlignment
  , formattingCapitalizationRules
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // case style
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Case style for headlines and titles.
data CaseStyle
  = TitleCase       -- Each Major Word Capitalized
  | SentenceCase    -- First word capitalized only
  | UpperCase       -- ALL CAPS
  | LowerCase       -- all lowercase

derive instance eqCaseStyle :: Eq CaseStyle

instance ordCaseStyle :: Ord CaseStyle where
  compare c1 c2 = compare (caseToInt c1) (caseToInt c2)
    where
      caseToInt :: CaseStyle -> Int
      caseToInt TitleCase = 0
      caseToInt SentenceCase = 1
      caseToInt UpperCase = 2
      caseToInt LowerCase = 3

instance showCaseStyle :: Show CaseStyle where
  show = caseStyleToString

-- | Convert case style to string.
caseStyleToString :: CaseStyle -> String
caseStyleToString TitleCase = "title-case"
caseStyleToString SentenceCase = "sentence-case"
caseStyleToString UpperCase = "upper-case"
caseStyleToString LowerCase = "lower-case"

-- | Parse case style from string.
parseCaseStyle :: String -> Maybe CaseStyle
parseCaseStyle s = case String.toLower s of
  "title-case" -> Just TitleCase
  "titlecase" -> Just TitleCase
  "title" -> Just TitleCase
  "sentence-case" -> Just SentenceCase
  "sentencecase" -> Just SentenceCase
  "sentence" -> Just SentenceCase
  "upper-case" -> Just UpperCase
  "uppercase" -> Just UpperCase
  "upper" -> Just UpperCase
  "all-caps" -> Just UpperCase
  "lower-case" -> Just LowerCase
  "lowercase" -> Just LowerCase
  "lower" -> Just LowerCase
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // headline rules
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Rules governing headline formatting.
type HeadlineRules =
  { caseStyle :: CaseStyle
  , maxWords :: Int                    -- Recommended max word count
  , preferAmpersand :: Boolean         -- Use "&" instead of "and"
  , fontWeight :: String               -- e.g., "Extra Bold"
  , kerning :: Number                  -- Kerning value (em units)
  }

-- | Create headline rules with validation.
mkHeadlineRules 
  :: CaseStyle 
  -> Int 
  -> Boolean 
  -> String 
  -> Number 
  -> Maybe HeadlineRules
mkHeadlineRules cs maxW ampersand fontW kern =
  if maxW >= 1 && String.length fontW >= 1
    then Just 
      { caseStyle: cs
      , maxWords: maxW
      , preferAmpersand: ampersand
      , fontWeight: fontW
      , kerning: kern
      }
    else Nothing

-- | Get case style.
headlineCaseStyle :: HeadlineRules -> CaseStyle
headlineCaseStyle hr = hr.caseStyle

-- | Get max words.
headlineMaxWords :: HeadlineRules -> Int
headlineMaxWords hr = hr.maxWords

-- | Check if ampersand preferred.
headlinePreferAmpersand :: HeadlineRules -> Boolean
headlinePreferAmpersand hr = hr.preferAmpersand

-- | Get font weight.
headlineFontWeight :: HeadlineRules -> String
headlineFontWeight hr = hr.fontWeight

-- | Get kerning value.
headlineKerning :: HeadlineRules -> Number
headlineKerning hr = hr.kerning

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // punctuation rules
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Rules governing punctuation usage.
type PunctuationRules =
  { oxfordComma :: Boolean             -- Use Oxford/serial comma
  , listItemPeriods :: Boolean         -- Period at end of bullet items
  , maxExclamations :: Int             -- Max exclamation points per piece
  , hyphenation :: String              -- Hyphenation policy description
  }

-- | Create punctuation rules.
mkPunctuationRules 
  :: Boolean 
  -> Boolean 
  -> Int 
  -> String 
  -> Maybe PunctuationRules
mkPunctuationRules oxford listPeriods maxExclam hyphen =
  if maxExclam >= 0 && String.length hyphen >= 1
    then Just
      { oxfordComma: oxford
      , listItemPeriods: listPeriods
      , maxExclamations: maxExclam
      , hyphenation: hyphen
      }
    else Nothing

-- | Check if Oxford comma used.
useOxfordComma :: PunctuationRules -> Boolean
useOxfordComma pr = pr.oxfordComma

-- | Check if list items end with periods.
listItemPeriods :: PunctuationRules -> Boolean
listItemPeriods pr = pr.listItemPeriods

-- | Get max exclamation points.
maxExclamationPoints :: PunctuationRules -> Int
maxExclamationPoints pr = pr.maxExclamations

-- | Get hyphenation policy.
hyphenationPolicy :: PunctuationRules -> String
hyphenationPolicy pr = pr.hyphenation

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // master style list
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete Master Style List for a brand.
type MasterStyleList =
  { headlines :: HeadlineRules
  , punctuation :: PunctuationRules
  , contactFormat :: ContactFormatRules
  , spelling :: SpellingConventions
  , formatting :: FormattingRules
  }

-- | Create master style list.
mkMasterStyleList 
  :: HeadlineRules 
  -> PunctuationRules 
  -> ContactFormatRules 
  -> SpellingConventions 
  -> FormattingRules 
  -> MasterStyleList
mkMasterStyleList headlines punct contact spelling formatting =
  { headlines: headlines
  , punctuation: punct
  , contactFormat: contact
  , spelling: spelling
  , formatting: formatting
  }

-- | Get headline rules.
styleListHeadlines :: MasterStyleList -> HeadlineRules
styleListHeadlines msl = msl.headlines

-- | Get punctuation rules.
styleListPunctuation :: MasterStyleList -> PunctuationRules
styleListPunctuation msl = msl.punctuation

-- | Get contact format rules.
styleListContactFormat :: MasterStyleList -> ContactFormatRules
styleListContactFormat msl = msl.contactFormat

-- | Get spelling conventions.
styleListSpelling :: MasterStyleList -> SpellingConventions
styleListSpelling msl = msl.spelling

-- | Get formatting rules.
styleListFormatting :: MasterStyleList -> FormattingRules
styleListFormatting msl = msl.formatting
