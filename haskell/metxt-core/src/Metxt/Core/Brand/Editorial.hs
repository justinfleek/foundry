{- |
Module      : Metxt.Core.Brand.Editorial
Description : Editorial style guide types
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Master style list for content consistency.
-}
module Metxt.Core.Brand.Editorial
  ( -- * Types
    HeadlineStyle (..)
  , PunctuationRule (..)
  , TimeFormat (..)
  , SpellingPreference (..)
  , MasterStyleList (..)
  ) where

import Data.Text (Text)

-- | Headline capitalization style
data HeadlineStyle
  = TitleCase
  | SentenceCase
  deriving stock (Eq, Show)

-- | Punctuation rule
data PunctuationRule = PunctuationRule
  { punctuationContext :: !Text
  , punctuationRule :: !Text
  }
  deriving stock (Eq, Show)

-- | Time format preference
data TimeFormat
  = TwelveHour
  | TwentyFourHour
  deriving stock (Eq, Show)

-- | Spelling preference (US/UK)
data SpellingPreference
  = AmericanEnglish
  | BritishEnglish
  deriving stock (Eq, Show)

-- | Complete editorial style guide
data MasterStyleList = MasterStyleList
  { styleHeadlines :: !HeadlineStyle
  , stylePunctuation :: ![PunctuationRule]
  , styleTimeFormat :: !TimeFormat
  , styleSpelling :: !SpellingPreference
  }
  deriving stock (Eq, Show)
