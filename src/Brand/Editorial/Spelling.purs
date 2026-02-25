-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // brand // editorial // spelling
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spelling conventions: regional spelling variants and conventions.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | DEPENDENCIES:
-- |   - None (foundational module)
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Editorial (main editorial module)

module Hydrogen.Schema.Brand.Editorial.Spelling
  ( -- * Regional Spelling
    RegionalSpelling
      ( AmericanEnglish
      , BritishEnglish
      , CanadianEnglish
      , AustralianEnglish
      )
  , regionalSpellingToString
  , parseRegionalSpelling
  
  -- * Spelling Conventions
  , SpellingConventions
  , mkSpellingConventions
  , spellingRegion
  , spellingExceptions
  , spellingConfusedWords
  
  -- * Text Alignment
  , TextAlignment
      ( AlignLeft
      , AlignCenter
      , AlignRight
      , AlignJustify
      )
  , textAlignmentToString
  , parseTextAlignment
  
  -- * Formatting Rules
  , FormattingRules
  , mkFormattingRules
  , formattingDefaultAlignment
  , formattingCapitalizationRules
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , show
  , compare
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (toLower) as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // spelling conventions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Regional spelling variant.
data RegionalSpelling
  = AmericanEnglish    -- color, gray, organize
  | BritishEnglish     -- colour, grey, organise
  | CanadianEnglish    -- colour, gray, organize
  | AustralianEnglish  -- colour, grey, organise

derive instance eqRegionalSpelling :: Eq RegionalSpelling

instance ordRegionalSpelling :: Ord RegionalSpelling where
  compare r1 r2 = compare (regionToInt r1) (regionToInt r2)
    where
      regionToInt :: RegionalSpelling -> Int
      regionToInt AmericanEnglish = 0
      regionToInt BritishEnglish = 1
      regionToInt CanadianEnglish = 2
      regionToInt AustralianEnglish = 3

instance showRegionalSpelling :: Show RegionalSpelling where
  show = regionalSpellingToString

-- | Convert regional spelling to string.
regionalSpellingToString :: RegionalSpelling -> String
regionalSpellingToString AmericanEnglish = "american-english"
regionalSpellingToString BritishEnglish = "british-english"
regionalSpellingToString CanadianEnglish = "canadian-english"
regionalSpellingToString AustralianEnglish = "australian-english"

-- | Parse regional spelling from string.
parseRegionalSpelling :: String -> Maybe RegionalSpelling
parseRegionalSpelling s = case String.toLower s of
  "american-english" -> Just AmericanEnglish
  "american" -> Just AmericanEnglish
  "us" -> Just AmericanEnglish
  "en-us" -> Just AmericanEnglish
  "british-english" -> Just BritishEnglish
  "british" -> Just BritishEnglish
  "uk" -> Just BritishEnglish
  "en-gb" -> Just BritishEnglish
  "canadian-english" -> Just CanadianEnglish
  "canadian" -> Just CanadianEnglish
  "en-ca" -> Just CanadianEnglish
  "australian-english" -> Just AustralianEnglish
  "australian" -> Just AustralianEnglish
  "en-au" -> Just AustralianEnglish
  _ -> Nothing

-- | Spelling conventions.
type SpellingConventions =
  { region :: RegionalSpelling
  , exceptions :: Array String      -- Specific words that override regional default
  , confusedWords :: Array String   -- Commonly confused words to watch for
  }

-- | Create spelling conventions.
mkSpellingConventions 
  :: RegionalSpelling 
  -> Array String 
  -> Array String 
  -> SpellingConventions
mkSpellingConventions reg exceptions confused =
  { region: reg
  , exceptions: exceptions
  , confusedWords: confused
  }

-- | Get regional spelling.
spellingRegion :: SpellingConventions -> RegionalSpelling
spellingRegion sc = sc.region

-- | Get spelling exceptions.
spellingExceptions :: SpellingConventions -> Array String
spellingExceptions sc = sc.exceptions

-- | Get commonly confused words.
spellingConfusedWords :: SpellingConventions -> Array String
spellingConfusedWords sc = sc.confusedWords

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // formatting rules
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Text alignment options.
data TextAlignment
  = AlignLeft
  | AlignCenter
  | AlignRight
  | AlignJustify

derive instance eqTextAlignment :: Eq TextAlignment

instance ordTextAlignment :: Ord TextAlignment where
  compare a1 a2 = compare (alignToInt a1) (alignToInt a2)
    where
      alignToInt :: TextAlignment -> Int
      alignToInt AlignLeft = 0
      alignToInt AlignCenter = 1
      alignToInt AlignRight = 2
      alignToInt AlignJustify = 3

instance showTextAlignment :: Show TextAlignment where
  show = textAlignmentToString

-- | Convert text alignment to string.
textAlignmentToString :: TextAlignment -> String
textAlignmentToString AlignLeft = "left"
textAlignmentToString AlignCenter = "center"
textAlignmentToString AlignRight = "right"
textAlignmentToString AlignJustify = "justify"

-- | Parse text alignment from string.
parseTextAlignment :: String -> Maybe TextAlignment
parseTextAlignment s = case String.toLower s of
  "left" -> Just AlignLeft
  "center" -> Just AlignCenter
  "centre" -> Just AlignCenter
  "right" -> Just AlignRight
  "justify" -> Just AlignJustify
  "justified" -> Just AlignJustify
  _ -> Nothing

-- | General formatting rules.
type FormattingRules =
  { defaultAlignment :: TextAlignment
  , capitalizationRules :: Array String  -- Specific capitalization rules
  }

-- | Create formatting rules.
mkFormattingRules :: TextAlignment -> Array String -> FormattingRules
mkFormattingRules align capRules =
  { defaultAlignment: align
  , capitalizationRules: capRules
  }

-- | Get default alignment.
formattingDefaultAlignment :: FormattingRules -> TextAlignment
formattingDefaultAlignment fr = fr.defaultAlignment

-- | Get capitalization rules.
formattingCapitalizationRules :: FormattingRules -> Array String
formattingCapitalizationRules fr = fr.capitalizationRules
