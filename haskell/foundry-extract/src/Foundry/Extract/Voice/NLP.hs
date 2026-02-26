{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // foundry // extract // voice/nlp
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Voice.NLP
Description : Basic NLP analysis for brand voice
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Provides basic NLP features for voice analysis without external dependencies.

== Features

* Sentence length analysis
* Word frequency counting
* Formality heuristics (contractions, pronouns)
* Simple keyword extraction

== Design Notes

This is a pure Haskell implementation without external NLP libraries.
For production use, consider integrating with a proper NLP service.

== Dependencies

Requires: text, containers
Required by: Foundry.Extract.Voice

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Voice.NLP
  ( -- * Types
    TextAnalysis (..)
  , SentenceStats (..)

    -- * Analysis
  , analyzeText
  , countWords
  , averageSentenceLength
  , detectContractions
  , detectPronouns

    -- * Formality
  , formalityScore
  , hasFirstPersonPronouns
  , hasSecondPersonPronouns
  ) where

import Data.Char (isAlpha, isSpace, toLower)
import Data.List (foldl')
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Complete text analysis result
data TextAnalysis = TextAnalysis
  { taWordCount       :: !Int
    -- ^ Total word count
  , taSentenceCount   :: !Int
    -- ^ Total sentence count
  , taAvgSentenceLen  :: !Double
    -- ^ Average sentence length in words
  , taWordFrequency   :: !(Map Text Int)
    -- ^ Word frequency map
  , taContractions    :: !Int
    -- ^ Count of contractions found
  , taFirstPerson     :: !Int
    -- ^ Count of first-person pronouns
  , taSecondPerson    :: !Int
    -- ^ Count of second-person pronouns
  , taFormality       :: !Double
    -- ^ Formality score [0, 1]
  }
  deriving stock (Eq, Show)

-- | Statistics about sentence structure
data SentenceStats = SentenceStats
  { ssCount      :: !Int
    -- ^ Number of sentences
  , ssMinLength  :: !Int
    -- ^ Minimum sentence length
  , ssMaxLength  :: !Int
    -- ^ Maximum sentence length
  , ssAvgLength  :: !Double
    -- ^ Average sentence length
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Analysis
--------------------------------------------------------------------------------

-- | Perform complete text analysis
analyzeText :: Text -> TextAnalysis
analyzeText text =
  let words' = extractWords text
      sentences = extractSentences text
      wordCount = length words'
      sentenceCount = length sentences
      avgLen = if sentenceCount == 0 
               then 0 
               else fromIntegral wordCount / fromIntegral sentenceCount
      wordFreq = countWords words'
      contractions = detectContractions text
      firstPerson = detectPronouns firstPersonPronouns text
      secondPerson = detectPronouns secondPersonPronouns text
      formality = formalityScore contractions firstPerson secondPerson wordCount
  in TextAnalysis
       { taWordCount = wordCount
       , taSentenceCount = sentenceCount
       , taAvgSentenceLen = avgLen
       , taWordFrequency = wordFreq
       , taContractions = contractions
       , taFirstPerson = firstPerson
       , taSecondPerson = secondPerson
       , taFormality = formality
       }

-- | Extract words from text
extractWords :: Text -> [Text]
extractWords = filter (not . T.null) . T.words . T.map normalizeChar
  where
    normalizeChar c = if isAlpha c || isSpace c then c else ' '

-- | Extract sentences from text
extractSentences :: Text -> [Text]
extractSentences text = filter (not . T.null) $ T.split isSentenceEnd text
  where
    isSentenceEnd c = c == '.' || c == '!' || c == '?'

-- | Count word frequencies
countWords :: [Text] -> Map Text Int
countWords = foldl' insertWord Map.empty
  where
    insertWord acc word = Map.insertWith (+) (T.toLower word) 1 acc

-- | Calculate average sentence length
averageSentenceLength :: Text -> Double
averageSentenceLength text =
  let sentences = extractSentences text
      wordCounts = map (length . extractWords) sentences
  in if null sentences
     then 0
     else fromIntegral (sum wordCounts) / fromIntegral (length sentences)

--------------------------------------------------------------------------------
-- Contractions and Pronouns
--------------------------------------------------------------------------------

-- | Detect contractions in text
detectContractions :: Text -> Int
detectContractions text = length $ filter isContraction (T.words text)
  where
    isContraction word = T.toLower word `Set.member` commonContractions

commonContractions :: Set Text
commonContractions = Set.fromList
  [ "i'm", "i've", "i'll", "i'd"
  , "you're", "you've", "you'll", "you'd"
  , "he's", "he'll", "he'd"
  , "she's", "she'll", "she'd"
  , "it's", "it'll"
  , "we're", "we've", "we'll", "we'd"
  , "they're", "they've", "they'll", "they'd"
  , "that's", "that'll", "that'd"
  , "who's", "who'll", "who'd"
  , "what's", "what'll", "what'd"
  , "where's", "where'll", "where'd"
  , "when's", "when'll", "when'd"
  , "why's", "why'll", "why'd"
  , "how's", "how'll", "how'd"
  , "isn't", "aren't", "wasn't", "weren't"
  , "haven't", "hasn't", "hadn't"
  , "won't", "wouldn't", "don't", "doesn't", "didn't"
  , "can't", "couldn't", "shouldn't", "mightn't", "mustn't"
  , "let's", "here's", "there's"
  ]

-- | Detect pronouns from a set
detectPronouns :: Set Text -> Text -> Int
detectPronouns pronounSet text = 
  length $ filter (`Set.member` pronounSet) $ map T.toLower $ T.words text

firstPersonPronouns :: Set Text
firstPersonPronouns = Set.fromList
  [ "i", "me", "my", "mine", "myself"
  , "we", "us", "our", "ours", "ourselves"
  ]

secondPersonPronouns :: Set Text
secondPersonPronouns = Set.fromList
  [ "you", "your", "yours", "yourself", "yourselves"
  ]

-- | Check for first-person pronouns
hasFirstPersonPronouns :: Text -> Bool
hasFirstPersonPronouns text = detectPronouns firstPersonPronouns text > 0

-- | Check for second-person pronouns
hasSecondPersonPronouns :: Text -> Bool
hasSecondPersonPronouns text = detectPronouns secondPersonPronouns text > 0

--------------------------------------------------------------------------------
-- Formality
--------------------------------------------------------------------------------

-- | Calculate formality score [0, 1]
-- 
-- Higher scores indicate more formal text:
-- - Fewer contractions
-- - Fewer first/second person pronouns
-- - Longer sentences
formalityScore :: Int -> Int -> Int -> Int -> Double
formalityScore contractions firstPerson secondPerson wordCount
  | wordCount == 0 = 0.5  -- Neutral for empty text
  | otherwise =
      let -- Normalize counts by word count
          contractionRate = fromIntegral contractions / fromIntegral wordCount
          pronounRate = fromIntegral (firstPerson + secondPerson) / fromIntegral wordCount
          
          -- Higher contraction rate = less formal
          contractionPenalty = min 1.0 (contractionRate * 20)
          
          -- Higher pronoun rate = less formal
          pronounPenalty = min 1.0 (pronounRate * 10)
          
          -- Base formality (inverted penalties)
          score = 1.0 - (contractionPenalty * 0.4 + pronounPenalty * 0.6)
      in max 0 (min 1 score)
