{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // foundry // extract // voice/tone
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Voice.Tone
Description : Tone detection from text analysis
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Maps text analysis features to brand tone categories.

== Tone Categories

* Formal - Long sentences, no contractions, third person
* Casual - Short sentences, contractions, first/second person
* Professional - Balanced, moderate formality
* Friendly - Second person, warm language
* Authoritative - Declarative, confident language
* Playful - Short sentences, exclamations, informal

== Dependencies

Requires: Foundry.Extract.Voice.NLP, Foundry.Core.Brand.Voice
Required by: Foundry.Extract.Voice

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Voice.Tone
  ( -- * Detection
    detectTone
  , detectTraits
  , ToneDetection (..)

    -- * Scoring
  , scoreTones
  , ToneScore (..)
  ) where

import Data.List (sortBy)
import Data.Ord (Down (..), comparing)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T

import Foundry.Core.Brand.Voice (Tone (..), Trait (..))
import Foundry.Extract.Voice.NLP (TextAnalysis (..))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Result of tone detection
data ToneDetection = ToneDetection
  { tdPrimaryTone   :: !Tone
    -- ^ Primary detected tone
  , tdSecondaryTone :: !(Maybe Tone)
    -- ^ Secondary tone (if present)
  , tdConfidence    :: !Double
    -- ^ Confidence in detection [0, 1]
  , tdScores        :: ![ToneScore]
    -- ^ Scores for all tones
  }
  deriving stock (Eq, Show)

-- | Score for a specific tone
data ToneScore = ToneScore
  { tssTone  :: !Tone
  , tssScore :: !Double
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Detection
--------------------------------------------------------------------------------

-- | Detect the primary tone from text analysis
detectTone :: TextAnalysis -> ToneDetection
detectTone analysis =
  let scores = scoreTones analysis
      sorted = sortBy (comparing (Down . tssScore)) scores
      primary = case sorted of
        (s:_) -> tssTone s
        []    -> Professional  -- Default
      secondary = case sorted of
        (_:s:_) | tssScore s > 0.3 -> Just (tssTone s)
        _ -> Nothing
      confidence = case sorted of
        (s:_) -> tssScore s
        []    -> 0.5
  in ToneDetection
       { tdPrimaryTone = primary
       , tdSecondaryTone = secondary
       , tdConfidence = confidence
       , tdScores = scores
       }

-- | Calculate scores for all tones
scoreTones :: TextAnalysis -> [ToneScore]
scoreTones analysis =
  [ ToneScore Formal (scoreFormal analysis)
  , ToneScore Casual (scoreCasual analysis)
  , ToneScore Professional (scoreProfessional analysis)
  , ToneScore Friendly (scoreFriendly analysis)
  , ToneScore Authoritative (scoreAuthoritative analysis)
  , ToneScore Playful (scorePlayful analysis)
  ]

-- | Score for Formal tone
scoreFormal :: TextAnalysis -> Double
scoreFormal analysis =
  let formalityWeight = taFormality analysis * 0.5
      longSentences = if taAvgSentenceLen analysis > 20 then 0.3 else 0
      noContractions = if taContractions analysis == 0 then 0.2 else 0
  in min 1 (formalityWeight + longSentences + noContractions)

-- | Score for Casual tone
scoreCasual :: TextAnalysis -> Double
scoreCasual analysis =
  let informalityWeight = (1 - taFormality analysis) * 0.4
      shortSentences = if taAvgSentenceLen analysis < 12 then 0.3 else 0
      hasContractions = if taContractions analysis > 2 then 0.3 else 0
  in min 1 (informalityWeight + shortSentences + hasContractions)

-- | Score for Professional tone
scoreProfessional :: TextAnalysis -> Double
scoreProfessional analysis =
  let -- Professional is balanced formality
      balancedFormality = 1 - abs (taFormality analysis - 0.6) * 2
      moderateSentences = if taAvgSentenceLen analysis >= 12 && taAvgSentenceLen analysis <= 20
                          then 0.3 else 0
      -- Not too many pronouns
      pronounRatio = fromIntegral (taFirstPerson analysis + taSecondPerson analysis) 
                     / max 1 (fromIntegral (taWordCount analysis))
      lowPronouns = if pronounRatio < 0.05 then 0.2 else 0
  in min 1 (max 0 balancedFormality * 0.5 + moderateSentences + lowPronouns)

-- | Score for Friendly tone
scoreFriendly :: TextAnalysis -> Double
scoreFriendly analysis =
  let -- Second person pronouns indicate direct address
      secondPersonRatio = fromIntegral (taSecondPerson analysis) 
                          / max 1 (fromIntegral (taWordCount analysis))
      secondPersonScore = min 0.5 (secondPersonRatio * 10)
      
      -- Moderate formality
      moderateFormality = if taFormality analysis > 0.3 && taFormality analysis < 0.7
                          then 0.3 else 0
      
      -- Some contractions
      someContractions = if taContractions analysis > 0 && taContractions analysis < 5
                         then 0.2 else 0
  in min 1 (secondPersonScore + moderateFormality + someContractions)

-- | Score for Authoritative tone
scoreAuthoritative :: TextAnalysis -> Double
scoreAuthoritative analysis =
  let -- High formality
      formalScore = if taFormality analysis > 0.7 then 0.4 else taFormality analysis * 0.3
      
      -- Longer sentences
      longSentences = if taAvgSentenceLen analysis > 15 then 0.3 else 0
      
      -- Few personal pronouns
      pronounRatio = fromIntegral (taFirstPerson analysis + taSecondPerson analysis) 
                     / max 1 (fromIntegral (taWordCount analysis))
      fewPronouns = if pronounRatio < 0.03 then 0.3 else 0
  in min 1 (formalScore + longSentences + fewPronouns)

-- | Score for Playful tone
scorePlayful :: TextAnalysis -> Double
scorePlayful analysis =
  let -- Low formality
      informalScore = (1 - taFormality analysis) * 0.3
      
      -- Short sentences
      shortSentences = if taAvgSentenceLen analysis < 10 then 0.3 else 0
      
      -- Lots of contractions
      manyContractions = if taContractions analysis > 3 then 0.2 else 0
      
      -- First person (we're having fun!)
      firstPersonRatio = fromIntegral (taFirstPerson analysis) 
                         / max 1 (fromIntegral (taWordCount analysis))
      firstPersonScore = min 0.2 (firstPersonRatio * 5)
  in min 1 (informalScore + shortSentences + manyContractions + firstPersonScore)

--------------------------------------------------------------------------------
-- Trait Detection
--------------------------------------------------------------------------------

-- | Detect personality traits from text analysis
detectTraits :: TextAnalysis -> Set Trait
detectTraits analysis =
  let scores = scoreTones analysis
      -- Map high-scoring tones to traits
      traits = concatMap toneToTraits $ filter ((> 0.4) . tssScore) scores
  in Set.fromList traits

-- | Map tone to associated traits
toneToTraits :: ToneScore -> [Trait]
toneToTraits (ToneScore tone score)
  | score < 0.4 = []
  | otherwise = case tone of
      Formal -> [Trait "sophisticated", Trait "trustworthy"]
      Casual -> [Trait "approachable", Trait "relaxed"]
      Professional -> [Trait "competent", Trait "reliable"]
      Friendly -> [Trait "warm", Trait "welcoming"]
      Authoritative -> [Trait "confident", Trait "expert"]
      Playful -> [Trait "fun", Trait "energetic"]
