{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // foundry // extract // voice
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Voice
Description : Voice extraction from scraped content
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Extracts brand voice from text content.

== Pipeline

1. Collect text from headings, paragraphs, buttons, navigation
2. Analyze text for NLP features (sentence length, formality, etc.)
3. Detect primary and secondary tones
4. Extract personality traits
5. Build vocabulary (preferred/avoided words)

== Dependencies

Requires: Foundry.Extract.Types, Foundry.Extract.Voice.*
Required by: Foundry.Extract.Compose

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Voice
  ( -- * Extraction
    extractVoice
  , VoiceExtractionResult (..)

    -- * Re-exports
  , module Foundry.Extract.Voice.NLP
  , module Foundry.Extract.Voice.Tone
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V

import Foundry.Core.Brand.Voice
  ( BrandVoice (..)
  , Tone (..)
  , Trait (..)
  , TraitSet (..)
  , Vocabulary (..)
  , VoiceSummary (..)
  , ToneAttribute (..)
  , ToneConstraint (..)
  , ToneDescriptor (..)
  )
import Foundry.Extract.Types
  ( ExtractionWarning (..)
  , ScrapeResult (..)
  , TextBlock (..)
  , TextContent (..)
  )
import Foundry.Extract.Voice.NLP
import Foundry.Extract.Voice.Tone

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Result of voice extraction
data VoiceExtractionResult = VoiceExtractionResult
  { verVoice      :: !BrandVoice
    -- ^ Extracted brand voice
  , verAnalysis   :: !TextAnalysis
    -- ^ Text analysis details
  , verTone       :: !ToneDetection
    -- ^ Tone detection details
  , verWarnings   :: ![ExtractionWarning]
    -- ^ Extraction warnings
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Extraction
--------------------------------------------------------------------------------

-- | Extract brand voice from scrape result
extractVoice :: ScrapeResult -> VoiceExtractionResult
extractVoice sr =
  let -- Collect all text content
      allText = collectText (srTextContent sr)
      
      -- Analyze text
      analysis = analyzeText allText
      
      -- Detect tone
      toneResult = detectTone analysis
      
      -- Extract traits
      traits = detectTraits analysis
      
      -- Build vocabulary
      vocabulary = extractVocabulary analysis
      
      -- Build BrandVoice with IS/NOT constraints
      -- Generate default voice summary from detected tone
      voiceSummary = VoiceSummary $ T.concat
        [ "Voice characterized by "
        , T.toLower (T.pack (show (tdPrimaryTone toneResult)))
        , " tone across all touchpoints"
        ]
      
      -- Generate tone attributes with IS/NOT constraints from detected tones
      toneAttrs = buildToneAttributes toneResult
      
      voice = BrandVoice
        { brandVoiceSummary = voiceSummary
        , brandVoiceAttributes = toneAttrs
        , brandVoiceTone = tdPrimaryTone toneResult
        , brandVoiceTraits = TraitSet (ensureNonEmpty traits)
        , brandVoiceVocabulary = vocabulary
        }
      
      -- Warnings
      warnings = if taWordCount analysis < 50
                 then [WarnFewTextSamples (taWordCount analysis)]
                 else []
  in VoiceExtractionResult
       { verVoice = voice
       , verAnalysis = analysis
       , verTone = toneResult
       , verWarnings = warnings
       }

-- | Build tone attributes with IS/NOT constraints from detected tones
-- 
-- This implements the SMART Framework's most enforceable element:
-- IS/NOT constraint pairs that define what the tone IS and is NOT.
buildToneAttributes :: ToneDetection -> Vector ToneAttribute
buildToneAttributes toneResult =
  let primary = tdPrimaryTone toneResult
      attrs = case primary of
        Formal -> 
          [ ToneAttribute "Formal" $ ToneConstraint
              { constraintIs = Set.fromList [ToneDescriptor "professional", ToneDescriptor "polished", ToneDescriptor "structured"]
              , constraintNot = Set.fromList [ToneDescriptor "casual", ToneDescriptor "slang", ToneDescriptor "colloquial"]
              }
          ]
        Casual ->
          [ ToneAttribute "Casual" $ ToneConstraint
              { constraintIs = Set.fromList [ToneDescriptor "relaxed", ToneDescriptor "conversational", ToneDescriptor "approachable"]
              , constraintNot = Set.fromList [ToneDescriptor "stiff", ToneDescriptor "formal", ToneDescriptor "distant"]
              }
          ]
        Professional ->
          [ ToneAttribute "Professional" $ ToneConstraint
              { constraintIs = Set.fromList [ToneDescriptor "competent", ToneDescriptor "reliable", ToneDescriptor "expert"]
              , constraintNot = Set.fromList [ToneDescriptor "amateur", ToneDescriptor "unprepared", ToneDescriptor "careless"]
              }
          ]
        Friendly ->
          [ ToneAttribute "Friendly" $ ToneConstraint
              { constraintIs = Set.fromList [ToneDescriptor "warm", ToneDescriptor "welcoming", ToneDescriptor "personable"]
              , constraintNot = Set.fromList [ToneDescriptor "cold", ToneDescriptor "distant", ToneDescriptor "impersonal"]
              }
          ]
        Authoritative ->
          [ ToneAttribute "Authoritative" $ ToneConstraint
              { constraintIs = Set.fromList [ToneDescriptor "knowledgeable", ToneDescriptor "trusted", ToneDescriptor "confident", ToneDescriptor "credible"]
              , constraintNot = Set.fromList [ToneDescriptor "overbearing", ToneDescriptor "pompous", ToneDescriptor "condescending"]
              }
          ]
        Playful ->
          [ ToneAttribute "Playful" $ ToneConstraint
              { constraintIs = Set.fromList [ToneDescriptor "fun", ToneDescriptor "lighthearted", ToneDescriptor "energetic"]
              , constraintNot = Set.fromList [ToneDescriptor "serious", ToneDescriptor "heavy", ToneDescriptor "dull"]
              }
          ]
  in V.fromList attrs

-- | Collect all text from TextContent
collectText :: TextContent -> Text
collectText tc = T.intercalate " " $ concat
  [ maybeToList (tcTitle tc)
  , V.toList $ V.map tbText (tcHeadings tc)
  , V.toList $ V.map tbText (tcParagraphs tc)
  , V.toList $ V.map tbText (tcButtons tc)
  , V.toList $ V.map tbText (tcNavigation tc)
  , V.toList $ V.map tbText (tcFooter tc)
  ]

maybeToList :: Maybe a -> [a]
maybeToList Nothing = []
maybeToList (Just x) = [x]

-- | Ensure trait set is non-empty
ensureNonEmpty :: Set Trait -> Set Trait
ensureNonEmpty s
  | Set.null s = Set.singleton (Trait "authentic")  -- Default trait
  | otherwise = s

-- | Extract vocabulary from text analysis
extractVocabulary :: TextAnalysis -> Vocabulary
extractVocabulary analysis =
  let wordFreq = taWordFrequency analysis
      -- Preferred: high-frequency content words
      preferred = extractPreferredWords wordFreq
      -- Avoided: empty for now (would need negative examples)
      avoided = Set.empty
  in Vocabulary preferred avoided

-- | Extract preferred words from frequency map
extractPreferredWords :: Map Text Int -> Set Text
extractPreferredWords wordFreq =
  let -- Filter out stop words and low-frequency words
      filtered = Map.filterWithKey (\w c -> c >= 2 && not (isStopWord w)) wordFreq
      -- Take top 20 by frequency
      sorted = take 20 $ Map.toDescList filtered
  in Set.fromList $ map fst sorted

-- | Check if word is a stop word
isStopWord :: Text -> Bool
isStopWord w = T.toLower w `Set.member` stopWords

stopWords :: Set Text
stopWords = Set.fromList
  [ "the", "a", "an", "and", "or", "but", "in", "on", "at", "to", "for"
  , "of", "with", "by", "from", "as", "is", "was", "are", "were", "been"
  , "be", "have", "has", "had", "do", "does", "did", "will", "would", "could"
  , "should", "may", "might", "must", "shall", "can", "this", "that", "these"
  , "those", "it", "its", "they", "them", "their", "we", "us", "our", "you"
  , "your", "i", "me", "my", "he", "him", "his", "she", "her", "not", "no"
  , "all", "each", "every", "both", "few", "more", "most", "other", "some"
  , "such", "only", "own", "same", "so", "than", "too", "very", "just"
  , "also", "now", "here", "there", "when", "where", "why", "how", "what"
  , "which", "who", "whom", "whose", "if", "then", "else", "because"
  , "while", "although", "though", "until", "unless", "since", "after"
  , "before", "about", "into", "through", "during", "above", "below"
  , "between", "under", "again", "further", "once", "any", "up", "down"
  , "out", "off", "over", "under", "again", "then", "once", "here", "there"
  ]
