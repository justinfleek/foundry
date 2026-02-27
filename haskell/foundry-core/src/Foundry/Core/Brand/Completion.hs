{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // foundry // brand/completion
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Completion
Description : LLM completion prompts for brand fields that can't be scraped
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Brands don't explicitly state what they ARE and AREN'T. This module encodes
25 years of strategic brand consulting expertise into prompt templates that
guide LLMs to infer:

1. IS/NOT voice constraints from text samples
2. Brand values from content analysis
3. Target customer psychographics
4. Strategic positioning

== Design Philosophy

The prompts encode Justin's expertise:

> "brands dont typically say what they are and arent, that is distilled from 
> my 25 yrs as a strategic brand consultant"

The LLM acts as a junior consultant receiving structured guidance from a
senior expert (the prompt template). The prompts constrain the LLM's output
to match the SMART framework schema.

== Invariants

* All prompts produce JSON output matching SMART framework types
* Prompts include explicit IS/NOT pairing requirement
* Confidence is always self-reported by the LLM
* Every completion includes reasoning (chain of thought)

== Dependencies

Requires: Foundry.Core.Brand.Voice, Foundry.Core.Brand.Source
Required by: LLM completion pipeline

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Completion
  ( -- * Prompt Templates
    CompletionPrompt (..)
  , PromptContext (..)
  
    -- * Voice Completion
  , voiceConstraintsPrompt
  , voiceSummaryPrompt
  
    -- * Strategy Completion
  , brandValuesPrompt
  , targetCustomerPrompt
  , positioningPrompt
  
    -- * Response Parsing
  , CompletionResponse (..)
  , VoiceConstraintsResponse (..)
  , BrandValuesResponse (..)
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Prompt Types
--------------------------------------------------------------------------------

-- | Context provided to LLM for brand completion
data PromptContext = PromptContext
  { pcDomain      :: !Text
    -- ^ Brand domain (e.g., "stripe.com")
  , pcTitle       :: !(Maybe Text)
    -- ^ Page title
  , pcHeadings    :: ![Text]
    -- ^ H1-H6 headings extracted
  , pcParagraphs  :: ![Text]
    -- ^ Sample paragraphs (first N)
  , pcButtonTexts :: ![Text]
    -- ^ CTA/button text
  , pcNavItems    :: ![Text]
    -- ^ Navigation items
  , pcColors      :: ![Text]
    -- ^ Primary colors (hex)
  , pcFonts       :: ![Text]
    -- ^ Font families detected
  }
  deriving stock (Eq, Show, Generic)

-- | A completion prompt with its template and expected output schema
data CompletionPrompt = CompletionPrompt
  { cpName        :: !Text
    -- ^ Prompt identifier
  , cpTemplate    :: !Text
    -- ^ The prompt template (with placeholders)
  , cpOutputSchema :: !Text
    -- ^ JSON schema the LLM should produce
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Voice Completion Prompts
--------------------------------------------------------------------------------

-- | Prompt for inferring IS/NOT voice constraints
--
-- This is THE MOST IMPORTANT completion. The IS/NOT pattern converts
-- subjective tone guidance into enforceable AI constraints.
voiceConstraintsPrompt :: PromptContext -> CompletionPrompt
voiceConstraintsPrompt ctx = CompletionPrompt
  { cpName = "voice-constraints"
  , cpTemplate = T.unlines
      [ "You are a senior brand strategist with 25 years of experience."
      , "Analyze the following brand content and infer the voice constraints."
      , ""
      , "CRITICAL: Every brand voice attribute MUST have BOTH:"
      , "1. IS descriptors - what the voice IS (3-5 adjectives)"
      , "2. NOT descriptors - what the voice is NOT (3-5 adjectives)"
      , ""
      , "The IS/NOT pattern is the most enforceable element of brand voice."
      , "It converts subjective guidance into AI-enforceable constraints."
      , ""
      , "== Brand Content =="
      , "Domain: " <> pcDomain ctx
      , "Title: " <> maybe "(not found)" id (pcTitle ctx)
      , ""
      , "Headlines:"
      , formatList (pcHeadings ctx)
      , ""
      , "Sample Text:"
      , formatList (take 5 (pcParagraphs ctx))
      , ""
      , "Call-to-Action Text:"
      , formatList (pcButtonTexts ctx)
      , ""
      , "Visual Context:"
      , "- Colors: " <> T.intercalate ", " (pcColors ctx)
      , "- Fonts: " <> T.intercalate ", " (pcFonts ctx)
      , ""
      , "== Instructions =="
      , "Based on this content, identify 3-5 voice attributes."
      , "For each attribute, provide:"
      , "1. attribute_name: The quality (e.g., \"Authoritative\", \"Approachable\")"
      , "2. is: List of 3-5 descriptors for what it IS"
      , "3. is_not: List of 3-5 descriptors for what it is NOT"
      , "4. evidence: Quote from the content that supports this"
      , "5. confidence: 0.0-1.0 how certain you are"
      , ""
      , "== Common IS/NOT Patterns =="
      , "Authoritative IS: knowledgeable, trusted, confident, credible"
      , "Authoritative NOT: overbearing, pompous, condescending"
      , ""
      , "Approachable IS: friendly, engaging, warm, conversational"
      , "Approachable NOT: overly casual, unprofessional, patronizing"
      , ""
      , "Innovative IS: creative, visionary, cutting edge, progressive"
      , "Innovative NOT: impractical, unrealistic, full of hype words"
      , ""
      , "Professional IS: competent, reliable, precise, clear"
      , "Professional NOT: stiff, bureaucratic, jargon-heavy, cold"
      , ""
      , "Respond with valid JSON only, matching the schema below."
      ]
  , cpOutputSchema = T.unlines
      [ "{"
      , "  \"attributes\": ["
      , "    {"
      , "      \"attribute_name\": \"string\","
      , "      \"is\": [\"string\", \"string\", \"string\"],"
      , "      \"is_not\": [\"string\", \"string\", \"string\"],"
      , "      \"evidence\": \"string\","
      , "      \"confidence\": number"
      , "    }"
      , "  ],"
      , "  \"overall_confidence\": number,"
      , "  \"reasoning\": \"string\""
      , "}"
      ]
  }

-- | Prompt for inferring voice summary (overarching principle)
voiceSummaryPrompt :: PromptContext -> CompletionPrompt
voiceSummaryPrompt ctx = CompletionPrompt
  { cpName = "voice-summary"
  , cpTemplate = T.unlines
      [ "You are a senior brand strategist."
      , "Based on the content below, write a single-sentence voice summary."
      , ""
      , "A voice summary is the overarching principle for how the brand communicates."
      , "Example: \"Cohesive, consistent, relevant across all touchpoints\""
      , ""
      , "Domain: " <> pcDomain ctx
      , "Headlines: " <> T.intercalate " | " (take 5 (pcHeadings ctx))
      , "Sample text: " <> T.intercalate " " (take 3 (pcParagraphs ctx))
      , ""
      , "Respond with JSON: {\"summary\": \"...\", \"confidence\": 0.0-1.0}"
      ]
  , cpOutputSchema = "{\"summary\": \"string\", \"confidence\": number}"
  }

--------------------------------------------------------------------------------
-- Strategy Completion Prompts
--------------------------------------------------------------------------------

-- | Prompt for inferring brand values
brandValuesPrompt :: PromptContext -> CompletionPrompt
brandValuesPrompt ctx = CompletionPrompt
  { cpName = "brand-values"
  , cpTemplate = T.unlines
      [ "You are a senior brand strategist."
      , "Analyze the content and identify the brand's core values."
      , ""
      , "Values are the principles that inform every decision, design, and communication."
      , "They should be ordered by importance (most important first)."
      , ""
      , "Domain: " <> pcDomain ctx
      , "Content: " <> T.intercalate " " (take 10 (pcParagraphs ctx))
      , ""
      , "Identify 3-6 values. For each:"
      , "1. value: The value name (e.g., \"Innovation\", \"Security\")"
      , "2. evidence: Text that demonstrates this value"
      , "3. confidence: 0.0-1.0"
      , ""
      , "Respond with valid JSON matching the schema."
      ]
  , cpOutputSchema = T.unlines
      [ "{"
      , "  \"values\": ["
      , "    {\"value\": \"string\", \"evidence\": \"string\", \"confidence\": number}"
      , "  ],"
      , "  \"overall_confidence\": number"
      , "}"
      ]
  }

-- | Prompt for inferring target customer psychographics
targetCustomerPrompt :: PromptContext -> CompletionPrompt
targetCustomerPrompt ctx = CompletionPrompt
  { cpName = "target-customer"
  , cpTemplate = T.unlines
      [ "You are a senior brand strategist."
      , "Identify the target customer segments from this brand's content."
      , ""
      , "For each segment, define:"
      , "1. segment_name: Descriptive label (e.g., \"Early Adopters & Innovators\")"
      , "2. description: Who they are and what drives them"
      , "3. motivations: What attracts them to brands in this category"
      , "4. language_calibration: How content should be adjusted for them"
      , ""
      , "Domain: " <> pcDomain ctx
      , "Headlines: " <> T.intercalate " | " (pcHeadings ctx)
      , "Navigation: " <> T.intercalate " | " (pcNavItems ctx)
      , "CTAs: " <> T.intercalate " | " (pcButtonTexts ctx)
      , ""
      , "Identify 2-4 segments. Respond with valid JSON."
      ]
  , cpOutputSchema = T.unlines
      [ "{"
      , "  \"segments\": ["
      , "    {"
      , "      \"segment_name\": \"string\","
      , "      \"description\": \"string\","
      , "      \"motivations\": [\"string\"],"
      , "      \"language_calibration\": \"string\""
      , "    }"
      , "  ],"
      , "  \"overall_confidence\": number"
      , "}"
      ]
  }

-- | Prompt for inferring strategic positioning
positioningPrompt :: PromptContext -> CompletionPrompt
positioningPrompt ctx = CompletionPrompt
  { cpName = "positioning"
  , cpTemplate = T.unlines
      [ "You are a senior brand strategist."
      , "Determine how this brand positions itself relative to users."
      , ""
      , "Positioning options:"
      , "- Ally: We're on your side, we help you"
      , "- Guide: We show you the way, we have expertise"
      , "- Facilitator: We make it easy, we remove friction"
      , "- Authority: We know best, trust us"
      , "- Peer: We're just like you"
      , "- Challenger: We disrupt, we're different"
      , ""
      , "Domain: " <> pcDomain ctx
      , "Headline style: " <> T.intercalate " | " (take 3 (pcHeadings ctx))
      , "CTA language: " <> T.intercalate " | " (pcButtonTexts ctx)
      , ""
      , "Choose primary and secondary positioning. Explain your reasoning."
      ]
  , cpOutputSchema = T.unlines
      [ "{"
      , "  \"primary_position\": \"string\","
      , "  \"secondary_position\": \"string\","
      , "  \"reasoning\": \"string\","
      , "  \"confidence\": number"
      , "}"
      ]
  }

--------------------------------------------------------------------------------
-- Response Types
--------------------------------------------------------------------------------

-- | Generic LLM completion response
data CompletionResponse = CompletionResponse
  { crRawJSON   :: !Text
    -- ^ Raw JSON from LLM
  , crParsed    :: !(Maybe Text)
    -- ^ Parsed and validated (or Nothing if parse failed)
  , crConfidence :: !Double
    -- ^ Self-reported confidence
  }
  deriving stock (Eq, Show, Generic)

-- | Parsed voice constraints response
data VoiceConstraintsResponse = VoiceConstraintsResponse
  { vcrAttributes :: ![(Text, [Text], [Text], Text, Double)]
    -- ^ (name, is, is_not, evidence, confidence)
  , vcrOverallConfidence :: !Double
  , vcrReasoning :: !Text
  }
  deriving stock (Eq, Show, Generic)

-- | Parsed brand values response
data BrandValuesResponse = BrandValuesResponse
  { bvrValues :: ![(Text, Text, Double)]
    -- ^ (value, evidence, confidence)
  , bvrOverallConfidence :: !Double
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

formatList :: [Text] -> Text
formatList [] = "(none found)"
formatList xs = T.intercalate "\n" (zipWith formatItem [1..] xs)
  where
    formatItem :: Int -> Text -> Text
    formatItem n t = T.pack (show n) <> ". " <> T.take 200 t
