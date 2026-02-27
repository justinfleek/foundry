{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                         // foundry // brand/source
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Source
Description : Field-level provenance tracking for brand data
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Every field in a Brand has a source: scraped, inferred, LLM-completed, 
manual, or default. This module provides the 'Sourced' wrapper that tracks
provenance at the field level.

== Design Rationale

Brands encode 25 years of strategic consulting expertise. Much of that
expertise (voice constraints, IS/NOT pairs, strategic positioning) cannot
be directly scraped from HTML. This module enables:

1. Distinguish scraped data from inferred data from LLM completions
2. Flag fields that need human review
3. Track confidence levels for each field
4. Maintain audit trails for brand compliance

== Invariants

* All confidence values are in [0, 1]
* needsReview = True implies either Default or low-confidence LLMCompleted
* Scraped sources always have a selector

== Dependencies

Requires: Foundry.Core.Brand.Provenance
Required by: All Brand molecule types, Foundry.Extract.*

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Source
  ( -- * Source Types
    Source (..)
  , ScrapedMeta (..)
  , InferredMeta (..)
  , LLMMeta (..)
  , ManualMeta (..)
  , DefaultMeta (..)
  
    -- * Sourced Wrapper
  , Sourced (..)
  , mkSourced
  , mkScraped
  , mkInferred
  , mkLLMCompleted
  , mkManual
  , mkDefault
  
    -- * Queries
  , isScraped
  , isInferred
  , isLLMCompleted
  , isManual
  , isDefault
  , needsReview
  , confidence
  
    -- * Combinators
  , mapSourced
  , traverseSourced
  , promoteToManual
  ) where

import Data.Text (Text)
import Data.Time (UTCTime)
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Source Metadata Types
--------------------------------------------------------------------------------

-- | Metadata for scraped (directly extracted) values
data ScrapedMeta = ScrapedMeta
  { smSelector   :: !Text
    -- ^ CSS selector or DOM path that matched
  , smProperty   :: !Text
    -- ^ CSS property or attribute extracted (e.g., "color", "font-family")
  , smRawValue   :: !Text
    -- ^ Raw value before parsing/normalization
  , smConfidence :: !Double
    -- ^ Extraction confidence [0, 1]
  , smTimestamp  :: !UTCTime
    -- ^ When extraction occurred
  }
  deriving stock (Eq, Show, Generic)

-- | Metadata for inferred (computed from other data) values
data InferredMeta = InferredMeta
  { imMethod     :: !Text
    -- ^ Inference method (e.g., "k-means-clustering", "geometric-regression")
  , imInputs     :: ![Text]
    -- ^ Names of source fields that fed this inference
  , imConfidence :: !Double
    -- ^ Inference confidence [0, 1]
  , imTimestamp  :: !UTCTime
    -- ^ When inference occurred
  }
  deriving stock (Eq, Show, Generic)

-- | Metadata for LLM-completed values
--
-- These are fields that cannot be scraped directly and require
-- semantic understanding (e.g., IS/NOT voice constraints, brand values)
data LLMMeta = LLMMeta
  { lmModel       :: !Text
    -- ^ Model identifier (e.g., "claude-opus-4", "gpt-4")
  , lmPromptHash  :: !Text
    -- ^ SHA256 of the prompt template used (for reproducibility)
  , lmInputFields :: ![Text]
    -- ^ Names of fields provided as context to the LLM
  , lmConfidence  :: !Double
    -- ^ LLM's self-reported confidence [0, 1]
  , lmNeedsReview :: !Bool
    -- ^ Whether human review is required before use
  , lmTimestamp   :: !UTCTime
    -- ^ When completion occurred
  }
  deriving stock (Eq, Show, Generic)

-- | Metadata for manually provided values
data ManualMeta = ManualMeta
  { mmSource     :: !Text
    -- ^ Who provided this (e.g., "brand-guide-pdf", "client-interview")
  , mmReviewer   :: !(Maybe Text)
    -- ^ Who reviewed/approved this value
  , mmNotes      :: !(Maybe Text)
    -- ^ Additional context
  , mmTimestamp  :: !UTCTime
    -- ^ When manually entered
  }
  deriving stock (Eq, Show, Generic)

-- | Metadata for default (placeholder) values
--
-- Default values are used when no data is available. They ALWAYS
-- need review before the brand is considered complete.
data DefaultMeta = DefaultMeta
  { dmReason     :: !Text
    -- ^ Why this default was chosen (e.g., "no-css-colors-found")
  , dmSuggestion :: !(Maybe Text)
    -- ^ Suggested action to complete this field
  , dmTimestamp  :: !UTCTime
    -- ^ When default was applied
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Source ADT
--------------------------------------------------------------------------------

-- | How was this data obtained?
--
-- The source hierarchy (from most trusted to least):
--
-- 1. 'Manual' - Human-provided, reviewed
-- 2. 'Scraped' - Directly extracted from source
-- 3. 'Inferred' - Computed from scraped data
-- 4. 'LLMCompleted' - Filled by LLM analysis
-- 5. 'Default' - Placeholder, needs completion
data Source
  = Scraped !ScrapedMeta
    -- ^ Directly extracted from website/document
  | Inferred !InferredMeta
    -- ^ Computed from other scraped data
  | LLMCompleted !LLMMeta
    -- ^ Filled in by LLM analysis (requires review)
  | Manual !ManualMeta
    -- ^ Human-provided (highest trust)
  | Default !DefaultMeta
    -- ^ Sensible default, MUST be reviewed
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Sourced Wrapper
--------------------------------------------------------------------------------

-- | A value with its provenance tracked
--
-- Every field in a Brand compound should be wrapped in 'Sourced'
-- to enable:
--
-- * Audit trails (where did this come from?)
-- * Completion tracking (what's missing?)
-- * Confidence aggregation (how reliable is this brand?)
-- * Review workflows (what needs human verification?)
data Sourced a = Sourced
  { sourcedValue  :: !a
    -- ^ The actual value
  , sourcedSource :: !Source
    -- ^ How it was obtained
  }
  deriving stock (Eq, Show, Generic, Functor)

-- | Create a sourced value
mkSourced :: a -> Source -> Sourced a
mkSourced = Sourced

-- | Create a scraped value
mkScraped 
  :: a 
  -> Text      -- ^ Selector
  -> Text      -- ^ Property
  -> Text      -- ^ Raw value
  -> Double    -- ^ Confidence
  -> UTCTime   -- ^ Timestamp
  -> Sourced a
mkScraped val selector prop raw conf ts = Sourced val $ Scraped ScrapedMeta
  { smSelector = selector
  , smProperty = prop
  , smRawValue = raw
  , smConfidence = clampConfidence conf
  , smTimestamp = ts
  }

-- | Create an inferred value
mkInferred
  :: a
  -> Text      -- ^ Method
  -> [Text]    -- ^ Input field names
  -> Double    -- ^ Confidence
  -> UTCTime   -- ^ Timestamp
  -> Sourced a
mkInferred val method inputs conf ts = Sourced val $ Inferred InferredMeta
  { imMethod = method
  , imInputs = inputs
  , imConfidence = clampConfidence conf
  , imTimestamp = ts
  }

-- | Create an LLM-completed value
mkLLMCompleted
  :: a
  -> Text      -- ^ Model
  -> Text      -- ^ Prompt hash
  -> [Text]    -- ^ Input field names
  -> Double    -- ^ Confidence
  -> UTCTime   -- ^ Timestamp
  -> Sourced a
mkLLMCompleted val model promptHash inputs conf ts = Sourced val $ LLMCompleted LLMMeta
  { lmModel = model
  , lmPromptHash = promptHash
  , lmInputFields = inputs
  , lmConfidence = clampConfidence conf
  , lmNeedsReview = conf < 0.9  -- Auto-flag low-confidence completions
  , lmTimestamp = ts
  }

-- | Create a manual value
mkManual
  :: a
  -> Text           -- ^ Source description
  -> Maybe Text     -- ^ Reviewer
  -> Maybe Text     -- ^ Notes
  -> UTCTime        -- ^ Timestamp
  -> Sourced a
mkManual val src reviewer notes ts = Sourced val $ Manual ManualMeta
  { mmSource = src
  , mmReviewer = reviewer
  , mmNotes = notes
  , mmTimestamp = ts
  }

-- | Create a default value (ALWAYS needs review)
mkDefault
  :: a
  -> Text           -- ^ Reason for default
  -> Maybe Text     -- ^ Suggestion to complete
  -> UTCTime        -- ^ Timestamp
  -> Sourced a
mkDefault val reason suggestion ts = Sourced val $ Default DefaultMeta
  { dmReason = reason
  , dmSuggestion = suggestion
  , dmTimestamp = ts
  }

--------------------------------------------------------------------------------
-- Queries
--------------------------------------------------------------------------------

-- | Is this value directly scraped?
isScraped :: Sourced a -> Bool
isScraped (Sourced _ (Scraped _)) = True
isScraped _ = False

-- | Is this value inferred from other data?
isInferred :: Sourced a -> Bool
isInferred (Sourced _ (Inferred _)) = True
isInferred _ = False

-- | Is this value LLM-completed?
isLLMCompleted :: Sourced a -> Bool
isLLMCompleted (Sourced _ (LLMCompleted _)) = True
isLLMCompleted _ = False

-- | Is this value manually provided?
isManual :: Sourced a -> Bool
isManual (Sourced _ (Manual _)) = True
isManual _ = False

-- | Is this a default value (placeholder)?
isDefault :: Sourced a -> Bool
isDefault (Sourced _ (Default _)) = True
isDefault _ = False

-- | Does this value need human review before use?
needsReview :: Sourced a -> Bool
needsReview (Sourced _ src) = case src of
  Default _ -> True  -- Defaults ALWAYS need review
  LLMCompleted meta -> lmNeedsReview meta
  _ -> False

-- | Get confidence level for this value
--
-- Returns 1.0 for Manual (human-verified = full confidence)
-- Returns 0.0 for Default (placeholder = no confidence)
confidence :: Sourced a -> Double
confidence (Sourced _ src) = case src of
  Scraped meta -> smConfidence meta
  Inferred meta -> imConfidence meta
  LLMCompleted meta -> lmConfidence meta
  Manual _ -> 1.0  -- Human-verified = full confidence
  Default _ -> 0.0 -- Placeholder = no confidence

--------------------------------------------------------------------------------
-- Combinators
--------------------------------------------------------------------------------

-- | Map over the value while preserving source
mapSourced :: (a -> b) -> Sourced a -> Sourced b
mapSourced f (Sourced val src) = Sourced (f val) src

-- | Traverse the value while preserving source
traverseSourced :: Applicative f => (a -> f b) -> Sourced a -> f (Sourced b)
traverseSourced f (Sourced val src) = flip Sourced src <$> f val

-- | Promote an LLM-completed or inferred value to Manual after human review
promoteToManual 
  :: Text           -- ^ Reviewer name
  -> UTCTime        -- ^ Review timestamp
  -> Sourced a 
  -> Sourced a
promoteToManual reviewer ts (Sourced val src) = Sourced val $ Manual ManualMeta
  { mmSource = sourceDescription src
  , mmReviewer = Just reviewer
  , mmNotes = Just "Promoted after human review"
  , mmTimestamp = ts
  }

--------------------------------------------------------------------------------
-- Internal Helpers
--------------------------------------------------------------------------------

-- | Clamp confidence to [0, 1]
clampConfidence :: Double -> Double
clampConfidence c
  | c < 0 = 0
  | c > 1 = 1
  | otherwise = c

-- | Describe the original source (for audit trail when promoting)
sourceDescription :: Source -> Text
sourceDescription = \case
  Scraped meta -> "scraped:" <> smSelector meta
  Inferred meta -> "inferred:" <> imMethod meta
  LLMCompleted meta -> "llm:" <> lmModel meta
  Manual meta -> "manual:" <> mmSource meta
  Default meta -> "default:" <> dmReason meta
