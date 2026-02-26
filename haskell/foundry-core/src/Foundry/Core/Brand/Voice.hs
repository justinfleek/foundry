{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                         // foundry // brand/voice
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Voice
Description : Brand voice and tone types with IS/NOT constraints
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Brand voice, tone, and vocabulary definitions following the SMART Framework.

== SMART Framework Section 6: Voice & Tone

The IS/NOT constraint pattern is THE MOST ENFORCEABLE element of any brand guide.
It converts subjective tone guidance into system-level AI constraints.

Example:
  Authoritative IS: knowledgeable, trusted, confident, credible
  Authoritative NOT: overbearing, pompous, condescending

== Invariants

* Every ToneAttribute has at least one IS and one NOT descriptor
* IS and NOT sets are disjoint (no overlap)
* VoiceSummary is non-empty

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Voice
  ( -- * IS/NOT Constraints (CRITICAL)
    ToneDescriptor (..)
  , mkToneDescriptor
  , ToneConstraint (..)
  , mkToneConstraint
  , ToneAttribute (..)
  , mkToneAttribute
  
    -- * Voice Summary
  , VoiceSummary (..)
  , mkVoiceSummary
  
    -- * Legacy Types (for compatibility)
  , Tone (..)
  , Trait (..)
  , TraitSet (..)
  , Vocabulary (..)
  
    -- * Complete Voice Specification
  , BrandVoice (..)
  , mkBrandVoice
  ) where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V

--------------------------------------------------------------------------------
-- IS/NOT Constraint System (SMART Framework Section 6)
--------------------------------------------------------------------------------

-- | A single tone descriptor (e.g., "knowledgeable", "pompous")
newtype ToneDescriptor = ToneDescriptor {unToneDescriptor :: Text}
  deriving stock (Eq, Ord, Show)

-- | Create tone descriptor with validation
mkToneDescriptor :: Text -> Maybe ToneDescriptor
mkToneDescriptor t
  | T.length t >= 1 = Just (ToneDescriptor (T.toLower (T.strip t)))
  | otherwise = Nothing

-- | IS/NOT constraint pair - the core enforcement mechanism
-- 
-- From SMART Framework:
-- "The IS/NOT pattern is the most valuable part of any brand voice specification.
-- It converts subjective tone guidance into enforceable constraints."
data ToneConstraint = ToneConstraint
  { constraintIs  :: !(Set ToneDescriptor)  -- ^ What this attribute IS
  , constraintNot :: !(Set ToneDescriptor)  -- ^ What this attribute is NOT
  }
  deriving stock (Eq, Show)

-- | Create IS/NOT constraint with invariant: sets must be disjoint
mkToneConstraint :: Set ToneDescriptor -> Set ToneDescriptor -> Maybe ToneConstraint
mkToneConstraint is notSet
  | Set.null is = Nothing  -- Must have at least one IS
  | Set.null notSet = Nothing  -- Must have at least one NOT
  | not (Set.disjoint is notSet) = Nothing  -- No overlap allowed
  | otherwise = Just ToneConstraint
      { constraintIs = is
      , constraintNot = notSet
      }

-- | A named tone attribute with its IS/NOT constraints
--
-- Example from SMART Framework:
--   Attribute: "Authoritative"
--   IS: knowledgeable, trusted, confident, credible
--   NOT: overbearing, pompous, condescending
data ToneAttribute = ToneAttribute
  { attributeName       :: !Text            -- ^ e.g., "Authoritative", "Approachable"
  , attributeConstraint :: !ToneConstraint  -- ^ The IS/NOT pair
  }
  deriving stock (Eq, Show)

-- | Create tone attribute with validation
mkToneAttribute :: Text -> ToneConstraint -> Maybe ToneAttribute
mkToneAttribute name constraint
  | T.length name >= 1 = Just ToneAttribute
      { attributeName = name
      , attributeConstraint = constraint
      }
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Voice Summary
--------------------------------------------------------------------------------

-- | Overarching voice principle
-- 
-- From SMART Framework:
-- "The overarching principle (e.g., 'cohesive, consistent, relevant across all touchpoints')"
newtype VoiceSummary = VoiceSummary {unVoiceSummary :: Text}
  deriving stock (Eq, Show)

-- | Create voice summary with validation (non-empty)
mkVoiceSummary :: Text -> Maybe VoiceSummary
mkVoiceSummary t
  | T.length (T.strip t) >= 1 = Just (VoiceSummary (T.strip t))
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Legacy Types (for backward compatibility)
--------------------------------------------------------------------------------

-- | Voice tone (coarse classification)
data Tone
  = Formal
  | Casual
  | Professional
  | Friendly
  | Authoritative
  | Playful
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | Personality trait
newtype Trait = Trait {unTrait :: Text}
  deriving stock (Eq, Ord, Show)

-- | Set of traits (non-empty)
newtype TraitSet = TraitSet {unTraitSet :: Set Trait}
  deriving stock (Eq, Show)

-- | Vocabulary constraints (preferred/avoided words)
data Vocabulary = Vocabulary
  { vocabularyPreferred :: !(Set Text)   -- ^ Words to use
  , vocabularyAvoided   :: !(Set Text)   -- ^ Words to avoid
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Complete Brand Voice Specification
--------------------------------------------------------------------------------

-- | Complete brand voice specification following SMART Framework Section 6
data BrandVoice = BrandVoice
  { brandVoiceSummary    :: !VoiceSummary           -- ^ Overarching voice principle
  , brandVoiceAttributes :: !(Vector ToneAttribute) -- ^ IS/NOT constrained attributes
  , brandVoiceTone       :: !Tone                   -- ^ Coarse tone classification
  , brandVoiceTraits     :: !TraitSet               -- ^ Personality traits
  , brandVoiceVocabulary :: !Vocabulary             -- ^ Word constraints
  }
  deriving stock (Eq, Show)

-- | Create brand voice with validation
mkBrandVoice
  :: VoiceSummary
  -> Vector ToneAttribute
  -> Tone
  -> TraitSet
  -> Vocabulary
  -> Maybe BrandVoice
mkBrandVoice summary attrs tone traits vocab
  | V.length attrs >= 1 = Just BrandVoice
      { brandVoiceSummary = summary
      , brandVoiceAttributes = attrs
      , brandVoiceTone = tone
      , brandVoiceTraits = traits
      , brandVoiceVocabulary = vocab
      }
  | otherwise = Nothing  -- Must have at least one tone attribute
