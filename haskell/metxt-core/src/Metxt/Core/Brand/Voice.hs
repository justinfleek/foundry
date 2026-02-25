{- |
Module      : Metxt.Core.Brand.Voice
Description : Brand voice and tone types
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Brand voice, tone, and vocabulary definitions.
-}
module Metxt.Core.Brand.Voice
  ( -- * Types
    Tone (..)
  , Trait (..)
  , TraitSet (..)
  , Vocabulary (..)
  , BrandVoice (..)
  ) where

import Data.Set (Set)
import Data.Text (Text)

-- | Voice tone
data Tone
  = Formal
  | Casual
  | Professional
  | Friendly
  | Authoritative
  | Playful
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | Personality trait
newtype Trait = Trait {unTrait :: !Text}
  deriving stock (Eq, Ord, Show)

-- | Set of traits (non-empty)
newtype TraitSet = TraitSet {unTraitSet :: !(Set Trait)}
  deriving stock (Eq, Show)

-- | Vocabulary constraints
data Vocabulary = Vocabulary
  { vocabularyPreferred :: !(Set Text)   -- ^ Words to use
  , vocabularyAvoided :: !(Set Text)     -- ^ Words to avoid
  }
  deriving stock (Eq, Show)

-- | Complete brand voice specification
data BrandVoice = BrandVoice
  { brandVoiceTone :: !Tone
  , brandVoiceTraits :: !TraitSet
  , brandVoiceVocabulary :: !Vocabulary
  }
  deriving stock (Eq, Show)
