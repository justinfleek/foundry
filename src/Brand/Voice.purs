-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // brand // voice
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brand voice and personality atoms and molecules.
-- |
-- | STATUS: PROVEN (Hydrogen.Schema.Brand.Voice)
-- |
-- | Invariants:
-- |   traits_nonempty: Every brand has >= 1 trait (PROVEN)
-- |   traits_unique: No duplicate traits (PROVEN)
-- |   tone_exclusive: Exactly one tone (PROVEN)
-- |   vocabulary_disjoint: Preferred ∩ Prohibited = empty (PROVEN)

module Hydrogen.Schema.Brand.Voice
  ( -- * Tone
    Tone
      ( Formal
      , Casual
      , Playful
      , Authoritative
      , Empathetic
      , Inspirational
      , Technical
      , Minimalist
      )
  , toneToString
  , toneFromString
  
  -- * Traits
  , Trait
      ( Trustworthy
      , Reliable
      , Authentic
      , Transparent
      , Innovative
      , Creative
      , Bold
      , Visionary
      , Friendly
      , Approachable
      , Warm
      , Inclusive
      , Expert
      , Knowledgeable
      , Sophisticated
      , Premium
      , Energetic
      , Passionate
      , Dynamic
      , Driven
      )
  , traitToString
  , TraitSet
  , mkTraitSet
  , traitSetToArray
  , hasTrait
  
  -- * Vocabulary
  , Term
  , mkTerm
  , unTerm
  , Vocabulary
  , emptyVocabulary
  , mkVocabulary
  , isPreferred
  , isProhibited
  
  -- * Brand Voice
  , BrandVoice
  , defaultVoice
  , mkBrandVoice
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>)
  , (<>)
  , compare
  , show
  , map
  , not
  )

import Data.Array (elem, nub, length, any, filter)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // tone
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tone atom.
-- |
-- | The primary emotional register of brand communication.
-- | A brand has exactly one tone — the foundation of voice consistency.
data Tone
  = Formal        -- Professional, reserved
  | Casual        -- Friendly, conversational
  | Playful       -- Fun, lighthearted
  | Authoritative -- Expert, commanding
  | Empathetic    -- Understanding, supportive
  | Inspirational -- Motivating, uplifting
  | Technical     -- Precise, detailed
  | Minimalist    -- Brief, essential

derive instance eqTone :: Eq Tone

instance ordTone :: Ord Tone where
  compare t1 t2 = compare (toneToInt t1) (toneToInt t2)
    where
      toneToInt :: Tone -> Int
      toneToInt Formal = 0
      toneToInt Casual = 1
      toneToInt Playful = 2
      toneToInt Authoritative = 3
      toneToInt Empathetic = 4
      toneToInt Inspirational = 5
      toneToInt Technical = 6
      toneToInt Minimalist = 7

instance showTone :: Show Tone where
  show = toneToString

-- | Convert tone to string.
toneToString :: Tone -> String
toneToString Formal = "formal"
toneToString Casual = "casual"
toneToString Playful = "playful"
toneToString Authoritative = "authoritative"
toneToString Empathetic = "empathetic"
toneToString Inspirational = "inspirational"
toneToString Technical = "technical"
toneToString Minimalist = "minimalist"

-- | Parse tone from string.
toneFromString :: String -> Maybe Tone
toneFromString s = case String.toLower s of
  "formal" -> Just Formal
  "casual" -> Just Casual
  "playful" -> Just Playful
  "authoritative" -> Just Authoritative
  "empathetic" -> Just Empathetic
  "inspirational" -> Just Inspirational
  "technical" -> Just Technical
  "minimalist" -> Just Minimalist
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // trait
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Trait atom.
-- |
-- | Individual personality traits that describe the brand.
-- | These inform content generation and voice calibration.
data Trait
  -- Trust & Reliability
  = Trustworthy
  | Reliable
  | Authentic
  | Transparent
  -- Innovation & Creativity
  | Innovative
  | Creative
  | Bold
  | Visionary
  -- Approachability
  | Friendly
  | Approachable
  | Warm
  | Inclusive
  -- Expertise
  | Expert
  | Knowledgeable
  | Sophisticated
  | Premium
  -- Energy
  | Energetic
  | Passionate
  | Dynamic
  | Driven

derive instance eqTrait :: Eq Trait

instance ordTrait :: Ord Trait where
  compare t1 t2 = compare (traitToInt t1) (traitToInt t2)
    where
      traitToInt :: Trait -> Int
      traitToInt Trustworthy = 0
      traitToInt Reliable = 1
      traitToInt Authentic = 2
      traitToInt Transparent = 3
      traitToInt Innovative = 4
      traitToInt Creative = 5
      traitToInt Bold = 6
      traitToInt Visionary = 7
      traitToInt Friendly = 8
      traitToInt Approachable = 9
      traitToInt Warm = 10
      traitToInt Inclusive = 11
      traitToInt Expert = 12
      traitToInt Knowledgeable = 13
      traitToInt Sophisticated = 14
      traitToInt Premium = 15
      traitToInt Energetic = 16
      traitToInt Passionate = 17
      traitToInt Dynamic = 18
      traitToInt Driven = 19

instance showTrait :: Show Trait where
  show = traitToString

-- | Convert trait to string.
traitToString :: Trait -> String
traitToString Trustworthy = "trustworthy"
traitToString Reliable = "reliable"
traitToString Authentic = "authentic"
traitToString Transparent = "transparent"
traitToString Innovative = "innovative"
traitToString Creative = "creative"
traitToString Bold = "bold"
traitToString Visionary = "visionary"
traitToString Friendly = "friendly"
traitToString Approachable = "approachable"
traitToString Warm = "warm"
traitToString Inclusive = "inclusive"
traitToString Expert = "expert"
traitToString Knowledgeable = "knowledgeable"
traitToString Sophisticated = "sophisticated"
traitToString Premium = "premium"
traitToString Energetic = "energetic"
traitToString Passionate = "passionate"
traitToString Dynamic = "dynamic"
traitToString Driven = "driven"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // trait set
-- ═══════════════════════════════════════════════════════════════════════════════

-- | TraitSet molecule.
-- |
-- | A non-empty, unique collection of personality traits.
-- |
-- | Invariants:
-- |   traits_nonempty: length >= 1
-- |   traits_unique: no duplicates
type TraitSet = 
  { traits :: Array Trait
  }

-- | Create trait set (deduplicates, ensures non-empty).
-- |
-- | Returns Nothing if input is empty after deduplication.
mkTraitSet :: Array Trait -> Maybe TraitSet
mkTraitSet ts =
  let deduped = nub ts
  in if length deduped > 0
     then Just { traits: deduped }
     else Nothing

-- | Get traits as array.
traitSetToArray :: TraitSet -> Array Trait
traitSetToArray ts = ts.traits

-- | Check if trait is in set.
hasTrait :: Trait -> TraitSet -> Boolean
hasTrait t ts = elem t ts.traits

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // term
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Term atom.
-- |
-- | A single vocabulary term (word or phrase).
-- | Must be non-empty.
newtype Term = Term String

derive instance eqTerm :: Eq Term

instance ordTerm :: Ord Term where
  compare (Term t1) (Term t2) = compare t1 t2

instance showTerm :: Show Term where
  show (Term t) = "Term(" <> t <> ")"

-- | Smart constructor with validation.
mkTerm :: String -> Maybe Term
mkTerm s =
  let trimmed = String.trim s
  in if String.length trimmed > 0
     then Just (Term trimmed)
     else Nothing

-- | Unwrap term to string.
unTerm :: Term -> String
unTerm (Term t) = t

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // vocabulary
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Vocabulary molecule.
-- |
-- | Words and phrases that define brand voice:
-- |   - preferred: Words to use
-- |   - prohibited: Words to avoid
-- |
-- | Invariant: vocabulary_disjoint (preferred and prohibited don't overlap)
type Vocabulary =
  { preferred :: Array Term
  , prohibited :: Array Term
  }

-- | Empty vocabulary (no restrictions).
emptyVocabulary :: Vocabulary
emptyVocabulary = { preferred: [], prohibited: [] }

-- | Create vocabulary, ensuring disjoint sets.
-- |
-- | Returns Nothing if any term appears in both preferred and prohibited.
mkVocabulary :: Array Term -> Array Term -> Maybe Vocabulary
mkVocabulary preferred prohibited =
  let 
    hasOverlap = any (\p -> elem p prohibited) preferred
  in 
    if not hasOverlap
    then Just { preferred, prohibited }
    else Nothing

-- | Check if a string is in preferred vocabulary.
isPreferred :: String -> Vocabulary -> Boolean
isPreferred s v = any (\t -> unTerm t == s) v.preferred

-- | Check if a string is in prohibited vocabulary.
isProhibited :: String -> Vocabulary -> Boolean
isProhibited s v = any (\t -> unTerm t == s) v.prohibited

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // brand voice
-- ═══════════════════════════════════════════════════════════════════════════════

-- | BrandVoice compound.
-- |
-- | Complete voice configuration for a brand:
-- |   - tone: Primary emotional register
-- |   - traits: Personality adjectives
-- |   - vocabulary: Preferred and prohibited terms
type BrandVoice =
  { tone :: Tone
  , traits :: TraitSet
  , vocabulary :: Vocabulary
  }

-- | Create brand voice.
mkBrandVoice :: Tone -> TraitSet -> Vocabulary -> BrandVoice
mkBrandVoice tone traits vocabulary = { tone, traits, vocabulary }

-- | Default voice (casual, friendly/approachable, empty vocabulary).
defaultVoice :: BrandVoice
defaultVoice =
  { tone: Casual
  , traits: { traits: [Friendly, Approachable] }
  , vocabulary: emptyVocabulary
  }
