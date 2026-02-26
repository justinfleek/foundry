{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // foundry // brand/strategy
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Strategy
Description : SMART Framework Sections 2, 4, 5 - Strategic Layer
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Mission, vision, values, personality, and brand positioning. This module
encodes the Strategic Layer of the SMART Brand Ingestion Framework.

== SMART Framework Alignment

  S - Story-driven: Mission and values define the brand narrative
  M - Memorable: Personality traits create distinctive character
  A - Agile: Positioning adapts messaging to different contexts
  R - Responsive: Strategy informs decisions across all channels
  T - Targeted: Positioning guides audience-specific communication

== Sections Covered

  Section 2: Mission Statement - Immutable declaration of purpose
  Section 4: Brand Values - Core principles that inform all decisions
  Section 5: Brand Personality - How the brand behaves as a person

== Dependencies

  - Data.Text
  - Data.Vector
  - Foundry.Core.Brand.Tagline (TaglineSet)

== Dependents

  - Foundry.Core.Brand (compound Brand type)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Strategy
  ( -- * Mission Statement (Section 2)
    MissionStatement (..)
  , mkMissionStatement
  , missionToText
  
    -- * Brand Values (Section 4)
  , BrandValue (..)
  , mkBrandValue
  , valueToText
  
  , BrandValues (..)
  , mkBrandValues
  , valuesCount
  
    -- * Personality Traits (Section 5)
  , PersonalityTrait (..)
  , mkPersonalityTrait
  , traitToText
  
  , PersonalityDescription (..)
  , mkPersonalityDescription
  
  , PositioningType (..)
  , positioningTypeToText
  , parsePositioningType
  
  , PositioningStatement (..)
  , mkPositioningStatement
  
  , BrandPersonality (..)
  , mkBrandPersonality
  
    -- * Complete Strategic Layer
  , StrategicLayer (..)
  , mkStrategicLayer
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V
import Data.Word (Word8)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // mission statement
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mission statement - the brand's declaration of purpose.
--
-- Per SMART Framework Section 2:
-- "A concise declaration of the brand's purpose and intended impact."
-- "This should be treated as locked copy; do not paraphrase or reword."
--
-- Like taglines, mission statements are IMMUTABLE once set.
newtype MissionStatement = MissionStatement { unMissionStatement :: Text }
  deriving stock (Eq, Ord)

-- | Show instance for debugging.
instance Show MissionStatement where
  show (MissionStatement t) = "(MissionStatement text:" <> show t <> ")"

-- | Create validated mission statement.
--
-- Validation rules:
--   * Text must be non-empty
--   * Text is stripped of leading/trailing whitespace
mkMissionStatement :: Text -> Maybe MissionStatement
mkMissionStatement t
  | T.null stripped = Nothing
  | otherwise = Just (MissionStatement stripped)
  where
    stripped = T.strip t

-- | Extract text from mission statement (read-only).
missionToText :: MissionStatement -> Text
missionToText = unMissionStatement

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                            // brand values
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | A single brand value.
--
-- Per SMART Framework Section 4:
-- "The core principles that inform every decision, design, and communication."
--
-- Examples: Innovation, Security, Accessibility, Transparency, Excellence
data BrandValue = BrandValue
  { brandValueName        :: !Text   -- ^ The value name (e.g., "Innovation")
  , brandValueDescription :: !Text   -- ^ How this value manifests
  }
  deriving stock (Eq)

-- | Show instance for debugging.
instance Show BrandValue where
  show (BrandValue n d) = 
    "(BrandValue name:" <> show n <> " desc:" <> show d <> ")"

-- | Create validated brand value.
mkBrandValue :: Text -> Text -> Maybe BrandValue
mkBrandValue name desc
  | T.null (T.strip name) = Nothing
  | otherwise = Just BrandValue
      { brandValueName = T.strip name
      , brandValueDescription = T.strip desc
      }

-- | Extract value name as text.
valueToText :: BrandValue -> Text
valueToText = brandValueName

-- | Ordered list of brand values.
--
-- The ordering is significant - typically from most to least important.
-- Most brands have 3-7 core values.
data BrandValues = BrandValues
  { brandValuesItems :: !(Vector BrandValue)  -- ^ Ordered list of values
  }
  deriving stock (Eq, Show)

-- | Create validated brand values.
--
-- Requires at least one value.
mkBrandValues :: Vector BrandValue -> Maybe BrandValues
mkBrandValues vals
  | V.null vals = Nothing
  | otherwise = Just BrandValues { brandValuesItems = vals }

-- | Count of brand values.
valuesCount :: BrandValues -> Word8
valuesCount bv = fromIntegral (V.length (brandValuesItems bv))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // personality traits
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | A single personality trait.
--
-- Per SMART Framework Section 5:
-- "Core Personality Traits — Typically 3–5 adjectives"
-- Examples: Friendly, Intelligent, Helpful, Bold, Trustworthy
newtype PersonalityTrait = PersonalityTrait { unPersonalityTrait :: Text }
  deriving stock (Eq, Ord)

-- | Show instance for debugging.
instance Show PersonalityTrait where
  show (PersonalityTrait t) = "(PersonalityTrait " <> show t <> ")"

-- | Create validated personality trait.
mkPersonalityTrait :: Text -> Maybe PersonalityTrait
mkPersonalityTrait t
  | T.null stripped = Nothing
  | otherwise = Just (PersonalityTrait stripped)
  where
    stripped = T.strip t

-- | Extract trait as text.
traitToText :: PersonalityTrait -> Text
traitToText = unPersonalityTrait

-- | Personality description - narrative explanation.
--
-- Per SMART Framework Section 5:
-- "A narrative explanation of how these traits manifest across touchpoints."
newtype PersonalityDescription = PersonalityDescription 
  { unPersonalityDescription :: Text }
  deriving stock (Eq, Ord)

-- | Show instance for debugging.
instance Show PersonalityDescription where
  show (PersonalityDescription t) = "(PersonalityDescription " <> show t <> ")"

-- | Create validated personality description.
mkPersonalityDescription :: Text -> Maybe PersonalityDescription
mkPersonalityDescription t
  | T.null stripped = Nothing
  | otherwise = Just (PersonalityDescription stripped)
  where
    stripped = T.strip t

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // positioning statement
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | How the brand positions itself relative to users.
--
-- Per SMART Framework Section 5:
-- "How the brand positions itself relative to users (e.g., ally, guide,
--  facilitator, authority)."
data PositioningType
  = Ally         -- ^ Partner and supporter
  | Guide        -- ^ Teacher and mentor
  | Facilitator  -- ^ Enabler and connector
  | Authority    -- ^ Expert and leader
  | Challenger   -- ^ Disruptor and innovator
  | Creator      -- ^ Imaginative and inventive
  | Caregiver    -- ^ Nurturing and protective
  | Everyman     -- ^ Relatable and approachable
  | Hero         -- ^ Bold and courageous
  | Sage         -- ^ Wise and thoughtful
  | Explorer     -- ^ Adventurous and curious
  | Rebel        -- ^ Independent and unconventional
  deriving stock (Eq, Ord, Show)

-- | Convert positioning type to text.
positioningTypeToText :: PositioningType -> Text
positioningTypeToText Ally = "ally"
positioningTypeToText Guide = "guide"
positioningTypeToText Facilitator = "facilitator"
positioningTypeToText Authority = "authority"
positioningTypeToText Challenger = "challenger"
positioningTypeToText Creator = "creator"
positioningTypeToText Caregiver = "caregiver"
positioningTypeToText Everyman = "everyman"
positioningTypeToText Hero = "hero"
positioningTypeToText Sage = "sage"
positioningTypeToText Explorer = "explorer"
positioningTypeToText Rebel = "rebel"

-- | Parse positioning type from text.
parsePositioningType :: Text -> Maybe PositioningType
parsePositioningType s = case T.toLower (T.strip s) of
  "ally"         -> Just Ally
  "partner"      -> Just Ally
  "supporter"    -> Just Ally
  "guide"        -> Just Guide
  "mentor"       -> Just Guide
  "teacher"      -> Just Guide
  "facilitator"  -> Just Facilitator
  "enabler"      -> Just Facilitator
  "connector"    -> Just Facilitator
  "authority"    -> Just Authority
  "expert"       -> Just Authority
  "leader"       -> Just Authority
  "challenger"   -> Just Challenger
  "disruptor"    -> Just Challenger
  "innovator"    -> Just Challenger
  "creator"      -> Just Creator
  "imaginative"  -> Just Creator
  "inventive"    -> Just Creator
  "caregiver"    -> Just Caregiver
  "nurturing"    -> Just Caregiver
  "protective"   -> Just Caregiver
  "everyman"     -> Just Everyman
  "relatable"    -> Just Everyman
  "approachable" -> Just Everyman
  "hero"         -> Just Hero
  "bold"         -> Just Hero
  "courageous"   -> Just Hero
  "sage"         -> Just Sage
  "wise"         -> Just Sage
  "thoughtful"   -> Just Sage
  "explorer"     -> Just Explorer
  "adventurous"  -> Just Explorer
  "curious"      -> Just Explorer
  "rebel"        -> Just Rebel
  "independent"  -> Just Rebel
  "unconventional" -> Just Rebel
  _              -> Nothing

-- | Complete positioning statement.
data PositioningStatement = PositioningStatement
  { positioningType     :: !PositioningType  -- ^ Archetype category
  , positioningNarrative :: !Text            -- ^ Full positioning narrative
  }
  deriving stock (Eq)

-- | Show instance for debugging.
instance Show PositioningStatement where
  show (PositioningStatement pt n) = 
    "(PositioningStatement type:" <> show pt <> " narrative:" <> show n <> ")"

-- | Create validated positioning statement.
mkPositioningStatement :: PositioningType -> Text -> PositioningStatement
mkPositioningStatement ptype narrative = PositioningStatement
  { positioningType = ptype
  , positioningNarrative = T.strip narrative
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // brand personality
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete brand personality specification.
--
-- Per SMART Framework Section 5:
-- "How the brand would behave if it were a person. This drives tone,
--  visual style, and interaction design."
data BrandPersonality = BrandPersonality
  { personalityTraits      :: !(Vector PersonalityTrait)  -- ^ 3-5 core traits
  , personalityDescription :: !PersonalityDescription     -- ^ Narrative explanation
  , personalityPositioning :: !PositioningStatement       -- ^ Brand archetype
  }
  deriving stock (Eq, Show)

-- | Create validated brand personality.
--
-- Requires at least one personality trait.
mkBrandPersonality 
  :: Vector PersonalityTrait 
  -> PersonalityDescription 
  -> PositioningStatement 
  -> Maybe BrandPersonality
mkBrandPersonality traits desc pos
  | V.null traits = Nothing
  | otherwise = Just BrandPersonality
      { personalityTraits = traits
      , personalityDescription = desc
      , personalityPositioning = pos
      }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // strategic layer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete Strategic Layer for a brand.
--
-- The Strategic Layer defines WHO the brand is - its purpose, values, and
-- personality. This drives all creative decisions in the Execution Layer.
--
-- Per SMART Framework:
-- "The story, personality, voice, and values that drive all creative decisions."
data StrategicLayer = StrategicLayer
  { strategicMission     :: !MissionStatement    -- ^ Declaration of purpose
  , strategicValues      :: !BrandValues         -- ^ Core principles
  , strategicPersonality :: !BrandPersonality    -- ^ Brand as a person
  }
  deriving stock (Eq, Show)

-- | Create validated strategic layer.
mkStrategicLayer 
  :: MissionStatement 
  -> BrandValues 
  -> BrandPersonality 
  -> StrategicLayer
mkStrategicLayer mission values personality = StrategicLayer
  { strategicMission = mission
  , strategicValues = values
  , strategicPersonality = personality
  }
