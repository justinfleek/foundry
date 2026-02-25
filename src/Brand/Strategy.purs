-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // brand // strategy
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SMART Framework Strategic Layer: Mission, Taglines, Values, Personality,
-- | Target Customers, and Tone Constraints.
-- |
-- | STATUS: PROVEN (Hydrogen.Schema.Brand.Strategy)
-- |
-- | Invariants:
-- |   mission_immutable: Mission statement is locked copy (non-empty)
-- |   taglines_immutable: Taglines cannot be edited or paraphrased
-- |   values_ordered: Brand values maintain priority ordering
-- |   personality_bounded: 3-5 core traits required
-- |   tone_constraints: IS/NOT pairs enforce guardrails
-- |   customers_segmented: At least one target segment defined
-- |
-- | SMART FRAMEWORK:
-- |   S - Story-driven: Mission, taglines, values tell the brand's story
-- |   M - Memorable: Personality traits create distinctive voice
-- |   A - Agile: IS/NOT constraints allow flexibility within guardrails
-- |   R - Responsive: Target customers inform tone calibration
-- |   T - Targeted: Psychographics drive content strategy

module Hydrogen.Schema.Brand.Strategy
  ( -- * Mission Statement
    MissionStatement
  , mkMissionStatement
  , unMissionStatement
  
  -- * Taglines
  , Tagline
  , mkTagline
  , unTagline
  , Taglines
  , mkTaglines
  , primaryTagline
  , secondaryTaglines
  , taglineCount
  
  -- * Brand Values
  , BrandValue
  , mkBrandValue
  , unBrandValue
  , BrandValues
  , mkBrandValues
  , primaryValue
  , allValues
  
  -- * Brand Personality
  , PersonalityTrait
  , mkPersonalityTrait
  , unPersonalityTrait
  , PositioningRole
      ( Ally
      , Guide
      , Facilitator
      , Authority
      , Friend
      , Mentor
      , Challenger
      , Protector
      )
  , positioningRoleToString
  , BrandPersonality
  , mkBrandPersonality
  , personalityTraits
  , personalityDescription
  , personalityPositioning
  
  -- * Tone Constraints (IS/NOT Pattern)
  , ToneAttribute
      ( ToneAuthoritative
      , ToneApproachable
      , ToneInnovative
      , ToneForwardThinking
      , TonePlayful
      , ToneProfessional
      , ToneEmpathetic
      , ToneTechnical
      , ToneMinimalist
      , ToneBold
      , ToneWarm
      , TonePrecise
      )
  , toneAttributeToString
  , ToneDescriptor
  , mkToneDescriptor
  , unToneDescriptor
  , ToneConstraint
  , mkToneConstraint
  , toneConstraintAttr
  , toneConstraintIs
  , toneConstraintNot
  , isAllowed
  , isForbidden
  
  -- Note: ToneGuide, TargetCustomers, BrandOverview, and StrategicLayer
  -- are in Hydrogen.Schema.Brand.Strategy.Compound to keep files under 500 lines.
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (&&)
  , (>=)
  , (<=)
  , (<>)
  , (+)
  , show
  , compare
  , map
  , otherwise
  )

import Data.Array (length, filter, any, head) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length) as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // mission statement
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Mission statement (non-empty, immutable copy).
-- |
-- | This is LOCKED COPY — never paraphrase, never reword, never "improve".
-- | Agents must use it verbatim.
newtype MissionStatement = MissionStatement String

derive instance eqMissionStatement :: Eq MissionStatement

instance showMissionStatement :: Show MissionStatement where
  show (MissionStatement s) = "MissionStatement(" <> show s <> ")"

-- | Smart constructor - ensures non-empty.
mkMissionStatement :: String -> Maybe MissionStatement
mkMissionStatement s =
  if String.length s >= 1
    then Just (MissionStatement s)
    else Nothing

-- | Extract mission text.
unMissionStatement :: MissionStatement -> String
unMissionStatement (MissionStatement s) = s

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // taglines
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A tagline (non-empty, immutable).
-- |
-- | Verbal signature of the brand. LOCKED COPY — never edit.
newtype Tagline = Tagline String

derive instance eqTagline :: Eq Tagline

instance showTagline :: Show Tagline where
  show (Tagline s) = "Tagline(" <> show s <> ")"

-- | Smart constructor.
mkTagline :: String -> Maybe Tagline
mkTagline s =
  if String.length s >= 1
    then Just (Tagline s)
    else Nothing

-- | Extract tagline text.
unTagline :: Tagline -> String
unTagline (Tagline s) = s

-- | Collection of brand taglines with primary + secondaries.
type Taglines =
  { primary :: Tagline
  , secondaries :: Array Tagline
  }

-- | Create taglines from primary and secondary strings.
mkTaglines :: String -> Array String -> Maybe Taglines
mkTaglines primaryStr secondaryStrs =
  case mkTagline primaryStr of
    Nothing -> Nothing
    Just p ->
      let secs = Array.filter (\s -> String.length s >= 1) secondaryStrs
          secTaglines = map (\s -> Tagline s) secs
      in Just { primary: p, secondaries: secTaglines }

-- | Get primary tagline.
primaryTagline :: Taglines -> Tagline
primaryTagline t = t.primary

-- | Get secondary taglines.
secondaryTaglines :: Taglines -> Array Tagline
secondaryTaglines t = t.secondaries

-- | Count total taglines.
taglineCount :: Taglines -> Int
taglineCount t = 1 + Array.length t.secondaries

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // brand values
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A single brand value (non-empty string).
newtype BrandValue = BrandValue String

derive instance eqBrandValue :: Eq BrandValue

instance showBrandValue :: Show BrandValue where
  show (BrandValue s) = "BrandValue(" <> show s <> ")"

-- | Smart constructor.
mkBrandValue :: String -> Maybe BrandValue
mkBrandValue s =
  if String.length s >= 1
    then Just (BrandValue s)
    else Nothing

-- | Extract value name.
unBrandValue :: BrandValue -> String
unBrandValue (BrandValue s) = s

-- | Ordered list of brand values (at least one required).
-- | The first value is the most important (priority ordering).
newtype BrandValues = BrandValues (Array BrandValue)

derive instance eqBrandValues :: Eq BrandValues

instance showBrandValues :: Show BrandValues where
  show (BrandValues vs) = "BrandValues(" <> show vs <> ")"

-- | Create from array of strings.
mkBrandValues :: Array String -> Maybe BrandValues
mkBrandValues strs =
  let filtered = Array.filter (\s -> String.length s >= 1) strs
      values = map BrandValue filtered
  in if Array.length values >= 1
       then Just (BrandValues values)
       else Nothing

-- | Get primary (most important) value.
primaryValue :: BrandValues -> Maybe BrandValue
primaryValue (BrandValues vs) = Array.head vs

-- | Get all values in priority order.
allValues :: BrandValues -> Array BrandValue
allValues (BrandValues vs) = vs

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // brand personality
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A personality trait (adjective).
newtype PersonalityTrait = PersonalityTrait String

derive instance eqPersonalityTrait :: Eq PersonalityTrait

instance showPersonalityTrait :: Show PersonalityTrait where
  show (PersonalityTrait s) = "PersonalityTrait(" <> show s <> ")"

-- | Smart constructor.
mkPersonalityTrait :: String -> Maybe PersonalityTrait
mkPersonalityTrait s =
  if String.length s >= 1
    then Just (PersonalityTrait s)
    else Nothing

-- | Extract trait adjective.
unPersonalityTrait :: PersonalityTrait -> String
unPersonalityTrait (PersonalityTrait s) = s

-- | Positioning statement - how brand relates to users.
data PositioningRole
  = Ally         -- Partner, supporter
  | Guide        -- Expert leading the way
  | Facilitator  -- Enabler, removes friction
  | Authority    -- Expert, trusted source
  | Friend       -- Casual, approachable peer
  | Mentor       -- Teacher, advisor
  | Challenger   -- Pushes to be better
  | Protector    -- Guardian, defender

derive instance eqPositioningRole :: Eq PositioningRole

instance ordPositioningRole :: Ord PositioningRole where
  compare r1 r2 = compare (roleToInt r1) (roleToInt r2)
    where
      roleToInt :: PositioningRole -> Int
      roleToInt Ally = 0
      roleToInt Guide = 1
      roleToInt Facilitator = 2
      roleToInt Authority = 3
      roleToInt Friend = 4
      roleToInt Mentor = 5
      roleToInt Challenger = 6
      roleToInt Protector = 7

instance showPositioningRole :: Show PositioningRole where
  show = positioningRoleToString

-- | Convert positioning role to string.
positioningRoleToString :: PositioningRole -> String
positioningRoleToString Ally = "ally"
positioningRoleToString Guide = "guide"
positioningRoleToString Facilitator = "facilitator"
positioningRoleToString Authority = "authority"
positioningRoleToString Friend = "friend"
positioningRoleToString Mentor = "mentor"
positioningRoleToString Challenger = "challenger"
positioningRoleToString Protector = "protector"

-- | Brand personality with constrained trait count (3-5 traits).
type BrandPersonality =
  { coreTraits :: Array PersonalityTrait
  , description :: String
  , positioning :: PositioningRole
  }

-- | Create brand personality. Requires 3-5 traits.
mkBrandPersonality 
  :: Array String 
  -> String 
  -> PositioningRole 
  -> Maybe BrandPersonality
mkBrandPersonality traitStrs desc pos =
  let filtered = Array.filter (\s -> String.length s >= 1) traitStrs
      traits = map PersonalityTrait filtered
      count = Array.length traits
  in if count >= 3 && count <= 5
       then Just { coreTraits: traits, description: desc, positioning: pos }
       else Nothing

-- | Get personality traits.
personalityTraits :: BrandPersonality -> Array PersonalityTrait
personalityTraits bp = bp.coreTraits

-- | Get personality description.
personalityDescription :: BrandPersonality -> String
personalityDescription bp = bp.description

-- | Get positioning role.
personalityPositioning :: BrandPersonality -> PositioningRole
personalityPositioning bp = bp.positioning

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // tone constraints (is/not)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tone attribute name.
-- |
-- | The IS/NOT pattern is the MOST VALUABLE part of any brand voice spec.
-- | It converts subjective tone guidance into enforceable constraints.
data ToneAttribute
  = ToneAuthoritative    -- knowledgeable, trusted vs overbearing, pompous
  | ToneApproachable     -- friendly, warm vs overly casual, patronizing
  | ToneInnovative       -- creative, visionary vs impractical, hype-filled
  | ToneForwardThinking  -- proactive, anticipatory vs speculative, baseless
  | TonePlayful          -- fun, lighthearted vs silly, unprofessional
  | ToneProfessional     -- polished, credible vs stiff, cold
  | ToneEmpathetic       -- understanding, supportive vs pitying, soft
  | ToneTechnical        -- precise, detailed vs jargon-heavy, inaccessible
  | ToneMinimalist       -- brief, essential vs vague, incomplete
  | ToneBold             -- confident, assertive vs aggressive, arrogant
  | ToneWarm             -- caring, personal vs saccharine, unprofessional
  | TonePrecise          -- accurate, specific vs pedantic, nitpicky

derive instance eqToneAttribute :: Eq ToneAttribute

instance ordToneAttribute :: Ord ToneAttribute where
  compare t1 t2 = compare (toneAttrToInt t1) (toneAttrToInt t2)
    where
      toneAttrToInt :: ToneAttribute -> Int
      toneAttrToInt ToneAuthoritative = 0
      toneAttrToInt ToneApproachable = 1
      toneAttrToInt ToneInnovative = 2
      toneAttrToInt ToneForwardThinking = 3
      toneAttrToInt TonePlayful = 4
      toneAttrToInt ToneProfessional = 5
      toneAttrToInt ToneEmpathetic = 6
      toneAttrToInt ToneTechnical = 7
      toneAttrToInt ToneMinimalist = 8
      toneAttrToInt ToneBold = 9
      toneAttrToInt ToneWarm = 10
      toneAttrToInt TonePrecise = 11

instance showToneAttribute :: Show ToneAttribute where
  show = toneAttributeToString

-- | Convert tone attribute to string.
toneAttributeToString :: ToneAttribute -> String
toneAttributeToString ToneAuthoritative = "authoritative"
toneAttributeToString ToneApproachable = "approachable"
toneAttributeToString ToneInnovative = "innovative"
toneAttributeToString ToneForwardThinking = "forward-thinking"
toneAttributeToString TonePlayful = "playful"
toneAttributeToString ToneProfessional = "professional"
toneAttributeToString ToneEmpathetic = "empathetic"
toneAttributeToString ToneTechnical = "technical"
toneAttributeToString ToneMinimalist = "minimalist"
toneAttributeToString ToneBold = "bold"
toneAttributeToString ToneWarm = "warm"
toneAttributeToString TonePrecise = "precise"

-- | A descriptor word (adjective describing the tone).
newtype ToneDescriptor = ToneDescriptor String

derive instance eqToneDescriptor :: Eq ToneDescriptor

instance showToneDescriptor :: Show ToneDescriptor where
  show (ToneDescriptor s) = s

-- | Smart constructor.
mkToneDescriptor :: String -> Maybe ToneDescriptor
mkToneDescriptor s =
  if String.length s >= 1
    then Just (ToneDescriptor s)
    else Nothing

-- | Extract descriptor word.
unToneDescriptor :: ToneDescriptor -> String
unToneDescriptor (ToneDescriptor s) = s

-- | IS/NOT constraint pair for a tone attribute.
type ToneConstraint =
  { toneAttr :: ToneAttribute
  , isWords :: Array ToneDescriptor    -- What the brand IS
  , notWords :: Array ToneDescriptor   -- What the brand is NOT
  }

-- | Create tone constraint. Both IS and NOT must be non-empty.
mkToneConstraint 
  :: ToneAttribute 
  -> Array String 
  -> Array String 
  -> Maybe ToneConstraint
mkToneConstraint attr isStrs notStrs =
  let isFiltered = Array.filter (\s -> String.length s >= 1) isStrs
      notFiltered = Array.filter (\s -> String.length s >= 1) notStrs
      isDescs = map ToneDescriptor isFiltered
      notDescs = map ToneDescriptor notFiltered
  in if Array.length isDescs >= 1 && Array.length notDescs >= 1
       then Just { toneAttr: attr, isWords: isDescs, notWords: notDescs }
       else Nothing

-- | Get tone attribute.
toneConstraintAttr :: ToneConstraint -> ToneAttribute
toneConstraintAttr tc = tc.toneAttr

-- | Get IS words.
toneConstraintIs :: ToneConstraint -> Array ToneDescriptor
toneConstraintIs tc = tc.isWords

-- | Get NOT words.
toneConstraintNot :: ToneConstraint -> Array ToneDescriptor
toneConstraintNot tc = tc.notWords

-- | Check if a word is in the IS list.
isAllowed :: ToneConstraint -> String -> Boolean
isAllowed tc word = Array.any (\(ToneDescriptor d) -> d == word) tc.isWords

-- | Check if a word is in the NOT list.
isForbidden :: ToneConstraint -> String -> Boolean
isForbidden tc word = Array.any (\(ToneDescriptor d) -> d == word) tc.notWords
