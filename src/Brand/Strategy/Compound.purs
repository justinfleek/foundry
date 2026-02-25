-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // brand // strategy
--                                                                    // compound
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SMART Framework Strategic Layer: Compound types for ToneGuide,
-- | CustomerSegment, TargetCustomers, IndustryCategory, BrandOverview,
-- | and the complete StrategicLayer.
-- |
-- | STATUS: PROVEN (Hydrogen.Schema.Brand.Strategy)
-- |
-- | Invariants:
-- |   tone_guide_nonempty: At least one tone constraint required
-- |   customers_segmented: At least one target segment defined
-- |   industry_defined: Industry and category must be non-empty
-- |   overview_complete: Brand name, description, promise all non-empty
-- |   strategic_complete: All strategic layer components present
-- |
-- | DEPENDENCIES:
-- |   - Hydrogen.Schema.Brand.Strategy (atomic types)
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Brand (compound Brand type)

module Hydrogen.Schema.Brand.Strategy.Compound
  ( -- * Tone Guide
    ToneGuide
  , mkToneGuide
  , toneGuideConstraints
  , toneGuideVoiceSummary
  , toneGuideConstraintCount
  
  -- * Customer Segment
  , CustomerSegment
  , mkCustomerSegment
  , segmentName
  , segmentDescription
  , segmentMotivations
  
  -- * Target Customers
  , TargetCustomers
  , mkTargetCustomers
  , mkSingleTargetCustomer
  , targetSegments
  , primarySegment
  , segmentCount
  
  -- * Industry Category
  , IndustryCategory
  , mkIndustryCategory
  , industryName
  , categoryName
  
  -- * Brand Overview
  , BrandOverview
  , mkBrandOverview
  , overviewBrandName
  , overviewParentOrg
  , overviewIndustryCategory
  , overviewOneLineDescription
  , overviewBrandPromise
  , overviewFoundingContext
  
  -- * Strategic Layer (Complete)
  , StrategicLayer
  , mkStrategicLayer
  , strategicOverview
  , strategicMission
  , strategicTaglines
  , strategicValues
  , strategicPersonality
  , strategicToneGuide
  , strategicTargetCustomers
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (&&)
  , (>=)
  , (<>)
  , (+)
  , show
  , compare
  , map
  )

import Data.Array (length, head, filter) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length) as String

import Hydrogen.Schema.Brand.Strategy
  ( MissionStatement
  , Taglines
  , BrandValues
  , BrandPersonality
  , ToneConstraint
  , toneConstraintAttr
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // tone guide
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Collection of tone constraints with voice summary.
-- |
-- | Invariant: At least one constraint required (tone_guide_nonempty).
-- | The voice summary captures the overarching tonal principle.
type ToneGuide =
  { constraints :: Array ToneConstraint
  , voiceSummary :: String
  }

-- | Create tone guide. Requires at least one constraint.
mkToneGuide :: Array ToneConstraint -> String -> Maybe ToneGuide
mkToneGuide constraints summary =
  if Array.length constraints >= 1
    then Just { constraints: constraints, voiceSummary: summary }
    else Nothing

-- | Get all tone constraints.
toneGuideConstraints :: ToneGuide -> Array ToneConstraint
toneGuideConstraints tg = tg.constraints

-- | Get voice summary.
toneGuideVoiceSummary :: ToneGuide -> String
toneGuideVoiceSummary tg = tg.voiceSummary

-- | Count constraints in guide.
toneGuideConstraintCount :: ToneGuide -> Int
toneGuideConstraintCount tg = Array.length tg.constraints

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // customer segment
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A target customer segment.
-- |
-- | Psychographic profile of an intended audience segment. These inform
-- | tone calibration and content strategy. An AI generating for
-- | "privacy-conscious users" writes differently than for "gamers seeking
-- | immersive experiences".
-- |
-- | Invariants:
-- |   name_nonempty: Segment name must be non-empty
-- |   desc_nonempty: Segment description must be non-empty
type CustomerSegment =
  { name :: String          -- e.g., "Early Adopters & Innovators"
  , description :: String   -- Who they are and what drives them
  , motivations :: Array String  -- What attracts them to brands in this category
  }

-- | Create customer segment. Name and description must be non-empty.
mkCustomerSegment :: String -> String -> Array String -> Maybe CustomerSegment
mkCustomerSegment name desc motivations =
  if String.length name >= 1 && String.length desc >= 1
    then Just { name: name, description: desc, motivations: motivations }
    else Nothing

-- | Get segment name.
segmentName :: CustomerSegment -> String
segmentName cs = cs.name

-- | Get segment description.
segmentDescription :: CustomerSegment -> String
segmentDescription cs = cs.description

-- | Get segment motivations.
segmentMotivations :: CustomerSegment -> Array String
segmentMotivations cs = cs.motivations

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // target customers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Collection of target customer segments.
-- |
-- | Invariant: At least one segment required (customers_segmented).
newtype TargetCustomers = TargetCustomers (Array CustomerSegment)

derive instance eqTargetCustomers :: Eq TargetCustomers

instance showTargetCustomers :: Show TargetCustomers where
  show (TargetCustomers segs) = "TargetCustomers(" <> show (Array.length segs) <> " segments)"

-- | Create target customers. Requires at least one valid segment.
mkTargetCustomers :: Array CustomerSegment -> Maybe TargetCustomers
mkTargetCustomers segments =
  let validSegments = Array.filter isValidSegment segments
  in if Array.length validSegments >= 1
       then Just (TargetCustomers validSegments)
       else Nothing
  where
    isValidSegment :: CustomerSegment -> Boolean
    isValidSegment seg = 
      String.length seg.name >= 1 && String.length seg.description >= 1

-- | Create target customers from a single segment.
mkSingleTargetCustomer :: String -> String -> Array String -> Maybe TargetCustomers
mkSingleTargetCustomer name desc motivations =
  case mkCustomerSegment name desc motivations of
    Nothing -> Nothing
    Just seg -> Just (TargetCustomers [seg])

-- | Get all target segments.
targetSegments :: TargetCustomers -> Array CustomerSegment
targetSegments (TargetCustomers segs) = segs

-- | Get primary (first) segment.
primarySegment :: TargetCustomers -> Maybe CustomerSegment
primarySegment (TargetCustomers segs) = Array.head segs

-- | Count total segments.
segmentCount :: TargetCustomers -> Int
segmentCount (TargetCustomers segs) = Array.length segs

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // industry category
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Industry and category classification.
-- |
-- | Invariants:
-- |   industry_nonempty: Industry must be non-empty
-- |   category_nonempty: Category must be non-empty
type IndustryCategory =
  { industry :: String    -- e.g., "Technology"
  , category :: String    -- e.g., "Software Development Tools"
  }

-- | Create industry category. Both fields must be non-empty.
mkIndustryCategory :: String -> String -> Maybe IndustryCategory
mkIndustryCategory industry category =
  if String.length industry >= 1 && String.length category >= 1
    then Just { industry: industry, category: category }
    else Nothing

-- | Get industry name.
industryName :: IndustryCategory -> String
industryName ic = ic.industry

-- | Get category name.
categoryName :: IndustryCategory -> String
categoryName ic = ic.category

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // brand overview
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete Brand Overview (Strategic Layer introduction).
-- |
-- | The foundational narrative combining all strategic elements.
-- |
-- | Invariants:
-- |   name_nonempty: Brand name must be non-empty
-- |   desc_nonempty: One-line description must be non-empty
-- |   promise_nonempty: Brand promise must be non-empty
type BrandOverview =
  { brandName :: String
  , parentOrganization :: Maybe String
  , industryCategory :: IndustryCategory
  , oneLineDescription :: String
  , brandPromise :: String
  , foundingContext :: String
  }

-- | Create brand overview. Name, description, and promise must be non-empty.
mkBrandOverview 
  :: String               -- brandName
  -> Maybe String         -- parentOrganization (optional)
  -> IndustryCategory     -- industryCategory
  -> String               -- oneLineDescription
  -> String               -- brandPromise
  -> String               -- foundingContext
  -> Maybe BrandOverview
mkBrandOverview name parentOrg ic desc promise founding =
  if String.length name >= 1 
     && String.length desc >= 1 
     && String.length promise >= 1
    then Just
      { brandName: name
      , parentOrganization: parentOrg
      , industryCategory: ic
      , oneLineDescription: desc
      , brandPromise: promise
      , foundingContext: founding
      }
    else Nothing

-- | Get brand name.
overviewBrandName :: BrandOverview -> String
overviewBrandName bo = bo.brandName

-- | Get parent organization.
overviewParentOrg :: BrandOverview -> Maybe String
overviewParentOrg bo = bo.parentOrganization

-- | Get industry category.
overviewIndustryCategory :: BrandOverview -> IndustryCategory
overviewIndustryCategory bo = bo.industryCategory

-- | Get one-line description.
overviewOneLineDescription :: BrandOverview -> String
overviewOneLineDescription bo = bo.oneLineDescription

-- | Get brand promise.
overviewBrandPromise :: BrandOverview -> String
overviewBrandPromise bo = bo.brandPromise

-- | Get founding context.
overviewFoundingContext :: BrandOverview -> String
overviewFoundingContext bo = bo.foundingContext

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // strategic layer
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete Strategic Layer of the SMART framework.
-- |
-- | This is the WHY behind every design decision. At billion-agent scale,
-- | an agent generating copy for a brand must know:
-- |   - Mission: The locked statement to never paraphrase
-- |   - Taglines: The verbal signature to never edit
-- |   - Values: The priority-ordered principles
-- |   - Personality: The IS/NOT constraints for tone
-- |   - Target Customers: Who we're speaking to
-- |
-- | Invariants (all proven in Lean4):
-- |   mission_nonempty: Mission text length > 0
-- |   tagline_nonempty: Primary tagline length > 0
-- |   values_nonempty: At least one value
-- |   personality_bounded: 3-5 traits
-- |   tone_guide_nonempty: At least one tone constraint
-- |   customers_nonempty: At least one segment
type StrategicLayer =
  { overview :: BrandOverview
  , mission :: MissionStatement
  , taglines :: Taglines
  , values :: BrandValues
  , personality :: BrandPersonality
  , toneGuide :: ToneGuide
  , targetCustomers :: TargetCustomers
  }

-- | Create strategic layer (all components required).
mkStrategicLayer
  :: BrandOverview
  -> MissionStatement
  -> Taglines
  -> BrandValues
  -> BrandPersonality
  -> ToneGuide
  -> TargetCustomers
  -> StrategicLayer
mkStrategicLayer overview mission taglines values personality toneGuide customers =
  { overview: overview
  , mission: mission
  , taglines: taglines
  , values: values
  , personality: personality
  , toneGuide: toneGuide
  , targetCustomers: customers
  }

-- | Get brand overview.
strategicOverview :: StrategicLayer -> BrandOverview
strategicOverview sl = sl.overview

-- | Get mission statement.
strategicMission :: StrategicLayer -> MissionStatement
strategicMission sl = sl.mission

-- | Get taglines.
strategicTaglines :: StrategicLayer -> Taglines
strategicTaglines sl = sl.taglines

-- | Get brand values.
strategicValues :: StrategicLayer -> BrandValues
strategicValues sl = sl.values

-- | Get brand personality.
strategicPersonality :: StrategicLayer -> BrandPersonality
strategicPersonality sl = sl.personality

-- | Get tone guide.
strategicToneGuide :: StrategicLayer -> ToneGuide
strategicToneGuide sl = sl.toneGuide

-- | Get target customers.
strategicTargetCustomers :: StrategicLayer -> TargetCustomers
strategicTargetCustomers sl = sl.targetCustomers
