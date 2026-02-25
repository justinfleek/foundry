-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // brand // imagery
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SMART Framework Imagery Layer: Image categories, color grading,
-- | and usage rules.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | Guidelines for the images, photographs, and visual content used to
-- | represent the brand across all media.
-- |
-- | SMART FRAMEWORK:
-- |   S - Story-driven: Images create experiences in the user's mind
-- |   M - Memorable: Consistent color grading creates recognition
-- |   A - Agile: Categories adapt to different campaigns
-- |   R - Responsive: Quality rules ensure sharpness across media
-- |   T - Targeted: Tone conveys warmth, expertise, approachability
-- |
-- | DEPENDENCIES:
-- |   - None (foundational module)
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Brand (compound Brand type)

module Hydrogen.Schema.Brand.Imagery
  ( -- * Image Category
    ImageCategory
  , mkImageCategory
  , categoryName
  , categoryDescription
  , categoryExamples
  
  -- * Color Grading Technique
  , ColorGradingTechnique
      ( ThreePointGrading
      , LUTBasedGrading
      , ManualAdjustment
      , PresetBased
      )
  , gradingTechniqueToString
  , parseGradingTechnique
  
  -- * Color Grading Spec
  , ColorGradingSpec
  , mkColorGradingSpec
  , gradingTechnique
  , gradingTargetPalette
  , gradingNotes
  
  -- * Image Quality Requirement
  , ImageQualityRequirement
      ( SharpnessRequired
      , ReadableText
      , ClearFaces
      , MinResolution
      , NoBlur
      )
  , qualityRequirementToString
  , parseQualityRequirement
  
  , QualityRule
  , mkQualityRule
  , qualityRequirement
  , qualityDescription
  , qualityException
  
  -- * Image Tone
  , ImageToneAttribute
  , mkImageToneAttribute
  , toneAttributeName
  , toneAttributeDescription
  
  -- * Image Content Strategy
  , ImageContentStrategy
  , mkImageContentStrategy
  , strategyPurpose
  , strategyColorGrading
  , strategyApprovalProcess
  
  -- * Image Usage Rule
  , ImageUsageRule
  , mkImageUsageRule
  , usageRuleName
  , usageRuleDescription
  , usageRuleMandatory
  
  -- * Complete Imagery Specification
  , ImagerySpecification
  , mkImagerySpecification
  , specContentStrategy
  , specCategories
  , specQualityRules
  , specToneAttributes
  , specUsageRules
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>=)
  , (&&)
  , (<>)
  , show
  , compare
  )

import Data.Array (length) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, toLower) as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // image category
-- ═══════════════════════════════════════════════════════════════════════════════

-- | An approved image category.
type ImageCategory =
  { name :: String                  -- Category identifier
  , description :: String           -- What this category includes
  , examples :: Array String        -- Example image types
  }

-- | Create image category.
mkImageCategory :: String -> String -> Array String -> Maybe ImageCategory
mkImageCategory name desc examples =
  if String.length name >= 1 && String.length desc >= 1
    then Just { name: name, description: desc, examples: examples }
    else Nothing

-- | Get category name.
categoryName :: ImageCategory -> String
categoryName ic = ic.name

-- | Get category description.
categoryDescription :: ImageCategory -> String
categoryDescription ic = ic.description

-- | Get category examples.
categoryExamples :: ImageCategory -> Array String
categoryExamples ic = ic.examples

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // color grading technique
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Color grading technique.
data ColorGradingTechnique
  = ThreePointGrading    -- Shadows, midtones, highlights
  | LUTBasedGrading      -- Look-Up Table based
  | ManualAdjustment     -- Manual color adjustment
  | PresetBased          -- Using pre-defined presets

derive instance eqColorGradingTechnique :: Eq ColorGradingTechnique

instance ordColorGradingTechnique :: Ord ColorGradingTechnique where
  compare t1 t2 = compare (techToInt t1) (techToInt t2)
    where
      techToInt :: ColorGradingTechnique -> Int
      techToInt ThreePointGrading = 0
      techToInt LUTBasedGrading = 1
      techToInt ManualAdjustment = 2
      techToInt PresetBased = 3

instance showColorGradingTechnique :: Show ColorGradingTechnique where
  show = gradingTechniqueToString

-- | Convert grading technique to string.
gradingTechniqueToString :: ColorGradingTechnique -> String
gradingTechniqueToString ThreePointGrading = "3-point"
gradingTechniqueToString LUTBasedGrading = "lut-based"
gradingTechniqueToString ManualAdjustment = "manual"
gradingTechniqueToString PresetBased = "preset"

-- | Parse grading technique from string.
parseGradingTechnique :: String -> Maybe ColorGradingTechnique
parseGradingTechnique s = case String.toLower s of
  "3-point" -> Just ThreePointGrading
  "three-point" -> Just ThreePointGrading
  "3point" -> Just ThreePointGrading
  "lut-based" -> Just LUTBasedGrading
  "lut" -> Just LUTBasedGrading
  "manual" -> Just ManualAdjustment
  "preset" -> Just PresetBased
  "presets" -> Just PresetBased
  _ -> Nothing

-- | Color grading specification.
type ColorGradingSpec =
  { technique :: ColorGradingTechnique
  , targetPalette :: Array String      -- Target hex colors
  , notes :: String                    -- Additional guidance
  }

-- | Create color grading spec.
mkColorGradingSpec
  :: ColorGradingTechnique
  -> Array String
  -> String
  -> Maybe ColorGradingSpec
mkColorGradingSpec tech palette notes =
  if Array.length palette >= 1 && String.length notes >= 1
    then Just
      { technique: tech
      , targetPalette: palette
      , notes: notes
      }
    else Nothing

-- | Get grading technique.
gradingTechnique :: ColorGradingSpec -> ColorGradingTechnique
gradingTechnique cgs = cgs.technique

-- | Get target palette.
gradingTargetPalette :: ColorGradingSpec -> Array String
gradingTargetPalette cgs = cgs.targetPalette

-- | Get grading notes.
gradingNotes :: ColorGradingSpec -> String
gradingNotes cgs = cgs.notes

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // image quality requirement
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Type of image quality requirement.
data ImageQualityRequirement
  = SharpnessRequired    -- Images must be sharp
  | ReadableText         -- On-screen text must be readable
  | ClearFaces           -- Faces must be clear, no overlays
  | MinResolution        -- Minimum resolution required
  | NoBlur               -- No blur unless intentional

derive instance eqImageQualityRequirement :: Eq ImageQualityRequirement

instance ordImageQualityRequirement :: Ord ImageQualityRequirement where
  compare q1 q2 = compare (qualToInt q1) (qualToInt q2)
    where
      qualToInt :: ImageQualityRequirement -> Int
      qualToInt SharpnessRequired = 0
      qualToInt ReadableText = 1
      qualToInt ClearFaces = 2
      qualToInt MinResolution = 3
      qualToInt NoBlur = 4

instance showImageQualityRequirement :: Show ImageQualityRequirement where
  show = qualityRequirementToString

-- | Convert quality requirement to string.
qualityRequirementToString :: ImageQualityRequirement -> String
qualityRequirementToString SharpnessRequired = "sharpness"
qualityRequirementToString ReadableText = "readable-text"
qualityRequirementToString ClearFaces = "clear-faces"
qualityRequirementToString MinResolution = "min-resolution"
qualityRequirementToString NoBlur = "no-blur"

-- | Parse quality requirement from string.
parseQualityRequirement :: String -> Maybe ImageQualityRequirement
parseQualityRequirement s = case String.toLower s of
  "sharpness" -> Just SharpnessRequired
  "sharp" -> Just SharpnessRequired
  "readable-text" -> Just ReadableText
  "readable" -> Just ReadableText
  "text" -> Just ReadableText
  "clear-faces" -> Just ClearFaces
  "faces" -> Just ClearFaces
  "min-resolution" -> Just MinResolution
  "resolution" -> Just MinResolution
  "no-blur" -> Just NoBlur
  "blur" -> Just NoBlur
  _ -> Nothing

-- | Quality rule specification.
type QualityRule =
  { requirement :: ImageQualityRequirement
  , description :: String
  , exception :: String    -- When this rule can be relaxed
  }

-- | Create quality rule.
mkQualityRule
  :: ImageQualityRequirement
  -> String
  -> String
  -> Maybe QualityRule
mkQualityRule req desc exception =
  if String.length desc >= 1
    then Just
      { requirement: req
      , description: desc
      , exception: exception
      }
    else Nothing

-- | Get quality requirement type.
qualityRequirement :: QualityRule -> ImageQualityRequirement
qualityRequirement qr = qr.requirement

-- | Get quality description.
qualityDescription :: QualityRule -> String
qualityDescription qr = qr.description

-- | Get quality exception.
qualityException :: QualityRule -> String
qualityException qr = qr.exception

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // image tone
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Image tone attribute.
type ImageToneAttribute =
  { name :: String           -- e.g., "warmth", "approachability"
  , description :: String    -- What this conveys
  }

-- | Create image tone attribute.
mkImageToneAttribute :: String -> String -> Maybe ImageToneAttribute
mkImageToneAttribute name desc =
  if String.length name >= 1 && String.length desc >= 1
    then Just { name: name, description: desc }
    else Nothing

-- | Get tone attribute name.
toneAttributeName :: ImageToneAttribute -> String
toneAttributeName ita = ita.name

-- | Get tone attribute description.
toneAttributeDescription :: ImageToneAttribute -> String
toneAttributeDescription ita = ita.description

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // image content strategy
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Image content strategy.
type ImageContentStrategy =
  { purpose :: String              -- Role imagery plays in brand
  , colorGrading :: ColorGradingSpec
  , approvalProcess :: String      -- How non-palette images are approved
  }

-- | Create image content strategy.
mkImageContentStrategy
  :: String
  -> ColorGradingSpec
  -> String
  -> Maybe ImageContentStrategy
mkImageContentStrategy purpose grading approval =
  if String.length purpose >= 1 && String.length approval >= 1
    then Just
      { purpose: purpose
      , colorGrading: grading
      , approvalProcess: approval
      }
    else Nothing

-- | Get strategy purpose.
strategyPurpose :: ImageContentStrategy -> String
strategyPurpose ics = ics.purpose

-- | Get color grading spec.
strategyColorGrading :: ImageContentStrategy -> ColorGradingSpec
strategyColorGrading ics = ics.colorGrading

-- | Get approval process.
strategyApprovalProcess :: ImageContentStrategy -> String
strategyApprovalProcess ics = ics.approvalProcess

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // image usage rule
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Image usage rule.
type ImageUsageRule =
  { name :: String            -- Rule identifier
  , description :: String     -- Full rule description
  , mandatory :: Boolean      -- Whether this rule is mandatory
  }

-- | Create image usage rule.
mkImageUsageRule :: String -> String -> Boolean -> Maybe ImageUsageRule
mkImageUsageRule name desc mandatory =
  if String.length name >= 1 && String.length desc >= 1
    then Just
      { name: name
      , description: desc
      , mandatory: mandatory
      }
    else Nothing

-- | Get usage rule name.
usageRuleName :: ImageUsageRule -> String
usageRuleName iur = iur.name

-- | Get usage rule description.
usageRuleDescription :: ImageUsageRule -> String
usageRuleDescription iur = iur.description

-- | Check if usage rule is mandatory.
usageRuleMandatory :: ImageUsageRule -> Boolean
usageRuleMandatory iur = iur.mandatory

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // imagery specification
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete imagery specification for a brand.
type ImagerySpecification =
  { contentStrategy :: ImageContentStrategy
  , categories :: Array ImageCategory
  , qualityRules :: Array QualityRule
  , toneAttributes :: Array ImageToneAttribute
  , usageRules :: Array ImageUsageRule
  }

-- | Create imagery specification.
mkImagerySpecification
  :: ImageContentStrategy
  -> Array ImageCategory
  -> Array QualityRule
  -> Array ImageToneAttribute
  -> Array ImageUsageRule
  -> Maybe ImagerySpecification
mkImagerySpecification strategy categories quality tone usage =
  if Array.length categories >= 1
    then Just
      { contentStrategy: strategy
      , categories: categories
      , qualityRules: quality
      , toneAttributes: tone
      , usageRules: usage
      }
    else Nothing

-- | Get content strategy.
specContentStrategy :: ImagerySpecification -> ImageContentStrategy
specContentStrategy is = is.contentStrategy

-- | Get image categories.
specCategories :: ImagerySpecification -> Array ImageCategory
specCategories is = is.categories

-- | Get quality rules.
specQualityRules :: ImagerySpecification -> Array QualityRule
specQualityRules is = is.qualityRules

-- | Get tone attributes.
specToneAttributes :: ImagerySpecification -> Array ImageToneAttribute
specToneAttributes is = is.toneAttributes

-- | Get usage rules.
specUsageRules :: ImagerySpecification -> Array ImageUsageRule
specUsageRules is = is.usageRules
