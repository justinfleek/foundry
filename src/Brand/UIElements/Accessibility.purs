-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // brand // uielements // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Accessibility requirements and rules.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | DEPENDENCIES:
-- |   - None (foundational module)
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.UIElements (main UI elements module)

module Hydrogen.Schema.Brand.UIElements.Accessibility
  ( -- * Accessibility Requirements
    AccessibilityRequirement
      ( MinContrastRatio
      , StrokeRequired
      , FocusIndicator
      , TouchTargetSize
      , ReducedMotion
      )
  , accessibilityRequirementToString
  
  -- * Accessibility Rule
  , AccessibilityRule
  , mkAccessibilityRule
  , accessibilityType
  , accessibilityValue
  , accessibilityDescription
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (>=)
  , (&&)
  , show
  , compare
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length) as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // accessibility requirement
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Type of accessibility requirement.
data AccessibilityRequirement
  = MinContrastRatio    -- WCAG contrast requirement
  | StrokeRequired      -- Stroke on neumorphic elements
  | FocusIndicator      -- Visible focus state
  | TouchTargetSize     -- Minimum touch target
  | ReducedMotion       -- Respect prefers-reduced-motion

derive instance eqAccessibilityRequirement :: Eq AccessibilityRequirement

instance ordAccessibilityRequirement :: Ord AccessibilityRequirement where
  compare a1 a2 = compare (accToInt a1) (accToInt a2)
    where
      accToInt :: AccessibilityRequirement -> Int
      accToInt MinContrastRatio = 0
      accToInt StrokeRequired = 1
      accToInt FocusIndicator = 2
      accToInt TouchTargetSize = 3
      accToInt ReducedMotion = 4

instance showAccessibilityRequirement :: Show AccessibilityRequirement where
  show = accessibilityRequirementToString

-- | Convert accessibility requirement to string.
accessibilityRequirementToString :: AccessibilityRequirement -> String
accessibilityRequirementToString MinContrastRatio = "min-contrast-ratio"
accessibilityRequirementToString StrokeRequired = "stroke-required"
accessibilityRequirementToString FocusIndicator = "focus-indicator"
accessibilityRequirementToString TouchTargetSize = "touch-target-size"
accessibilityRequirementToString ReducedMotion = "reduced-motion"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // accessibility rule
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Accessibility rule.
type AccessibilityRule =
  { requirement :: AccessibilityRequirement
  , value :: String               -- e.g., "4.5:1", "44px", "true"
  , description :: String         -- Explanation
  }

-- | Create accessibility rule.
mkAccessibilityRule
  :: AccessibilityRequirement
  -> String
  -> String
  -> Maybe AccessibilityRule
mkAccessibilityRule req val desc =
  if String.length val >= 1 && String.length desc >= 1
    then Just
      { requirement: req
      , value: val
      , description: desc
      }
    else Nothing

-- | Get requirement type.
accessibilityType :: AccessibilityRule -> AccessibilityRequirement
accessibilityType ar = ar.requirement

-- | Get requirement value.
accessibilityValue :: AccessibilityRule -> String
accessibilityValue ar = ar.value

-- | Get requirement description.
accessibilityDescription :: AccessibilityRule -> String
accessibilityDescription ar = ar.description
