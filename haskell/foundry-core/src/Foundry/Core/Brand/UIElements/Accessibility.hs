{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                // foundry // core // brand // uielements // accessibility
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.UIElements.Accessibility
Description : Accessibility requirements and rules
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines accessibility-related types including WCAG requirements,
touch targets, focus indicators, and reduced motion preferences.

== SMART Brand Framework Section

Accessibility ensures inclusive brand experiences across all users
and complies with WCAG 2.1 AA/AAA standards.

== Dependencies

Requires: text, aeson
Required by: Foundry.Core.Brand.UIElements

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.UIElements.Accessibility
  ( -- * Accessibility Requirement
    AccessibilityRequirement (..)
  , accessibilityRequirementToText
  , parseAccessibilityRequirement

    -- * Accessibility Rule
  , AccessibilityRule (..)
  , mkAccessibilityRule
  ) where

import Data.Aeson
  ( FromJSON (..)
  , ToJSON (..)
  , object
  , withObject
  , withText
  , (.:)
  , (.=)
  )
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Accessibility Requirement
--------------------------------------------------------------------------------

-- | Type of accessibility requirement.
data AccessibilityRequirement
  = MinContrastRatio  -- ^ WCAG contrast requirement (4.5:1 AA, 7:1 AAA)
  | StrokeRequired    -- ^ Stroke on neumorphic/soft elements for visibility
  | FocusIndicator    -- ^ Visible focus state for keyboard navigation
  | TouchTargetSize   -- ^ Minimum touch target (44x44px recommended)
  | ReducedMotion     -- ^ Respect prefers-reduced-motion media query
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

-- | Convert accessibility requirement to text.
accessibilityRequirementToText :: AccessibilityRequirement -> Text
accessibilityRequirementToText MinContrastRatio = "min-contrast-ratio"
accessibilityRequirementToText StrokeRequired   = "stroke-required"
accessibilityRequirementToText FocusIndicator   = "focus-indicator"
accessibilityRequirementToText TouchTargetSize  = "touch-target-size"
accessibilityRequirementToText ReducedMotion    = "reduced-motion"

-- | Parse accessibility requirement from text.
parseAccessibilityRequirement :: Text -> Maybe AccessibilityRequirement
parseAccessibilityRequirement t = case T.toLower t of
  "min-contrast-ratio" -> Just MinContrastRatio
  "contrast"           -> Just MinContrastRatio
  "wcag-contrast"      -> Just MinContrastRatio
  "stroke-required"    -> Just StrokeRequired
  "stroke"             -> Just StrokeRequired
  "focus-indicator"    -> Just FocusIndicator
  "focus"              -> Just FocusIndicator
  "focus-ring"         -> Just FocusIndicator
  "touch-target-size"  -> Just TouchTargetSize
  "touch-target"       -> Just TouchTargetSize
  "tap-target"         -> Just TouchTargetSize
  "reduced-motion"     -> Just ReducedMotion
  "prefers-reduced-motion" -> Just ReducedMotion
  _                    -> Nothing

instance ToJSON AccessibilityRequirement where
  toJSON = toJSON . accessibilityRequirementToText

instance FromJSON AccessibilityRequirement where
  parseJSON = withText "AccessibilityRequirement" $ \t ->
    case parseAccessibilityRequirement t of
      Just req -> pure req
      Nothing  -> fail $ "Invalid accessibility requirement: " <> T.unpack t

--------------------------------------------------------------------------------
-- Accessibility Rule
--------------------------------------------------------------------------------

-- | An accessibility rule with requirement type, value, and description.
data AccessibilityRule = AccessibilityRule
  { arRequirement  :: !AccessibilityRequirement
    -- ^ The type of requirement
  , arValue        :: !Text
    -- ^ The value (e.g., "4.5:1", "44px", "true")
  , arDescription  :: !Text
    -- ^ Human-readable explanation
  }
  deriving stock (Eq, Show, Generic)

-- | Create accessibility rule with validation.
mkAccessibilityRule
  :: AccessibilityRequirement
  -> Text   -- ^ Value
  -> Text   -- ^ Description
  -> Maybe AccessibilityRule
mkAccessibilityRule req val desc
  | T.length val >= 1
  , T.length desc >= 1
  = Just AccessibilityRule
      { arRequirement = req
      , arValue       = val
      , arDescription = desc
      }
  | otherwise = Nothing

instance ToJSON AccessibilityRule where
  toJSON AccessibilityRule{..} = object
    [ "requirement"  .= arRequirement
    , "value"        .= arValue
    , "description"  .= arDescription
    ]

instance FromJSON AccessibilityRule where
  parseJSON = withObject "AccessibilityRule" $ \o -> do
    arRequirement  <- o .: "requirement"
    arValue        <- o .: "value"
    arDescription  <- o .: "description"
    pure AccessibilityRule{..}
