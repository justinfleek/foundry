{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                             // foundry // core // brand // spacing
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Spacing
Description : Spacing scale types
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Spacing units and scales for consistent layouts.

== Design Notes

This module mirrors Hydrogen.Schema.Dimension.Spacing to ensure type
compatibility between backend extraction and frontend rendering.

Spacing systems typically use a base unit (often 4px or 8px) with a
multiplier scale. We support multiple CSS length units to preserve
the original unit type from scraped content.

== Dependencies

Requires: Nothing (leaf module)
Required by: Foundry.Core.Brand, Foundry.Extract.Spacing

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Spacing
  ( -- * Length Units
    LengthUnit (..)
  
    -- * Spacing Value
  , SpacingValue (..)
  , mkSpacingValue
  , spacingPx
  , spacingRem
  , spacingEm
  
    -- * Spacing Scale
  , SpacingScale (..)
  
    -- * Legacy (deprecated, for compatibility)
  , SpacingUnit (..)
  ) where

--------------------------------------------------------------------------------
-- Length Units
--------------------------------------------------------------------------------

-- | CSS length units supported by spacing values.
--
-- Mirrors Hydrogen.Schema.Dimension.Spacing.Unit for frontend compatibility.
data LengthUnit
  = Px       -- ^ CSS pixels (reference pixels at 96 PPI)
  | Rem      -- ^ Root em (relative to html font-size, typically 16px)
  | Em       -- ^ Em (relative to element font-size)
  | Percent  -- ^ Percentage of containing block
  | Vw       -- ^ Viewport width percentage
  | Vh       -- ^ Viewport height percentage
  | Vmin     -- ^ Minimum of vw/vh
  | Vmax     -- ^ Maximum of vw/vh
  deriving stock (Eq, Ord, Show, Enum, Bounded)

--------------------------------------------------------------------------------
-- Spacing Value
--------------------------------------------------------------------------------

-- | A spacing value with its unit.
--
-- Values are bounded to [-10000, 10000] to prevent layout-breaking extremes.
-- Negative values are allowed for margin offsets.
data SpacingValue = SpacingValue
  { svValue :: !Double      -- ^ Numeric value (clamped to bounds)
  , svUnit  :: !LengthUnit  -- ^ CSS length unit
  }
  deriving stock (Eq, Show)

instance Ord SpacingValue where
  compare a b = compare (svValue a) (svValue b)

-- | Smart constructor that clamps values to valid bounds.
--
-- Handles NaN and Infinity by defaulting to 0.
mkSpacingValue :: Double -> LengthUnit -> SpacingValue
mkSpacingValue v u = SpacingValue (clampSpacing (ensureFinite v)) u
  where
    clampSpacing x = max (-10000) (min 10000 x)
    ensureFinite x
      | isNaN x      = 0
      | isInfinite x = 0
      | otherwise    = x

-- | Construct spacing in CSS pixels.
spacingPx :: Double -> SpacingValue
spacingPx v = mkSpacingValue v Px

-- | Construct spacing in root ems.
spacingRem :: Double -> SpacingValue
spacingRem v = mkSpacingValue v Rem

-- | Construct spacing in ems.
spacingEm :: Double -> SpacingValue
spacingEm v = mkSpacingValue v Em

--------------------------------------------------------------------------------
-- Spacing Scale
--------------------------------------------------------------------------------

-- | Spacing scale (base and ratio, like type scale).
--
-- Used to generate consistent spacing values across a design system.
-- The scale generates values as: base * ratio^n for n in [-2, -1, 0, 1, 2, ...]
data SpacingScale = SpacingScale
  { spacingScaleBase  :: !Double  -- ^ Base spacing in rem
  , spacingScaleRatio :: !Double  -- ^ Scale ratio (typically 2.0 for doubling)
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Legacy Types (Deprecated)
--------------------------------------------------------------------------------

-- | Legacy spacing unit in rem.
--
-- DEPRECATED: Use 'SpacingValue' with 'LengthUnit' instead.
-- Kept for backward compatibility during migration.
newtype SpacingUnit = SpacingUnit {unSpacingUnit :: Double}
  deriving stock (Eq, Ord, Show)
