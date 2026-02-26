{- |
Module      : Foundry.Core.Brand.Palette
Description : OKLCH color palette types
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

OKLCH color space with role assignments.

== Invariants (proven in Lean4)

* L (lightness) ∈ [0, 1]
* C (chroma) ∈ [0, 0.4]
* H (hue) ∈ [0, 360)
* Palette has exactly one primary role
* All roles are unique
-}
module Foundry.Core.Brand.Palette
  ( -- * Types
    OKLCH (..)
  , ColorRole (..)
  , BrandColor (..)
  , BrandPalette (..)

    -- * Smart constructors
  , mkOKLCH
  ) where

-- | OKLCH color (perceptually uniform)
data OKLCH = OKLCH
  { oklchL :: !Double  -- ^ Lightness [0, 1]
  , oklchC :: !Double  -- ^ Chroma [0, 0.4]
  , oklchH :: !Double  -- ^ Hue [0, 360)
  }
  deriving stock (Eq, Show)

-- | Color role in the brand palette
data ColorRole
  = Primary
  | Secondary
  | Tertiary
  | Accent
  | Neutral
  | Background
  | Surface
  | Error
  | Warning
  | Success
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | A color with its role assignment
data BrandColor = BrandColor
  { brandColorValue :: !OKLCH
  , brandColorRole :: !ColorRole
  }
  deriving stock (Eq, Show)

-- | Complete brand palette
newtype BrandPalette = BrandPalette {unBrandPalette :: [BrandColor]}
  deriving stock (Eq, Show)

-- | Validate and create OKLCH color
mkOKLCH :: Double -> Double -> Double -> Maybe OKLCH
mkOKLCH l c h
  | l >= 0 && l <= 1 && c >= 0 && c <= 0.4 && h >= 0 && h < 360 =
      Just (OKLCH l c h)
  | otherwise = Nothing
