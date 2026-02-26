{- |
Module      : Foundry.Core.Brand.Spacing
Description : Spacing scale types
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Spacing units and scales for consistent layouts.
-}
module Foundry.Core.Brand.Spacing
  ( -- * Types
    SpacingUnit (..)
  , SpacingScale (..)
  ) where

-- | Spacing unit in rem
newtype SpacingUnit = SpacingUnit {unSpacingUnit :: Double}
  deriving stock (Eq, Ord, Show)

-- | Spacing scale (base and ratio, like type scale)
data SpacingScale = SpacingScale
  { spacingScaleBase :: !Double   -- ^ Base spacing in rem
  , spacingScaleRatio :: !Double  -- ^ Scale ratio
  }
  deriving stock (Eq, Show)
