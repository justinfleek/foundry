{- |
Module      : Metxt.Core.Brand.Typography
Description : Typography scale types
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Font families, weights, and type scale definitions.
-}
module Metxt.Core.Brand.Typography
  ( -- * Types
    FontWeight (..)
  , FontFamily (..)
  , TypeScale (..)
  , Typography (..)
  ) where

import Data.Text (Text)

-- | Font weight (100-900)
newtype FontWeight = FontWeight {unFontWeight :: !Int}
  deriving stock (Eq, Ord, Show)

-- | Font family specification
data FontFamily = FontFamily
  { fontFamilyName :: !Text
  , fontFamilyFallbacks :: ![Text]
  }
  deriving stock (Eq, Show)

-- | Type scale (base size and ratio)
data TypeScale = TypeScale
  { typeScaleBase :: !Double    -- ^ Base font size in rem
  , typeScaleRatio :: !Double   -- ^ Scale ratio (e.g., 1.25 for major third)
  }
  deriving stock (Eq, Show)

-- | Complete typography specification
data Typography = Typography
  { typographyHeadingFamily :: !FontFamily
  , typographyBodyFamily :: !FontFamily
  , typographyScale :: !TypeScale
  }
  deriving stock (Eq, Show)
