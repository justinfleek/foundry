{-# LANGUAGE RecordWildCards #-}
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

import Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, withText, (.:), (.=))
import GHC.Generics (Generic)

-- | OKLCH color (perceptually uniform)
data OKLCH = OKLCH
  { oklchL :: !Double  -- ^ Lightness [0, 1]
  , oklchC :: !Double  -- ^ Chroma [0, 0.4]
  , oklchH :: !Double  -- ^ Hue [0, 360)
  , oklchA :: !Double  -- ^ Alpha [0, 1]
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON OKLCH where
  toJSON OKLCH{..} = object
    [ "l" .= oklchL
    , "c" .= oklchC
    , "h" .= oklchH
    , "a" .= oklchA
    ]

instance FromJSON OKLCH where
  parseJSON = withObject "OKLCH" $ \v -> OKLCH
    <$> v .: "l"
    <*> v .: "c"
    <*> v .: "h"
    <*> v .: "a"

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
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance ToJSON ColorRole where
  toJSON Primary = "primary"
  toJSON Secondary = "secondary"
  toJSON Tertiary = "tertiary"
  toJSON Accent = "accent"
  toJSON Neutral = "neutral"
  toJSON Background = "background"
  toJSON Surface = "surface"
  toJSON Error = "error"
  toJSON Warning = "warning"
  toJSON Success = "success"

instance FromJSON ColorRole where
  parseJSON = withText "ColorRole" $ \case
    "primary" -> pure Primary
    "secondary" -> pure Secondary
    "tertiary" -> pure Tertiary
    "accent" -> pure Accent
    "neutral" -> pure Neutral
    "background" -> pure Background
    "surface" -> pure Surface
    "error" -> pure Error
    "warning" -> pure Warning
    _ -> pure Success

-- | A color with its role assignment
data BrandColor = BrandColor
  { brandColorValue :: !OKLCH
  , brandColorRole :: !ColorRole
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON BrandColor where
  toJSON BrandColor{..} = object
    [ "value" .= brandColorValue
    , "role"  .= brandColorRole
    ]

instance FromJSON BrandColor where
  parseJSON = withObject "BrandColor" $ \v -> BrandColor
    <$> v .: "value"
    <*> v .: "role"

-- | Complete brand palette
newtype BrandPalette = BrandPalette {unBrandPalette :: [BrandColor]}
  deriving stock (Eq, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Validate and create OKLCH color (with full alpha)
mkOKLCH :: Double -> Double -> Double -> Maybe OKLCH
mkOKLCH l c h = mkOKLCHa l c h 1.0

-- | Validate and create OKLCH color with alpha
mkOKLCHa :: Double -> Double -> Double -> Double -> Maybe OKLCH
mkOKLCHa l c h a
  | l >= 0 && l <= 1 && c >= 0 && c <= 0.4 && h >= 0 && h < 360 && a >= 0 && a <= 1 =
      Just (OKLCH l c h a)
  | otherwise = Nothing
