{- |
Module      : Metxt.Core.Brand.Strategy
Description : Strategic brand layer types
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Mission, vision, values, and brand positioning.
-}
module Metxt.Core.Brand.Strategy
  ( -- * Types
    MissionStatement (..)
  , Tagline (..)
  , BrandValue (..)
  , PersonalityTrait (..)
  , StrategicLayer (..)
  ) where

import Data.Text (Text)

-- | Mission statement (immutable after creation)
newtype MissionStatement = MissionStatement {unMissionStatement :: !Text}
  deriving stock (Eq, Show)

-- | Brand tagline
newtype Tagline = Tagline {unTagline :: !Text}
  deriving stock (Eq, Show)

-- | Core brand value
newtype BrandValue = BrandValue {unBrandValue :: !Text}
  deriving stock (Eq, Show)

-- | Brand personality trait
newtype PersonalityTrait = PersonalityTrait {unPersonalityTrait :: !Text}
  deriving stock (Eq, Show)

-- | Complete strategic layer
data StrategicLayer = StrategicLayer
  { strategicMission :: !MissionStatement
  , strategicTaglines :: ![Tagline]
  , strategicValues :: ![BrandValue]
  , strategicPersonality :: ![PersonalityTrait]
  }
  deriving stock (Eq, Show)
