{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                               // foundry // core // brand // layout
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Layout
Description : Layout grid system and breakpoint definitions
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines the layout grid system including breakpoints, container widths,
column configurations, and content zones for responsive brand applications.

== SMART Brand Framework Section

This module implements Section 23-25 of the SMART Brand Framework:
- Grid System: Column counts, gutters, margins
- Breakpoints: Responsive design thresholds
- Content Zones: Header, main, sidebar, footer definitions

== Dependencies

Requires: vector, text, aeson
Required by: Foundry.Core.Brand.Complete

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Layout
  ( -- * Breakpoints
    Breakpoint (..)
  , BreakpointName (..)
  , mkBreakpointName
  , breakpointNameToText
  , BreakpointValue (..)
  , mkBreakpointValue
  , BreakpointSet (..)
  , mkBreakpointSet
  , defaultBreakpoints

    -- * Grid System
  , ColumnCount (..)
  , mkColumnCount
  , GutterWidth (..)
  , mkGutterWidth
  , MarginWidth (..)
  , mkMarginWidth
  , GridConfig (..)
  , mkGridConfig
  , ResponsiveGrid (..)
  , mkResponsiveGrid

    -- * Container
  , ContainerWidth (..)
  , mkContainerWidth
  , ContainerConfig (..)
  , mkContainerConfig

    -- * Content Zones
  , ContentZone (..)
  , ZoneName (..)
  , mkZoneName
  , zoneNameToText
  , ZoneConfig (..)
  , mkZoneConfig

    -- * Layout System
  , LayoutSystem (..)
  , mkLayoutSystem
  ) where

import Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, (.:), (.=))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Breakpoints
--------------------------------------------------------------------------------

-- | Named breakpoint for responsive design
newtype BreakpointName = BreakpointName Text
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor for breakpoint names
mkBreakpointName :: Text -> Maybe BreakpointName
mkBreakpointName t
  | T.null (T.strip t) = Nothing
  | otherwise = Just $ BreakpointName (T.strip t)

-- | Extract text from breakpoint name
breakpointNameToText :: BreakpointName -> Text
breakpointNameToText (BreakpointName t) = t

-- | Breakpoint value in pixels (must be positive)
newtype BreakpointValue = BreakpointValue Int
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor for breakpoint values
mkBreakpointValue :: Int -> Maybe BreakpointValue
mkBreakpointValue px
  | px > 0 = Just $ BreakpointValue px
  | otherwise = Nothing

-- | A single breakpoint definition
data Breakpoint = Breakpoint
  { bpName  :: !BreakpointName
    -- ^ Semantic name (e.g., "sm", "md", "lg")
  , bpValue :: !BreakpointValue
    -- ^ Minimum width in pixels
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON Breakpoint where
  toJSON Breakpoint{..} = object
    [ "name"  .= bpName
    , "value" .= bpValue
    ]

instance FromJSON Breakpoint where
  parseJSON = withObject "Breakpoint" $ \v -> Breakpoint
    <$> v .: "name"
    <*> v .: "value"

-- | Set of breakpoints (must be non-empty, ordered by value)
newtype BreakpointSet = BreakpointSet (Vector Breakpoint)
  deriving stock (Eq, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor ensures non-empty and sorted
mkBreakpointSet :: Vector Breakpoint -> Maybe BreakpointSet
mkBreakpointSet bps
  | V.null bps = Nothing
  | otherwise = Just $ BreakpointSet $ V.fromList $ 
      sortByValue $ V.toList bps
  where
    sortByValue = foldr insertSorted []
    insertSorted bp [] = [bp]
    insertSorted bp (x:xs)
      | bpValue bp <= bpValue x = bp : x : xs
      | otherwise = x : insertSorted bp xs

-- | Default breakpoint set (mobile-first)
defaultBreakpoints :: BreakpointSet
defaultBreakpoints = BreakpointSet $ V.fromList
  [ Breakpoint (BreakpointName "xs") (BreakpointValue 0)
  , Breakpoint (BreakpointName "sm") (BreakpointValue 640)
  , Breakpoint (BreakpointName "md") (BreakpointValue 768)
  , Breakpoint (BreakpointName "lg") (BreakpointValue 1024)
  , Breakpoint (BreakpointName "xl") (BreakpointValue 1280)
  , Breakpoint (BreakpointName "2xl") (BreakpointValue 1536)
  ]

--------------------------------------------------------------------------------
-- Grid System
--------------------------------------------------------------------------------

-- | Number of columns in grid (1-24)
newtype ColumnCount = ColumnCount Int
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor for column count
mkColumnCount :: Int -> Maybe ColumnCount
mkColumnCount n
  | n >= 1 && n <= 24 = Just $ ColumnCount n
  | otherwise = Nothing

-- | Gutter width in pixels (non-negative)
newtype GutterWidth = GutterWidth Double
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor for gutter width
mkGutterWidth :: Double -> Maybe GutterWidth
mkGutterWidth w
  | w >= 0 && not (isNaN w) && not (isInfinite w) = Just $ GutterWidth w
  | otherwise = Nothing

-- | Margin width in pixels (non-negative)
newtype MarginWidth = MarginWidth Double
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor for margin width
mkMarginWidth :: Double -> Maybe MarginWidth
mkMarginWidth w
  | w >= 0 && not (isNaN w) && not (isInfinite w) = Just $ MarginWidth w
  | otherwise = Nothing

-- | Grid configuration for a single breakpoint
data GridConfig = GridConfig
  { gcColumns :: !ColumnCount
    -- ^ Number of columns
  , gcGutter  :: !GutterWidth
    -- ^ Space between columns
  , gcMargin  :: !MarginWidth
    -- ^ Outer margin
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON GridConfig where
  toJSON GridConfig{..} = object
    [ "columns" .= gcColumns
    , "gutter"  .= gcGutter
    , "margin"  .= gcMargin
    ]

instance FromJSON GridConfig where
  parseJSON = withObject "GridConfig" $ \v -> GridConfig
    <$> v .: "columns"
    <*> v .: "gutter"
    <*> v .: "margin"

-- | Smart constructor for grid config
mkGridConfig :: ColumnCount -> GutterWidth -> MarginWidth -> GridConfig
mkGridConfig = GridConfig

-- | Responsive grid with configurations per breakpoint
data ResponsiveGrid = ResponsiveGrid
  { rgBreakpoints :: !BreakpointSet
    -- ^ Breakpoint definitions
  , rgConfigs     :: !(Vector (BreakpointName, GridConfig))
    -- ^ Grid config per breakpoint
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ResponsiveGrid where
  toJSON ResponsiveGrid{..} = object
    [ "breakpoints" .= rgBreakpoints
    , "configs"     .= rgConfigs
    ]

instance FromJSON ResponsiveGrid where
  parseJSON = withObject "ResponsiveGrid" $ \v -> ResponsiveGrid
    <$> v .: "breakpoints"
    <*> v .: "configs"

-- | Smart constructor for responsive grid
mkResponsiveGrid :: BreakpointSet -> Vector (BreakpointName, GridConfig) -> ResponsiveGrid
mkResponsiveGrid = ResponsiveGrid

--------------------------------------------------------------------------------
-- Container
--------------------------------------------------------------------------------

-- | Maximum container width in pixels
newtype ContainerWidth = ContainerWidth Double
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor for container width
mkContainerWidth :: Double -> Maybe ContainerWidth
mkContainerWidth w
  | w > 0 && not (isNaN w) && not (isInfinite w) = Just $ ContainerWidth w
  | otherwise = Nothing

-- | Container configuration per breakpoint
data ContainerConfig = ContainerConfig
  { ccBreakpoint :: !BreakpointName
    -- ^ At which breakpoint
  , ccMaxWidth   :: !(Maybe ContainerWidth)
    -- ^ Maximum width (Nothing = full width)
  , ccCentered   :: !Bool
    -- ^ Whether container is centered
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ContainerConfig where
  toJSON ContainerConfig{..} = object
    [ "breakpoint" .= ccBreakpoint
    , "maxWidth"   .= ccMaxWidth
    , "centered"   .= ccCentered
    ]

instance FromJSON ContainerConfig where
  parseJSON = withObject "ContainerConfig" $ \v -> ContainerConfig
    <$> v .: "breakpoint"
    <*> v .: "maxWidth"
    <*> v .: "centered"

-- | Smart constructor
mkContainerConfig :: BreakpointName -> Maybe ContainerWidth -> Bool -> ContainerConfig
mkContainerConfig = ContainerConfig

--------------------------------------------------------------------------------
-- Content Zones
--------------------------------------------------------------------------------

-- | Predefined content zone types
data ContentZone
  = ZoneHeader
  | ZoneNavigation
  | ZoneHero
  | ZoneMain
  | ZoneSidebar
  | ZoneFooter
  | ZoneModal
  | ZoneToast
  | ZoneCustom !ZoneName
  deriving stock (Eq, Show, Generic)

instance ToJSON ContentZone where
  toJSON ZoneHeader = "header"
  toJSON ZoneNavigation = "navigation"
  toJSON ZoneHero = "hero"
  toJSON ZoneMain = "main"
  toJSON ZoneSidebar = "sidebar"
  toJSON ZoneFooter = "footer"
  toJSON ZoneModal = "modal"
  toJSON ZoneToast = "toast"
  toJSON (ZoneCustom (ZoneName n)) = toJSON n

instance FromJSON ContentZone where
  parseJSON v = do
    t <- parseJSON v
    pure $ case t :: Text of
      "header" -> ZoneHeader
      "navigation" -> ZoneNavigation
      "hero" -> ZoneHero
      "main" -> ZoneMain
      "sidebar" -> ZoneSidebar
      "footer" -> ZoneFooter
      "modal" -> ZoneModal
      "toast" -> ZoneToast
      custom -> ZoneCustom (ZoneName custom)

-- | Custom zone name
newtype ZoneName = ZoneName Text
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor for zone name
mkZoneName :: Text -> Maybe ZoneName
mkZoneName t
  | T.null (T.strip t) = Nothing
  | otherwise = Just $ ZoneName (T.strip t)

-- | Extract text from zone name
zoneNameToText :: ZoneName -> Text
zoneNameToText (ZoneName t) = t

-- | Configuration for a content zone
data ZoneConfig = ZoneConfig
  { zcZone       :: !ContentZone
    -- ^ Which zone
  , zcColumnSpan :: !ColumnCount
    -- ^ How many columns it spans
  , zcSticky     :: !Bool
    -- ^ Whether zone is sticky
  , zcZIndex     :: !Int
    -- ^ Stacking order
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ZoneConfig where
  toJSON ZoneConfig{..} = object
    [ "zone"       .= zcZone
    , "columnSpan" .= zcColumnSpan
    , "sticky"     .= zcSticky
    , "zIndex"     .= zcZIndex
    ]

instance FromJSON ZoneConfig where
  parseJSON = withObject "ZoneConfig" $ \v -> ZoneConfig
    <$> v .: "zone"
    <*> v .: "columnSpan"
    <*> v .: "sticky"
    <*> v .: "zIndex"

-- | Smart constructor
mkZoneConfig :: ContentZone -> ColumnCount -> Bool -> Int -> ZoneConfig
mkZoneConfig = ZoneConfig

--------------------------------------------------------------------------------
-- Layout System
--------------------------------------------------------------------------------

-- | Complete layout system specification
data LayoutSystem = LayoutSystem
  { lsGrid       :: !ResponsiveGrid
    -- ^ Grid configuration
  , lsContainers :: !(Vector ContainerConfig)
    -- ^ Container configurations
  , lsZones      :: !(Vector ZoneConfig)
    -- ^ Content zone configurations
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON LayoutSystem where
  toJSON LayoutSystem{..} = object
    [ "grid"       .= lsGrid
    , "containers" .= lsContainers
    , "zones"      .= lsZones
    ]

instance FromJSON LayoutSystem where
  parseJSON = withObject "LayoutSystem" $ \v -> LayoutSystem
    <$> v .: "grid"
    <*> v .: "containers"
    <*> v .: "zones"

-- | Smart constructor
mkLayoutSystem :: ResponsiveGrid -> Vector ContainerConfig -> Vector ZoneConfig -> LayoutSystem
mkLayoutSystem = LayoutSystem
