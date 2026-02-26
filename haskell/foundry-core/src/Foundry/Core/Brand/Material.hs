{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                             // foundry // core // brand // material
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Material
Description : Material design system (shadows, elevation, surfaces)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines the material/surface design system including elevation levels,
shadow definitions, border radii, and surface treatments.

== SMART Brand Framework Section

This module implements material design specifications for UI elements.

== Dependencies

Requires: vector, text, aeson
Required by: Foundry.Core.Brand.Complete

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Material
  ( -- * Elevation
    ElevationLevel (..)
  , elevationLevelToInt
  , intToElevationLevel
  , ElevationScale (..)
  , mkElevationScale
  , defaultElevationScale

    -- * Shadows
  , ShadowLayer (..)
  , mkShadowLayer
  , ShadowDefinition (..)
  , mkShadowDefinition
  , ShadowScale (..)
  , mkShadowScale

    -- * Border Radius
  , RadiusSize (..)
  , radiusSizeToText
  , RadiusValue (..)
  , mkRadiusValue
  , RadiusScale (..)
  , mkRadiusScale
  , defaultRadiusScale

    -- * Surface
  , SurfaceType (..)
  , surfaceTypeToText
  , SurfaceOpacity (..)
  , mkSurfaceOpacity
  , Surface (..)
  , mkSurface

    -- * Material System
  , MaterialSystem (..)
  , mkMaterialSystem
  ) where

import Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, withText, (.:), (.=))
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as V
import GHC.Generics (Generic)

import Foundry.Core.Brand.Palette (OKLCH)

--------------------------------------------------------------------------------
-- Elevation
--------------------------------------------------------------------------------

-- | Elevation level (0-5, following Material Design conventions)
data ElevationLevel
  = Elevation0  -- ^ Flat, no elevation
  | Elevation1  -- ^ Slight raise (cards, buttons)
  | Elevation2  -- ^ Raised (app bar, menus)
  | Elevation3  -- ^ Higher (dialogs, popovers)
  | Elevation4  -- ^ High (modals, drawers)
  | Elevation5  -- ^ Highest (tooltips, dropdowns)
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

instance ToJSON ElevationLevel where
  toJSON = toJSON . elevationLevelToInt

instance FromJSON ElevationLevel where
  parseJSON v = do
    n <- parseJSON v
    pure $ intToElevationLevel n

-- | Convert elevation to integer
elevationLevelToInt :: ElevationLevel -> Int
elevationLevelToInt Elevation0 = 0
elevationLevelToInt Elevation1 = 1
elevationLevelToInt Elevation2 = 2
elevationLevelToInt Elevation3 = 3
elevationLevelToInt Elevation4 = 4
elevationLevelToInt Elevation5 = 5

-- | Convert integer to elevation (clamped)
intToElevationLevel :: Int -> ElevationLevel
intToElevationLevel n
  | n <= 0 = Elevation0
  | n == 1 = Elevation1
  | n == 2 = Elevation2
  | n == 3 = Elevation3
  | n == 4 = Elevation4
  | otherwise = Elevation5

-- | Elevation scale mapping levels to pixel values
data ElevationScale = ElevationScale
  { esLevel0 :: !Double  -- ^ Always 0
  , esLevel1 :: !Double
  , esLevel2 :: !Double
  , esLevel3 :: !Double
  , esLevel4 :: !Double
  , esLevel5 :: !Double
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ElevationScale where
  toJSON ElevationScale{..} = object
    [ "0" .= esLevel0
    , "1" .= esLevel1
    , "2" .= esLevel2
    , "3" .= esLevel3
    , "4" .= esLevel4
    , "5" .= esLevel5
    ]

instance FromJSON ElevationScale where
  parseJSON = withObject "ElevationScale" $ \v -> ElevationScale
    <$> v .: "0"
    <*> v .: "1"
    <*> v .: "2"
    <*> v .: "3"
    <*> v .: "4"
    <*> v .: "5"

-- | Smart constructor (values must be monotonically increasing)
mkElevationScale :: Double -> Double -> Double -> Double -> Double -> Maybe ElevationScale
mkElevationScale l1 l2 l3 l4 l5
  | l1 > 0 && l2 > l1 && l3 > l2 && l4 > l3 && l5 > l4 = 
      Just $ ElevationScale 0 l1 l2 l3 l4 l5
  | otherwise = Nothing

-- | Default elevation scale (Material Design inspired)
defaultElevationScale :: ElevationScale
defaultElevationScale = ElevationScale
  { esLevel0 = 0
  , esLevel1 = 1
  , esLevel2 = 3
  , esLevel3 = 6
  , esLevel4 = 8
  , esLevel5 = 12
  }

--------------------------------------------------------------------------------
-- Shadows
--------------------------------------------------------------------------------

-- | A single shadow layer (CSS box-shadow component)
data ShadowLayer = ShadowLayer
  { slOffsetX :: !Double
    -- ^ Horizontal offset in pixels
  , slOffsetY :: !Double
    -- ^ Vertical offset in pixels
  , slBlur    :: !Double
    -- ^ Blur radius in pixels
  , slSpread  :: !Double
    -- ^ Spread radius in pixels
  , slColor   :: !OKLCH
    -- ^ Shadow color (with alpha)
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ShadowLayer where
  toJSON ShadowLayer{..} = object
    [ "offsetX" .= slOffsetX
    , "offsetY" .= slOffsetY
    , "blur"    .= slBlur
    , "spread"  .= slSpread
    , "color"   .= slColor
    ]

instance FromJSON ShadowLayer where
  parseJSON = withObject "ShadowLayer" $ \v -> ShadowLayer
    <$> v .: "offsetX"
    <*> v .: "offsetY"
    <*> v .: "blur"
    <*> v .: "spread"
    <*> v .: "color"

-- | Smart constructor
mkShadowLayer :: Double -> Double -> Double -> Double -> OKLCH -> Maybe ShadowLayer
mkShadowLayer x y blur spread color
  | blur >= 0 && not (isNaN blur) && not (isInfinite blur) = 
      Just $ ShadowLayer x y blur spread color
  | otherwise = Nothing

-- | Complete shadow definition (can have multiple layers)
data ShadowDefinition = ShadowDefinition
  { sdElevation :: !ElevationLevel
    -- ^ Which elevation this shadow represents
  , sdLayers    :: !(Vector ShadowLayer)
    -- ^ Shadow layers (applied in order)
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ShadowDefinition where
  toJSON ShadowDefinition{..} = object
    [ "elevation" .= sdElevation
    , "layers"    .= sdLayers
    ]

instance FromJSON ShadowDefinition where
  parseJSON = withObject "ShadowDefinition" $ \v -> ShadowDefinition
    <$> v .: "elevation"
    <*> v .: "layers"

-- | Smart constructor
mkShadowDefinition :: ElevationLevel -> Vector ShadowLayer -> ShadowDefinition
mkShadowDefinition = ShadowDefinition

-- | Complete shadow scale for all elevations
newtype ShadowScale = ShadowScale (Vector ShadowDefinition)
  deriving stock (Eq, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor (should have definitions for all elevations)
mkShadowScale :: Vector ShadowDefinition -> ShadowScale
mkShadowScale = ShadowScale

--------------------------------------------------------------------------------
-- Border Radius
--------------------------------------------------------------------------------

-- | Named radius sizes
data RadiusSize
  = RadiusNone   -- ^ 0
  | RadiusSm     -- ^ Small
  | RadiusMd     -- ^ Medium (default)
  | RadiusLg     -- ^ Large
  | RadiusXl     -- ^ Extra large
  | Radius2xl    -- ^ 2x large
  | RadiusFull   -- ^ Fully rounded (pill shape)
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

instance ToJSON RadiusSize where
  toJSON = toJSON . radiusSizeToText

instance FromJSON RadiusSize where
  parseJSON = withText "RadiusSize" $ \case
    "none" -> pure RadiusNone
    "sm"   -> pure RadiusSm
    "md"   -> pure RadiusMd
    "lg"   -> pure RadiusLg
    "xl"   -> pure RadiusXl
    "2xl"  -> pure Radius2xl
    "full" -> pure RadiusFull
    _      -> pure RadiusMd

-- | Convert to text
radiusSizeToText :: RadiusSize -> Text
radiusSizeToText RadiusNone = "none"
radiusSizeToText RadiusSm = "sm"
radiusSizeToText RadiusMd = "md"
radiusSizeToText RadiusLg = "lg"
radiusSizeToText RadiusXl = "xl"
radiusSizeToText Radius2xl = "2xl"
radiusSizeToText RadiusFull = "full"

-- | Radius value in pixels
newtype RadiusValue = RadiusValue Double
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor
mkRadiusValue :: Double -> Maybe RadiusValue
mkRadiusValue r
  | r >= 0 && not (isNaN r) && not (isInfinite r) = Just $ RadiusValue r
  | otherwise = Nothing

-- | Radius scale mapping sizes to values
data RadiusScale = RadiusScale
  { rsNone :: !RadiusValue
  , rsSm   :: !RadiusValue
  , rsMd   :: !RadiusValue
  , rsLg   :: !RadiusValue
  , rsXl   :: !RadiusValue
  , rs2xl  :: !RadiusValue
  , rsFull :: !RadiusValue
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON RadiusScale where
  toJSON RadiusScale{..} = object
    [ "none" .= rsNone
    , "sm"   .= rsSm
    , "md"   .= rsMd
    , "lg"   .= rsLg
    , "xl"   .= rsXl
    , "2xl"  .= rs2xl
    , "full" .= rsFull
    ]

instance FromJSON RadiusScale where
  parseJSON = withObject "RadiusScale" $ \v -> RadiusScale
    <$> v .: "none"
    <*> v .: "sm"
    <*> v .: "md"
    <*> v .: "lg"
    <*> v .: "xl"
    <*> v .: "2xl"
    <*> v .: "full"

-- | Smart constructor
mkRadiusScale 
  :: RadiusValue -> RadiusValue -> RadiusValue -> RadiusValue 
  -> RadiusValue -> RadiusValue -> RadiusValue 
  -> RadiusScale
mkRadiusScale = RadiusScale

-- | Default radius scale
defaultRadiusScale :: RadiusScale
defaultRadiusScale = RadiusScale
  { rsNone = RadiusValue 0
  , rsSm   = RadiusValue 2
  , rsMd   = RadiusValue 4
  , rsLg   = RadiusValue 8
  , rsXl   = RadiusValue 12
  , rs2xl  = RadiusValue 16
  , rsFull = RadiusValue 9999  -- Effectively infinite
  }

--------------------------------------------------------------------------------
-- Surface
--------------------------------------------------------------------------------

-- | Types of surfaces
data SurfaceType
  = SurfaceCard
    -- ^ Card/panel surface
  | SurfaceButton
    -- ^ Interactive button
  | SurfaceInput
    -- ^ Form input field
  | SurfaceModal
    -- ^ Modal/dialog surface
  | SurfaceTooltip
    -- ^ Tooltip/popover
  | SurfaceNavigation
    -- ^ Navigation element
  | SurfaceCustom !Text
    -- ^ Custom surface type
  deriving stock (Eq, Show, Generic)

instance ToJSON SurfaceType where
  toJSON SurfaceCard = "card"
  toJSON SurfaceButton = "button"
  toJSON SurfaceInput = "input"
  toJSON SurfaceModal = "modal"
  toJSON SurfaceTooltip = "tooltip"
  toJSON SurfaceNavigation = "navigation"
  toJSON (SurfaceCustom t) = toJSON t

instance FromJSON SurfaceType where
  parseJSON = withText "SurfaceType" $ \t ->
    pure $ case t of
      "card" -> SurfaceCard
      "button" -> SurfaceButton
      "input" -> SurfaceInput
      "modal" -> SurfaceModal
      "tooltip" -> SurfaceTooltip
      "navigation" -> SurfaceNavigation
      custom -> SurfaceCustom custom

-- | Convert to text
surfaceTypeToText :: SurfaceType -> Text
surfaceTypeToText SurfaceCard = "card"
surfaceTypeToText SurfaceButton = "button"
surfaceTypeToText SurfaceInput = "input"
surfaceTypeToText SurfaceModal = "modal"
surfaceTypeToText SurfaceTooltip = "tooltip"
surfaceTypeToText SurfaceNavigation = "navigation"
surfaceTypeToText (SurfaceCustom t) = t

-- | Surface opacity (0-1)
newtype SurfaceOpacity = SurfaceOpacity Double
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor
mkSurfaceOpacity :: Double -> Maybe SurfaceOpacity
mkSurfaceOpacity o
  | o >= 0 && o <= 1 && not (isNaN o) = Just $ SurfaceOpacity o
  | otherwise = Nothing

-- | Surface definition
data Surface = Surface
  { surfType      :: !SurfaceType
    -- ^ Type of surface
  , surfElevation :: !ElevationLevel
    -- ^ Elevation level
  , surfRadius    :: !RadiusSize
    -- ^ Corner radius
  , surfOpacity   :: !SurfaceOpacity
    -- ^ Background opacity
  , surfBlur      :: !(Maybe Double)
    -- ^ Backdrop blur (for glass effect)
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON Surface where
  toJSON Surface{..} = object
    [ "type"      .= surfType
    , "elevation" .= surfElevation
    , "radius"    .= surfRadius
    , "opacity"   .= surfOpacity
    , "blur"      .= surfBlur
    ]

instance FromJSON Surface where
  parseJSON = withObject "Surface" $ \v -> Surface
    <$> v .: "type"
    <*> v .: "elevation"
    <*> v .: "radius"
    <*> v .: "opacity"
    <*> v .: "blur"

-- | Smart constructor
mkSurface 
  :: SurfaceType 
  -> ElevationLevel 
  -> RadiusSize 
  -> SurfaceOpacity 
  -> Maybe Double 
  -> Surface
mkSurface = Surface

--------------------------------------------------------------------------------
-- Material System
--------------------------------------------------------------------------------

-- | Complete material design system
data MaterialSystem = MaterialSystem
  { msElevation :: !ElevationScale
    -- ^ Elevation scale
  , msShadows   :: !ShadowScale
    -- ^ Shadow definitions
  , msRadii     :: !RadiusScale
    -- ^ Border radius scale
  , msSurfaces  :: !(Vector Surface)
    -- ^ Surface definitions
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON MaterialSystem where
  toJSON MaterialSystem{..} = object
    [ "elevation" .= msElevation
    , "shadows"   .= msShadows
    , "radii"     .= msRadii
    , "surfaces"  .= msSurfaces
    ]

instance FromJSON MaterialSystem where
  parseJSON = withObject "MaterialSystem" $ \v -> MaterialSystem
    <$> v .: "elevation"
    <*> v .: "shadows"
    <*> v .: "radii"
    <*> v .: "surfaces"

-- | Smart constructor
mkMaterialSystem 
  :: ElevationScale 
  -> ShadowScale 
  -> RadiusScale 
  -> Vector Surface 
  -> MaterialSystem
mkMaterialSystem = MaterialSystem
