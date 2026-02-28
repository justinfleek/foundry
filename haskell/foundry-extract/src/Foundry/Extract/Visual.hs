{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // foundry // extract // visual
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Visual
Description : Visual decomposition compositor and renderer preparation
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Compositor that separates visual elements into semantic layers for rendering.
This module transforms a VisualDecomposition into render-ready data structures.

== Semantic Layers

Elements are grouped into layers for composited rendering:

1. Background Layer - Full-page and section backgrounds
2. Content Layer - Text, headings, paragraphs
3. Interactive Layer - Buttons, links, inputs
4. Media Layer - Images, icons, logos
5. Navigation Layer - Headers, nav menus, footers

== Dependencies

Requires: Foundry.Extract.Types.Visual
Required by: Foundry.Core.GPU.Renderer

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Visual
  ( -- * Compositor
    CompositorResult (..)
  , SemanticLayer (..)
  , SemanticLayerType (..)
  , composeLayers
  
    -- * Element Queries
  , findElementsByType
  , findElementById
  , findElementsInBounds
  , findElementsAtZIndex
  
    -- * Statistics
  , CompositionStats (..)
  , computeStats
  
    -- * Re-exports
  , module Foundry.Extract.Types.Visual
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as V
import Foundry.Extract.Types.Visual

--------------------------------------------------------------------------------
-- Semantic Layer Types
--------------------------------------------------------------------------------

-- | Types of semantic layers for rendering
data SemanticLayerType
  = SLBackground   -- ^ Backgrounds and containers
  | SLContent      -- ^ Text content (headings, paragraphs)
  | SLInteractive  -- ^ Interactive elements (buttons, links, inputs)
  | SLMedia        -- ^ Media elements (images, icons, logos)
  | SLNavigation   -- ^ Navigation (header, nav, footer)
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | A semantic layer containing elements of a particular type
data SemanticLayer = SemanticLayer
  { slType     :: !SemanticLayerType
    -- ^ Type of this layer
  , slElements :: !(Vector VisualElement)
    -- ^ Elements in this layer
  , slZRange   :: !(Int, Int)
    -- ^ Z-index range (min, max) for this layer
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Compositor Result
--------------------------------------------------------------------------------

-- | Result of composing visual elements into semantic layers
data CompositorResult = CompositorResult
  { crViewport   :: !Dimensions
    -- ^ Viewport dimensions
  , crPageSize   :: !Dimensions
    -- ^ Full page dimensions
  , crLayers     :: !(Map SemanticLayerType SemanticLayer)
    -- ^ Semantic layers by type
  , crAllElements :: !(Vector VisualElement)
    -- ^ All elements in z-order (back to front)
  , crElementIndex :: !(Map Text VisualElement)
    -- ^ Element lookup by ID
  , crStats      :: !CompositionStats
    -- ^ Statistics about the composition
  }
  deriving stock (Eq, Show)

-- | Statistics about a composition
data CompositionStats = CompositionStats
  { cssTotalElements   :: !Int
    -- ^ Total number of elements
  , cssBackgroundCount :: !Int
    -- ^ Number of background elements
  , cssContentCount    :: !Int
    -- ^ Number of content elements
  , cssInteractiveCount :: !Int
    -- ^ Number of interactive elements
  , cssMediaCount      :: !Int
    -- ^ Number of media elements
  , cssNavigationCount :: !Int
    -- ^ Number of navigation elements
  , cssZIndexLayers    :: !Int
    -- ^ Number of z-index layers
  , cssMaxZIndex       :: !Int
    -- ^ Maximum z-index
  , cssMinZIndex       :: !Int
    -- ^ Minimum z-index
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Main Composition Function
--------------------------------------------------------------------------------

-- | Compose visual elements into semantic layers.
--
-- This function takes a VisualDecomposition and organizes elements
-- into semantic layers suitable for rendering.
composeLayers :: VisualDecomposition -> CompositorResult
composeLayers VisualDecomposition{..} = CompositorResult
  { crViewport = vdViewport
  , crPageSize = vdPageSize
  , crLayers = layers
  , crAllElements = vdElements
  , crElementIndex = elementIndex
  , crStats = stats
  }
  where
    -- Build element index
    elementIndex :: Map Text VisualElement
    elementIndex = Map.fromList [(veId e, e) | e <- V.toList vdElements]

    -- Group elements by semantic type
    grouped :: Map SemanticLayerType (Vector VisualElement)
    grouped = Map.fromListWith (<>) 
      [(classifyLayer (veType e), V.singleton e) | e <- V.toList vdElements]

    -- Build semantic layers
    layers :: Map SemanticLayerType SemanticLayer
    layers = Map.mapWithKey buildLayer grouped

    buildLayer :: SemanticLayerType -> Vector VisualElement -> SemanticLayer
    buildLayer slt elems = SemanticLayer
      { slType = slt
      , slElements = elems
      , slZRange = computeZRange elems
      }

    -- Compute statistics
    stats :: CompositionStats
    stats = CompositionStats
      { cssTotalElements = V.length vdElements
      , cssBackgroundCount = maybe 0 (V.length . slElements) (Map.lookup SLBackground layers)
      , cssContentCount = maybe 0 (V.length . slElements) (Map.lookup SLContent layers)
      , cssInteractiveCount = maybe 0 (V.length . slElements) (Map.lookup SLInteractive layers)
      , cssMediaCount = maybe 0 (V.length . slElements) (Map.lookup SLMedia layers)
      , cssNavigationCount = maybe 0 (V.length . slElements) (Map.lookup SLNavigation layers)
      , cssZIndexLayers = V.length vdLayers
      , cssMaxZIndex = if V.null vdElements then 0 else V.maximum (V.map veZIndex vdElements)
      , cssMinZIndex = if V.null vdElements then 0 else V.minimum (V.map veZIndex vdElements)
      }

-- | Classify a VisualElementType into a SemanticLayerType
classifyLayer :: VisualElementType -> SemanticLayerType
classifyLayer = \case
  VEBackground  -> SLBackground
  VEContainer   -> SLBackground
  VEHeader      -> SLNavigation
  VENavigation  -> SLNavigation
  VEFooter      -> SLNavigation
  VELogo        -> SLMedia
  VEHero        -> SLBackground
  VEHeading     -> SLContent
  VEParagraph   -> SLContent
  VEButton      -> SLInteractive
  VELink        -> SLInteractive
  VEImage       -> SLMedia
  VEIcon        -> SLMedia
  VECard        -> SLBackground
  VEForm        -> SLInteractive
  VEInput       -> SLInteractive
  VEUnknown     -> SLBackground

-- | Compute the z-index range for a set of elements
computeZRange :: Vector VisualElement -> (Int, Int)
computeZRange elems
  | V.null elems = (0, 0)
  | otherwise = (V.minimum zs, V.maximum zs)
  where
    zs = V.map veZIndex elems

--------------------------------------------------------------------------------
-- Element Queries
--------------------------------------------------------------------------------

-- | Find all elements of a given type
findElementsByType :: VisualElementType -> CompositorResult -> Vector VisualElement
findElementsByType vt cr = V.filter ((== vt) . veType) (crAllElements cr)

-- | Find an element by ID
findElementById :: Text -> CompositorResult -> Maybe VisualElement
findElementById eid cr = Map.lookup eid (crElementIndex cr)

-- | Find elements within a bounding box
findElementsInBounds :: BoundingBox -> CompositorResult -> Vector VisualElement
findElementsInBounds bounds cr = V.filter (intersects bounds . veBounds) (crAllElements cr)
  where
    intersects :: BoundingBox -> BoundingBox -> Bool
    intersects a b =
      bbX a < bbX b + bbWidth b &&
      bbX a + bbWidth a > bbX b &&
      bbY a < bbY b + bbHeight b &&
      bbY a + bbHeight a > bbY b

-- | Find elements at a specific z-index
findElementsAtZIndex :: Int -> CompositorResult -> Vector VisualElement
findElementsAtZIndex z cr = V.filter ((== z) . veZIndex) (crAllElements cr)

--------------------------------------------------------------------------------
-- Statistics
--------------------------------------------------------------------------------

-- | Compute statistics from a VisualDecomposition
computeStats :: VisualDecomposition -> CompositionStats
computeStats vd = crStats (composeLayers vd)
