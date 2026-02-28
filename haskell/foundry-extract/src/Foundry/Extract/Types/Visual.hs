{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // foundry // extract // types // visual
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Types.Visual
Description : Visual element types for pixel-perfect website extraction
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Types representing visual elements extracted from web pages with exact
pixel coordinates, enabling pixel-perfect reconstruction as pure data.

== Design Notes

A VisualElement captures everything needed to render an element:
- Bounding box (x, y, width, height)
- Z-index for stacking order
- Visual styles (colors, fonts, shadows)
- Optional screenshot of the element itself

The VisualDecomposition groups elements into layers by z-index,
enabling composited rendering from back to front.

== Dependencies

Requires: aeson, bytestring, text, vector
Required by: Foundry.Extract.Compose, Foundry.Core.GPU.Renderer

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Types.Visual
  ( -- * Visual Elements
    VisualElement (..)
  , VisualElementType (..)
  
    -- * Geometry
  , BoundingBox (..)
  , Dimensions (..)
  
    -- * Styles
  , VisualStyles (..)
  
    -- * Decomposition
  , VisualDecomposition (..)
  , VisualLayer (..)
  ) where

import Data.Aeson (FromJSON (..), ToJSON (..), withObject, (.:), (.:?), (.=), object)
import Data.ByteString (ByteString)
import Data.ByteString.Base64 qualified as Base64
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import Data.Vector (Vector)
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Bounding Box and Dimensions
--------------------------------------------------------------------------------

-- | Pixel-precise bounding box in page coordinates
data BoundingBox = BoundingBox
  { bbX      :: {-# UNPACK #-} !Double
    -- ^ X coordinate (left edge)
  , bbY      :: {-# UNPACK #-} !Double
    -- ^ Y coordinate (top edge)
  , bbWidth  :: {-# UNPACK #-} !Double
    -- ^ Width in pixels
  , bbHeight :: {-# UNPACK #-} !Double
    -- ^ Height in pixels
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON BoundingBox
instance ToJSON BoundingBox

-- | Width/height dimensions
data Dimensions = Dimensions
  { dimWidth  :: {-# UNPACK #-} !Double
    -- ^ Width in pixels
  , dimHeight :: {-# UNPACK #-} !Double
    -- ^ Height in pixels
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON Dimensions where
  parseJSON = withObject "Dimensions" $ \v -> Dimensions
    <$> v .: "width"
    <*> v .: "height"

instance ToJSON Dimensions where
  toJSON Dimensions{..} = object
    [ "width"  .= dimWidth
    , "height" .= dimHeight
    ]

--------------------------------------------------------------------------------
-- Visual Element Types
--------------------------------------------------------------------------------

-- | Semantic classification of visual elements
data VisualElementType
  = VEBackground     -- ^ Full-page or section backgrounds
  | VEHeader         -- ^ Header/navigation area
  | VENavigation     -- ^ Navigation menus
  | VELogo           -- ^ Logo images
  | VEHero           -- ^ Hero sections
  | VEHeading        -- ^ Headings (h1-h6)
  | VEParagraph      -- ^ Paragraph text
  | VEButton         -- ^ Buttons and CTAs
  | VELink           -- ^ Links
  | VEImage          -- ^ Images
  | VEIcon           -- ^ Icons
  | VECard           -- ^ Card components
  | VEForm           -- ^ Form elements
  | VEInput          -- ^ Input fields
  | VEFooter         -- ^ Footer area
  | VEContainer      -- ^ Generic container
  | VEUnknown        -- ^ Unclassified
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON VisualElementType
instance ToJSON VisualElementType

--------------------------------------------------------------------------------
-- Visual Styles
--------------------------------------------------------------------------------

-- | Visual styles relevant for rendering an element
data VisualStyles = VisualStyles
  { vsBackgroundColor    :: !(Maybe Text)
    -- ^ Background color (computed)
  , vsBackgroundImage    :: !(Maybe Text)
    -- ^ Background image URL
  , vsBackgroundGradient :: !(Maybe Text)
    -- ^ Background gradient (if any)
  , vsColor              :: !(Maybe Text)
    -- ^ Text color
  , vsFontFamily         :: !(Maybe Text)
    -- ^ Font family
  , vsFontSize           :: !(Maybe Double)
    -- ^ Font size in pixels
  , vsFontWeight         :: !(Maybe Int)
    -- ^ Font weight (100-900)
  , vsLineHeight         :: !(Maybe Double)
    -- ^ Line height
  , vsTextAlign          :: !(Maybe Text)
    -- ^ Text alignment
  , vsBorderRadius       :: !(Maybe Text)
    -- ^ Border radius (all corners)
  , vsBoxShadow          :: !(Maybe Text)
    -- ^ Box shadow
  , vsOpacity            :: !(Maybe Double)
    -- ^ Opacity (0-1)
  , vsTransform          :: !(Maybe Text)
    -- ^ Transform matrix
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON VisualStyles
instance ToJSON VisualStyles

--------------------------------------------------------------------------------
-- Visual Element
--------------------------------------------------------------------------------

-- | A visual element extracted from the DOM with exact pixel coordinates.
-- 
-- Captures everything needed for pixel-perfect reconstruction:
-- - Identity and hierarchy
-- - Geometry (bounding box, z-index)
-- - Visual appearance (styles, colors)
-- - Content (text, image source)
-- - Optional screenshot
data VisualElement = VisualElement
  { veId         :: !Text
    -- ^ Unique identifier (CSS selector path)
  , veTagName    :: !Text
    -- ^ Element tag name (e.g., "div", "button")
  , veType       :: !VisualElementType
    -- ^ Semantic type of the element
  , veBounds     :: !BoundingBox
    -- ^ Bounding box in page coordinates
  , veZIndex     :: !Int
    -- ^ Z-index / stacking layer
  , veVisible    :: !Bool
    -- ^ Is element visible?
  , veStyles     :: !VisualStyles
    -- ^ Computed visual styles
  , veText       :: !(Maybe Text)
    -- ^ Text content (if any)
  , veImageSrc   :: !(Maybe Text)
    -- ^ Image source URL (if image element)
  , veScreenshot :: !(Maybe ByteString)
    -- ^ Screenshot of just this element (PNG bytes)
  , veParentId   :: !(Maybe Text)
    -- ^ Parent element ID
  , veChildIds   :: !(Vector Text)
    -- ^ Child element IDs
  }
  deriving stock (Eq, Show, Generic)

-- | Custom FromJSON for VisualElement to handle screenshot as Base64
instance FromJSON VisualElement where
  parseJSON = withObject "VisualElement" $ \v -> VisualElement
    <$> v .: "veId"
    <*> v .: "veTagName"
    <*> v .: "veType"
    <*> v .: "veBounds"
    <*> v .: "veZIndex"
    <*> v .: "veVisible"
    <*> v .: "veStyles"
    <*> v .:? "veText"
    <*> v .:? "veImageSrc"
    <*> (fmap decodeBase64 <$> v .:? "veScreenshot")
    <*> v .:? "veParentId"
    <*> v .: "veChildIds"
    where
      decodeBase64 :: Text -> ByteString
      decodeBase64 t = case Base64.decode (Text.encodeUtf8 t) of
        Left _err -> mempty
        Right bs  -> bs

-- | Custom ToJSON for VisualElement to encode screenshot as Base64
instance ToJSON VisualElement where
  toJSON VisualElement{..} = object
    [ "veId"         .= veId
    , "veTagName"    .= veTagName
    , "veType"       .= veType
    , "veBounds"     .= veBounds
    , "veZIndex"     .= veZIndex
    , "veVisible"    .= veVisible
    , "veStyles"     .= veStyles
    , "veText"       .= veText
    , "veImageSrc"   .= veImageSrc
    , "veScreenshot" .= fmap encodeBase64 veScreenshot
    , "veParentId"   .= veParentId
    , "veChildIds"   .= veChildIds
    ]
    where
      encodeBase64 :: ByteString -> Text
      encodeBase64 = Text.decodeUtf8 . Base64.encode

--------------------------------------------------------------------------------
-- Visual Layers
--------------------------------------------------------------------------------

-- | A visual layer (elements at same z-index)
data VisualLayer = VisualLayer
  { vlZIndex     :: !Int
    -- ^ Z-index of this layer
  , vlElementIds :: !(Vector Text)
    -- ^ Element IDs in this layer
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON VisualLayer
instance ToJSON VisualLayer

--------------------------------------------------------------------------------
-- Visual Decomposition
--------------------------------------------------------------------------------

-- | Complete visual decomposition of a web page.
--
-- Contains all information needed to reconstruct the page:
-- - Viewport and page dimensions
-- - All visual elements with geometry
-- - Layer structure for compositing
-- - Full page screenshot for reference
data VisualDecomposition = VisualDecomposition
  { vdViewport       :: !Dimensions
    -- ^ Viewport dimensions
  , vdPageSize       :: !Dimensions
    -- ^ Full page dimensions (including scroll)
  , vdElements       :: !(Vector VisualElement)
    -- ^ All visual elements in z-order (back to front)
  , vdFullScreenshot :: !ByteString
    -- ^ Full page screenshot (PNG bytes)
  , vdLayers         :: !(Vector VisualLayer)
    -- ^ Layers: elements grouped by z-index
  }
  deriving stock (Eq, Show, Generic)

-- | Custom FromJSON for VisualDecomposition to handle screenshot as Base64
instance FromJSON VisualDecomposition where
  parseJSON = withObject "VisualDecomposition" $ \v -> VisualDecomposition
    <$> v .: "vdViewport"
    <*> v .: "vdPageSize"
    <*> v .: "vdElements"
    <*> (decodeBase64 <$> v .: "vdFullScreenshot")
    <*> v .: "vdLayers"
    where
      decodeBase64 :: Text -> ByteString
      decodeBase64 t = case Base64.decode (Text.encodeUtf8 t) of
        Left _err -> mempty
        Right bs  -> bs

-- | Custom ToJSON for VisualDecomposition to encode screenshot as Base64
instance ToJSON VisualDecomposition where
  toJSON VisualDecomposition{..} = object
    [ "vdViewport"       .= vdViewport
    , "vdPageSize"       .= vdPageSize
    , "vdElements"       .= vdElements
    , "vdFullScreenshot" .= encodeBase64 vdFullScreenshot
    , "vdLayers"         .= vdLayers
    ]
    where
      encodeBase64 :: ByteString -> Text
      encodeBase64 = Text.decodeUtf8 . Base64.encode
