{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // foundry // extract // types/asset
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Types.Asset
Description : Asset types for TOTAL brand ingestion
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Types for representing ALL brand assets:
  - Images (raster and vector)
  - SVG logos with full analysis
  - Icons
  - Videos
  - Documents (PDFs, brand guidelines)

== Design Notes

Logos are the most valuable brand asset. We capture:
  - Multiple variants (color, mono, reversed)
  - Size specifications (minimum, clear space)
  - Context (header, footer, favicon)
  - SVG internals (paths, colors, text)

== Dependencies

Requires: aeson, bytestring, text, vector
Required by: Foundry.Extract.Types, Foundry.Extract.Logo

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Types.Asset
  ( -- * Asset Types
    AssetType (..)
  , AssetContext (..)
  
    -- * Dimensions
  , AssetDimensions (..)
  
    -- * Basic Asset
  , AssetData (..)
  
    -- * Image Asset
  , ImageAsset (..)
  , ImageFormat (..)
  
    -- * SVG Logo
  , SVGLogoData (..)
  , SVGViewBox (..)
  , LogoVariant (..)
  , LogoContext (..)
  
    -- * Icon
  , IconData (..)
  , IconLibrary (..)
  
    -- * Video
  , VideoAsset (..)
  
    -- * Document
  , DocumentAsset (..)
  , DocumentType (..)
  
    -- * Complete Assets
  , AssetsComplete (..)
  ) where

import Data.Aeson (FromJSON, ToJSON)
import Data.ByteString (ByteString)
import Data.Text (Text)
import Data.Vector (Vector)
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Asset Types
--------------------------------------------------------------------------------

-- | Type of asset
data AssetType
  = ATImage       -- ^ Raster image (JPG, PNG, WebP, AVIF)
  | ATSVG         -- ^ Vector SVG
  | ATFavicon     -- ^ Favicon (ICO, PNG, SVG)
  | ATLogo        -- ^ Identified as logo
  | ATIcon        -- ^ UI icon
  | ATVideo       -- ^ Video file
  | ATAudio       -- ^ Audio file
  | ATDocument    -- ^ Document (PDF, etc.)
  | ATFont        -- ^ Font file
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON AssetType
instance ToJSON AssetType

-- | Context where asset appears
data AssetContext
  = CtxHeader     -- ^ Page header
  | CtxNavigation -- ^ Navigation area
  | CtxHero       -- ^ Hero section
  | CtxContent    -- ^ Main content
  | CtxSidebar    -- ^ Sidebar
  | CtxFooter     -- ^ Page footer
  | CtxMeta       -- ^ Meta tags (OG, favicon)
  | CtxBackground -- ^ CSS background
  | CtxInline     -- ^ Inline in text
  | CtxModal      -- ^ Modal/overlay
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON AssetContext
instance ToJSON AssetContext

--------------------------------------------------------------------------------
-- Dimensions
--------------------------------------------------------------------------------

-- | Asset dimensions
data AssetDimensions = AssetDimensions
  { adWidth    :: !Int     -- ^ Width in pixels
  , adHeight   :: !Int     -- ^ Height in pixels
  , adRatio    :: !Double  -- ^ Aspect ratio (width/height)
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON AssetDimensions
instance ToJSON AssetDimensions

--------------------------------------------------------------------------------
-- Basic Asset
--------------------------------------------------------------------------------

-- | Basic asset data (legacy compatible)
data AssetData = AssetData
  { adURL       :: !Text
  , adType      :: !AssetType
  , adAlt       :: !(Maybe Text)
  , adContext   :: !Text
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON AssetData
instance ToJSON AssetData

--------------------------------------------------------------------------------
-- Image Asset
--------------------------------------------------------------------------------

-- | Image format
data ImageFormat
  = ImgJPEG
  | ImgPNG
  | ImgWebP
  | ImgAVIF
  | ImgGIF
  | ImgBMP
  | ImgICO
  | ImgSVG
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON ImageFormat
instance ToJSON ImageFormat

-- | Complete image asset data
data ImageAsset = ImageAsset
  { iaURL          :: !Text
    -- ^ Image URL
  , iaFormat       :: !ImageFormat
    -- ^ Image format
  , iaDimensions   :: !(Maybe AssetDimensions)
    -- ^ Dimensions if known
  , iaAlt          :: !(Maybe Text)
    -- ^ Alt text
  , iaTitle        :: !(Maybe Text)
    -- ^ Title attribute
  , iaContext      :: !AssetContext
    -- ^ Where it appears
  , iaFileSize     :: !(Maybe Int)
    -- ^ File size in bytes
  , iaContentHash  :: !(Maybe ByteString)
    -- ^ SHA-256 hash
  , iaSrcset       :: !(Vector (Text, Maybe Int))
    -- ^ srcset entries (url, width)
  , iaSizes        :: !(Maybe Text)
    -- ^ sizes attribute
  , iaLoading      :: !(Maybe Text)
    -- ^ loading attribute (lazy, eager)
  , iaDecoding     :: !(Maybe Text)
    -- ^ decoding attribute (async, sync, auto)
  , iaDominantColor :: !(Maybe Text)
    -- ^ Dominant color (for placeholders)
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON ImageAsset
instance ToJSON ImageAsset

--------------------------------------------------------------------------------
-- SVG Logo
--------------------------------------------------------------------------------

-- | SVG viewBox
data SVGViewBox = SVGViewBox
  { vbMinX   :: !Double
  , vbMinY   :: !Double
  , vbWidth  :: !Double
  , vbHeight :: !Double
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON SVGViewBox
instance ToJSON SVGViewBox

-- | Logo variant
data LogoVariant
  = LogoFullColor      -- ^ Full color version
  | LogoMonochrome     -- ^ Single color
  | LogoReversed       -- ^ For dark backgrounds
  | LogoBlack          -- ^ Black version
  | LogoWhite          -- ^ White version
  | LogoGrayscale      -- ^ Grayscale
  | LogoIconOnly       -- ^ Symbol/icon without wordmark
  | LogoWordmarkOnly   -- ^ Wordmark without symbol
  | LogoStacked        -- ^ Stacked layout
  | LogoHorizontal     -- ^ Horizontal layout
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON LogoVariant
instance ToJSON LogoVariant

-- | Logo context (where it appears)
data LogoContext
  = LogoHeader         -- ^ In page header
  | LogoFooter         -- ^ In page footer
  | LogoFavicon        -- ^ As favicon
  | LogoOGImage        -- ^ In Open Graph meta
  | LogoAppleTouch     -- ^ Apple touch icon
  | LogoManifest       -- ^ Web manifest
  | LogoEmail          -- ^ Email signature
  | LogoPrint          -- ^ Print materials
  | LogoWatermark      -- ^ Watermark usage
  | LogoLoading        -- ^ Loading/splash screen
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON LogoContext
instance ToJSON LogoContext

-- | Complete SVG logo data
--
-- Full analysis of SVG logos for brand extraction.
data SVGLogoData = SVGLogoData
  { slURL           :: !Text
    -- ^ SVG URL
  , slRawContent    :: !(Maybe ByteString)
    -- ^ Raw SVG content (if fetched)
  , slContentHash   :: !(Maybe ByteString)
    -- ^ SHA-256 hash
  , slViewBox       :: !(Maybe SVGViewBox)
    -- ^ viewBox attribute
  , slDimensions    :: !(Maybe AssetDimensions)
    -- ^ width/height attributes
  , slColors        :: !(Vector Text)
    -- ^ Colors found in SVG (fill, stroke)
  , slPathCount     :: !Int
    -- ^ Number of path elements (complexity)
  , slTextContent   :: !(Vector Text)
    -- ^ Text elements in SVG
  , slFontFamilies  :: !(Vector Text)
    -- ^ Font families used
  , slHasGradients  :: !Bool
    -- ^ Contains gradients
  , slHasFilters    :: !Bool
    -- ^ Contains filters
  , slHasAnimations :: !Bool
    -- ^ Contains animations
  , slContext       :: !LogoContext
    -- ^ Where it appears
  , slVariant       :: !(Maybe LogoVariant)
    -- ^ Detected variant
  , slAlt           :: !(Maybe Text)
    -- ^ Alt text
  , slTitle         :: !(Maybe Text)
    -- ^ SVG title element
  , slDesc          :: !(Maybe Text)
    -- ^ SVG desc element
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON SVGLogoData
instance ToJSON SVGLogoData

--------------------------------------------------------------------------------
-- Icon
--------------------------------------------------------------------------------

-- | Icon library source
data IconLibrary
  = IconFontAwesome
  | IconMaterial
  | IconFeather
  | IconHeroicons
  | IconLucide
  | IconPhosphor
  | IconTabler
  | IconCustom
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON IconLibrary
instance ToJSON IconLibrary

-- | Icon data
data IconData = IconData
  { icName     :: !Text
    -- ^ Icon name/identifier
  , icLibrary  :: !(Maybe IconLibrary)
    -- ^ Source library
  , icSVG      :: !(Maybe Text)
    -- ^ SVG content (inline)
  , icClass    :: !(Maybe Text)
    -- ^ CSS class
  , icSize     :: !(Maybe Int)
    -- ^ Size in pixels
  , icColor    :: !(Maybe Text)
    -- ^ Color
  , icContext  :: !AssetContext
    -- ^ Where used
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON IconData
instance ToJSON IconData

--------------------------------------------------------------------------------
-- Video
--------------------------------------------------------------------------------

-- | Video asset
data VideoAsset = VideoAsset
  { vaURL        :: !Text
  , vaPoster     :: !(Maybe Text)
    -- ^ Poster image URL
  , vaDimensions :: !(Maybe AssetDimensions)
  , vaDuration   :: !(Maybe Double)
    -- ^ Duration in seconds
  , vaFormat     :: !(Maybe Text)
    -- ^ Video format
  , vaAutoplay   :: !Bool
  , vaMuted      :: !Bool
  , vaLoop       :: !Bool
  , vaContext    :: !AssetContext
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON VideoAsset
instance ToJSON VideoAsset

--------------------------------------------------------------------------------
-- Document
--------------------------------------------------------------------------------

-- | Document type
data DocumentType
  = DocPDF
  | DocWord
  | DocExcel
  | DocPowerPoint
  | DocOther
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON DocumentType
instance ToJSON DocumentType

-- | Document asset (PDFs, brand guidelines, etc.)
data DocumentAsset = DocumentAsset
  { daURL       :: !Text
  , daType      :: !DocumentType
  , daTitle     :: !(Maybe Text)
  , daFileSize  :: !(Maybe Int)
  , daPageCount :: !(Maybe Int)
  , daContext   :: !AssetContext
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON DocumentAsset
instance ToJSON DocumentAsset

--------------------------------------------------------------------------------
-- Complete Assets
--------------------------------------------------------------------------------

-- | All assets from a scrape
data AssetsComplete = AssetsComplete
  { acImages     :: !(Vector ImageAsset)
  , acLogos      :: !(Vector SVGLogoData)
  , acIcons      :: !(Vector IconData)
  , acVideos     :: !(Vector VideoAsset)
  , acDocuments  :: !(Vector DocumentAsset)
  , acTotalSize  :: !Int
    -- ^ Total size of all assets in bytes
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON AssetsComplete
instance ToJSON AssetsComplete
