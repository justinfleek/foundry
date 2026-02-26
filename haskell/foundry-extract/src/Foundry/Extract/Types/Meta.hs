{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // foundry // extract // types/meta
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Types.Meta
Description : Metadata types for brand identity extraction
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Types for representing ALL metadata from brand pages:
  - Open Graph (social sharing)
  - Twitter Cards
  - JSON-LD structured data
  - Favicons and touch icons
  - Theme colors
  - SEO metadata

== Design Notes

Metadata often contains brand assets that aren't visible on the page:
  - OG images (sized for social)
  - Brand names and taglines
  - Official social profiles
  - Corporate structure (JSON-LD Organization)

== Dependencies

Requires: aeson, text, vector
Required by: Foundry.Extract.Types, Foundry.Extract.Identity

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Types.Meta
  ( -- * Open Graph
    OpenGraphData (..)
  , OGType (..)
  
    -- * Twitter Cards
  , TwitterCardData (..)
  , TwitterCardType (..)
  
    -- * JSON-LD Structured Data
  , StructuredData (..)
  , OrganizationData (..)
  , WebSiteData (..)
  , BreadcrumbData (..)
  
    -- * Favicons
  , FaviconData (..)
  , FaviconType (..)
  
    -- * Theme
  , ThemeData (..)
  
    -- * Complete Metadata
  , MetaData (..)
  ) where

import Data.Aeson (FromJSON, ToJSON, Value)
import Data.Text (Text)
import Data.Vector (Vector)
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Open Graph
--------------------------------------------------------------------------------

-- | Open Graph type
data OGType
  = OGWebsite
  | OGArticle
  | OGProduct
  | OGProfile
  | OGVideo
  | OGMusic
  | OGBook
  | OGOther !Text
  deriving stock (Eq, Show, Generic)

instance FromJSON OGType
instance ToJSON OGType

-- | Open Graph metadata
--
-- Used for social media sharing previews (Facebook, LinkedIn, etc.)
data OpenGraphData = OpenGraphData
  { ogTitle        :: !(Maybe Text)
    -- ^ og:title - Title for sharing
  , ogDescription  :: !(Maybe Text)
    -- ^ og:description - Description for sharing
  , ogImage        :: !(Maybe Text)
    -- ^ og:image - Preview image URL
  , ogImageWidth   :: !(Maybe Int)
    -- ^ og:image:width
  , ogImageHeight  :: !(Maybe Int)
    -- ^ og:image:height
  , ogImageAlt     :: !(Maybe Text)
    -- ^ og:image:alt
  , ogType         :: !(Maybe OGType)
    -- ^ og:type - Content type
  , ogUrl          :: !(Maybe Text)
    -- ^ og:url - Canonical URL
  , ogSiteName     :: !(Maybe Text)
    -- ^ og:site_name - Brand name
  , ogLocale       :: !(Maybe Text)
    -- ^ og:locale - e.g., "en_US"
  , ogLocaleAlt    :: !(Vector Text)
    -- ^ og:locale:alternate - Other locales
  , ogAudio        :: !(Maybe Text)
    -- ^ og:audio - Audio URL
  , ogVideo        :: !(Maybe Text)
    -- ^ og:video - Video URL
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON OpenGraphData
instance ToJSON OpenGraphData

--------------------------------------------------------------------------------
-- Twitter Cards
--------------------------------------------------------------------------------

-- | Twitter Card type
data TwitterCardType
  = CardSummary           -- ^ Summary card
  | CardSummaryLargeImage -- ^ Summary with large image
  | CardPlayer            -- ^ Video/audio player
  | CardApp               -- ^ App download
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON TwitterCardType
instance ToJSON TwitterCardType

-- | Twitter Card metadata
data TwitterCardData = TwitterCardData
  { tcCard         :: !(Maybe TwitterCardType)
    -- ^ twitter:card - Card type
  , tcSite         :: !(Maybe Text)
    -- ^ twitter:site - @username of site
  , tcCreator      :: !(Maybe Text)
    -- ^ twitter:creator - @username of content creator
  , tcTitle        :: !(Maybe Text)
    -- ^ twitter:title
  , tcDescription  :: !(Maybe Text)
    -- ^ twitter:description
  , tcImage        :: !(Maybe Text)
    -- ^ twitter:image
  , tcImageAlt     :: !(Maybe Text)
    -- ^ twitter:image:alt
  , tcPlayer       :: !(Maybe Text)
    -- ^ twitter:player - Player URL
  , tcPlayerWidth  :: !(Maybe Int)
    -- ^ twitter:player:width
  , tcPlayerHeight :: !(Maybe Int)
    -- ^ twitter:player:height
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON TwitterCardData
instance ToJSON TwitterCardData

--------------------------------------------------------------------------------
-- JSON-LD Structured Data
--------------------------------------------------------------------------------

-- | Organization structured data (schema.org/Organization)
data OrganizationData = OrganizationData
  { odName           :: !(Maybe Text)
    -- ^ Organization name
  , odLegalName      :: !(Maybe Text)
    -- ^ Legal name
  , odUrl            :: !(Maybe Text)
    -- ^ Official website
  , odLogo           :: !(Maybe Text)
    -- ^ Logo URL
  , odFoundingDate   :: !(Maybe Text)
    -- ^ Founding date
  , odFounders       :: !(Vector Text)
    -- ^ Founder names
  , odAddress        :: !(Maybe Text)
    -- ^ Address (simplified)
  , odSameAs         :: !(Vector Text)
    -- ^ Social profile URLs
  , odContactPoint   :: !(Maybe Text)
    -- ^ Contact information
  , odDescription    :: !(Maybe Text)
    -- ^ Description
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON OrganizationData
instance ToJSON OrganizationData

-- | WebSite structured data (schema.org/WebSite)
data WebSiteData = WebSiteData
  { wsName           :: !(Maybe Text)
    -- ^ Site name
  , wsUrl            :: !(Maybe Text)
    -- ^ Site URL
  , wsSearchAction   :: !(Maybe Text)
    -- ^ Search action URL template
  , wsPotentialAction :: !(Maybe Value)
    -- ^ Potential action (raw JSON)
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON WebSiteData
instance ToJSON WebSiteData

-- | Breadcrumb structured data
data BreadcrumbData = BreadcrumbData
  { bcItems :: !(Vector (Text, Text))
    -- ^ (name, url) pairs
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON BreadcrumbData
instance ToJSON BreadcrumbData

-- | Parsed structured data from JSON-LD
data StructuredData = StructuredData
  { sdType         :: !Text
    -- ^ @type (Organization, WebSite, etc.)
  , sdRaw          :: !Value
    -- ^ Raw JSON-LD object
  , sdOrganization :: !(Maybe OrganizationData)
    -- ^ Parsed if type is Organization
  , sdWebSite      :: !(Maybe WebSiteData)
    -- ^ Parsed if type is WebSite
  , sdBreadcrumb   :: !(Maybe BreadcrumbData)
    -- ^ Parsed if type is BreadcrumbList
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON StructuredData
instance ToJSON StructuredData

--------------------------------------------------------------------------------
-- Favicons
--------------------------------------------------------------------------------

-- | Favicon type
data FaviconType
  = FavIcon           -- ^ Standard favicon.ico
  | FavIcon16         -- ^ 16x16 PNG
  | FavIcon32         -- ^ 32x32 PNG
  | FavIcon96         -- ^ 96x96 PNG
  | FavIcon192        -- ^ 192x192 PNG (Android)
  | FavIcon512        -- ^ 512x512 PNG (PWA)
  | FavAppleTouch     -- ^ apple-touch-icon (180x180)
  | FavAppleTouch76   -- ^ apple-touch-icon 76x76
  | FavAppleTouch120  -- ^ apple-touch-icon 120x120
  | FavAppleTouch152  -- ^ apple-touch-icon 152x152
  | FavMaskIcon       -- ^ Safari pinned tab (SVG)
  | FavMSTile         -- ^ MS tile image
  | FavManifestIcon   -- ^ Web manifest icon
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON FaviconType
instance ToJSON FaviconType

-- | Favicon data
data FaviconData = FaviconData
  { fiURL    :: !Text
    -- ^ Favicon URL
  , fiType   :: !FaviconType
    -- ^ Favicon type
  , fiSize   :: !(Maybe Text)
    -- ^ Size string (e.g., "32x32")
  , fiRel    :: !Text
    -- ^ Link rel value
  , fiColor  :: !(Maybe Text)
    -- ^ Color (for mask-icon)
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON FaviconData
instance ToJSON FaviconData

--------------------------------------------------------------------------------
-- Theme
--------------------------------------------------------------------------------

-- | Theme-related metadata
data ThemeData = ThemeData
  { tdThemeColor       :: !(Maybe Text)
    -- ^ <meta name="theme-color">
  , tdMsAppTileColor   :: !(Maybe Text)
    -- ^ msapplication-TileColor
  , tdMsAppTileImage   :: !(Maybe Text)
    -- ^ msapplication-TileImage
  , tdMsAppConfig      :: !(Maybe Text)
    -- ^ msapplication-config URL
  , tdAppleStatusBar   :: !(Maybe Text)
    -- ^ apple-mobile-web-app-status-bar-style
  , tdColorScheme      :: !(Maybe Text)
    -- ^ <meta name="color-scheme">
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON ThemeData
instance ToJSON ThemeData

--------------------------------------------------------------------------------
-- Complete Metadata
--------------------------------------------------------------------------------

-- | All metadata from a page
data MetaData = MetaData
  { mdTitle          :: !(Maybe Text)
    -- ^ <title> element
  , mdDescription    :: !(Maybe Text)
    -- ^ <meta name="description">
  , mdKeywords       :: !(Vector Text)
    -- ^ <meta name="keywords">
  , mdAuthor         :: !(Maybe Text)
    -- ^ <meta name="author">
  , mdCanonical      :: !(Maybe Text)
    -- ^ <link rel="canonical">
  , mdAlternate      :: !(Vector (Text, Text))
    -- ^ Alternate links (hreflang, url)
  , mdOpenGraph      :: !OpenGraphData
    -- ^ Open Graph data
  , mdTwitterCard    :: !TwitterCardData
    -- ^ Twitter Card data
  , mdStructured     :: !(Vector StructuredData)
    -- ^ JSON-LD structured data
  , mdFavicons       :: !(Vector FaviconData)
    -- ^ All favicon links
  , mdTheme          :: !ThemeData
    -- ^ Theme metadata
  , mdRobots         :: !(Maybe Text)
    -- ^ Robots directive
  , mdGenerator      :: !(Maybe Text)
    -- ^ Generator meta (CMS detection)
  , mdViewport       :: !(Maybe Text)
    -- ^ Viewport meta
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON MetaData
instance ToJSON MetaData
