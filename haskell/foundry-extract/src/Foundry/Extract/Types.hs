{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // foundry // extract // types
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Types
Description : Input types for brand extraction
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Types representing raw scraped content before extraction into Brand molecules.

== Design Notes

This module defines the boundary between the scraper (untrusted, sandboxed)
and the extractor (pure, deterministic). All data enters through 'ScrapeResult'
and exits as typed Brand molecules.

== Dependencies

Requires: (none - leaf module)
Required by: Foundry.Extract.Color, Foundry.Extract.Typography, Foundry.Extract.Spacing,
             Foundry.Extract.Voice, Foundry.Extract.Compose

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Types
  ( -- * Scrape Result
    ScrapeResult (..)

    -- * CSS Data
  , CSSStylesheet (..)
  , CSSRule (..)
  , CSSProperty (..)
  , CSSValue (..)
  , CSSSelector (..)

    -- * Computed Styles
  , ComputedStyle (..)
  , ElementStyles (..)

    -- * Text Content
  , TextContent (..)
  , TextBlock (..)
  , TextBlockType (..)

    -- * Font Data
  , FontData (..)
  , FontFace (..)

    -- * Asset Data
  , AssetData (..)
  , AssetType (..)

    -- * Extraction Errors
  , ExtractionError (..)
  , ExtractionWarning (..)
  ) where

import Data.Aeson (FromJSON (..), ToJSON (..), withObject, (.:), (.=), object)
import Data.ByteString (ByteString)
import Data.ByteString.Base64 qualified as Base64
import Data.Map.Strict (Map)
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import Data.Vector (Vector)
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Scrape Result (top-level input)
--------------------------------------------------------------------------------

-- | Complete result from scraping a web page
--
-- This is the primary input to all extractors. Contains raw CSS, computed
-- styles, text content, and discovered assets.
data ScrapeResult = ScrapeResult
  { srDomain       :: !Text
    -- ^ Source domain (e.g., "stripe.com")
  , srURL          :: !Text
    -- ^ Full URL scraped
  , srStylesheets  :: !(Vector CSSStylesheet)
    -- ^ All CSS stylesheets (inline, linked, imported)
  , srComputedStyles :: !(Vector ElementStyles)
    -- ^ Computed styles for key DOM elements
  , srTextContent  :: !TextContent
    -- ^ Extracted text content with structure
  , srFontData     :: !FontData
    -- ^ Font-related data (faces, metrics)
  , srAssets       :: !(Vector AssetData)
    -- ^ Discovered assets (images, SVGs, etc.)
  , srRawHTML      :: !ByteString
    -- ^ Raw HTML for hash computation
  }
  deriving stock (Eq, Show, Generic)

-- | Custom FromJSON for ScrapeResult to handle ByteString as Base64
instance FromJSON ScrapeResult where
  parseJSON = withObject "ScrapeResult" $ \v -> ScrapeResult
    <$> v .: "srDomain"
    <*> v .: "srURL"
    <*> v .: "srStylesheets"
    <*> v .: "srComputedStyles"
    <*> v .: "srTextContent"
    <*> v .: "srFontData"
    <*> v .: "srAssets"
    <*> (decodeBase64 <$> v .: "srRawHTML")
    where
      decodeBase64 :: Text -> ByteString
      decodeBase64 t = case Base64.decode (Text.encodeUtf8 t) of
        Left _err -> mempty  -- Safe fallback: empty ByteString on decode failure
        Right bs  -> bs

-- | Custom ToJSON for ScrapeResult to encode ByteString as Base64
instance ToJSON ScrapeResult where
  toJSON sr = object
    [ "srDomain"         .= srDomain sr
    , "srURL"            .= srURL sr
    , "srStylesheets"    .= srStylesheets sr
    , "srComputedStyles" .= srComputedStyles sr
    , "srTextContent"    .= srTextContent sr
    , "srFontData"       .= srFontData sr
    , "srAssets"         .= srAssets sr
    , "srRawHTML"        .= encodeBase64 (srRawHTML sr)
    ]
    where
      encodeBase64 :: ByteString -> Text
      encodeBase64 = Text.decodeUtf8 . Base64.encode

--------------------------------------------------------------------------------
-- CSS Data
--------------------------------------------------------------------------------

-- | A CSS stylesheet with its rules
data CSSStylesheet = CSSStylesheet
  { cssSource   :: !Text
    -- ^ Source URL or "inline"
  , cssRules    :: !(Vector CSSRule)
    -- ^ Parsed CSS rules
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON CSSStylesheet
instance ToJSON CSSStylesheet

-- | A CSS rule (selector + declarations)
data CSSRule = CSSRule
  { cssSelector    :: !CSSSelector
    -- ^ CSS selector
  , cssProperties  :: !(Vector CSSProperty)
    -- ^ Declarations (property: value pairs)
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON CSSRule
instance ToJSON CSSRule

-- | A CSS selector
newtype CSSSelector = CSSSelector {unCSSSelector :: Text}
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (FromJSON, ToJSON)

-- | A CSS property declaration
data CSSProperty = CSSProperty
  { cssPropName  :: !Text
    -- ^ Property name (e.g., "color", "font-family")
  , cssPropValue :: !CSSValue
    -- ^ Property value
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON CSSProperty
instance ToJSON CSSProperty

-- | A CSS value (parsed into variants)
data CSSValue
  = CSSColor !Text
    -- ^ Color value (hex, rgb, hsl, oklch, named)
  | CSSLength !Double !Text
    -- ^ Length value (number + unit: px, rem, em, %)
  | CSSFont !Text
    -- ^ Font family value
  | CSSKeyword !Text
    -- ^ Keyword value
  | CSSNumber !Double
    -- ^ Unitless number
  | CSSRaw !Text
    -- ^ Unparsed value (fallback)
  deriving stock (Eq, Show, Generic)

instance FromJSON CSSValue
instance ToJSON CSSValue

--------------------------------------------------------------------------------
-- Computed Styles
--------------------------------------------------------------------------------

-- | Computed style for a DOM element
data ComputedStyle = ComputedStyle
  { csColor            :: !(Maybe Text)
    -- ^ Computed color
  , csBackgroundColor  :: !(Maybe Text)
    -- ^ Computed background-color
  , csFontFamily       :: !(Maybe Text)
    -- ^ Computed font-family
  , csFontSize         :: !(Maybe Double)
    -- ^ Computed font-size in px
  , csFontWeight       :: !(Maybe Int)
    -- ^ Computed font-weight (100-900)
  , csLineHeight       :: !(Maybe Double)
    -- ^ Computed line-height
  , csMarginTop        :: !(Maybe Double)
    -- ^ Computed margin-top in px
  , csMarginRight      :: !(Maybe Double)
    -- ^ Computed margin-right in px
  , csMarginBottom     :: !(Maybe Double)
    -- ^ Computed margin-bottom in px
  , csMarginLeft       :: !(Maybe Double)
    -- ^ Computed margin-left in px
  , csPaddingTop       :: !(Maybe Double)
    -- ^ Computed padding-top in px
  , csPaddingRight     :: !(Maybe Double)
    -- ^ Computed padding-right in px
  , csPaddingBottom    :: !(Maybe Double)
    -- ^ Computed padding-bottom in px
  , csPaddingLeft      :: !(Maybe Double)
    -- ^ Computed padding-left in px
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON ComputedStyle
instance ToJSON ComputedStyle

-- | Computed styles for an element with its selector
data ElementStyles = ElementStyles
  { esSelector :: !Text
    -- ^ Selector that matched this element (e.g., "h1", ".button")
  , esTagName  :: !Text
    -- ^ Tag name (e.g., "H1", "DIV")
  , esStyles   :: !ComputedStyle
    -- ^ Computed style values
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON ElementStyles
instance ToJSON ElementStyles

--------------------------------------------------------------------------------
-- Text Content
--------------------------------------------------------------------------------

-- | All extracted text content from the page
data TextContent = TextContent
  { tcTitle       :: !(Maybe Text)
    -- ^ Page title
  , tcHeadings    :: !(Vector TextBlock)
    -- ^ Headings (h1-h6)
  , tcParagraphs  :: !(Vector TextBlock)
    -- ^ Paragraph text
  , tcButtons     :: !(Vector TextBlock)
    -- ^ Button/CTA text
  , tcNavigation  :: !(Vector TextBlock)
    -- ^ Navigation items
  , tcFooter      :: !(Vector TextBlock)
    -- ^ Footer text
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON TextContent
instance ToJSON TextContent

-- | A block of text with its type and source
data TextBlock = TextBlock
  { tbText     :: !Text
    -- ^ The text content
  , tbType     :: !TextBlockType
    -- ^ Type of text block
  , tbSelector :: !Text
    -- ^ CSS selector that matched
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON TextBlock
instance ToJSON TextBlock

-- | Types of text blocks
data TextBlockType
  = TBHeading1
  | TBHeading2
  | TBHeading3
  | TBHeading4
  | TBHeading5
  | TBHeading6
  | TBParagraph
  | TBButton
  | TBLink
  | TBListItem
  | TBBlockquote
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON TextBlockType
instance ToJSON TextBlockType

--------------------------------------------------------------------------------
-- Font Data
--------------------------------------------------------------------------------

-- | All font-related data from the page
data FontData = FontData
  { fdFaces     :: !(Vector FontFace)
    -- ^ @font-face declarations
  , fdUsedFonts :: !(Map Text Int)
    -- ^ Font families used and their frequency
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON FontData
instance ToJSON FontData

-- | A @font-face declaration
data FontFace = FontFace
  { ffFamily  :: !Text
    -- ^ Font family name
  , ffWeight  :: !(Maybe Text)
    -- ^ Font weight (e.g., "400", "bold")
  , ffStyle   :: !(Maybe Text)
    -- ^ Font style (e.g., "normal", "italic")
  , ffSrc     :: !Text
    -- ^ Font source URL
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON FontFace
instance ToJSON FontFace

--------------------------------------------------------------------------------
-- Asset Data
--------------------------------------------------------------------------------

-- | Discovered asset from the page
data AssetData = AssetData
  { adURL       :: !Text
    -- ^ Asset URL
  , adType      :: !AssetType
    -- ^ Type of asset
  , adAlt       :: !(Maybe Text)
    -- ^ Alt text (for images)
  , adContext   :: !Text
    -- ^ Where the asset appears (e.g., "header", "hero")
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON AssetData
instance ToJSON AssetData

-- | Types of assets
data AssetType
  = ATImage
  | ATSVG
  | ATFavicon
  | ATLogo
  | ATIcon
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON AssetType
instance ToJSON AssetType

--------------------------------------------------------------------------------
-- Extraction Errors and Warnings
--------------------------------------------------------------------------------

-- | Errors that halt extraction
data ExtractionError
  = ErrNoDomain
    -- ^ No domain in scrape result
  | ErrNoColors
    -- ^ Could not extract any colors
  | ErrNoFonts
    -- ^ Could not extract any font families
  | ErrInvalidCSS !Text
    -- ^ CSS parsing failed
  | ErrInvalidColor !Text
    -- ^ Color value invalid
  deriving stock (Eq, Show)

-- | Warnings that don't halt extraction
data ExtractionWarning
  = WarnLowColorContrast !Double
    -- ^ Contrast ratio below WCAG threshold
  | WarnMissingFont !Text
    -- ^ Referenced font not found
  | WarnNoTypeScale
    -- ^ Could not detect type scale
  | WarnNoSpacingScale
    -- ^ Could not detect spacing scale
  | WarnFewTextSamples !Int
    -- ^ Too few text samples for voice analysis
  deriving stock (Eq, Show)
