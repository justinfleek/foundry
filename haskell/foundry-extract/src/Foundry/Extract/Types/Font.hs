{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  // foundry // extract // types/font
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Types.Font
Description : Complete font type definitions for TOTAL brand ingestion
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Types for representing ALL font data from brand assets.

== Coverage

This module supports extraction of:
  - @font-face declarations (all properties)
  - Variable font axes (wght, wdth, slnt, opsz, custom)
  - Font file metadata (format, hash, size, license)
  - Unicode ranges for subsetting
  - Font display strategies
  - OpenType feature settings

== Design Notes

Font types must capture EVERYTHING needed to:
  1. Reconstruct the exact font stack
  2. Download and verify font files
  3. Understand variable font capabilities
  4. Preserve fallback ordering
  5. Track font licenses for compliance

== Dependencies

Requires: aeson, bytestring, text, vector
Required by: Foundry.Extract.Types, Foundry.Extract.Typography

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Types.Font
  ( -- * Font Formats
    FontFormat (..)
  , fontFormatExtension
  , fontFormatMimeType
  
    -- * Font Display
  , FontDisplay (..)
  
    -- * Variable Font Axes
  , VariableFontAxis (..)
  , StandardAxis (..)
  , standardAxisTag
  
    -- * OpenType Features
  , OpenTypeFeature (..)
  , FeatureTag (..)
  
    -- * Font Face (Complete)
  , FontFaceComplete (..)
  
    -- * Font File Data
  , FontFileData (..)
  
    -- * Font Data (Aggregate)
  , FontDataComplete (..)
  
    -- * Legacy (for backward compatibility)
  , FontFace (..)
  , FontData (..)
  ) where

import Data.Aeson (FromJSON, ToJSON)
import Data.ByteString (ByteString)
import Data.Map.Strict (Map)
import Data.Text (Text)
import Data.Vector (Vector)
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Font Formats
--------------------------------------------------------------------------------

-- | Web font file formats
--
-- Modern web fonts support multiple formats for browser compatibility.
-- WOFF2 is preferred for smallest file size and widest modern support.
data FontFormat
  = FormatWOFF2     -- ^ WOFF2 - Web Open Font Format 2.0 (best compression)
  | FormatWOFF      -- ^ WOFF - Web Open Font Format 1.0
  | FormatOpenType  -- ^ OTF - OpenType Format
  | FormatTrueType  -- ^ TTF - TrueType Format
  | FormatEOT       -- ^ EOT - Embedded OpenType (IE legacy)
  | FormatSVG       -- ^ SVG Font (deprecated, iOS < 5)
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON FontFormat
instance ToJSON FontFormat

-- | Get file extension for font format
fontFormatExtension :: FontFormat -> Text
fontFormatExtension FormatWOFF2    = ".woff2"
fontFormatExtension FormatWOFF     = ".woff"
fontFormatExtension FormatOpenType = ".otf"
fontFormatExtension FormatTrueType = ".ttf"
fontFormatExtension FormatEOT      = ".eot"
fontFormatExtension FormatSVG      = ".svg"

-- | Get MIME type for font format
fontFormatMimeType :: FontFormat -> Text
fontFormatMimeType FormatWOFF2    = "font/woff2"
fontFormatMimeType FormatWOFF     = "font/woff"
fontFormatMimeType FormatOpenType = "font/otf"
fontFormatMimeType FormatTrueType = "font/ttf"
fontFormatMimeType FormatEOT      = "application/vnd.ms-fontobject"
fontFormatMimeType FormatSVG      = "image/svg+xml"

--------------------------------------------------------------------------------
-- Font Display Strategy
--------------------------------------------------------------------------------

-- | CSS font-display property values
--
-- Controls how fonts are displayed during loading.
data FontDisplay
  = DisplayAuto     -- ^ Browser default behavior
  | DisplayBlock    -- ^ Short block period, infinite swap
  | DisplaySwap     -- ^ Very short block, infinite swap (recommended)
  | DisplayFallback -- ^ Very short block, short swap
  | DisplayOptional -- ^ Very short block, no swap
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON FontDisplay
instance ToJSON FontDisplay

--------------------------------------------------------------------------------
-- Variable Font Axes
--------------------------------------------------------------------------------

-- | Standard registered axes for variable fonts
--
-- These are the official OpenType specification axes.
data StandardAxis
  = AxisWeight   -- ^ wght: 1-999, typically 100-900
  | AxisWidth    -- ^ wdth: 50-200%, default 100%
  | AxisSlant    -- ^ slnt: -90 to 90 degrees
  | AxisItalic   -- ^ ital: 0 (upright) or 1 (italic)
  | AxisOptical  -- ^ opsz: optical size in points
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON StandardAxis
instance ToJSON StandardAxis

-- | Get the four-letter tag for a standard axis
standardAxisTag :: StandardAxis -> Text
standardAxisTag AxisWeight  = "wght"
standardAxisTag AxisWidth   = "wdth"
standardAxisTag AxisSlant   = "slnt"
standardAxisTag AxisItalic  = "ital"
standardAxisTag AxisOptical = "opsz"

-- | Variable font axis definition
--
-- Captures both standard and custom axes with their full range.
data VariableFontAxis = VariableFontAxis
  { vfaTag      :: !Text      -- ^ Four-letter tag ("wght", "wdth", "GRAD", etc.)
  , vfaName     :: !Text      -- ^ Human-readable name ("Weight", "Width")
  , vfaMin      :: !Double    -- ^ Minimum value
  , vfaMax      :: !Double    -- ^ Maximum value
  , vfaDefault  :: !Double    -- ^ Default value
  , vfaStandard :: !(Maybe StandardAxis)  -- ^ Standard axis if registered
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON VariableFontAxis
instance ToJSON VariableFontAxis

--------------------------------------------------------------------------------
-- OpenType Features
--------------------------------------------------------------------------------

-- | OpenType feature tag (4 characters)
newtype FeatureTag = FeatureTag {unFeatureTag :: Text}
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (FromJSON, ToJSON)

-- | OpenType feature with enabled state
data OpenTypeFeature = OpenTypeFeature
  { otfTag     :: !FeatureTag  -- ^ Feature tag (e.g., "liga", "smcp")
  , otfEnabled :: !Bool        -- ^ Whether enabled
  , otfValue   :: !(Maybe Int) -- ^ Value for stylistic sets (ss01-ss20)
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON OpenTypeFeature
instance ToJSON OpenTypeFeature

--------------------------------------------------------------------------------
-- Complete Font Face
--------------------------------------------------------------------------------

-- | Complete @font-face declaration data
--
-- Captures ALL properties from @font-face, not just the basics.
data FontFaceComplete = FontFaceComplete
  { ffcFamily       :: !Text
    -- ^ Font family name
  , ffcWeight       :: !(Maybe Text)
    -- ^ Font weight ("400", "bold", "100 900" for ranges)
  , ffcStyle        :: !(Maybe Text)
    -- ^ Font style ("normal", "italic", "oblique")
  , ffcStretch      :: !(Maybe Text)
    -- ^ Font stretch ("condensed", "expanded", "50% 200%")
  , ffcSrc          :: !(Vector FontFileData)
    -- ^ Font sources (multiple for fallbacks)
  , ffcUnicodeRange :: !(Maybe Text)
    -- ^ Unicode range ("U+0000-00FF, U+0131")
  , ffcDisplay      :: !FontDisplay
    -- ^ Font display strategy
  , ffcFeatures     :: !(Vector OpenTypeFeature)
    -- ^ Default OpenType features
  , ffcVariableAxes :: !(Vector VariableFontAxis)
    -- ^ Variable font axes (empty for static fonts)
  , ffcAscentOverride    :: !(Maybe Double)
    -- ^ Ascent metric override
  , ffcDescentOverride   :: !(Maybe Double)
    -- ^ Descent metric override
  , ffcLineGapOverride   :: !(Maybe Double)
    -- ^ Line gap metric override
  , ffcSizeAdjust        :: !(Maybe Double)
    -- ^ Size adjustment factor (for metric compatibility)
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON FontFaceComplete
instance ToJSON FontFaceComplete

--------------------------------------------------------------------------------
-- Font File Data
--------------------------------------------------------------------------------

-- | Complete font file metadata
--
-- For each font source URL, we capture full metadata for:
--   - Download and caching
--   - Integrity verification
--   - License compliance
--   - Format negotiation
data FontFileData = FontFileData
  { ffdURL          :: !Text
    -- ^ Font file URL
  , ffdFormat       :: !FontFormat
    -- ^ Font format
  , ffdTech         :: !(Maybe Text)
    -- ^ Technology hint ("variations" for variable fonts)
  , ffdFileSize     :: !(Maybe Int)
    -- ^ File size in bytes (for optimization analysis)
  , ffdContentHash  :: !(Maybe ByteString)
    -- ^ SHA-256 hash of content (for integrity/dedup)
  , ffdLocal        :: !(Maybe Text)
    -- ^ Local font name (for local() sources)
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON FontFileData
instance ToJSON FontFileData

--------------------------------------------------------------------------------
-- Complete Font Data (Aggregate)
--------------------------------------------------------------------------------

-- | Complete font data from a scrape
--
-- Aggregates all font information:
--   - @font-face declarations (complete)
--   - Font usage frequency
--   - Detected font stacks
--   - Variable font capabilities
data FontDataComplete = FontDataComplete
  { fdcFaces        :: !(Vector FontFaceComplete)
    -- ^ All @font-face declarations
  , fdcUsedFonts    :: !(Map Text Int)
    -- ^ Font families and usage frequency
  , fdcFontStacks   :: !(Map Text (Vector Text))
    -- ^ Detected font stacks (primary -> fallbacks)
  , fdcVariableFonts :: !(Vector Text)
    -- ^ Font families that are variable
  , fdcTotalFontSize :: !Int
    -- ^ Total bytes of all font files
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON FontDataComplete
instance ToJSON FontDataComplete

--------------------------------------------------------------------------------
-- Legacy Types (Backward Compatibility)
--------------------------------------------------------------------------------

-- | Legacy @font-face declaration (minimal)
--
-- DEPRECATED: Use 'FontFaceComplete' for new code.
-- Kept for backward compatibility during migration.
data FontFace = FontFace
  { ffFamily  :: !Text
  , ffWeight  :: !(Maybe Text)
  , ffStyle   :: !(Maybe Text)
  , ffSrc     :: !Text
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON FontFace
instance ToJSON FontFace

-- | Legacy font data (minimal)
--
-- DEPRECATED: Use 'FontDataComplete' for new code.
data FontData = FontData
  { fdFaces     :: !(Vector FontFace)
  , fdUsedFonts :: !(Map Text Int)
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON FontData
instance ToJSON FontData
