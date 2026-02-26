{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // foundry // brand/typography
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Typography
Description : SMART Framework Typography System (Sections 17-19)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Professional typography specification with full type scale tables.

== SMART Framework Sections 17-19: Typography

Section 17 - Font Pairing:
"For each font: Font Name, Role, Rationale, Fallback Fonts"

Section 18 - Type Scale & Weights:
"Base Size, Scale Ratio, Line Height per level, Kerning per level"

Section 19 - Body Text Specifications:
"Paragraph, Links, Bold, Block Quote, Lists with specific properties"

== AI Ingestion Priority #4

"Capture the scale ratio and base size, not just the individual sizes.
This allows the system to extrapolate if custom sizes are needed."

== Type Scale Levels (SMART Framework Table)

| Level | Usage |
|-------|-------|
| HL    | Hero/Display - Single text elements, section headings |
| H1-H6 | Heading hierarchy |
| p     | Body paragraph (1rem = base) |
| small | De-emphasized text |
| footnotes | Legal, citations |

DEPENDENCIES:
  - None (base types)

DEPENDENTS:
  - Foundry.Core.Brand (compound type)
  - Foundry.Extract.Typography

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Typography
  ( -- * Font Weight
    FontWeight (..)
  , mkFontWeight
  , fontWeightName
  
    -- * Font Family
  , FontFamily (..)
  , mkFontFamily
  
    -- * Font Role
  , FontRole (..)
  , fontRoleToText
  
    -- * Type Scale Level
  , TypeLevel (..)
  , typeLevelToText
  
    -- * Type Scale Entry (per level)
  , TypeScaleEntry (..)
  , mkTypeScaleEntry
  
    -- * Type Scale (base + ratio)
  , TypeScale (..)
  , mkTypeScale
  , computeSize
  
    -- * Line Height
  , LineHeight (..)
  , mkLineHeight
  
    -- * Kerning
  , Kerning (..)
  , mkKerning
  
    -- * Complete Typography
  , Typography (..)
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)

--------------------------------------------------------------------------------
-- Font Weight
--------------------------------------------------------------------------------

-- | Font weight (100-900 in increments of 100)
-- 
-- Standard weights:
--   100 = Thin, 200 = Extra Light, 300 = Light, 400 = Regular
--   500 = Medium, 600 = Semi Bold, 700 = Bold, 800 = Extra Bold, 900 = Black
newtype FontWeight = FontWeight {unFontWeight :: Int}
  deriving stock (Eq, Ord, Show)

-- | Create font weight with validation (100-900)
mkFontWeight :: Int -> Maybe FontWeight
mkFontWeight w
  | w >= 100 && w <= 900 = Just (FontWeight w)
  | otherwise = Nothing

-- | Get human-readable weight name
fontWeightName :: FontWeight -> Text
fontWeightName (FontWeight w) = case w of
  100 -> "Thin"
  200 -> "Extra Light"
  300 -> "Light"
  400 -> "Regular"
  500 -> "Medium"
  600 -> "Semi Bold"
  700 -> "Bold"
  800 -> "Extra Bold"
  900 -> "Black"
  _   -> "Weight " <> T.pack (show w)

--------------------------------------------------------------------------------
-- Font Family
--------------------------------------------------------------------------------

-- | Font family specification with fallbacks
-- 
-- From SMART Framework Section 17:
-- "For each font: Font Name, Role, Rationale, Fallback Fonts"
data FontFamily = FontFamily
  { fontFamilyName      :: !Text     -- ^ Primary font name (e.g., "Archivo")
  , fontFamilyFallbacks :: ![Text]   -- ^ Fallback fonts in order
  , fontFamilyRationale :: !Text     -- ^ Why this font was chosen
  }
  deriving stock (Eq, Show)

-- | Create font family with validation
mkFontFamily :: Text -> [Text] -> Text -> Maybe FontFamily
mkFontFamily name fallbacks rationale
  | T.length (T.strip name) >= 1 = Just FontFamily
      { fontFamilyName = T.strip name
      , fontFamilyFallbacks = fallbacks
      , fontFamilyRationale = rationale
      }
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Font Role
--------------------------------------------------------------------------------

-- | Role a font plays in the typography system
data FontRole
  = PrimaryFont      -- ^ Headlines, display text
  | SupportingFont   -- ^ Body copy
  | AccentFont       -- ^ Special emphasis, pull quotes
  | MonospaceFont    -- ^ Code, technical content
  | FallbackFont     -- ^ System fallback
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | Convert font role to text
fontRoleToText :: FontRole -> Text
fontRoleToText PrimaryFont = "primary"
fontRoleToText SupportingFont = "supporting"
fontRoleToText AccentFont = "accent"
fontRoleToText MonospaceFont = "monospace"
fontRoleToText FallbackFont = "fallback"

--------------------------------------------------------------------------------
-- Type Scale Level
--------------------------------------------------------------------------------

-- | Type scale level (from SMART Framework Table)
data TypeLevel
  = LevelHL        -- ^ Hero/Display - largest, single text elements
  | LevelH1        -- ^ Heading 1
  | LevelH2        -- ^ Heading 2
  | LevelH3        -- ^ Heading 3
  | LevelH4        -- ^ Heading 4
  | LevelH5        -- ^ Heading 5
  | LevelH6        -- ^ Heading 6
  | LevelP         -- ^ Paragraph (base = 1rem)
  | LevelSmall     -- ^ Small/de-emphasized text
  | LevelFootnote  -- ^ Footnotes, legal text
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | Convert type level to CSS/HTML equivalent
typeLevelToText :: TypeLevel -> Text
typeLevelToText LevelHL = "display"
typeLevelToText LevelH1 = "h1"
typeLevelToText LevelH2 = "h2"
typeLevelToText LevelH3 = "h3"
typeLevelToText LevelH4 = "h4"
typeLevelToText LevelH5 = "h5"
typeLevelToText LevelH6 = "h6"
typeLevelToText LevelP = "p"
typeLevelToText LevelSmall = "small"
typeLevelToText LevelFootnote = "footnote"

--------------------------------------------------------------------------------
-- Line Height
--------------------------------------------------------------------------------

-- | Line height (unitless multiplier)
newtype LineHeight = LineHeight { unLineHeight :: Double }
  deriving stock (Eq, Ord, Show)

-- | Create line height with validation (0.5 - 3.0)
mkLineHeight :: Double -> Maybe LineHeight
mkLineHeight lh
  | lh >= 0.5 && lh <= 3.0 = Just (LineHeight lh)
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Kerning
--------------------------------------------------------------------------------

-- | Kerning (letter-spacing in em units)
newtype Kerning = Kerning { unKerning :: Double }
  deriving stock (Eq, Ord, Show)

-- | Create kerning with validation (-0.5 to 1.0 em)
mkKerning :: Double -> Maybe Kerning
mkKerning k
  | k >= -0.5 && k <= 1.0 = Just (Kerning k)
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Type Scale Entry
--------------------------------------------------------------------------------

-- | Complete specification for a single type scale level
-- 
-- From SMART Framework Section 18 Type Scale Table:
-- "Level, Size, Font, Style, Kerning, Usage"
data TypeScaleEntry = TypeScaleEntry
  { tseLevel      :: !TypeLevel   -- ^ Which level (H1, H2, p, etc.)
  , tseSize       :: !Double      -- ^ Size in pixels
  , tseFont       :: !Text        -- ^ Font name
  , tseWeight     :: !FontWeight  -- ^ Weight
  , tseLineHeight :: !LineHeight  -- ^ Line height
  , tseKerning    :: !Kerning     -- ^ Letter spacing
  , tseUsage      :: !Text        -- ^ Description of when to use
  }
  deriving stock (Eq, Show)

-- | Create type scale entry
mkTypeScaleEntry
  :: TypeLevel -> Double -> Text -> FontWeight 
  -> LineHeight -> Kerning -> Text 
  -> Maybe TypeScaleEntry
mkTypeScaleEntry level size font weight lh kern usage
  | size > 0 && T.length font >= 1 = Just TypeScaleEntry
      { tseLevel = level
      , tseSize = size
      , tseFont = font
      , tseWeight = weight
      , tseLineHeight = lh
      , tseKerning = kern
      , tseUsage = usage
      }
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Type Scale (Mathematical)
--------------------------------------------------------------------------------

-- | Type scale definition (mathematical basis)
-- 
-- AI Ingestion Priority #4:
-- "Capture the scale ratio and base size, not just the individual sizes."
data TypeScale = TypeScale
  { typeScaleBase  :: !Double  -- ^ Base font size (typically 16px = 1rem)
  , typeScaleRatio :: !Double  -- ^ Scale ratio (e.g., 1.25 = Major Third)
  }
  deriving stock (Eq, Show)

-- | Create type scale with validation
mkTypeScale :: Double -> Double -> Maybe TypeScale
mkTypeScale base ratio
  | base > 0 && ratio > 1.0 = Just (TypeScale base ratio)
  | otherwise = Nothing

-- | Compute size at a given scale step
-- 
-- step 0 = base, step 1 = base * ratio, step -1 = base / ratio
computeSize :: TypeScale -> Int -> Double
computeSize (TypeScale base ratio) step = base * (ratio ** fromIntegral step)

--------------------------------------------------------------------------------
-- Complete Typography Specification
--------------------------------------------------------------------------------

-- | Complete typography specification for a brand
data Typography = Typography
  { typographyHeadingFamily :: !FontFamily           -- ^ Primary/heading font
  , typographyBodyFamily    :: !FontFamily           -- ^ Supporting/body font
  , typographyScale         :: !TypeScale            -- ^ Mathematical scale
  , typographyHeadingLH     :: !LineHeight           -- ^ Line height for headlines
  , typographyBodyLH        :: !LineHeight           -- ^ Line height for body
  , typographyScaleTable    :: !(Vector TypeScaleEntry)  -- ^ Full scale table
  }
  deriving stock (Eq, Show)
