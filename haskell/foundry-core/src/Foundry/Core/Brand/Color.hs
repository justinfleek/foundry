{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // foundry // brand/color
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Color
Description : SMART Framework Color System (Section 15)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Professional color representation with all industry-standard formats.

== SMART Framework Section 15: Color Palette

From the framework:
"Colors must be reproduced faithfully. Any color outside the approved 
palette is unauthorized."

AI Ingestion Priority #2:
"Always capture hex as the canonical value. RGB, CMYK, and Pantone are 
format-specific translations."

== Color Spaces

* Hex  - Canonical web format (#RRGGBB)
* RGB  - Screen display (0-255 per channel)
* CMYK - Print (0-100% per channel)
* OKLCH - Perceptually uniform (for palette generation)
* Pantone - Spot color matching (string reference)

== Invariants

* Hex is always 6 characters (no shorthand)
* RGB channels ∈ [0, 255]
* CMYK channels ∈ [0, 100]
* OKLCH L ∈ [0, 1], C ∈ [0, 0.4], H ∈ [0, 360)

DEPENDENCIES:
  - None (base types)

DEPENDENTS:
  - Foundry.Core.Brand.Palette
  - Foundry.Extract.Color

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Color
  ( -- * Hex Color (Canonical)
    HexColor (..)
  , mkHexColor
  , hexToText
  
    -- * RGB Color
  , RGB (..)
  , mkRGB
  , rgbToHex
  , hexToRGB
  
    -- * CMYK Color (Print)
  , CMYK (..)
  , mkCMYK
  , rgbToCMYK
  , cmykToRGB
  
    -- * Pantone Reference
  , PantoneRef (..)
  , mkPantoneRef
  
    -- * Complete Color Specification
  , ColorSpec (..)
  , mkColorSpec
  , colorSpecFromHex
  ) where

import Data.Char (isHexDigit, toUpper)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word8)
import Numeric (readHex, showHex)

--------------------------------------------------------------------------------
-- Hex Color (Canonical Format)
--------------------------------------------------------------------------------

-- | Hex color - the canonical representation per SMART Framework
-- 
-- Stored as 6 hex characters (no # prefix, no shorthand).
-- "Always capture hex as the canonical value."
newtype HexColor = HexColor { unHexColor :: Text }
  deriving stock (Eq, Ord, Show)

-- | Create hex color with validation
-- 
-- Accepts formats: "RRGGBB", "#RRGGBB", "RGB" (expands to RRGGBB)
-- Always normalizes to uppercase 6-char format.
mkHexColor :: Text -> Maybe HexColor
mkHexColor input =
  let stripped = T.toUpper $ T.dropWhile (== '#') input
  in case T.length stripped of
    6 | T.all isHexDigit stripped -> Just (HexColor stripped)
    3 | T.all isHexDigit stripped -> 
        -- Expand shorthand: "ABC" -> "AABBCC"
        let expanded = T.concatMap (\c -> T.pack [c, c]) stripped
        in Just (HexColor expanded)
    _ -> Nothing

-- | Convert to CSS format with # prefix
hexToText :: HexColor -> Text
hexToText (HexColor h) = T.cons '#' h

--------------------------------------------------------------------------------
-- RGB Color
--------------------------------------------------------------------------------

-- | RGB color for screen display
-- 
-- Each channel is 0-255 (8-bit per channel).
data RGB = RGB
  { rgbR :: !Word8  -- ^ Red channel [0, 255]
  , rgbG :: !Word8  -- ^ Green channel [0, 255]
  , rgbB :: !Word8  -- ^ Blue channel [0, 255]
  }
  deriving stock (Eq, Ord, Show)

-- | Create RGB color (always valid for Word8 inputs)
mkRGB :: Word8 -> Word8 -> Word8 -> RGB
mkRGB = RGB

-- | Convert RGB to canonical hex format
rgbToHex :: RGB -> HexColor
rgbToHex (RGB r g b) = 
  let toHex w = let h = showHex w ""
                in if length h == 1 then '0' : h else h
      upper = map toUpper
  in HexColor $ T.pack $ upper $ toHex r <> toHex g <> toHex b

-- | Convert hex to RGB
hexToRGB :: HexColor -> RGB
hexToRGB (HexColor h) =
  let parseHex :: Text -> Word8
      parseHex t = case readHex (T.unpack t) of
        ((n, _):_) -> fromIntegral (n :: Integer)
        []         -> 0  -- Should never happen with valid HexColor
      r = parseHex (T.take 2 h)
      g = parseHex (T.take 2 (T.drop 2 h))
      b = parseHex (T.drop 4 h)
  in RGB r g b

--------------------------------------------------------------------------------
-- CMYK Color (Print)
--------------------------------------------------------------------------------

-- | CMYK color for print production
-- 
-- Each channel is 0-100 (percentage).
-- Note: RGB↔CMYK conversion is approximate without ICC profile.
data CMYK = CMYK
  { cmykC :: !Double  -- ^ Cyan [0, 100]
  , cmykM :: !Double  -- ^ Magenta [0, 100]
  , cmykY :: !Double  -- ^ Yellow [0, 100]
  , cmykK :: !Double  -- ^ Key/Black [0, 100]
  }
  deriving stock (Eq, Show)

-- | Create CMYK color with validation
mkCMYK :: Double -> Double -> Double -> Double -> Maybe CMYK
mkCMYK c m y k
  | all (\v -> v >= 0 && v <= 100) [c, m, y, k] = Just (CMYK c m y k)
  | otherwise = Nothing

-- | Convert RGB to CMYK (approximate, no ICC profile)
rgbToCMYK :: RGB -> CMYK
rgbToCMYK (RGB r g b) =
  let r' = fromIntegral r / 255.0
      g' = fromIntegral g / 255.0
      b' = fromIntegral b / 255.0
      k = 1.0 - max r' (max g' b')
      c = if k < 1.0 then (1.0 - r' - k) / (1.0 - k) else 0.0
      m = if k < 1.0 then (1.0 - g' - k) / (1.0 - k) else 0.0
      y = if k < 1.0 then (1.0 - b' - k) / (1.0 - k) else 0.0
  in CMYK (c * 100) (m * 100) (y * 100) (k * 100)

-- | Convert CMYK to RGB (approximate, no ICC profile)
cmykToRGB :: CMYK -> RGB
cmykToRGB (CMYK c m y k) =
  let c' = c / 100.0
      m' = m / 100.0
      y' = y / 100.0
      k' = k / 100.0
      r = round $ 255.0 * (1.0 - c') * (1.0 - k')
      g = round $ 255.0 * (1.0 - m') * (1.0 - k')
      b = round $ 255.0 * (1.0 - y') * (1.0 - k')
  in RGB r g b

--------------------------------------------------------------------------------
-- Pantone Reference
--------------------------------------------------------------------------------

-- | Pantone Matching System reference
-- 
-- This is a string reference (e.g., "PMS 286 C", "Pantone 7463 C").
-- Actual color matching requires physical Pantone books/software.
newtype PantoneRef = PantoneRef { unPantoneRef :: Text }
  deriving stock (Eq, Ord, Show)

-- | Create Pantone reference with validation (non-empty)
mkPantoneRef :: Text -> Maybe PantoneRef
mkPantoneRef t
  | T.length (T.strip t) >= 1 = Just (PantoneRef (T.strip t))
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Complete Color Specification
--------------------------------------------------------------------------------

-- | Complete color specification with all industry formats
-- 
-- From SMART Framework Section 15:
-- "For each named color, capture: Color Name, Hex Code, Pantone, RGB, CMYK, Role"
-- 
-- Hex is canonical; other formats are derived or manually specified.
data ColorSpec = ColorSpec
  { colorName    :: !Text             -- ^ Internal reference name (e.g., "Brand_P1")
  , colorHex     :: !HexColor         -- ^ Canonical hex value
  , colorRGB     :: !RGB              -- ^ RGB (derived from hex)
  , colorCMYK    :: !CMYK             -- ^ CMYK (derived or manual)
  , colorPantone :: !(Maybe PantoneRef) -- ^ Pantone reference (manual)
  }
  deriving stock (Eq, Show)

-- | Create complete color spec from all components
mkColorSpec 
  :: Text           -- ^ Name
  -> HexColor       -- ^ Hex (canonical)
  -> CMYK           -- ^ CMYK
  -> Maybe PantoneRef  -- ^ Pantone (optional)
  -> Maybe ColorSpec
mkColorSpec name hex cmyk pantone
  | T.length (T.strip name) >= 1 = Just ColorSpec
      { colorName = T.strip name
      , colorHex = hex
      , colorRGB = hexToRGB hex
      , colorCMYK = cmyk
      , colorPantone = pantone
      }
  | otherwise = Nothing

-- | Create color spec from hex, auto-deriving RGB and CMYK
colorSpecFromHex :: Text -> HexColor -> ColorSpec
colorSpecFromHex name hex =
  let rgb = hexToRGB hex
      cmyk = rgbToCMYK rgb
  in ColorSpec
       { colorName = name
       , colorHex = hex
       , colorRGB = rgb
       , colorCMYK = cmyk
       , colorPantone = Nothing
       }
