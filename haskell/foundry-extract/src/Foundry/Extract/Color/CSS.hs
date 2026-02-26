{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // foundry // extract // color/css
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Color.CSS
Description : CSS color parsing
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Parses CSS color values into a normalized OKLCH representation.

== Supported Formats

* Hex: #rgb, #rgba, #rrggbb, #rrggbbaa
* RGB: rgb(r, g, b), rgba(r, g, b, a)
* HSL: hsl(h, s%, l%), hsla(h, s%, l%, a)
* OKLCH: oklch(L C H), oklch(L C H / a)
* Named colors: all CSS4 named colors

== Design Notes

All colors are converted to OKLCH for perceptual uniformity. This enables
meaningful color distance calculations and proper contrast computation.

== Dependencies

Requires: attoparsec, text
Required by: Foundry.Extract.Color

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Color.CSS
  ( -- * Types
    ParsedColor (..)
  , RGB (..)
  , HSL (..)
  , OKLCH' (..)

    -- * Parsing
  , parseColor
  , parseColorText

    -- * Conversion
  , rgbToOKLCH
  , hslToOKLCH
  , namedToRGB
  ) where

import Data.Attoparsec.Text
  ( Parser
  , char
  , choice
  , decimal
  , double
  , hexadecimal
  , option
  , parseOnly
  , skipSpace
  , string
  , takeWhile1
  )
import Data.Char (isAlpha, toLower)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Parsed color in source format
data ParsedColor
  = PCHex !RGB
  | PCRGB !RGB
  | PCHSL !HSL
  | PCOKLCH !OKLCH'
  | PCNamed !Text !RGB
  deriving stock (Eq, Show)

-- | RGB color (0-255 for each channel)
data RGB = RGB
  { rgbR :: !Double
  , rgbG :: !Double
  , rgbB :: !Double
  , rgbA :: !Double
  }
  deriving stock (Eq, Show)

-- | HSL color
data HSL = HSL
  { hslH :: !Double  -- ^ Hue [0, 360)
  , hslS :: !Double  -- ^ Saturation [0, 1]
  , hslL :: !Double  -- ^ Lightness [0, 1]
  , hslA :: !Double  -- ^ Alpha [0, 1]
  }
  deriving stock (Eq, Show)

-- | OKLCH color (internal representation)
data OKLCH' = OKLCH'
  { oklchL' :: !Double  -- ^ Lightness [0, 1]
  , oklchC' :: !Double  -- ^ Chroma [0, 0.4]
  , oklchH' :: !Double  -- ^ Hue [0, 360)
  , oklchA' :: !Double  -- ^ Alpha [0, 1]
  }
  deriving stock (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- Parsing
--------------------------------------------------------------------------------

-- | Parse a CSS color string
parseColorText :: Text -> Maybe ParsedColor
parseColorText t = case parseOnly colorParser (T.strip t) of
  Left _  -> Nothing
  Right c -> Just c

-- | Parse a CSS color (attoparsec parser)
parseColor :: Parser ParsedColor
parseColor = colorParser

colorParser :: Parser ParsedColor
colorParser = choice
  [ hexColorParser
  , rgbColorParser
  , hslColorParser
  , oklchColorParser
  , namedColorParser
  ]

-- | Parse hex color: #rgb, #rgba, #rrggbb, #rrggbbaa
hexColorParser :: Parser ParsedColor
hexColorParser = do
  _ <- char '#'
  digits <- takeWhile1 isHexDigit
  case T.length digits of
    3 -> pure $ PCHex (expandShortHex digits 1.0)
    4 -> let (rgb, a) = T.splitAt 3 digits
         in pure $ PCHex (expandShortHex rgb (hexToAlpha a))
    6 -> pure $ PCHex (parseLongHex digits 1.0)
    8 -> let (rgb, a) = T.splitAt 6 digits
         in pure $ PCHex (parseLongHex rgb (hexToAlpha a))
    _ -> fail "Invalid hex color length"

isHexDigit :: Char -> Bool
isHexDigit c = c >= '0' && c <= '9' || c >= 'a' && c <= 'f' || c >= 'A' && c <= 'F'

expandShortHex :: Text -> Double -> RGB
expandShortHex t a = case T.unpack t of
  [r, g, b] -> RGB
    (hexCharToDouble r * 17)
    (hexCharToDouble g * 17)
    (hexCharToDouble b * 17)
    a
  _ -> RGB 0 0 0 a

parseLongHex :: Text -> Double -> RGB
parseLongHex t a = case T.unpack t of
  [r1, r2, g1, g2, b1, b2] -> RGB
    (hexPairToDouble r1 r2)
    (hexPairToDouble g1 g2)
    (hexPairToDouble b1 b2)
    a
  _ -> RGB 0 0 0 a

hexToAlpha :: Text -> Double
hexToAlpha t = case T.unpack t of
  [c]      -> hexCharToDouble c * 17 / 255
  [c1, c2] -> hexPairToDouble c1 c2 / 255
  _        -> 1.0

hexCharToDouble :: Char -> Double
hexCharToDouble c
  | c >= '0' && c <= '9' = fromIntegral (fromEnum c - fromEnum '0')
  | c >= 'a' && c <= 'f' = fromIntegral (fromEnum c - fromEnum 'a' + 10)
  | c >= 'A' && c <= 'F' = fromIntegral (fromEnum c - fromEnum 'A' + 10)
  | otherwise            = 0

hexPairToDouble :: Char -> Char -> Double
hexPairToDouble c1 c2 = hexCharToDouble c1 * 16 + hexCharToDouble c2

-- | Parse rgb/rgba color
rgbColorParser :: Parser ParsedColor
rgbColorParser = do
  _ <- choice [string "rgba(", string "rgb("]
  skipSpace
  r <- double
  skipSpace >> option () (char ',' >> pure ()) >> skipSpace
  g <- double
  skipSpace >> option () (char ',' >> pure ()) >> skipSpace
  b <- double
  a <- option 1.0 (skipSpace >> choice [char ',' >> pure (), char '/' >> pure ()] >> skipSpace >> double)
  skipSpace
  _ <- char ')'
  pure $ PCRGB (RGB r g b a)

-- | Parse hsl/hsla color
hslColorParser :: Parser ParsedColor
hslColorParser = do
  _ <- choice [string "hsla(", string "hsl("]
  skipSpace
  h <- double
  skipSpace >> option () (char ',' >> pure ()) >> skipSpace
  s <- percentValue
  skipSpace >> option () (char ',' >> pure ()) >> skipSpace
  l <- percentValue
  a <- option 1.0 (skipSpace >> choice [char ',' >> pure (), char '/' >> pure ()] >> skipSpace >> double)
  skipSpace
  _ <- char ')'
  pure $ PCHSL (HSL h s l a)

percentValue :: Parser Double
percentValue = do
  n <- double
  hasPercent <- option False (char '%' >> pure True)
  pure $ if hasPercent then n / 100 else n

-- | Parse oklch color
oklchColorParser :: Parser ParsedColor
oklchColorParser = do
  _ <- string "oklch("
  skipSpace
  l <- percentValue
  skipSpace
  c <- double
  skipSpace
  h <- double
  a <- option 1.0 (skipSpace >> char '/' >> skipSpace >> double)
  skipSpace
  _ <- char ')'
  pure $ PCOKLCH (OKLCH' l c h a)

-- | Parse named color
namedColorParser :: Parser ParsedColor
namedColorParser = do
  name <- takeWhile1 isAlpha
  let lowerName = T.map toLower name
  case Map.lookup lowerName namedColors of
    Just rgb -> pure $ PCNamed lowerName rgb
    Nothing  -> fail "Unknown color name"

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

-- | Convert RGB to OKLCH
rgbToOKLCH :: RGB -> OKLCH'
rgbToOKLCH (RGB r g b a) = 
  let -- Normalize to [0, 1]
      r' = r / 255
      g' = g / 255
      b' = b / 255
      
      -- Linear RGB (sRGB gamma correction)
      linearize x = if x <= 0.04045
                    then x / 12.92
                    else ((x + 0.055) / 1.055) ** 2.4
      rl = linearize r'
      gl = linearize g'
      bl = linearize b'
      
      -- RGB to OKLab
      l_ = 0.4122214708 * rl + 0.5363325363 * gl + 0.0514459929 * bl
      m_ = 0.2119034982 * rl + 0.6806995451 * gl + 0.1073969566 * bl
      s_ = 0.0883024619 * rl + 0.2817188376 * gl + 0.6299787005 * bl
      
      l_' = cbrt l_
      m_' = cbrt m_
      s_' = cbrt s_
      
      labL = 0.2104542553 * l_' + 0.7936177850 * m_' - 0.0040720468 * s_'
      labA = 1.9779984951 * l_' - 2.4285922050 * m_' + 0.4505937099 * s_'
      labB = 0.0259040371 * l_' + 0.7827717662 * m_' - 0.8086757660 * s_'
      
      -- OKLab to OKLCH
      c = sqrt (labA * labA + labB * labB)
      h = if c < 0.00001 then 0 else atan2 labB labA * 180 / pi
      h' = if h < 0 then h + 360 else h
  in OKLCH' labL (min 0.4 c) h' a

cbrt :: Double -> Double
cbrt x = if x < 0 then -((-x) ** (1/3)) else x ** (1/3)

-- | Convert HSL to OKLCH (via RGB)
hslToOKLCH :: HSL -> OKLCH'
hslToOKLCH (HSL h s l a) = rgbToOKLCH (hslToRGB h s l a)

hslToRGB :: Double -> Double -> Double -> Double -> RGB
hslToRGB h s l a =
  let c = (1 - abs (2 * l - 1)) * s
      h' = h / 60
      x = c * (1 - abs (h' `fmod` 2 - 1))
      m = l - c / 2
      (r', g', b') = case floor h' :: Int of
        0 -> (c, x, 0)
        1 -> (x, c, 0)
        2 -> (0, c, x)
        3 -> (0, x, c)
        4 -> (x, 0, c)
        5 -> (c, 0, x)
        _ -> (c, 0, x)
  in RGB ((r' + m) * 255) ((g' + m) * 255) ((b' + m) * 255) a

fmod :: Double -> Double -> Double
fmod x y = x - fromIntegral (floor (x / y) :: Int) * y

-- | Get RGB for a named color
namedToRGB :: Text -> Maybe RGB
namedToRGB = flip Map.lookup namedColors

--------------------------------------------------------------------------------
-- Named Colors (CSS4 specification)
--------------------------------------------------------------------------------

namedColors :: Map Text RGB
namedColors = Map.fromList
  [ ("black", RGB 0 0 0 1)
  , ("white", RGB 255 255 255 1)
  , ("red", RGB 255 0 0 1)
  , ("green", RGB 0 128 0 1)
  , ("blue", RGB 0 0 255 1)
  , ("yellow", RGB 255 255 0 1)
  , ("cyan", RGB 0 255 255 1)
  , ("magenta", RGB 255 0 255 1)
  , ("gray", RGB 128 128 128 1)
  , ("grey", RGB 128 128 128 1)
  , ("silver", RGB 192 192 192 1)
  , ("maroon", RGB 128 0 0 1)
  , ("olive", RGB 128 128 0 1)
  , ("lime", RGB 0 255 0 1)
  , ("aqua", RGB 0 255 255 1)
  , ("teal", RGB 0 128 128 1)
  , ("navy", RGB 0 0 128 1)
  , ("fuchsia", RGB 255 0 255 1)
  , ("purple", RGB 128 0 128 1)
  , ("orange", RGB 255 165 0 1)
  , ("pink", RGB 255 192 203 1)
  , ("brown", RGB 165 42 42 1)
  , ("coral", RGB 255 127 80 1)
  , ("crimson", RGB 220 20 60 1)
  , ("darkblue", RGB 0 0 139 1)
  , ("darkgray", RGB 169 169 169 1)
  , ("darkgreen", RGB 0 100 0 1)
  , ("darkred", RGB 139 0 0 1)
  , ("gold", RGB 255 215 0 1)
  , ("indigo", RGB 75 0 130 1)
  , ("ivory", RGB 255 255 240 1)
  , ("lavender", RGB 230 230 250 1)
  , ("lightblue", RGB 173 216 230 1)
  , ("lightgray", RGB 211 211 211 1)
  , ("lightgreen", RGB 144 238 144 1)
  , ("lightyellow", RGB 255 255 224 1)
  , ("mintcream", RGB 245 255 250 1)
  , ("mistyrose", RGB 255 228 225 1)
  , ("moccasin", RGB 255 228 181 1)
  , ("navajowhite", RGB 255 222 173 1)
  , ("oldlace", RGB 253 245 230 1)
  , ("olivedrab", RGB 107 142 35 1)
  , ("orangered", RGB 255 69 0 1)
  , ("orchid", RGB 218 112 214 1)
  , ("palegoldenrod", RGB 238 232 170 1)
  , ("palegreen", RGB 152 251 152 1)
  , ("paleturquoise", RGB 175 238 238 1)
  , ("palevioletred", RGB 219 112 147 1)
  , ("papayawhip", RGB 255 239 213 1)
  , ("peachpuff", RGB 255 218 185 1)
  , ("peru", RGB 205 133 63 1)
  , ("plum", RGB 221 160 221 1)
  , ("powderblue", RGB 176 224 230 1)
  , ("rosybrown", RGB 188 143 143 1)
  , ("royalblue", RGB 65 105 225 1)
  , ("saddlebrown", RGB 139 69 19 1)
  , ("salmon", RGB 250 128 114 1)
  , ("sandybrown", RGB 244 164 96 1)
  , ("seagreen", RGB 46 139 87 1)
  , ("seashell", RGB 255 245 238 1)
  , ("sienna", RGB 160 82 45 1)
  , ("skyblue", RGB 135 206 235 1)
  , ("slateblue", RGB 106 90 205 1)
  , ("slategray", RGB 112 128 144 1)
  , ("snow", RGB 255 250 250 1)
  , ("springgreen", RGB 0 255 127 1)
  , ("steelblue", RGB 70 130 180 1)
  , ("tan", RGB 210 180 140 1)
  , ("thistle", RGB 216 191 216 1)
  , ("tomato", RGB 255 99 71 1)
  , ("turquoise", RGB 64 224 208 1)
  , ("violet", RGB 238 130 238 1)
  , ("wheat", RGB 245 222 179 1)
  , ("whitesmoke", RGB 245 245 245 1)
  , ("yellowgreen", RGB 154 205 50 1)
  , ("rebeccapurple", RGB 102 51 153 1)
  , ("transparent", RGB 0 0 0 0)
  ]
