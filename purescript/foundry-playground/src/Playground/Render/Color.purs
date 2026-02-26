-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // playground // render // color
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color types for GPU rendering.
-- |
-- | All colors are OKLCH internally (perceptually uniform).
-- | Conversion to linear sRGB happens at the render boundary for GPU.
-- |
-- | This module re-exports from the brand schema and adds GPU-specific formats.

module Playground.Render.Color
  ( -- * Re-export OKLCH from Brand
    module Hydrogen.Schema.Brand.Palette
  
  -- * GPU Color Formats
  , LinearRGB
  , mkLinearRGB
  , linearR
  , linearG
  , linearB
  
  -- * RGBA for GPU (linear, premultiplied alpha)
  , LinearRGBA
  , mkLinearRGBA
  , opaqueLinear
  , transparentLinear
  
  -- * Conversions
  , oklchToLinearRGB
  , linearRGBToOKLCH
  , oklchToLinearRGBA
  
  -- * GPU Buffer Format
  , colorToVec4
  ) where

import Prelude
  ( (<>)
  , (-)
  , (*)
  , (+)
  , (/)
  , (>=)
  , (<=)
  , (>)
  , max
  , min
  , otherwise
  , show
  , negate
  )

import Data.Number (pow, abs, sqrt, cos, sin, atan2, pi)

-- Re-export the canonical color types
import Hydrogen.Schema.Brand.Palette
  ( Lightness
  , mkLightness
  , unLightness
  , Chroma
  , mkChroma
  , unChroma
  , Hue
  , mkHue
  , unHue
  , OKLCH
  , oklch
  )

import Playground.Render.Geometry (Vec4, mkVec4)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // linear rgb
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Linear RGB color (not gamma-corrected).
-- |
-- | This is what the GPU expects for blending.
-- | Components are in [0, 1] range (clamped).
type LinearRGB =
  { r :: Number
  , g :: Number
  , b :: Number
  }

-- | Create linear RGB with clamping.
mkLinearRGB :: Number -> Number -> Number -> LinearRGB
mkLinearRGB r g b =
  { r: clamp01 r
  , g: clamp01 g
  , b: clamp01 b
  }

-- | Get R component.
linearR :: LinearRGB -> Number
linearR c = c.r

-- | Get G component.
linearG :: LinearRGB -> Number
linearG c = c.g

-- | Get B component.
linearB :: LinearRGB -> Number
linearB c = c.b

-- | Clamp to [0, 1].
clamp01 :: Number -> Number
clamp01 x
  | x <= 0.0 = 0.0
  | x >= 1.0 = 1.0
  | otherwise = x

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // linear rgba
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Linear RGBA with premultiplied alpha.
-- |
-- | Premultiplied alpha is standard for GPU compositing:
-- | rgb values are already multiplied by alpha.
type LinearRGBA =
  { r :: Number    -- Premultiplied R
  , g :: Number    -- Premultiplied G
  , b :: Number    -- Premultiplied B
  , a :: Number    -- Alpha (0 = transparent, 1 = opaque)
  }

-- | Create linear RGBA with premultiplied alpha.
mkLinearRGBA :: Number -> Number -> Number -> Number -> LinearRGBA
mkLinearRGBA r g b a =
  let alpha = clamp01 a
  in
    { r: clamp01 r * alpha
    , g: clamp01 g * alpha
    , b: clamp01 b * alpha
    , a: alpha
    }

-- | Opaque color (alpha = 1).
opaqueLinear :: LinearRGB -> LinearRGBA
opaqueLinear c = { r: c.r, g: c.g, b: c.b, a: 1.0 }

-- | Fully transparent.
transparentLinear :: LinearRGBA
transparentLinear = { r: 0.0, g: 0.0, b: 0.0, a: 0.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert OKLCH to Linear RGB.
-- |
-- | OKLCH → OKLab → Linear sRGB
-- | This is the standard conversion for GPU rendering.
oklchToLinearRGB :: OKLCH -> LinearRGB
oklchToLinearRGB color =
  let
    l = unLightness color.l
    c = unChroma color.c
    h = unHue color.h
    
    -- OKLCH to OKLab
    hRad = h * pi / 180.0
    labA = c * cos hRad
    labB = c * sin hRad
    
    -- OKLab to linear RGB (via LMS)
    l_ = l + 0.3963377774 * labA + 0.2158037573 * labB
    m_ = l - 0.1055613458 * labA - 0.0638541728 * labB
    s_ = l - 0.0894841775 * labA - 1.2914855480 * labB
    
    lCube = l_ * l_ * l_
    mCube = m_ * m_ * m_
    sCube = s_ * s_ * s_
    
    r = 4.0767416621 * lCube - 3.3077115913 * mCube + 0.2309699292 * sCube
    g = negate 1.2684380046 * lCube + 2.6097574011 * mCube - 0.3413193965 * sCube
    b = negate 0.0041960863 * lCube - 0.7034186147 * mCube + 1.7076147010 * sCube
  in
    mkLinearRGB r g b

-- | Convert Linear RGB to OKLCH.
-- |
-- | Linear sRGB → OKLab → OKLCH
linearRGBToOKLCH :: LinearRGB -> OKLCH
linearRGBToOKLCH color =
  let
    -- Linear RGB to LMS
    l_ = 0.4122214708 * color.r + 0.5363325363 * color.g + 0.0514459929 * color.b
    m_ = 0.2119034982 * color.r + 0.6806995451 * color.g + 0.1073969566 * color.b
    s_ = 0.0883024619 * color.r + 0.2817188376 * color.g + 0.6299787005 * color.b
    
    -- Cube root
    lCbrt = cbrt l_
    mCbrt = cbrt m_
    sCbrt = cbrt s_
    
    -- LMS to OKLab
    labL = 0.2104542553 * lCbrt + 0.7936177850 * mCbrt - 0.0040720468 * sCbrt
    labA = 1.9779984951 * lCbrt - 2.4285922050 * mCbrt + 0.4505937099 * sCbrt
    labB = 0.0259040371 * lCbrt + 0.7827717662 * mCbrt - 0.8086757660 * sCbrt
    
    -- OKLab to OKLCH
    c = sqrt (labA * labA + labB * labB)
    h = atan2 labB labA * 180.0 / pi
    hNorm = if h >= 0.0 then h else h + 360.0
  in
    oklch labL c hNorm

-- | Cube root (handles negative numbers).
cbrt :: Number -> Number
cbrt x =
  if x >= 0.0
  then pow x (1.0 / 3.0)
  else negate (pow (negate x) (1.0 / 3.0))

-- | Convert OKLCH to Linear RGBA (opaque).
oklchToLinearRGBA :: OKLCH -> LinearRGBA
oklchToLinearRGBA c = opaqueLinear (oklchToLinearRGB c)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // gpu buffer format
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert color to Vec4 for GPU uniform/vertex buffer.
-- |
-- | Format: [r, g, b, a] as f32 in linear space, premultiplied.
colorToVec4 :: LinearRGBA -> Vec4
colorToVec4 c = mkVec4 c.r c.g c.b c.a
