-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // brand // typography
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brand typography atoms and molecules.
-- |
-- | STATUS: PROVEN (Hydrogen.Schema.Brand.Typography)
-- |
-- | Invariants:
-- |   weight_bounded: 100 <= weight <= 900 (PROVEN)
-- |   weight_multiple: weight % 100 == 0 (PROVEN)
-- |   scale_gt_one: ratio > 1 (PROVEN)
-- |   scale_monotonic: larger level = larger size (PROVEN)
-- |   family_nonempty: name.length > 0 (PROVEN)

module Hydrogen.Schema.Brand.Typography
  ( -- * Font Weight
    FontWeight
      ( Thin
      , ExtraLight
      , Light
      , Regular
      , Medium
      , SemiBold
      , Bold
      , ExtraBold
      , Black
      )
  , fontWeightToInt
  , fontWeightFromInt
  
  -- * Font Family
  , FontFamily
  , mkFontFamily
  , unFontFamily
  , sansSerif
  , serif
  , monospace
  , systemUI
  
  -- * Font Size
  , FontSize
  , mkFontSize
  , unFontSize
  
  -- * Type Scale
  , ScaleRatio
  , mkScaleRatio
  , unScaleRatio
  , TypeScale
  , mkTypeScale
  , sizeAt
  , scaleXS
  , scaleSM
  , scaleMD
  , scaleLG
  , scaleXL
  , scaleXXL
  
  -- * Brand Typography
  , BrandTypography
  , defaultTypography
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>)
  , (>=)
  , (*)
  , (<>)
  , compare
  , negate
  , otherwise
  , show
  )

import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (pow)
import Data.String as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // font weight
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Font weight atom (CSS standard values).
-- |
-- | Bounded: 100-900 in multiples of 100.
-- | These are the standard CSS font-weight values.
data FontWeight
  = Thin       -- 100
  | ExtraLight -- 200
  | Light      -- 300
  | Regular    -- 400
  | Medium     -- 500
  | SemiBold   -- 600
  | Bold       -- 700
  | ExtraBold  -- 800
  | Black      -- 900

derive instance eqFontWeight :: Eq FontWeight

instance ordFontWeight :: Ord FontWeight where
  compare w1 w2 = compare (fontWeightToInt w1) (fontWeightToInt w2)

instance showFontWeight :: Show FontWeight where
  show Thin = "100"
  show ExtraLight = "200"
  show Light = "300"
  show Regular = "400"
  show Medium = "500"
  show SemiBold = "600"
  show Bold = "700"
  show ExtraBold = "800"
  show Black = "900"

-- | Convert to integer (CSS value).
fontWeightToInt :: FontWeight -> Int
fontWeightToInt Thin = 100
fontWeightToInt ExtraLight = 200
fontWeightToInt Light = 300
fontWeightToInt Regular = 400
fontWeightToInt Medium = 500
fontWeightToInt SemiBold = 600
fontWeightToInt Bold = 700
fontWeightToInt ExtraBold = 800
fontWeightToInt Black = 900

-- | Parse from integer.
fontWeightFromInt :: Int -> Maybe FontWeight
fontWeightFromInt 100 = Just Thin
fontWeightFromInt 200 = Just ExtraLight
fontWeightFromInt 300 = Just Light
fontWeightFromInt 400 = Just Regular
fontWeightFromInt 500 = Just Medium
fontWeightFromInt 600 = Just SemiBold
fontWeightFromInt 700 = Just Bold
fontWeightFromInt 800 = Just ExtraBold
fontWeightFromInt 900 = Just Black
fontWeightFromInt _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // font family
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Font family atom.
-- |
-- | A validated font family name (non-empty, trimmed).
-- | Examples: "Inter", "Roboto", "Georgia", "system-ui"
newtype FontFamily = FontFamily String

derive instance eqFontFamily :: Eq FontFamily

instance ordFontFamily :: Ord FontFamily where
  compare (FontFamily f1) (FontFamily f2) = compare f1 f2

instance showFontFamily :: Show FontFamily where
  show (FontFamily f) = "FontFamily(" <> f <> ")"

-- | Smart constructor with validation.
mkFontFamily :: String -> Maybe FontFamily
mkFontFamily s =
  let trimmed = String.trim s
  in if String.length trimmed > 0
     then Just (FontFamily trimmed)
     else Nothing

-- | Unwrap font family to string.
unFontFamily :: FontFamily -> String
unFontFamily (FontFamily f) = f

-- | Generic fallback: sans-serif
sansSerif :: FontFamily
sansSerif = FontFamily "sans-serif"

-- | Generic fallback: serif
serif :: FontFamily
serif = FontFamily "serif"

-- | Generic fallback: monospace
monospace :: FontFamily
monospace = FontFamily "monospace"

-- | Generic fallback: system-ui
systemUI :: FontFamily
systemUI = FontFamily "system-ui"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // font size
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Font size atom (in pixels, positive).
-- |
-- | Bounded: Must be > 0. Values <= 0 are clamped to 1.0.
newtype FontSize = FontSize Number

derive instance eqFontSize :: Eq FontSize
derive instance ordFontSize :: Ord FontSize

instance showFontSize :: Show FontSize where
  show (FontSize px) = "FontSize(" <> show px <> "px)"

-- | Smart constructor with clamping.
mkFontSize :: Number -> FontSize
mkFontSize n = if n > 0.0 then FontSize n else FontSize 1.0

-- | Unwrap font size to number (pixels).
unFontSize :: FontSize -> Number
unFontSize (FontSize px) = px

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // scale ratio
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Type scale ratio atom.
-- |
-- | Bounded: Must be > 1.0. Values <= 1.0 are set to 1.125 (minor second).
-- |
-- | Common ratios:
-- |   1.125 (minor second)
-- |   1.250 (major third)
-- |   1.333 (perfect fourth)
-- |   1.414 (augmented fourth)
-- |   1.500 (perfect fifth)
-- |   1.618 (golden ratio)
newtype ScaleRatio = ScaleRatio Number

derive instance eqScaleRatio :: Eq ScaleRatio
derive instance ordScaleRatio :: Ord ScaleRatio

instance showScaleRatio :: Show ScaleRatio where
  show (ScaleRatio r) = "ScaleRatio(" <> show r <> ")"

-- | Smart constructor with validation.
mkScaleRatio :: Number -> ScaleRatio
mkScaleRatio r = if r > 1.0 then ScaleRatio r else ScaleRatio 1.125

-- | Unwrap scale ratio to number.
unScaleRatio :: ScaleRatio -> Number
unScaleRatio (ScaleRatio r) = r

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // type scale
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Type scale molecule.
-- |
-- | Composed of a base size and a scale ratio.
-- | Produces font sizes as: base * ratio^level
-- |
-- | Invariant: scale_monotonic (larger level = larger size)
type TypeScale =
  { base :: FontSize
  , ratio :: ScaleRatio
  }

-- | Create a type scale.
mkTypeScale :: Number -> Number -> TypeScale
mkTypeScale base ratio =
  { base: mkFontSize base
  , ratio: mkScaleRatio ratio
  }

-- | Get size at scale level.
-- |
-- | Level 0 = base
-- | Level 1 = base * ratio
-- | Level 2 = base * ratio^2
-- | Level -1 = base / ratio
-- | etc.
sizeAt :: TypeScale -> Int -> FontSize
sizeAt scale level =
  let 
    ScaleRatio r = scale.ratio
    FontSize b = scale.base
  in 
    FontSize (b * pow r (toNumber level))

-- | Scale level: extra small (level -2)
scaleXS :: TypeScale -> FontSize
scaleXS s = sizeAt s (-2)

-- | Scale level: small (level -1)
scaleSM :: TypeScale -> FontSize
scaleSM s = sizeAt s (-1)

-- | Scale level: medium/base (level 0)
scaleMD :: TypeScale -> FontSize
scaleMD s = sizeAt s 0

-- | Scale level: large (level 1)
scaleLG :: TypeScale -> FontSize
scaleLG s = sizeAt s 1

-- | Scale level: extra large (level 2)
scaleXL :: TypeScale -> FontSize
scaleXL s = sizeAt s 2

-- | Scale level: extra extra large (level 3)
scaleXXL :: TypeScale -> FontSize
scaleXXL s = sizeAt s 3

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // brand typography
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Brand typography compound.
-- |
-- | Complete typography configuration for a brand:
-- |   - headingFamily: Font for headings
-- |   - bodyFamily: Font for body text
-- |   - monoFamily: Font for code/monospace
-- |   - scale: Type scale for size progression
-- |   - regularWeight: Default text weight
-- |   - boldWeight: Emphasis text weight
type BrandTypography =
  { headingFamily :: FontFamily
  , bodyFamily :: FontFamily
  , monoFamily :: FontFamily
  , scale :: TypeScale
  , regularWeight :: FontWeight
  , boldWeight :: FontWeight
  }

-- | Default typography (Inter family, 1.25 scale).
defaultTypography :: BrandTypography
defaultTypography =
  { headingFamily: FontFamily "Inter"
  , bodyFamily: FontFamily "Inter"
  , monoFamily: monospace
  , scale: mkTypeScale 16.0 1.25
  , regularWeight: Regular
  , boldWeight: Bold
  }
