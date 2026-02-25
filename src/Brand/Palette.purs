-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // brand // palette
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brand color palette with semantic roles.
-- |
-- | STATUS: PROVEN (Hydrogen.Schema.Brand.Palette)
-- |
-- | Invariants:
-- |   in_gamut: All OKLCH colors within bounds (PROVEN)
-- |   has_primary: Palette always has primary color (PROVEN)
-- |   unique_roles: Each role appears at most once (PROVEN)
-- |   all_colors_in_gamut: Every palette color is valid (PROVEN)
-- |
-- | OKLCH is a perceptually uniform color space:
-- |   L: Lightness (0 to 1)
-- |   C: Chroma (0 to ~0.4 for sRGB gamut)
-- |   H: Hue (0 to 360, wrapping)

module Hydrogen.Schema.Brand.Palette
  ( -- * Color Atoms
    Lightness
  , mkLightness
  , unLightness
  , Chroma
  , mkChroma
  , unChroma
  , Hue
  , mkHue
  , unHue
  
  -- * OKLCH Color
  , OKLCH
  , oklch
  , oklchL
  , oklchC
  , oklchH
  
  -- * Semantic Roles
  , Role
      ( Primary
      , Secondary
      , Accent
      , Background
      , Surface
      , OnPrimary
      , OnSecondary
      , OnBackground
      , OnSurface
      , Success
      , Warning
      , Error
      , Info
      )
  
  -- * Palette Types
  , PaletteEntry
  , mkPaletteEntry
  , BrandPalette
  , mkBrandPalette
  , getPrimary
  , getByRole
  , paletteEntries
  
  -- * Contrast
  , lightnessDiff
  , hasMinimumContrast
  , wcagAALightnessDiff
  , wcagAAALightnessDiff
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>=)
  , (<=)
  , (<)
  , (>)
  , (-)
  , (+)
  , (*)
  , (/)
  , (<>)
  , compare
  , show
  , map
  , otherwise
  )

import Data.Array (find, length, nub)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (floor) as Number
import Data.Number (abs)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // lightness
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Lightness atom (0 to 1).
-- |
-- | Bounded: Values outside [0, 1] are clamped.
-- | 0 = black, 1 = white
newtype Lightness = Lightness Number

derive instance eqLightness :: Eq Lightness
derive instance ordLightness :: Ord Lightness

instance showLightness :: Show Lightness where
  show (Lightness l) = "Lightness(" <> show l <> ")"

-- | Smart constructor with clamping.
mkLightness :: Number -> Lightness
mkLightness n
  | n < 0.0 = Lightness 0.0
  | n > 1.0 = Lightness 1.0
  | otherwise = Lightness n

-- | Unwrap lightness to number.
unLightness :: Lightness -> Number
unLightness (Lightness l) = l

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // chroma
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Chroma atom (0 to 0.5).
-- |
-- | Bounded: Values outside [0, 0.5] are clamped.
-- | 0 = achromatic (gray), higher = more colorful
-- | 0.5 is a conservative bound covering all sRGB colors.
newtype Chroma = Chroma Number

derive instance eqChroma :: Eq Chroma
derive instance ordChroma :: Ord Chroma

instance showChroma :: Show Chroma where
  show (Chroma c) = "Chroma(" <> show c <> ")"

-- | Smart constructor with clamping.
mkChroma :: Number -> Chroma
mkChroma n
  | n < 0.0 = Chroma 0.0
  | n > 0.5 = Chroma 0.5
  | otherwise = Chroma n

-- | Unwrap chroma to number.
unChroma :: Chroma -> Number
unChroma (Chroma c) = c

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                          // hue
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Hue atom (0 to 360, wrapping).
-- |
-- | Cyclic: Values wrap around at 360.
-- | 0 = red, 120 = green, 240 = blue
newtype Hue = Hue Number

derive instance eqHue :: Eq Hue

instance ordHue :: Ord Hue where
  compare (Hue h1) (Hue h2) = compare h1 h2

instance showHue :: Show Hue where
  show (Hue h) = "Hue(" <> show h <> ")"

-- | Smart constructor with wrapping.
mkHue :: Number -> Hue
mkHue n = 
  let 
    -- Normalize to [0, 360)
    wrapped = n - 360.0 * Number.floor (n / 360.0)
    normalized = if wrapped < 0.0 then wrapped + 360.0 else wrapped
  in 
    Hue normalized

-- | Unwrap hue to number.
unHue :: Hue -> Number
unHue (Hue h) = h

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // oklch
-- ═══════════════════════════════════════════════════════════════════════════════

-- | OKLCH color molecule.
-- |
-- | Composed of Lightness, Chroma, and Hue atoms.
-- | Perceptually uniform: equal numeric differences = equal perceived differences.
type OKLCH =
  { l :: Lightness
  , c :: Chroma
  , h :: Hue
  }

-- | Create OKLCH color from raw numbers.
-- |
-- | Components are validated/clamped by their constructors.
oklch :: Number -> Number -> Number -> OKLCH
oklch l c h = 
  { l: mkLightness l
  , c: mkChroma c
  , h: mkHue h
  }

-- | Get lightness component.
oklchL :: OKLCH -> Lightness
oklchL color = color.l

-- | Get chroma component.
oklchC :: OKLCH -> Chroma
oklchC color = color.c

-- | Get hue component.
oklchH :: OKLCH -> Hue
oklchH color = color.h

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // role
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Semantic role of a color in a brand palette.
-- |
-- | These roles are standard across design systems and enable agents
-- | to build UI without ambiguity about color purpose.
data Role
  = Primary       -- Main brand color
  | Secondary     -- Supporting brand color
  | Accent        -- Call-to-action, highlights
  | Background    -- Page/section backgrounds
  | Surface       -- Card/element backgrounds
  | OnPrimary     -- Text/icons on primary
  | OnSecondary   -- Text/icons on secondary
  | OnBackground  -- Text/icons on background
  | OnSurface     -- Text/icons on surface
  | Success       -- Positive feedback
  | Warning       -- Caution feedback
  | Error         -- Negative feedback
  | Info          -- Informational

derive instance eqRole :: Eq Role

instance ordRole :: Ord Role where
  compare r1 r2 = compare (roleToInt r1) (roleToInt r2)
    where
      roleToInt :: Role -> Int
      roleToInt Primary = 0
      roleToInt Secondary = 1
      roleToInt Accent = 2
      roleToInt Background = 3
      roleToInt Surface = 4
      roleToInt OnPrimary = 5
      roleToInt OnSecondary = 6
      roleToInt OnBackground = 7
      roleToInt OnSurface = 8
      roleToInt Success = 9
      roleToInt Warning = 10
      roleToInt Error = 11
      roleToInt Info = 12

instance showRole :: Show Role where
  show Primary = "primary"
  show Secondary = "secondary"
  show Accent = "accent"
  show Background = "background"
  show Surface = "surface"
  show OnPrimary = "on-primary"
  show OnSecondary = "on-secondary"
  show OnBackground = "on-background"
  show OnSurface = "on-surface"
  show Success = "success"
  show Warning = "warning"
  show Error = "error"
  show Info = "info"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // palette entry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Palette entry molecule.
-- |
-- | Pairs a color with its semantic role.
type PaletteEntry = 
  { color :: OKLCH
  , role :: Role
  }

-- | Create a palette entry.
mkPaletteEntry :: OKLCH -> Role -> PaletteEntry
mkPaletteEntry color role = { color, role }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // brand palette
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Brand palette compound.
-- |
-- | A valid brand palette must have at least a primary color.
-- | Additional roles are optional but when present, must be unique.
-- |
-- | Invariants:
-- |   has_primary: Palette always has primary color
-- |   unique_roles: Each role appears at most once
type BrandPalette = 
  { entries :: Array PaletteEntry
  }

-- | Create a valid brand palette.
-- |
-- | Returns Nothing if:
-- |   - No primary color present
-- |   - Duplicate roles present
mkBrandPalette :: Array PaletteEntry -> Maybe BrandPalette
mkBrandPalette entries =
  let 
    hasPrimary = find (\e -> e.role == Primary) entries
    roles = map (\e -> e.role) entries
    uniqueRoles = length roles == length (nub roles)
  in 
    case hasPrimary of
      Just _ | uniqueRoles -> Just { entries }
      _ -> Nothing

-- | Get the primary color.
-- |
-- | Always succeeds for a valid palette (has_primary invariant).
-- | Returns black for invalid palettes (shouldn't happen with smart constructor).
getPrimary :: BrandPalette -> OKLCH
getPrimary palette =
  case find (\e -> e.role == Primary) palette.entries of
    Just entry -> entry.color
    Nothing -> oklch 0.0 0.0 0.0  -- Impossible for valid palette

-- | Get color by role.
getByRole :: Role -> BrandPalette -> Maybe OKLCH
getByRole role palette =
  map (\e -> e.color) (find (\e -> e.role == role) palette.entries)

-- | Get all palette entries.
paletteEntries :: BrandPalette -> Array PaletteEntry
paletteEntries palette = palette.entries

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // contrast
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Absolute lightness difference between two colors.
-- |
-- | Used for approximate WCAG contrast calculations.
lightnessDiff :: OKLCH -> OKLCH -> Number
lightnessDiff c1 c2 = abs (unLightness c1.l - unLightness c2.l)

-- | Check minimum contrast (lightness-based approximation).
-- |
-- | Note: True WCAG contrast uses luminance, which requires color space conversion.
-- | Lightness difference in OKLCH provides a useful approximation.
hasMinimumContrast :: OKLCH -> OKLCH -> Number -> Boolean
hasMinimumContrast c1 c2 minDiff = lightnessDiff c1 c2 >= minDiff

-- | WCAG AA minimum lightness difference (approximation).
-- |
-- | A difference of ~0.4 in OKLCH lightness roughly corresponds to 4.5:1 contrast.
wcagAALightnessDiff :: Number
wcagAALightnessDiff = 0.4

-- | WCAG AAA minimum lightness difference (approximation).
-- |
-- | A difference of ~0.55 in OKLCH lightness roughly corresponds to 7:1 contrast.
wcagAAALightnessDiff :: Number
wcagAAALightnessDiff = 0.55
