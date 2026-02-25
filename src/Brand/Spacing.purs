-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // brand // spacing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brand spacing scale atoms and molecules.
-- |
-- | STATUS: PROVEN (Hydrogen.Schema.Brand.Spacing)
-- |
-- | Invariants:
-- |   base_positive: All spacing units > 0 (PROVEN)
-- |   scale_gt_one: Geometric ratio > 1 (PROVEN)
-- |   monotonic: Higher levels = larger spacing (PROVEN)

module Hydrogen.Schema.Brand.Spacing
  ( -- * Spacing Unit
    SpacingUnit
  , mkSpacingUnit
  , unSpacingUnit
  , px4
  , px8
  , px16
  
  -- * Spacing Scale (Geometric)
  , SpacingRatio
  , mkSpacingRatio
  , unSpacingRatio
  , SpacingScale
  , mkSpacingScale
  , scaleAt
  , base4Scale
  , base8Scale
  
  -- * Linear Spacing
  , LinearSpacing
  , mkLinearSpacing
  , linearAt
  , grid4
  , grid8
  
  -- * Brand Spacing
  , SpacingSystem
      ( Geometric
      , Linear
      )
  , BrandSpacing
  , defaultSpacing
  , getSpacing
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (>)
  , (+)
  , (*)
  , (<>)
  , compare
  , otherwise
  , show
  )

import Data.Int (toNumber)
import Data.Number (pow)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // spacing unit
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spacing unit atom (in pixels, positive).
-- |
-- | Bounded: Must be > 0. Values <= 0 are set to 4.0 (safe default).
newtype SpacingUnit = SpacingUnit Number

derive instance eqSpacingUnit :: Eq SpacingUnit
derive instance ordSpacingUnit :: Ord SpacingUnit

instance showSpacingUnit :: Show SpacingUnit where
  show (SpacingUnit px) = "SpacingUnit(" <> show px <> "px)"

-- | Smart constructor with validation.
mkSpacingUnit :: Number -> SpacingUnit
mkSpacingUnit n = if n > 0.0 then SpacingUnit n else SpacingUnit 4.0

-- | Unwrap spacing unit to number (pixels).
unSpacingUnit :: SpacingUnit -> Number
unSpacingUnit (SpacingUnit px) = px

-- | Common spacing: 4px
px4 :: SpacingUnit
px4 = SpacingUnit 4.0

-- | Common spacing: 8px
px8 :: SpacingUnit
px8 = SpacingUnit 8.0

-- | Common spacing: 16px
px16 :: SpacingUnit
px16 = SpacingUnit 16.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // spacing ratio
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spacing scale ratio atom.
-- |
-- | Bounded: Must be > 1.0. Values <= 1.0 are set to 2.0.
newtype SpacingRatio = SpacingRatio Number

derive instance eqSpacingRatio :: Eq SpacingRatio
derive instance ordSpacingRatio :: Ord SpacingRatio

instance showSpacingRatio :: Show SpacingRatio where
  show (SpacingRatio r) = "SpacingRatio(" <> show r <> ")"

-- | Smart constructor with validation.
mkSpacingRatio :: Number -> SpacingRatio
mkSpacingRatio r = if r > 1.0 then SpacingRatio r else SpacingRatio 2.0

-- | Unwrap spacing ratio to number.
unSpacingRatio :: SpacingRatio -> Number
unSpacingRatio (SpacingRatio r) = r

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // spacing scale
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Geometric spacing scale molecule.
-- |
-- | Produces spacing values as: base * ratio^level
-- |
-- | Examples:
-- |   base 4px, ratio 2: 4, 8, 16, 32, 64...
-- |   base 8px, ratio 1.5: 8, 12, 18, 27...
type SpacingScale =
  { base :: SpacingUnit
  , ratio :: SpacingRatio
  }

-- | Create a spacing scale.
mkSpacingScale :: Number -> Number -> SpacingScale
mkSpacingScale base ratio =
  { base: mkSpacingUnit base
  , ratio: mkSpacingRatio ratio
  }

-- | Get spacing at level (geometric).
-- |
-- | Level 0 = base
-- | Level 1 = base * ratio
-- | Level 2 = base * ratio^2
-- | etc.
scaleAt :: SpacingScale -> Int -> SpacingUnit
scaleAt scale level =
  let 
    SpacingRatio r = scale.ratio
    SpacingUnit b = scale.base
  in 
    SpacingUnit (b * pow r (toNumber level))

-- | Common scale: 4px base, 2x ratio
base4Scale :: SpacingScale
base4Scale = mkSpacingScale 4.0 2.0

-- | Common scale: 8px base, 1.5x ratio
base8Scale :: SpacingScale
base8Scale = mkSpacingScale 8.0 1.5

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // linear spacing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Linear spacing molecule (base + n * step).
-- |
-- | Produces spacing values as: base + level * step
-- |
-- | Examples:
-- |   base 4px, step 4px: 4, 8, 12, 16, 20...
-- |   base 8px, step 8px: 8, 16, 24, 32...
type LinearSpacing =
  { base :: SpacingUnit
  , step :: SpacingUnit
  }

-- | Create a linear spacing system.
mkLinearSpacing :: Number -> Number -> LinearSpacing
mkLinearSpacing base step =
  { base: mkSpacingUnit base
  , step: mkSpacingUnit step
  }

-- | Get spacing at level (linear).
-- |
-- | Level 0 = base
-- | Level 1 = base + step
-- | Level 2 = base + 2*step
-- | etc.
linearAt :: LinearSpacing -> Int -> SpacingUnit
linearAt lin n =
  let 
    SpacingUnit b = lin.base
    SpacingUnit s = lin.step
  in 
    SpacingUnit (b + toNumber n * s)

-- | Common grid: 4px base and step
grid4 :: LinearSpacing
grid4 = mkLinearSpacing 4.0 4.0

-- | Common grid: 8px base and step
grid8 :: LinearSpacing
grid8 = mkLinearSpacing 8.0 8.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // spacing system
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spacing system sum type.
-- |
-- | A brand can use either geometric or linear spacing.
data SpacingSystem
  = Geometric SpacingScale
  | Linear LinearSpacing

derive instance eqSpacingSystem :: Eq SpacingSystem

instance showSpacingSystem :: Show SpacingSystem where
  show (Geometric scale) = "Geometric(" <> show scale.base <> ", " <> show scale.ratio <> ")"
  show (Linear lin) = "Linear(" <> show lin.base <> ", " <> show lin.step <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // brand spacing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Brand spacing compound.
-- |
-- | Wraps a spacing system (geometric or linear).
type BrandSpacing = 
  { system :: SpacingSystem
  }

-- | Default spacing (4px linear grid).
defaultSpacing :: BrandSpacing
defaultSpacing = { system: Linear grid4 }

-- | Get spacing at level.
-- |
-- | Dispatches to geometric or linear based on system type.
getSpacing :: BrandSpacing -> Int -> SpacingUnit
getSpacing spacing level =
  case spacing.system of
    Geometric scale -> scaleAt scale level
    Linear lin -> linearAt lin level
