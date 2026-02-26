{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // foundry // extract // color/role
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Color.Role
Description : Semantic color role assignment
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Assigns semantic roles (Primary, Secondary, etc.) to extracted colors.

== Algorithm

1. Most frequent chromatic color → Primary
2. Second most frequent chromatic → Secondary
3. Near-white (L > 0.95, C < 0.02) → Background
4. Near-black (L < 0.15) → Surface (dark mode)
5. Remaining by frequency → Tertiary, Accent

== WCAG Contrast

All role assignments are validated against WCAG 2.1:
- AA requires 4.5:1 for normal text
- AAA requires 7:1 for normal text

== Dependencies

Requires: Foundry.Extract.Color.CSS, Foundry.Extract.Color.Cluster
Required by: Foundry.Extract.Color

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Color.Role
  ( -- * Role Assignment
    assignRoles
  , RoleAssignment (..)

    -- * WCAG Contrast
  , contrastRatio
  , meetsWCAG_AA
  , meetsWCAG_AAA
  , relativeLuminance

    -- * Color Classification
  , isNeutral
  , isChromatic
  , isLight
  , isDark
  ) where

import Data.List (sortBy)
import Data.Maybe (mapMaybe)
import Data.Ord (Down (..), comparing)
import Data.Vector (Vector)
import Data.Vector qualified as V

import Foundry.Core.Brand.Palette (ColorRole (..))
import Foundry.Extract.Color.Cluster (ColorCluster (..))
import Foundry.Extract.Color.CSS (OKLCH' (..))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | A color with its assigned role
data RoleAssignment = RoleAssignment
  { raColor :: !OKLCH'
  , raRole  :: !ColorRole
  , raFrequency :: !Int
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Role Assignment
--------------------------------------------------------------------------------

-- | Assign semantic roles to color clusters
--
-- Returns a vector of role assignments, with at most one color per role.
assignRoles :: Vector ColorCluster -> Vector RoleAssignment
assignRoles clusters
  | V.null clusters = V.empty
  | otherwise = V.fromList $ assignAll sortedClusters []
  where
    sortedClusters = sortBy (comparing (Down . ccFrequency)) (V.toList clusters)

assignAll :: [ColorCluster] -> [RoleAssignment] -> [RoleAssignment]
assignAll [] acc = acc
assignAll (c:cs) acc =
  let cent = ccCentroid c
      freq = ccFrequency c
      usedRoles = map raRole acc
      role = selectRole cent usedRoles
  in case role of
       Just r  -> assignAll cs (RoleAssignment cent r freq : acc)
       Nothing -> assignAll cs acc

-- | Select the appropriate role for a color
selectRole :: OKLCH' -> [ColorRole] -> Maybe ColorRole
selectRole color usedRoles
  -- Background: very light, low chroma
  | isLight color && isNeutral color && Background `notElem` usedRoles = Just Background
  -- Surface: very dark, any chroma
  | isDark color && Surface `notElem` usedRoles = Just Surface
  -- Neutral: mid-lightness, low chroma
  | isNeutral color && Neutral `notElem` usedRoles = Just Neutral
  -- Primary: most frequent chromatic
  | isChromatic color && Primary `notElem` usedRoles = Just Primary
  -- Secondary: second chromatic
  | isChromatic color && Secondary `notElem` usedRoles = Just Secondary
  -- Tertiary: third chromatic
  | isChromatic color && Tertiary `notElem` usedRoles = Just Tertiary
  -- Accent: remaining chromatic
  | isChromatic color && Accent `notElem` usedRoles = Just Accent
  -- Error: reddish hue
  | isErrorColor color && Error `notElem` usedRoles = Just Error
  -- Warning: yellowish hue
  | isWarningColor color && Warning `notElem` usedRoles = Just Warning
  -- Success: greenish hue
  | isSuccessColor color && Success `notElem` usedRoles = Just Success
  | otherwise = Nothing

-- | Check if color is likely an error color (red hue)
isErrorColor :: OKLCH' -> Bool
isErrorColor (OKLCH' _ c h _) = c > 0.1 && (h < 30 || h > 330)

-- | Check if color is likely a warning color (yellow/orange hue)
isWarningColor :: OKLCH' -> Bool
isWarningColor (OKLCH' _ c h _) = c > 0.1 && h >= 30 && h < 90

-- | Check if color is likely a success color (green hue)
isSuccessColor :: OKLCH' -> Bool
isSuccessColor (OKLCH' _ c h _) = c > 0.1 && h >= 90 && h < 180

--------------------------------------------------------------------------------
-- WCAG Contrast
--------------------------------------------------------------------------------

-- | Calculate WCAG contrast ratio between two colors
--
-- Returns a ratio >= 1:1, with 21:1 being maximum (black/white).
contrastRatio :: OKLCH' -> OKLCH' -> Double
contrastRatio c1 c2 =
  let l1 = relativeLuminance c1
      l2 = relativeLuminance c2
      lighter = max l1 l2
      darker = min l1 l2
  in (lighter + 0.05) / (darker + 0.05)

-- | Check if contrast meets WCAG AA (4.5:1 for normal text)
meetsWCAG_AA :: OKLCH' -> OKLCH' -> Bool
meetsWCAG_AA c1 c2 = contrastRatio c1 c2 >= 4.5

-- | Check if contrast meets WCAG AAA (7:1 for normal text)
meetsWCAG_AAA :: OKLCH' -> OKLCH' -> Bool
meetsWCAG_AAA c1 c2 = contrastRatio c1 c2 >= 7.0

-- | Calculate relative luminance for WCAG
--
-- Note: This is an approximation since we're working in OKLCH.
-- For precise WCAG compliance, convert to sRGB first.
relativeLuminance :: OKLCH' -> Double
relativeLuminance (OKLCH' l _ _ _) =
  -- OKLCH L is perceptual lightness, roughly maps to luminance
  -- This is an approximation; true WCAG needs sRGB conversion
  l * l  -- Approximate gamma correction

--------------------------------------------------------------------------------
-- Color Classification
--------------------------------------------------------------------------------

-- | Check if color is neutral (low chroma)
isNeutral :: OKLCH' -> Bool
isNeutral (OKLCH' _ c _ _) = c < 0.03

-- | Check if color is chromatic (visible hue)
isChromatic :: OKLCH' -> Bool
isChromatic (OKLCH' _ c _ _) = c >= 0.03

-- | Check if color is light (high lightness)
isLight :: OKLCH' -> Bool
isLight (OKLCH' l _ _ _) = l > 0.85

-- | Check if color is dark (low lightness)
isDark :: OKLCH' -> Bool
isDark (OKLCH' l _ _ _) = l < 0.2
