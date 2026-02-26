{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                           // foundry // extract // typography/scale
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Typography.Scale
Description : Type scale detection
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Detects the typographic scale ratio from observed font sizes.

== Algorithm

Uses geometric regression to find the scale ratio that best fits the
observed font sizes. Common ratios:

* 1.067 - Minor Second
* 1.125 - Major Second
* 1.200 - Minor Third
* 1.250 - Major Third (most common)
* 1.333 - Perfect Fourth
* 1.414 - Augmented Fourth
* 1.500 - Perfect Fifth
* 1.618 - Golden Ratio

== Dependencies

Requires: (none - pure math)
Required by: Foundry.Extract.Typography

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Typography.Scale
  ( -- * Types
    DetectedScale (..)
  , KnownRatio (..)

    -- * Detection
  , detectScale
  , detectScaleFromSizes

    -- * Analysis
  , fitScaleRatio
  , closestKnownRatio
  , scaleError
  ) where

import Data.List (minimumBy, nub, sort)
import Data.Ord (comparing)
import Data.Vector (Vector)
import Data.Vector qualified as V

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Result of scale detection
data DetectedScale = DetectedScale
  { dsBaseSize     :: !Double
    -- ^ Detected base font size (rem)
  , dsRatio        :: !Double
    -- ^ Detected scale ratio
  , dsKnownRatio   :: !(Maybe KnownRatio)
    -- ^ Closest known ratio (if within tolerance)
  , dsConfidence   :: !Double
    -- ^ Confidence score [0, 1]
  , dsSamples      :: !Int
    -- ^ Number of samples used
  }
  deriving stock (Eq, Show)

-- | Known typographic scale ratios
data KnownRatio
  = MinorSecond      -- ^ 1.067 (15:16)
  | MajorSecond      -- ^ 1.125 (8:9)
  | MinorThird       -- ^ 1.200 (5:6)
  | MajorThird       -- ^ 1.250 (4:5)
  | PerfectFourth    -- ^ 1.333 (3:4)
  | AugmentedFourth  -- ^ 1.414 (√2)
  | PerfectFifth     -- ^ 1.500 (2:3)
  | GoldenRatio      -- ^ 1.618 (φ)
  deriving stock (Eq, Ord, Show, Enum, Bounded)

--------------------------------------------------------------------------------
-- Detection
--------------------------------------------------------------------------------

-- | Detect type scale from font sizes (in px)
detectScale :: Vector Double -> Maybe DetectedScale
detectScale sizes
  | V.length sizes < 2 = Nothing
  | otherwise = detectScaleFromSizes (V.toList sizes)

-- | Detect scale from a list of font sizes
detectScaleFromSizes :: [Double] -> Maybe DetectedScale
detectScaleFromSizes sizes
  | length uniqueSizes < 2 = Nothing
  | otherwise =
      let sorted = sort uniqueSizes
          (base, ratio, confidence) = fitScaleRatio sorted
          mKnown = closestKnownRatio ratio
      in Just $ DetectedScale
           { dsBaseSize = base
           , dsRatio = ratio
           , dsKnownRatio = mKnown
           , dsConfidence = confidence
           , dsSamples = length uniqueSizes
           }
  where
    uniqueSizes = nub $ filter (> 0) sizes

-- | Fit a scale ratio to a list of sorted font sizes
--
-- Returns (baseSize, ratio, confidence)
fitScaleRatio :: [Double] -> (Double, Double, Double)
fitScaleRatio [] = (1.0, 1.25, 0.0)
fitScaleRatio [x] = (x, 1.25, 0.5)
fitScaleRatio sizes =
  let -- Try each known ratio and find best fit
      candidates = map (\kr -> fitWithRatio sizes (knownRatioValue kr)) [minBound..maxBound]
      -- Also try a custom fit using geometric regression
      customFit = geometricRegression sizes
      allFits = customFit : candidates
      (base, ratio, err) = minimumBy (comparing (\(_, _, e) -> e)) allFits
      -- Convert error to confidence (lower error = higher confidence)
      confidence = max 0 (1 - err / (maximum sizes - minimum sizes))
  in (base, ratio, confidence)

-- | Fit sizes using a specific ratio
fitWithRatio :: [Double] -> Double -> (Double, Double, Double)
fitWithRatio sizes ratio =
  let -- Find the base size that minimizes error
      minSize = minimum sizes
      maxSize = maximum sizes
      -- Base size is likely the smallest or a common size
      candidateBases = [minSize, minSize / ratio, minSize / (ratio * ratio)]
      errors = map (\b -> (b, ratio, totalError b ratio sizes)) candidateBases
  in minimumBy (comparing (\(_, _, e) -> e)) errors

-- | Calculate total error for a base/ratio pair
totalError :: Double -> Double -> [Double] -> Double
totalError base ratio sizes =
  sum $ map (sizeError base ratio) sizes

-- | Error for a single size given base and ratio
sizeError :: Double -> Double -> Double -> Double
sizeError base ratio size =
  let -- Find the closest scale step
      logRatio = log ratio
      step = round (log (size / base) / logRatio) :: Int
      expected = base * (ratio ^^ step)
  in abs (size - expected)

-- | Geometric regression to find optimal ratio
geometricRegression :: [Double] -> (Double, Double, Double)
geometricRegression sizes =
  let sorted = sort sizes
      base = Prelude.head sorted
      -- Calculate ratios between consecutive sizes
      ratios = zipWith (/) (Prelude.tail sorted) (Prelude.init sorted)
      avgRatio = if null ratios then 1.25 else exp (sum (map log ratios) / fromIntegral (length ratios))
      err = totalError base avgRatio sorted
  in (base, avgRatio, err)

--------------------------------------------------------------------------------
-- Analysis
--------------------------------------------------------------------------------

-- | Find the closest known ratio within tolerance
closestKnownRatio :: Double -> Maybe KnownRatio
closestKnownRatio ratio =
  let tolerance = 0.05
      candidates = [(kr, abs (knownRatioValue kr - ratio)) | kr <- [minBound..maxBound]]
      (closest, diff) = minimumBy (comparing snd) candidates
  in if diff <= tolerance then Just closest else Nothing

-- | Get the numeric value of a known ratio
knownRatioValue :: KnownRatio -> Double
knownRatioValue = \case
  MinorSecond     -> 1.067
  MajorSecond     -> 1.125
  MinorThird      -> 1.200
  MajorThird      -> 1.250
  PerfectFourth   -> 1.333
  AugmentedFourth -> 1.414
  PerfectFifth    -> 1.500
  GoldenRatio     -> 1.618

-- | Calculate the error between expected and actual scales
scaleError :: Double -> Double -> [Double] -> Double
scaleError = totalError
