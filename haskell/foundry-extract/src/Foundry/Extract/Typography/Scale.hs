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
--
-- SECURITY: Must handle wild inputs (NaN, Infinity, huge/tiny values).
-- Returns Nothing or valid DetectedScale, never NaN/Infinity in fields.
detectScaleFromSizes :: [Double] -> Maybe DetectedScale
detectScaleFromSizes sizes
  | length uniqueSizes < 2 = Nothing
  | otherwise =
      let sorted = sort uniqueSizes
          (base, ratio, confidence) = fitScaleRatio sorted
          mKnown = closestKnownRatio ratio
          -- Sanitize outputs
          safeBase = sanitizePositive base 16.0
          safeRatio = sanitizePositive ratio 1.25
          safeConf = max 0 (min 1 (sanitize confidence))
      in Just $ DetectedScale
           { dsBaseSize = safeBase
           , dsRatio = safeRatio
           , dsKnownRatio = mKnown
           , dsConfidence = safeConf
           , dsSamples = length uniqueSizes
           }
  where
    -- Filter out NaN, Infinity, non-positive, and extreme values
    uniqueSizes = nub $ filter isValidSize sizes
    isValidSize x = not (isNaN x) 
                 && not (isInfinite x) 
                 && x > 0 
                 && x < 1e6  -- Reasonable upper bound for font size
    sanitize x = if isNaN x || isInfinite x then 0 else x
    sanitizePositive x def = if isNaN x || isInfinite x || x <= 0 then def else x

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
--
-- SECURITY: Returns finite error value, never NaN/Infinity
totalError :: Double -> Double -> [Double] -> Double
totalError base ratio sizes =
  let errs = map (sizeError base ratio) sizes
      total = sum errs
  in if isNaN total || isInfinite total then 1e10 else total

-- | Error for a single size given base and ratio
--
-- SECURITY: Handles edge cases (log of <=0, division by zero, negative exponents)
sizeError :: Double -> Double -> Double -> Double
sizeError base ratio size
  | base <= 0 || ratio <= 1 || size <= 0 = 1e10  -- Invalid inputs
  | otherwise =
      let logRatio = log ratio
          logSizeBase = log (size / base)
          -- Guard against division by very small logRatio
          step = if abs logRatio < 1e-10 
                 then 0 
                 else round (logSizeBase / logRatio) :: Int
          -- Use ** instead of ^^ to handle negative exponents safely
          expected = base * (ratio ** fromIntegral step)
          err = abs (size - expected)
      in if isNaN err || isInfinite err then 1e10 else err

-- | Geometric regression to find optimal ratio
--
-- SECURITY: Handles edge cases that could produce NaN/Infinity
geometricRegression :: [Double] -> (Double, Double, Double)
geometricRegression sizes =
  let sorted = sort $ filter (> 0) sizes  -- Ensure positive
      base = case sorted of
               []    -> 16.0
               (x:_) -> x
      -- Calculate ratios between consecutive sizes, filtering invalid
      ratios = [ b / a 
               | (a, b) <- zip sorted (drop 1 sorted)
               , a > 0
               , b > 0
               , let r = b / a
               , not (isNaN r)
               , not (isInfinite r)
               , r > 0
               ]
      -- Safe log with fallback
      safeLogRatios = [ log r | r <- ratios, r > 0 ]
      avgRatio = if null safeLogRatios 
                 then 1.25 
                 else let avg = exp (sum safeLogRatios / fromIntegral (length safeLogRatios))
                      in if isNaN avg || isInfinite avg || avg <= 0 then 1.25 else avg
      err = totalError base avgRatio sorted
      safeErr = if isNaN err || isInfinite err then 1e10 else err
  in (base, avgRatio, safeErr)

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
