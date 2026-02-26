{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // foundry // extract // spacing
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Spacing
Description : Spacing extraction from scraped content
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Extracts spacing scale from margin and padding values.

== Algorithm

1. Collect all margin and padding values from computed styles
2. Filter to positive values (ignore 0 and auto)
3. Find the GCD-like base unit
4. Detect scale ratio (similar to type scale)

== Design Notes

Spacing systems typically use a base unit (often 4px or 8px) with a
multiplier scale. We detect both the base and the typical multipliers
used.

== Dependencies

Requires: Foundry.Extract.Types
Required by: Foundry.Extract.Compose

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Spacing
  ( -- * Extraction
    extractSpacing
  , SpacingExtractionResult (..)

    -- * Analysis
  , detectBaseUnit
  , detectSpacingScale
  , SpacingAnalysis (..)
  ) where

import Data.List (nub, sort, sortBy)
import Data.Maybe (catMaybes, mapMaybe)
import Data.Ord (comparing)
import Data.Vector (Vector)
import Data.Vector qualified as V

import Foundry.Core.Brand.Spacing 
  ( LengthUnit (..)
  , SpacingScale (..)
  , SpacingValue (..)
  , mkSpacingValue
  )
import Foundry.Extract.Types
  ( ComputedStyle (..)
  , ElementStyles (..)
  , ExtractionWarning (..)
  , ScrapeResult (..)
  )

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Result of spacing extraction
data SpacingExtractionResult = SpacingExtractionResult
  { serSpacing  :: !SpacingScale
    -- ^ Extracted spacing scale
  , serValues   :: ![SpacingValue]
    -- ^ Individual spacing values with inferred units
  , serAnalysis :: !SpacingAnalysis
    -- ^ Analysis details
  , serWarnings :: ![ExtractionWarning]
    -- ^ Extraction warnings
  }
  deriving stock (Eq, Show)

-- | Detailed spacing analysis
data SpacingAnalysis = SpacingAnalysis
  { saBaseUnit   :: !Double
    -- ^ Detected base unit (px)
  , saMultipliers :: ![Int]
    -- ^ Common multipliers found
  , saSamples    :: !Int
    -- ^ Number of spacing values analyzed
  , saConfidence :: !Double
    -- ^ Confidence score [0, 1]
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Extraction
--------------------------------------------------------------------------------

-- | Extract spacing scale from scrape result
extractSpacing :: ScrapeResult -> SpacingExtractionResult
extractSpacing sr =
  let -- Collect all spacing values (raw doubles)
      rawValues = extractSpacingValues (srComputedStyles sr)
      valueList = V.toList rawValues
      
      -- Analyze to find base unit and multipliers
      analysis = analyzeSpacing valueList
      baseUnit = saBaseUnit analysis
      
      -- Build SpacingScale (convert px to rem, assuming 16px base)
      scale = SpacingScale
        { spacingScaleBase = baseUnit / 16
        , spacingScaleRatio = if length (saMultipliers analysis) >= 2
                              then detectRatio (saMultipliers analysis)
                              else 2.0  -- Default to doubling
        }
      
      -- Convert raw values to SpacingValues with inferred units
      -- Sort by frequency to prioritize commonly-used values
      valueCounts = countValues valueList
      sortedByFreq = sortByFrequency valueCounts
      spacingVals = map (\(v, _count) -> toSpacingValue baseUnit v) sortedByFreq
      
      warnings = if saSamples analysis < 5
                 then [WarnNoSpacingScale]
                 else []
  in SpacingExtractionResult scale spacingVals analysis warnings

-- | Count occurrences of each spacing value
countValues :: [Double] -> [(Double, Int)]
countValues values = 
  let grouped = groupByValue (sort values)
  in map (\vs -> (safeHead 0 vs, length vs)) grouped
  where
    -- Group consecutive equal values
    groupByValue :: [Double] -> [[Double]]
    groupByValue [] = []
    groupByValue (x:xs) = 
      let (same, rest) = span (== x) xs
      in (x : same) : groupByValue rest
    
    -- Safe head that returns a default for empty lists
    safeHead :: Double -> [Double] -> Double
    safeHead def [] = def
    safeHead _ (x:_) = x

-- | Extract all margin/padding values from computed styles
extractSpacingValues :: Vector ElementStyles -> Vector Double
extractSpacingValues elements = V.fromList $ nub $ sort $ filter (> 0) allValues
  where
    allValues = V.toList $ V.concatMap extractFromElement elements
    
    extractFromElement es =
      let style = esStyles es
      in V.fromList $ catMaybes
           [ csMarginTop style
           , csMarginRight style
           , csMarginBottom style
           , csMarginLeft style
           , csPaddingTop style
           , csPaddingRight style
           , csPaddingBottom style
           , csPaddingLeft style
           ]

--------------------------------------------------------------------------------
-- Analysis
--------------------------------------------------------------------------------

-- | Analyze spacing values to find base unit and scale
analyzeSpacing :: [Double] -> SpacingAnalysis
analyzeSpacing [] = SpacingAnalysis 8 [1, 2, 4] 0 0.0
analyzeSpacing values =
  let uniqueValues = nub $ sort $ filter (> 0) values
      baseUnit = detectBaseUnit uniqueValues
      multipliers = detectMultipliers baseUnit uniqueValues
      confidence = calculateConfidence baseUnit uniqueValues
  in SpacingAnalysis
       { saBaseUnit = baseUnit
       , saMultipliers = multipliers
       , saSamples = length uniqueValues
       , saConfidence = confidence
       }

-- | Detect the base spacing unit
--
-- Uses a GCD-like approach, looking for common factors.
detectBaseUnit :: [Double] -> Double
detectBaseUnit [] = 8.0  -- Default
detectBaseUnit values =
  let -- Common base units to test
      candidates = [4, 5, 6, 8, 10, 12, 16]
      -- Score each candidate
      scores = map (\b -> (b, scoreBaseUnit b values)) candidates
      -- Pick the best (default to 16 if empty, though this shouldn't happen)
  in case minimumByMay (comparing snd) scores of
       Just (best, _) -> best
       Nothing        -> 16  -- Safe default: standard browser base

-- | Score how well a base unit fits the values
scoreBaseUnit :: Double -> [Double] -> Double
scoreBaseUnit base values =
  let -- For each value, calculate the error when dividing by base
      errors = map (\v -> let ratio = v / base
                              rounded = fromIntegral (round ratio :: Int)
                          in abs (ratio - rounded)) values
  in sum errors

-- | Detect multipliers used with the base unit
detectMultipliers :: Double -> [Double] -> [Int]
detectMultipliers base values =
  let -- Calculate multipliers for each value
      mults = mapMaybe (\v -> let ratio = v / base
                                  rounded = round ratio :: Int
                              in if abs (v - fromIntegral rounded * base) < 0.5
                                 then Just rounded
                                 else Nothing) values
  in sort $ nub mults

-- | Calculate confidence in the detected base unit
calculateConfidence :: Double -> [Double] -> Double
calculateConfidence base values =
  let -- Percentage of values that fit the base unit well
      goodFits = length $ filter fitsWell values
      total = length values
  in if total == 0 then 0 else fromIntegral goodFits / fromIntegral total
  where
    fitsWell v = 
      let ratio = v / base
          rounded = fromIntegral (round ratio :: Int)
      in abs (ratio - rounded) < 0.1

-- | Detect the scale ratio between common spacing values
--
-- SECURITY: Must handle any input safely. Returns valid ratio in [1, 10].
detectRatio :: [Int] -> Double
detectRatio [] = 2.0
detectRatio [_] = 2.0
detectRatio mults =
  let sorted = sort $ filter (> 0) mults  -- Filter out zero/negative
      -- Calculate ratios between consecutive multipliers (using drop 1 for totality)
      -- Only use ratios where denominator > 0
      ratios = [ fromIntegral b / fromIntegral a 
               | (a, b) <- zip sorted (drop 1 sorted)
               , a > 0  -- Prevent division by zero
               ]
      -- Filter out NaN/Infinite ratios and clamp to reasonable range
      validRatios = [ r | r <- ratios
                    , not (isNaN r)
                    , not (isInfinite r)
                    , r > 0
                    , r <= 10  -- Reasonable upper bound
                    ]
      -- Average ratio (geometric mean would be better)
      avgRatio = if null validRatios 
                 then 2.0 
                 else sum validRatios / fromIntegral (length validRatios)
      -- Final clamp to ensure valid output
      finalRatio = if isNaN avgRatio || isInfinite avgRatio || avgRatio <= 0
                   then 2.0
                   else max 1.0 (min 10.0 avgRatio)
  in finalRatio

-- | Detect spacing scale (simplified version for external use)
--
-- SECURITY: Must handle wild inputs (NaN, Infinity, huge/tiny values).
-- Returns Nothing or valid SpacingScale, never NaN/Infinity in fields.
detectSpacingScale :: [Double] -> Maybe SpacingScale
detectSpacingScale values
  | length validValues < 2 = Nothing
  | otherwise =
      let analysis = analyzeSpacing validValues
          base = saBaseUnit analysis / 16
          ratio = detectRatio (saMultipliers analysis)
          -- Ensure outputs are valid
          safeBase = if isNaN base || isInfinite base || base <= 0 
                     then 0.5  -- Default: 8px / 16 = 0.5rem
                     else base
          safeRatio = if isNaN ratio || isInfinite ratio || ratio <= 0
                      then 2.0
                      else ratio
      in Just $ SpacingScale
           { spacingScaleBase = safeBase
           , spacingScaleRatio = safeRatio
           }
  where
    -- Filter out NaN, Infinity, and non-positive values
    validValues = [ v | v <- values
                  , not (isNaN v)
                  , not (isInfinite v)
                  , v > 0
                  ]

-- | Helper to find minimum by comparison (total, returns Maybe)
minimumByMay :: (a -> a -> Ordering) -> [a] -> Maybe a
minimumByMay _ [] = Nothing
minimumByMay cmp (x:xs) = Just $ foldl (\a b -> if cmp a b == LT then a else b) x xs

-- | Sort spacing values by their frequency in usage
-- Uses sortBy for custom comparison
sortByFrequency :: [(Double, Int)] -> [(Double, Int)]
sortByFrequency = sortBy (flip (comparing snd))

-- | Convert base unit to LengthUnit type.
--
-- This preserves the unit type information for downstream processing.
-- Common base units map to their typical CSS representation:
--   - 4px, 8px bases → Px (pixel-based grids)
--   - 16px base → Rem (rem-based systems, 1rem = 16px default)
baseToLengthUnit :: Double -> LengthUnit
baseToLengthUnit base
  | base == 4  = Px
  | base == 8  = Px
  | base == 16 = Rem
  | otherwise  = Px  -- Default to pixels

-- | Convert a detected spacing value to a SpacingValue with inferred unit.
--
-- Uses the base unit detection to determine whether the spacing system
-- is pixel-based or rem-based.
toSpacingValue :: Double -> Double -> SpacingValue
toSpacingValue base value =
  let unit = baseToLengthUnit base
  in mkSpacingValue value unit
