{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                             // foundry // extract // color/cluster
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Color.Cluster
Description : OKLCH color clustering
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Clusters colors by perceptual similarity in OKLCH space.

== Algorithm

Uses k-means clustering with OKLCH distance metric:
  ΔE = sqrt(ΔL² + ΔC² + ΔH²)

Where ΔH is computed as angular distance on the hue circle.

== Design Notes

The OKLCH color space is perceptually uniform, meaning equal numerical
distances correspond to equal perceived differences. This makes k-means
clustering meaningful for finding distinct brand colors.

== Dependencies

Requires: Foundry.Extract.Color.CSS
Required by: Foundry.Extract.Color

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Color.Cluster
  ( -- * Types
    ColorCluster (..)
  , ClusterResult (..)

    -- * Clustering
  , clusterColors
  , oklchDistance

    -- * Analysis
  , findDominantColors
  , filterByFrequency
  ) where

import Data.List (sortBy)
import Data.Ord (Down (..), comparing)
import Data.Vector (Vector)
import Data.Vector qualified as V

import Foundry.Extract.Color.CSS (OKLCH' (..))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | A cluster of similar colors
data ColorCluster = ColorCluster
  { ccCentroid  :: !OKLCH'
    -- ^ Cluster centroid (average color)
  , ccMembers   :: !(Vector OKLCH')
    -- ^ Colors in this cluster
  , ccFrequency :: !Int
    -- ^ Total occurrence count
  }
  deriving stock (Eq, Show)

-- | Result of clustering operation
data ClusterResult = ClusterResult
  { crClusters    :: !(Vector ColorCluster)
    -- ^ Resulting clusters, sorted by frequency
  , crIterations  :: !Int
    -- ^ Number of k-means iterations
  , crConverged   :: !Bool
    -- ^ Whether algorithm converged
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Clustering
--------------------------------------------------------------------------------

-- | Cluster colors using k-means in OKLCH space
--
-- @clusterColors k maxIter colors@ clusters @colors@ into @k@ groups
-- using at most @maxIter@ iterations.
clusterColors 
  :: Int                       -- ^ Number of clusters (k)
  -> Int                       -- ^ Maximum iterations
  -> Vector (OKLCH', Int)      -- ^ Colors with occurrence counts
  -> ClusterResult
clusterColors k maxIter colorsWithFreq
  | V.null colorsWithFreq = ClusterResult V.empty 0 True
  | k <= 0 = ClusterResult V.empty 0 True
  | otherwise = 
      let colors = V.map fst colorsWithFreq
          freqs = V.map snd colorsWithFreq
          initialCentroids = selectInitialCentroids k colors
          (finalCentroids, iters, converged) = kmeans maxIter 0.001 initialCentroids colors freqs
          clusters = buildClusters finalCentroids colors freqs
      in ClusterResult clusters iters converged

-- | Select initial centroids using k-means++ strategy
selectInitialCentroids :: Int -> Vector OKLCH' -> Vector OKLCH'
selectInitialCentroids k colors
  | V.null colors = V.empty
  | k <= 0 = V.empty
  | otherwise = go (V.singleton firstCentroid) (k - 1)
  where
    firstCentroid = V.unsafeIndex colors 0
    
    go centroids remaining
      | remaining <= 0 = centroids
      | V.length centroids >= V.length colors = centroids
      | otherwise =
          let -- Find the color furthest from all centroids
              distances = V.map (minDistToCentroids centroids) colors
              maxIdx = V.maxIndex distances
              newCentroid = V.unsafeIndex colors maxIdx
          in go (V.snoc centroids newCentroid) (remaining - 1)
    
    minDistToCentroids cents c = V.minimum (V.map (oklchDistance c) cents)

-- | K-means iteration
kmeans 
  :: Int                  -- ^ Max iterations
  -> Double               -- ^ Convergence threshold
  -> Vector OKLCH'        -- ^ Centroids
  -> Vector OKLCH'        -- ^ Colors
  -> Vector Int           -- ^ Frequencies
  -> (Vector OKLCH', Int, Bool)
kmeans maxIter threshold centroids colors freqs = go centroids 0
  where
    go cents iter
      | iter >= maxIter = (cents, iter, False)
      | otherwise =
          let assignments = V.map (assignToCluster cents) colors
              newCents = computeCentroids cents assignments colors freqs
              maxDelta = maxCentroidDelta cents newCents
          in if maxDelta < threshold
             then (newCents, iter + 1, True)
             else go newCents (iter + 1)

-- | Assign a color to the nearest centroid
assignToCluster :: Vector OKLCH' -> OKLCH' -> Int
assignToCluster centroids color = V.minIndex distances
  where
    distances = V.map (oklchDistance color) centroids

-- | Compute new centroids from assignments
computeCentroids 
  :: Vector OKLCH'   -- ^ Old centroids (for count)
  -> Vector Int      -- ^ Cluster assignments
  -> Vector OKLCH'   -- ^ Colors
  -> Vector Int      -- ^ Frequencies
  -> Vector OKLCH'
computeCentroids oldCentroids assignments colors freqs =
  V.generate (V.length oldCentroids) computeOne
  where
    computeOne clusterIdx =
      let indices = V.findIndices (== clusterIdx) assignments
          memberColors = V.map (V.unsafeIndex colors) indices
          memberFreqs = V.map (V.unsafeIndex freqs) indices
      in if V.null memberColors
         then V.unsafeIndex oldCentroids clusterIdx  -- Keep old if empty
         else weightedCentroid memberColors memberFreqs

-- | Compute weighted centroid of colors
weightedCentroid :: Vector OKLCH' -> Vector Int -> OKLCH'
weightedCentroid colors freqs =
  let totalWeight = fromIntegral (V.sum freqs) :: Double
      weighted = V.zipWith weightColor colors freqs
      sumL = V.sum (V.map (\(l, _, _, _) -> l) weighted)
      sumC = V.sum (V.map (\(_, c, _, _) -> c) weighted)
      -- Hue needs circular mean
      sumSin = V.sum (V.map (\(_, _, s, _) -> s) weighted)
      sumCos = V.sum (V.map (\(_, _, _, c) -> c) weighted)
      avgH = atan2 sumSin sumCos * 180 / pi
      avgH' = if avgH < 0 then avgH + 360 else avgH
  in OKLCH' (sumL / totalWeight) (sumC / totalWeight) avgH' 1.0
  where
    weightColor (OKLCH' l c h _) freq =
      let w = fromIntegral freq
          hRad = h * pi / 180
      in (l * w, c * w, sin hRad * w, cos hRad * w)

-- | Maximum change between old and new centroids
maxCentroidDelta :: Vector OKLCH' -> Vector OKLCH' -> Double
maxCentroidDelta old new
  | V.length old /= V.length new = 1.0  -- Force continue
  | V.null old = 0.0
  | otherwise = V.maximum (V.zipWith oklchDistance old new)

-- | Build cluster structures from assignments
buildClusters 
  :: Vector OKLCH'   -- ^ Centroids
  -> Vector OKLCH'   -- ^ Colors
  -> Vector Int      -- ^ Frequencies
  -> Vector ColorCluster
buildClusters centroids colors freqs =
  let assignments = V.map (assignToCluster centroids) colors
      clusters = V.imap (buildCluster assignments colors freqs) centroids
      sorted = V.fromList $ sortBy (comparing (Down . ccFrequency)) (V.toList clusters)
  in sorted
  where
    buildCluster assignments' colors' freqs' clusterIdx centroid =
      let indices = V.findIndices (== clusterIdx) assignments'
          members = V.map (V.unsafeIndex colors') indices
          freq = V.sum (V.map (V.unsafeIndex freqs') indices)
      in ColorCluster centroid members freq

--------------------------------------------------------------------------------
-- Distance Metric
--------------------------------------------------------------------------------

-- | Perceptual distance between two OKLCH colors
--
-- Uses the standard OKLCH delta E formula with hue angle adjustment.
oklchDistance :: OKLCH' -> OKLCH' -> Double
oklchDistance (OKLCH' l1 c1 h1 _) (OKLCH' l2 c2 h2 _) =
  let dL = l1 - l2
      dC = c1 - c2
      dH = hueDistance h1 h2
  in sqrt (dL * dL + dC * dC + dH * dH)

-- | Angular distance between two hues
hueDistance :: Double -> Double -> Double
hueDistance h1 h2 =
  let diff = abs (h1 - h2)
  in min diff (360 - diff) / 180  -- Normalize to [0, 1]

--------------------------------------------------------------------------------
-- Analysis
--------------------------------------------------------------------------------

-- | Find dominant colors by frequency
findDominantColors 
  :: Int                     -- ^ Number of dominant colors to find
  -> Vector (OKLCH', Int)    -- ^ Colors with frequencies
  -> Vector OKLCH'
findDominantColors n colorsWithFreq =
  let sorted = V.fromList $ sortBy (comparing (Down . snd)) (V.toList colorsWithFreq)
  in V.map fst (V.take n sorted)

-- | Filter colors by minimum frequency
filterByFrequency 
  :: Int                     -- ^ Minimum frequency
  -> Vector (OKLCH', Int)    -- ^ Colors with frequencies
  -> Vector (OKLCH', Int)
filterByFrequency minFreq = V.filter (\(_, f) -> f >= minFreq)
