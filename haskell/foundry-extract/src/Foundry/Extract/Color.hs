{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // foundry // extract // color
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Color
Description : Color extraction from scraped content
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Extracts brand palette from CSS and computed styles.

== Pipeline

1. Parse all CSS color values from stylesheets and computed styles
2. Convert to OKLCH for perceptual uniformity
3. Cluster similar colors using k-means
4. Assign semantic roles based on frequency and properties
5. Validate WCAG contrast requirements

== Dependencies

Requires: Foundry.Extract.Types, Foundry.Extract.Color.*
Required by: Foundry.Extract.Compose

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Color
  ( -- * Extraction
    extractPalette
  , ColorExtractionResult (..)

    -- * Accessors
  , extractOKLCH

    -- * Re-exports
  , module Foundry.Extract.Color.CSS
  , module Foundry.Extract.Color.Cluster
  , module Foundry.Extract.Color.Role
  ) where

-- Note: foldl' is re-exported from Prelude in GHC 9.12+
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as V

import Foundry.Core.Brand.Palette (BrandColor (..), BrandPalette (..), ColorRole (..), OKLCH (..), mkOKLCH)
import Foundry.Extract.Color.CSS
import Foundry.Extract.Color.Cluster
import Foundry.Extract.Color.Role
import Foundry.Extract.Types
  ( CSSProperty (..)
  , CSSRule (..)
  , CSSStylesheet (..)
  , CSSValue (..)
  , ComputedStyle (..)
  , ElementStyles (..)
  , ExtractionError (..)
  , ExtractionWarning (..)
  , ScrapeResult (..)
  )

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Result of color extraction
data ColorExtractionResult = ColorExtractionResult
  { cerPalette  :: !BrandPalette
    -- ^ Extracted brand palette
  , cerClusters :: !(Vector ColorCluster)
    -- ^ Color clusters (for debugging/visualization)
  , cerWarnings :: ![ExtractionWarning]
    -- ^ Extraction warnings
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Extraction
--------------------------------------------------------------------------------

-- | Extract brand palette from scrape result
extractPalette :: ScrapeResult -> Either ExtractionError ColorExtractionResult
extractPalette sr = do
  -- Collect all colors from CSS and computed styles
  let cssColors = extractCSSColors (srStylesheets sr)
      computedColors = extractComputedColors (srComputedStyles sr)
      allColors = mergeColorMaps cssColors computedColors
  
  -- Check we have colors to work with
  if Map.null allColors
    then Left ErrNoColors
    else Right $ processColors allColors

-- | Extract colors from CSS stylesheets
extractCSSColors :: Vector CSSStylesheet -> Map OKLCH' Int
extractCSSColors sheets = V.foldl' processSheet Map.empty sheets
  where
    processSheet acc sheet = V.foldl' processRule acc (cssRules sheet)
    processRule acc rule = V.foldl' processProp acc (cssProperties rule)
    processProp acc prop = case cssPropValue prop of
      CSSColor colorText -> 
        case parseColorText colorText of
          Just pc -> Map.insertWith (+) (toOKLCH' pc) 1 acc
          Nothing -> acc
      _ -> acc

-- | Extract colors from computed styles
extractComputedColors :: Vector ElementStyles -> Map OKLCH' Int
extractComputedColors elements = V.foldl' processElement Map.empty elements
  where
    processElement acc es =
      let style = esStyles es
          colors = mapMaybe parseAndConvert
            [ csColor style
            , csBackgroundColor style
            ]
      in foldl' (\m c -> Map.insertWith (+) c 1 m) acc colors
    
    parseAndConvert :: Maybe Text -> Maybe OKLCH'
    parseAndConvert Nothing = Nothing
    parseAndConvert (Just t) = toOKLCH' <$> parseColorText t

-- | Convert ParsedColor to internal OKLCH'
toOKLCH' :: ParsedColor -> OKLCH'
toOKLCH' = \case
  PCHex rgb     -> rgbToOKLCH rgb
  PCRGB rgb     -> rgbToOKLCH rgb
  PCHSL hsl     -> hslToOKLCH hsl
  PCOKLCH oklch -> oklch
  PCNamed _ rgb -> rgbToOKLCH rgb

-- | Merge two color frequency maps
mergeColorMaps :: Map OKLCH' Int -> Map OKLCH' Int -> Map OKLCH' Int
mergeColorMaps = Map.unionWith (+)

-- | Process collected colors into a palette
processColors :: Map OKLCH' Int -> ColorExtractionResult
processColors colorMap =
  let -- Convert to vector for clustering
      colorList = Map.toList colorMap
      colorsWithFreq = V.fromList colorList
      
      -- Cluster colors (aim for 6-10 clusters)
      clusterCount = min 10 (max 3 (V.length colorsWithFreq `div` 5))
      clusterResult = clusterColors clusterCount 100 colorsWithFreq
      clusters = crClusters clusterResult
      
      -- Assign semantic roles
      roleAssignments = assignRoles clusters
      
      -- Convert to BrandPalette
      brandColors = V.toList $ V.mapMaybe toBrandColor roleAssignments
      palette = BrandPalette brandColors
      
      -- Check for contrast warnings
      warnings = checkContrastWarnings roleAssignments
      
  in ColorExtractionResult palette clusters warnings

-- | Convert RoleAssignment to BrandColor
toBrandColor :: RoleAssignment -> Maybe BrandColor
toBrandColor (RoleAssignment (OKLCH' l c h _) role _) =
  case mkOKLCH l c h of
    Just oklch -> Just $ BrandColor oklch role
    Nothing    -> Nothing

-- | Check WCAG contrast and generate warnings
checkContrastWarnings :: Vector RoleAssignment -> [ExtractionWarning]
checkContrastWarnings assignments =
  let mPrimary = V.find (\ra -> raRole ra == Primary) assignments
      mBackground = V.find (\ra -> raRole ra == Background) assignments
  in case (mPrimary, mBackground) of
       (Just primary, Just bg) ->
         let ratio = contrastRatio (raColor primary) (raColor bg)
         in if ratio < 4.5
            then [WarnLowColorContrast ratio]
            else []
       _ -> []

-- | Extract OKLCH components from a BrandColor
-- Provides direct access to the OKLCH type from the palette
extractOKLCH :: BrandColor -> OKLCH
extractOKLCH (BrandColor oklch _role) = oklch
