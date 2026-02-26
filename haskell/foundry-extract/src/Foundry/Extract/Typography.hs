{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // foundry // extract // typography
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Typography
Description : Typography extraction from scraped content
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Extracts typography specification from CSS and computed styles.

== Pipeline

1. Parse font-family declarations from CSS and computed styles
2. Identify heading vs body font families
3. Collect font sizes from computed styles
4. Detect type scale using geometric regression
5. Build Typography molecule

== Dependencies

Requires: Foundry.Extract.Types, Foundry.Extract.Typography.*
Required by: Foundry.Extract.Compose

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Typography
  ( -- * Extraction
    extractTypography
  , TypographyExtractionResult (..)

    -- * Re-exports
  , module Foundry.Extract.Typography.FontFamily
  , module Foundry.Extract.Typography.Scale
  ) where

import Data.List (sortBy)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, listToMaybe, mapMaybe)
import Data.Ord (Down (..), comparing)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V

import Foundry.Core.Brand.Typography 
  ( FontFamily (..)
  , FontWeight (..)
  , LineHeight (..)
  , TypeScale (..)
  , Typography (..)
  )
import Foundry.Extract.Typography.FontFamily
import Foundry.Extract.Typography.Scale
import Foundry.Extract.Types
  ( CSSProperty (..)
  , CSSRule (..)
  , CSSSelector (..)
  , CSSStylesheet (..)
  , CSSValue (..)
  , ComputedStyle (..)
  , ElementStyles (..)
  , ExtractionError (..)
  , ExtractionWarning (..)
  , FontData (..)
  , FontFace (..)
  , ScrapeResult (..)
  , TextBlockType (..)
  )

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Result of typography extraction
data TypographyExtractionResult = TypographyExtractionResult
  { terTypography :: !Typography
    -- ^ Extracted typography specification
  , terScale      :: !(Maybe DetectedScale)
    -- ^ Detected type scale (for debugging)
  , terWarnings   :: ![ExtractionWarning]
    -- ^ Extraction warnings
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Extraction
--------------------------------------------------------------------------------

-- | Extract typography from scrape result
extractTypography :: ScrapeResult -> Either ExtractionError TypographyExtractionResult
extractTypography sr = do
  -- Collect font families
  let cssFonts = extractCSSFonts (srStylesheets sr)
      computedFonts = extractComputedFonts (srComputedStyles sr)
      fontFaceData = srFontData sr
      
      -- Merge font usage data
      allFonts = mergeUsageMaps cssFonts computedFonts (fdUsedFonts fontFaceData)
  
  -- Find heading and body fonts
  let headingFont = findHeadingFont (srStylesheets sr) (srComputedStyles sr) allFonts
      bodyFont = findBodyFont (srComputedStyles sr) allFonts
  
  case (headingFont, bodyFont) of
    (Nothing, Nothing) -> Left ErrNoFonts
    (mHead, mBody) -> do
      -- Use body font as default if heading not found
      let finalHeading = maybe defaultFont id (mHead <|> mBody)
          finalBody = maybe defaultFont id (mBody <|> mHead)
      
      -- Detect type scale from font sizes
      let fontSizes = extractFontSizes (srComputedStyles sr)
          mScale = detectScale fontSizes
          typeScale = maybe defaultScale toTypeScale mScale
          
          warnings = case mScale of
            Nothing -> [WarnNoTypeScale]
            Just _  -> []
      
      -- Default line heights per SMART Framework
      let defaultHeadingLH = LineHeight 1.3
          defaultBodyLH = LineHeight 1.6
      
      Right $ TypographyExtractionResult
        { terTypography = Typography
            { typographyHeadingFamily = finalHeading
            , typographyBodyFamily = finalBody
            , typographyScale = typeScale
            , typographyHeadingLH = defaultHeadingLH
            , typographyBodyLH = defaultBodyLH
            , typographyScaleTable = V.empty  -- TODO: build scale table from detected sizes
            }
        , terScale = mScale
        , terWarnings = warnings
        }

-- | Alternative combinator for Maybe
(<|>) :: Maybe a -> Maybe a -> Maybe a
Nothing <|> y = y
x       <|> _ = x

-- | Default font if none detected
defaultFont :: FontFamily
defaultFont = FontFamily 
  { fontFamilyName = "system-ui"
  , fontFamilyFallbacks = ["sans-serif"]
  , fontFamilyRationale = "System default fallback"
  }

-- | Default type scale
defaultScale :: TypeScale
defaultScale = TypeScale 1.0 1.25  -- 1rem base, major third

-- | Convert DetectedScale to TypeScale
toTypeScale :: DetectedScale -> TypeScale
toTypeScale ds = TypeScale (dsBaseSize ds / 16) (dsRatio ds)  -- Convert px to rem

--------------------------------------------------------------------------------
-- Font Family Extraction
--------------------------------------------------------------------------------

-- | Extract font families from CSS stylesheets
extractCSSFonts :: Vector CSSStylesheet -> Map Text Int
extractCSSFonts sheets = V.foldl' processSheet Map.empty sheets
  where
    processSheet acc sheet = V.foldl' processRule acc (cssRules sheet)
    processRule acc rule = V.foldl' processProp acc (cssProperties rule)
    processProp acc prop
      | cssPropName prop == "font-family" = case cssPropValue prop of
          CSSFont fontValue -> 
            case parseFontFamily fontValue of
              Just stack -> Map.insertWith (+) (fsPrimary stack) 1 acc
              Nothing -> acc
          CSSRaw fontValue ->
            case parseFontFamily fontValue of
              Just stack -> Map.insertWith (+) (fsPrimary stack) 1 acc
              Nothing -> acc
          _ -> acc
      | otherwise = acc

-- | Extract font families from computed styles
extractComputedFonts :: Vector ElementStyles -> Map Text Int
extractComputedFonts elements = V.foldl' processElement Map.empty elements
  where
    processElement acc es = case csFontFamily (esStyles es) of
      Just fontValue -> case parseFontFamily fontValue of
        Just stack -> Map.insertWith (+) (fsPrimary stack) 1 acc
        Nothing -> acc
      Nothing -> acc

-- | Merge font usage maps
mergeUsageMaps :: Map Text Int -> Map Text Int -> Map Text Int -> Map Text Int
mergeUsageMaps m1 m2 m3 = Map.unionsWith (+) [m1, m2, m3]

--------------------------------------------------------------------------------
-- Font Role Detection
--------------------------------------------------------------------------------

-- | Find the heading font family
findHeadingFont :: Vector CSSStylesheet -> Vector ElementStyles -> Map Text Int -> Maybe FontFamily
findHeadingFont sheets elements allFonts =
  let -- Look for fonts used in heading selectors
      headingFonts = extractHeadingFonts sheets
      -- Look for fonts on computed h1-h6 elements
      computedHeadingFonts = extractComputedHeadingFonts elements
      -- Combine and pick most frequent
      combined = Map.unionsWith (+) [headingFonts, computedHeadingFonts]
  in if Map.null combined
     then Nothing
     else case maximumEntry combined of
       Nothing -> Nothing
       Just (fontName, _) -> Just $ toFontFamily fontName allFonts

-- | Extract fonts from heading selectors in CSS
extractHeadingFonts :: Vector CSSStylesheet -> Map Text Int
extractHeadingFonts sheets = V.foldl' processSheet Map.empty sheets
  where
    processSheet acc sheet = V.foldl' processRule acc (cssRules sheet)
    processRule acc rule
      | isHeadingSelector (cssSelector rule) = 
          V.foldl' (processProp 1) acc (cssProperties rule)
      | otherwise = acc
    processProp weight acc prop
      | cssPropName prop == "font-family" = case cssPropValue prop of
          CSSFont fontValue -> 
            case parseFontFamily fontValue of
              Just stack -> Map.insertWith (+) (fsPrimary stack) weight acc
              Nothing -> acc
          CSSRaw fontValue ->
            case parseFontFamily fontValue of
              Just stack -> Map.insertWith (+) (fsPrimary stack) weight acc
              Nothing -> acc
          _ -> acc
      | otherwise = acc

-- | Check if selector targets headings
isHeadingSelector :: CSSSelector -> Bool
isHeadingSelector (CSSSelector sel) =
  let lower = T.toLower sel
  in any (`T.isInfixOf` lower) ["h1", "h2", "h3", "h4", "h5", "h6", "heading", "title"]

-- | Extract fonts from computed heading elements
extractComputedHeadingFonts :: Vector ElementStyles -> Map Text Int
extractComputedHeadingFonts elements = V.foldl' processElement Map.empty elements
  where
    processElement acc es
      | isHeadingElement es = case csFontFamily (esStyles es) of
          Just fontValue -> case parseFontFamily fontValue of
            Just stack -> Map.insertWith (+) (fsPrimary stack) 1 acc
            Nothing -> acc
          Nothing -> acc
      | otherwise = acc

-- | Check if element is a heading
isHeadingElement :: ElementStyles -> Bool
isHeadingElement es =
  let tag = T.toUpper (esTagName es)
  in tag `elem` ["H1", "H2", "H3", "H4", "H5", "H6"]

-- | Find the body font family
findBodyFont :: Vector ElementStyles -> Map Text Int -> Maybe FontFamily
findBodyFont elements allFonts =
  let -- Look for fonts on body/paragraph elements
      bodyFonts = V.foldl' processElement Map.empty elements
  in if Map.null bodyFonts
     then -- Fall back to most common font overall
          if Map.null allFonts
          then Nothing
          else case maximumEntry allFonts of
            Nothing -> Nothing
            Just (fontName, _) -> Just $ toFontFamily fontName allFonts
     else case maximumEntry bodyFonts of
       Nothing -> Nothing
       Just (fontName, _) -> Just $ toFontFamily fontName allFonts
  where
    processElement acc es
      | isBodyElement es = case csFontFamily (esStyles es) of
          Just fontValue -> case parseFontFamily fontValue of
            Just stack -> Map.insertWith (+) (fsPrimary stack) 1 acc
            Nothing -> acc
          Nothing -> acc
      | otherwise = acc

-- | Check if element is body text
isBodyElement :: ElementStyles -> Bool
isBodyElement es =
  let tag = T.toUpper (esTagName es)
  in tag `elem` ["P", "BODY", "DIV", "SPAN", "LI", "TD", "ARTICLE", "SECTION"]

-- | Convert font name to FontFamily
toFontFamily :: Text -> Map Text Int -> FontFamily
toFontFamily name _ = FontFamily 
  { fontFamilyName = name
  , fontFamilyFallbacks = []
  , fontFamilyRationale = "Extracted from website CSS"
  }

-- | Get maximum entry from a map (returns Maybe to avoid partiality)
maximumEntry :: Ord v => Map k v -> Maybe (k, v)
maximumEntry m = case Map.toList m of
  []    -> Nothing
  pairs -> Just (foldl1 maxBySnd pairs)
  where
    maxBySnd a b = if snd a >= snd b then a else b

--------------------------------------------------------------------------------
-- Font Size Extraction
--------------------------------------------------------------------------------

-- | Extract font sizes from computed styles
extractFontSizes :: Vector ElementStyles -> Vector Double
extractFontSizes = V.mapMaybe (\es -> csFontSize (esStyles es))
