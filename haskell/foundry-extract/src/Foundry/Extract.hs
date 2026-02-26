{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                           // foundry // extract
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract
Description : Brand extraction from scraped web content
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Main entry point for the METXT extraction pipeline.

== Overview

This module provides the complete extraction pipeline that transforms
raw scraped web content into typed Brand molecules. The pipeline:

1. Parses CSS color values and clusters them into a palette
2. Detects font families, sizes, and type scale
3. Analyzes spacing values to detect base unit and scale
4. Performs NLP analysis on text to detect brand voice
5. Composes all components into a complete Brand

== Usage

> import Foundry.Extract
> import Foundry.Extract.Types (ScrapeResult(..))
> import Data.Time (getCurrentTime)
>
> main :: IO ()
> main = do
>   timestamp <- getCurrentTime
>   let scrapeResult = ... -- from scraper
>   case composeBrand timestamp scrapeResult of
>     Left err    -> print err
>     Right brand -> print (berPalette brand)

== Dependencies

Requires: Foundry.Core
Required by: (external consumers)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract
  ( -- * Composition (primary entry point)
    composeBrand
  , BrandExtractionResult (..)
  , ExtractionComponents (..)

    -- * Individual Extractors
  , extractPalette
  , extractTypography
  , extractSpacing
  , extractVoice

    -- * Types
  , module Foundry.Extract.Types
  ) where

import Foundry.Extract.Color (extractPalette)
import Foundry.Extract.Compose (BrandExtractionResult (..), ExtractionComponents (..), composeBrand)
import Foundry.Extract.Spacing (extractSpacing)
import Foundry.Extract.Typography (extractTypography)
import Foundry.Extract.Types
import Foundry.Extract.Voice (extractVoice)
