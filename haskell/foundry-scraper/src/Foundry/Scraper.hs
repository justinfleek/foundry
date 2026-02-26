{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                           // foundry // scraper
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Scraper
Description : ZMQ-based web scraper client
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Main entry point for the scraper client library.

== Overview

This module provides a ZMQ client that communicates with a sandboxed
Playwright-based scraper service. The scraper runs in an isolated
environment (gVisor/Bubblewrap) and extracts:

* CSS stylesheets (inline, linked, imported)
* Computed styles for DOM elements
* Text content (headings, paragraphs, buttons)
* Font data (@font-face declarations)
* Asset URLs (images, SVGs, favicons)

== Usage

> import Foundry.Scraper
> import Foundry.Extract (composeBrand)
> import Data.Time (getCurrentTime)
>
> main :: IO ()
> main = withScraperClient defaultConfig $ \client -> do
>   result <- scrape client "https://example.com"
>   case result of
>     Left err -> print err
>     Right scrapeResult -> do
>       timestamp <- getCurrentTime
>       case composeBrand timestamp scrapeResult of
>         Left err -> print err
>         Right brand -> print brand

== Dependencies

Requires: zeromq4-haskell
Required by: (external consumers)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Scraper
  ( -- * Client
    ScraperClient
  , withScraperClient
  , newScraperClient
  , closeScraperClient

    -- * Configuration
  , ScraperConfig (..)
  , defaultConfig
  , CurveKeys (..)

    -- * Operations
  , scrape
  , scrapeWithOptions

    -- * Options
  , ScrapeOptions (..)
  , defaultOptions

    -- * Errors
  , ScraperClientError (..)
  , ScrapeError (..)
  ) where

import Foundry.Scraper.Client
  ( ScraperClient
  , ScraperClientError (..)
  , closeScraperClient
  , newScraperClient
  , scrape
  , scrapeWithOptions
  , withScraperClient
  )
import Foundry.Scraper.Config (CurveKeys (..), ScraperConfig (..), defaultConfig)
import Foundry.Scraper.Protocol (ScrapeError (..), ScrapeOptions (..), defaultOptions)
