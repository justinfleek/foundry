{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // foundry // scraper // app
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Main
Description : Command-line scraper client
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

CLI tool to scrape brand data from URLs using the Playwright scraper service.

== Usage

  foundry-scrape --url https://example.com [--endpoint tcp://localhost:5555]

== Dependencies

Requires: foundry-scraper, optparse-applicative
Required by: N/A (executable entry point)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Main (main) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Options.Applicative
  ( Parser
  , ParserInfo
  , execParser
  , fullDesc
  , header
  , help
  , helper
  , info
  , long
  , metavar
  , progDesc
  , showDefault
  , strOption
  , value
  , (<**>)
  )

import Foundry.Scraper (withScraperClient, scrape)
import Foundry.Scraper.Config (ScraperConfig (..), defaultConfig)

--------------------------------------------------------------------------------
-- CLI Options
--------------------------------------------------------------------------------

-- | Command-line options
data Options = Options
  { optURL      :: !Text
    -- ^ URL to scrape
  , optEndpoint :: !Text
    -- ^ ZMQ endpoint for scraper service
  }
  deriving stock (Eq, Show)

-- | Parser for options
optionsParser :: Parser Options
optionsParser = Options
  <$> strOption
        ( long "url"
       <> metavar "URL"
       <> help "URL to scrape for brand data"
        )
  <*> strOption
        ( long "endpoint"
       <> metavar "ENDPOINT"
       <> value "tcp://127.0.0.1:5555"
       <> showDefault
       <> help "ZMQ endpoint of scraper service"
        )

-- | Parser info with description
optionsParserInfo :: ParserInfo Options
optionsParserInfo = info (optionsParser <**> helper)
  ( fullDesc
 <> progDesc "Scrape brand data from a URL"
 <> header "foundry-scrape - SMART brand extraction tool"
  )

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

-- | Entry point
main :: IO ()
main = do
  opts <- execParser optionsParserInfo
  
  let config = defaultConfig { scEndpoint = optEndpoint opts }
  
  TIO.putStrLn $ "Connecting to scraper at: " <> scEndpoint config
  TIO.putStrLn $ "Scraping URL: " <> optURL opts
  
  result <- withScraperClient config $ \client ->
    scrape client (optURL opts)
  
  case result of
    Left err -> do
      TIO.putStrLn $ "Error: " <> T.pack (show err)
    Right scrapeResult -> do
      TIO.putStrLn "Success!"
      TIO.putStrLn $ "Result: " <> T.pack (show scrapeResult)
