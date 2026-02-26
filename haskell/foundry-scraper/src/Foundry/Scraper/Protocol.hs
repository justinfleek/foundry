{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // foundry // scraper // protocol
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Scraper.Protocol
Description : ZMQ message protocol for scraper communication
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines the message protocol between Haskell client and TypeScript scraper.

== Protocol Overview

Client (Haskell) sends ScrapeRequest via ZMQ DEALER socket.
Server (TypeScript/Playwright) responds with ScrapeResponse.

All messages are JSON-encoded with a message type header.

== Message Flow

1. Client → Server: ScrapeRequest (URL to scrape)
2. Server → Client: ScrapeResponse (extracted data or error)

== Dependencies

Requires: aeson, bytestring, text
Required by: Foundry.Scraper.Client

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Scraper.Protocol
  ( -- * Request Types
    ScrapeRequest (..)
  , ScrapeOptions (..)
  , defaultOptions

    -- * Response Types
  , ScrapeResponse (..)
  , ScrapeError (..)

    -- * Encoding/Decoding
  , encodeRequest
  , decodeResponse
  ) where

import Data.Aeson
  ( FromJSON (..)
  , ToJSON (..)
  , Value (..)
  , object
  , withObject
  , (.:)
  , (.:?)
  , (.=)
  )
import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as LBS
import Data.Aeson qualified as Aeson
import Data.Text (Text)
import GHC.Generics (Generic)

import Foundry.Extract.Types (ScrapeResult (..))

--------------------------------------------------------------------------------
-- Request Types
--------------------------------------------------------------------------------

-- | Request to scrape a URL
data ScrapeRequest = ScrapeRequest
  { srqURL     :: !Text
    -- ^ URL to scrape
  , srqOptions :: !ScrapeOptions
    -- ^ Scraping options
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ScrapeRequest where
  toJSON ScrapeRequest{..} = object
    [ "type"    .= ("scrape" :: Text)
    , "url"     .= srqURL
    , "options" .= srqOptions
    ]

-- | Options controlling scrape behavior
data ScrapeOptions = ScrapeOptions
  { soTimeout       :: !Int
    -- ^ Timeout in milliseconds
  , soWaitForJS     :: !Bool
    -- ^ Wait for JavaScript to execute
  , soExtractImages :: !Bool
    -- ^ Extract image assets
  , soExtractFonts  :: !Bool
    -- ^ Extract font information
  , soMaxDepth      :: !Int
    -- ^ Maximum CSS import depth to follow
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ScrapeOptions where
  toJSON ScrapeOptions{..} = object
    [ "timeout"       .= soTimeout
    , "waitForJS"     .= soWaitForJS
    , "extractImages" .= soExtractImages
    , "extractFonts"  .= soExtractFonts
    , "maxDepth"      .= soMaxDepth
    ]

instance FromJSON ScrapeOptions where
  parseJSON = withObject "ScrapeOptions" $ \v -> ScrapeOptions
    <$> v .: "timeout"
    <*> v .: "waitForJS"
    <*> v .: "extractImages"
    <*> v .: "extractFonts"
    <*> v .: "maxDepth"

-- | Default scrape options
defaultOptions :: ScrapeOptions
defaultOptions = ScrapeOptions
  { soTimeout = 30000        -- 30 seconds
  , soWaitForJS = True       -- Wait for JS rendering
  , soExtractImages = True   -- Get images
  , soExtractFonts = True    -- Get fonts
  , soMaxDepth = 3           -- Follow 3 levels of CSS imports
  }

--------------------------------------------------------------------------------
-- Response Types
--------------------------------------------------------------------------------

-- | Response from scraper
data ScrapeResponse
  = ScrapeSuccess !ScrapeResult
    -- ^ Successful scrape with extracted data
  | ScrapeFailure !ScrapeError
    -- ^ Scrape failed with error
  deriving stock (Eq, Show)

instance FromJSON ScrapeResponse where
  parseJSON = withObject "ScrapeResponse" $ \v -> do
    msgType <- v .: "type" :: Aeson.Parser Text
    case msgType of
      "success" -> ScrapeSuccess <$> v .: "result"
      "error"   -> ScrapeFailure <$> v .: "error"
      other     -> fail $ "Unknown response type: " <> show other

-- | Error from scraper
data ScrapeError = ScrapeError
  { seCode    :: !Text
    -- ^ Error code
  , seMessage :: !Text
    -- ^ Human-readable message
  , seDetails :: !(Maybe Text)
    -- ^ Additional details
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON ScrapeError where
  parseJSON = withObject "ScrapeError" $ \v -> ScrapeError
    <$> v .: "code"
    <*> v .: "message"
    <*> v .:? "details"

--------------------------------------------------------------------------------
-- Encoding/Decoding
--------------------------------------------------------------------------------

-- | Encode request to ByteString for ZMQ
encodeRequest :: ScrapeRequest -> ByteString
encodeRequest = LBS.toStrict . Aeson.encode

-- | Decode response from ByteString
decodeResponse :: ByteString -> Either String ScrapeResponse
decodeResponse = Aeson.eitherDecodeStrict
