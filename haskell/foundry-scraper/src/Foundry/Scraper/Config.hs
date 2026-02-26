{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // foundry // scraper // config
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Scraper.Config
Description : Scraper client configuration
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Configuration for ZMQ connection to the scraper service.

== Dependencies

Requires: text
Required by: Foundry.Scraper.Client

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Scraper.Config
  ( -- * Configuration
    ScraperConfig (..)
  , defaultConfig

    -- * CURVE Keys
  , CurveKeys (..)
  ) where

import Data.ByteString (ByteString)
import Data.Text (Text)

--------------------------------------------------------------------------------
-- Configuration
--------------------------------------------------------------------------------

-- | Configuration for scraper client
data ScraperConfig = ScraperConfig
  { scEndpoint       :: !Text
    -- ^ ZMQ endpoint (e.g., "tcp://localhost:5555")
  , scTimeout        :: !Int
    -- ^ Request timeout in milliseconds
  , scReconnectDelay :: !Int
    -- ^ Delay between reconnection attempts (ms)
  , scMaxRetries     :: !Int
    -- ^ Maximum number of retries
  , scCurveKeys      :: !(Maybe CurveKeys)
    -- ^ CURVE encryption keys (if enabled)
  }
  deriving stock (Eq, Show)

-- | Default configuration for local development
defaultConfig :: ScraperConfig
defaultConfig = ScraperConfig
  { scEndpoint = "tcp://127.0.0.1:5555"
  , scTimeout = 60000         -- 60 seconds
  , scReconnectDelay = 1000   -- 1 second
  , scMaxRetries = 3
  , scCurveKeys = Nothing     -- No encryption by default
  }

--------------------------------------------------------------------------------
-- CURVE Encryption
--------------------------------------------------------------------------------

-- | CURVE encryption keys for secure communication
data CurveKeys = CurveKeys
  { ckPublicKey  :: !ByteString
    -- ^ Client public key (32 bytes, Z85 encoded = 40 chars)
  , ckSecretKey  :: !ByteString
    -- ^ Client secret key (32 bytes, Z85 encoded = 40 chars)
  , ckServerKey  :: !ByteString
    -- ^ Server public key (32 bytes, Z85 encoded = 40 chars)
  }
  deriving stock (Eq, Show)
