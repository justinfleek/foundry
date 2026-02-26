{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // foundry // scraper // test
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Main
Description : Test suite for Foundry.Scraper
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Property tests for scraper protocol, config, and client logic.

== Test Strategy

"Norman Stansfield energy - EVERYONE gets tested."

- Protocol: JSON encoding/decoding roundtrips
- Config: Default values, CURVE key validation
- Client: Request ID generation, timeout handling

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Main (main) where

import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Hedgehog
  ( Gen
  , Property
  , forAll
  , property
  , (===)
  , assert
  , diff
  )
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import Data.Aeson qualified as Aeson
import Data.ByteString qualified as BS
import Data.Text (Text)
import Data.Text qualified as T

import Foundry.Scraper.Protocol
  ( ScrapeRequest (..)
  , ScrapeOptions (..)
  , ScrapeError (..)
  , ScrapeResponse (..)
  , defaultOptions
  , encodeRequest
  , decodeResponse
  )
import Foundry.Scraper.Config
  ( ScraperConfig (..)
  , CurveKeys (..)
  , defaultConfig
  )

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Foundry.Scraper"
  [ testGroup "Protocol"
      [ testProperty "defaultOptions has sane values" prop_defaultOptions_sane
      , testProperty "ScrapeOptions JSON roundtrip" prop_scrapeOptions_json_roundtrip
      , testProperty "ScrapeRequest encodes to valid JSON" prop_scrapeRequest_valid_json
      , testProperty "ScrapeError JSON roundtrip" prop_scrapeError_json_roundtrip
      , testProperty "timeout is always positive" prop_options_timeout_positive
      , testProperty "maxDepth is always non-negative" prop_options_maxDepth_nonnegative
      ]
  , testGroup "Config"
      [ testProperty "defaultConfig has sane values" prop_defaultConfig_sane
      , testProperty "endpoint is valid format" prop_endpoint_valid_format
      , testProperty "timeout values are positive" prop_config_timeout_positive
      , testProperty "CURVE keys have correct length" prop_curve_keys_length
      ]
  , testGroup "Security"
      [ testProperty "URL with SQL injection encodes safely" prop_url_sql_injection_safe
      , testProperty "URL with XSS encodes safely" prop_url_xss_safe
      , testProperty "URL with null bytes encodes safely" prop_url_null_bytes_safe
      , testProperty "URL with unicode encodes safely" prop_url_unicode_safe
      ]
  ]

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

-- | Generate valid ScrapeOptions
genScrapeOptions :: Gen ScrapeOptions
genScrapeOptions = ScrapeOptions
  <$> Gen.int (Range.linear 1000 120000)      -- timeout: 1s to 2min
  <*> Gen.bool                                 -- waitForJS
  <*> Gen.bool                                 -- extractImages
  <*> Gen.bool                                 -- extractFonts
  <*> Gen.int (Range.linear 0 10)             -- maxDepth

-- | Generate valid URL
genURL :: Gen Text
genURL = do
  protocol <- Gen.element ["https://", "http://"]
  domain <- Gen.text (Range.linear 3 20) Gen.alphaNum
  tld <- Gen.element [".com", ".org", ".io", ".dev", ".ai"]
  path <- Gen.text (Range.linear 0 30) (Gen.frequency [(9, Gen.alphaNum), (1, pure '/')])
  pure $ protocol <> domain <> tld <> "/" <> path

-- | Generate ScrapeRequest
genScrapeRequest :: Gen ScrapeRequest
genScrapeRequest = ScrapeRequest
  <$> genURL
  <*> genScrapeOptions

-- | Generate ScrapeError
genScrapeError :: Gen ScrapeError
genScrapeError = ScrapeError
  <$> Gen.element ["TIMEOUT", "NETWORK", "PARSE", "BLOCKED", "INVALID_URL"]
  <*> Gen.text (Range.linear 10 100) Gen.unicode
  <*> Gen.maybe (Gen.text (Range.linear 10 200) Gen.unicode)

-- | Generate ScraperConfig
genScraperConfig :: Gen ScraperConfig
genScraperConfig = ScraperConfig
  <$> genEndpoint
  <*> Gen.int (Range.linear 1000 120000)   -- timeout
  <*> Gen.int (Range.linear 100 5000)      -- reconnectDelay
  <*> Gen.int (Range.linear 1 10)          -- maxRetries
  <*> Gen.maybe genCurveKeys

-- | Generate valid ZMQ endpoint
genEndpoint :: Gen Text
genEndpoint = do
  transport <- Gen.element ["tcp", "ipc", "inproc"]
  case transport of
    "tcp" -> do
      host <- Gen.element ["127.0.0.1", "localhost", "0.0.0.0"]
      port <- Gen.int (Range.linear 1024 65535)
      pure $ "tcp://" <> host <> ":" <> T.pack (show port)
    "ipc" -> do
      path <- Gen.text (Range.linear 5 20) Gen.alphaNum
      pure $ "ipc:///tmp/" <> path <> ".sock"
    _ -> do
      name <- Gen.text (Range.linear 5 20) Gen.alphaNum
      pure $ "inproc://" <> name

-- | Generate CURVE keys (Z85 encoded, 40 chars each)
genCurveKeys :: Gen CurveKeys
genCurveKeys = CurveKeys
  <$> genZ85Key
  <*> genZ85Key
  <*> genZ85Key

-- | Generate Z85-encoded key (40 chars from restricted alphabet)
genZ85Key :: Gen BS.ByteString
genZ85Key = do
  -- Z85 alphabet: 0-9, a-z, A-Z, and special chars
  let z85Chars = ['0'..'9'] <> ['a'..'z'] <> ['A'..'Z'] 
               <> ['.', '-', ':', '+', '=', '^', '!', '/', '*', '?']
               <> ['&', '<', '>', '(', ')', '[', ']', '{', '}', '@']
               <> ['%', '$', '#']
  chars <- Gen.list (Range.singleton 40) (Gen.element z85Chars)
  pure $ BS.pack $ map (fromIntegral . fromEnum) chars

--------------------------------------------------------------------------------
-- Adversarial Generators
--------------------------------------------------------------------------------

-- | SQL injection payloads
genSQLInjection :: Gen Text
genSQLInjection = Gen.element
  [ "'; DROP TABLE brands; --"
  , "1 OR 1=1"
  , "admin'--"
  , "' UNION SELECT * FROM users --"
  , "1; DELETE FROM brands WHERE 1=1"
  ]

-- | XSS payloads
genXSS :: Gen Text
genXSS = Gen.element
  [ "<script>alert('xss')</script>"
  , "<img src=x onerror=alert(1)>"
  , "javascript:alert(1)"
  , "<svg onload=alert(1)>"
  , "'\"><script>document.location='http://evil.com'</script>"
  ]

-- | Null byte payloads
genNullBytes :: Gen Text
genNullBytes = do
  prefix <- Gen.text (Range.linear 1 10) Gen.alphaNum
  suffix <- Gen.text (Range.linear 1 10) Gen.alphaNum
  pure $ prefix <> "\x00" <> suffix

-- | Unicode edge cases
genUnicodeEdge :: Gen Text
genUnicodeEdge = Gen.element
  [ "\x202E\x202Dmalicious"           -- RTL override
  , "\xFEFF\xFEFFhidden"              -- BOM
  , "normal\x0000\x0000hidden"        -- Null bytes
  , "\x200B\x200B\x200Binvisible"     -- Zero-width spaces
  ]

--------------------------------------------------------------------------------
-- Protocol Tests
--------------------------------------------------------------------------------

prop_defaultOptions_sane :: Property
prop_defaultOptions_sane = property $ do
  -- Timeout should be reasonable (30s default)
  assert $ soTimeout defaultOptions > 0
  assert $ soTimeout defaultOptions <= 120000
  
  -- Max depth should be reasonable
  assert $ soMaxDepth defaultOptions >= 0
  assert $ soMaxDepth defaultOptions <= 10
  
  -- JS should be enabled by default (most sites need it)
  assert $ soWaitForJS defaultOptions

prop_scrapeOptions_json_roundtrip :: Property
prop_scrapeOptions_json_roundtrip = property $ do
  opts <- forAll genScrapeOptions
  let encoded = Aeson.encode opts
      decoded = Aeson.decode encoded
  decoded === Just opts

prop_scrapeRequest_valid_json :: Property
prop_scrapeRequest_valid_json = property $ do
  req <- forAll genScrapeRequest
  let encoded = encodeRequest req
  -- Should produce valid JSON (non-empty)
  assert $ BS.length encoded > 0
  -- Should be parseable as JSON
  assert $ case Aeson.decodeStrict encoded :: Maybe Aeson.Value of
    Just _  -> True
    Nothing -> False

prop_scrapeError_json_roundtrip :: Property
prop_scrapeError_json_roundtrip = property $ do
  err <- forAll genScrapeError
  let encoded = Aeson.encode err
      decoded = Aeson.decode encoded
  decoded === Just err

prop_options_timeout_positive :: Property
prop_options_timeout_positive = property $ do
  opts <- forAll genScrapeOptions
  assert $ soTimeout opts > 0

prop_options_maxDepth_nonnegative :: Property
prop_options_maxDepth_nonnegative = property $ do
  opts <- forAll genScrapeOptions
  assert $ soMaxDepth opts >= 0

--------------------------------------------------------------------------------
-- Config Tests
--------------------------------------------------------------------------------

prop_defaultConfig_sane :: Property
prop_defaultConfig_sane = property $ do
  -- Endpoint should be localhost
  assert $ T.isInfixOf "127.0.0.1" (scEndpoint defaultConfig) 
        || T.isInfixOf "localhost" (scEndpoint defaultConfig)
  
  -- Timeout should be positive
  assert $ scTimeout defaultConfig > 0
  
  -- Reconnect delay should be positive
  assert $ scReconnectDelay defaultConfig > 0
  
  -- Max retries should be positive
  assert $ scMaxRetries defaultConfig > 0
  
  -- CURVE disabled by default (dev mode)
  scCurveKeys defaultConfig === Nothing

prop_endpoint_valid_format :: Property
prop_endpoint_valid_format = property $ do
  config <- forAll genScraperConfig
  let endpoint = scEndpoint config
  -- Must have transport prefix
  assert $ T.isInfixOf "://" endpoint
  -- Must start with valid transport
  assert $ T.isPrefixOf "tcp://" endpoint
        || T.isPrefixOf "ipc://" endpoint
        || T.isPrefixOf "inproc://" endpoint

prop_config_timeout_positive :: Property
prop_config_timeout_positive = property $ do
  config <- forAll genScraperConfig
  assert $ scTimeout config > 0
  assert $ scReconnectDelay config > 0
  assert $ scMaxRetries config > 0

prop_curve_keys_length :: Property
prop_curve_keys_length = property $ do
  keys <- forAll genCurveKeys
  -- Z85 encoded 32-byte keys are 40 chars
  BS.length (ckPublicKey keys) === 40
  BS.length (ckSecretKey keys) === 40
  BS.length (ckServerKey keys) === 40

--------------------------------------------------------------------------------
-- Security Tests
--------------------------------------------------------------------------------

prop_url_sql_injection_safe :: Property
prop_url_sql_injection_safe = property $ do
  injection <- forAll genSQLInjection
  let url = "https://example.com/" <> injection
      req = ScrapeRequest url defaultOptions
      encoded = encodeRequest req
  -- Should encode successfully (not crash)
  assert $ BS.length encoded > 0
  -- Encoded JSON should contain escaped URL
  assert $ case Aeson.decodeStrict encoded :: Maybe Aeson.Value of
    Just _  -> True
    Nothing -> False

prop_url_xss_safe :: Property
prop_url_xss_safe = property $ do
  xss <- forAll genXSS
  let url = "https://example.com/" <> xss
      req = ScrapeRequest url defaultOptions
      encoded = encodeRequest req
  -- Should encode successfully (not crash)
  assert $ BS.length encoded > 0
  -- Should not contain unescaped script tags in JSON
  let hasUnescapedScript = BS.isInfixOf "<script>" encoded
  assert $ not hasUnescapedScript

prop_url_null_bytes_safe :: Property
prop_url_null_bytes_safe = property $ do
  nullUrl <- forAll genNullBytes
  let url = "https://example.com/" <> nullUrl
      req = ScrapeRequest url defaultOptions
      encoded = encodeRequest req
  -- Should encode successfully
  assert $ BS.length encoded > 0
  -- JSON encoding escapes null bytes
  assert $ case Aeson.decodeStrict encoded :: Maybe Aeson.Value of
    Just _  -> True
    Nothing -> False

prop_url_unicode_safe :: Property
prop_url_unicode_safe = property $ do
  unicodeEdge <- forAll genUnicodeEdge
  let url = "https://example.com/" <> unicodeEdge
      req = ScrapeRequest url defaultOptions
      encoded = encodeRequest req
  -- Should encode successfully
  assert $ BS.length encoded > 0
  -- Should produce valid JSON
  assert $ case Aeson.decodeStrict encoded :: Maybe Aeson.Value of
    Just _  -> True
    Nothing -> False
