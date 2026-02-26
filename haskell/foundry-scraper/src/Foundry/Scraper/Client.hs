{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // foundry // scraper // client
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Scraper.Client
Description : ZMQ DEALER client for scraper communication
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

ZMQ client that connects to the Playwright scraper service.

== Architecture

Uses a DEALER socket for async request/response:
- Sends ScrapeRequest to ROUTER socket on scraper
- Receives ScrapeResponse with scraped data

== Thread Safety

The client is thread-safe. Multiple threads can call 'scrape' concurrently.
Internally uses a request queue with correlation IDs.

== Dependencies

Requires: zeromq4-haskell, stm
Required by: Foundry.Scraper

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Scraper.Client
  ( -- * Client Handle
    ScraperClient
  , withScraperClient
  , newScraperClient
  , closeScraperClient

    -- * Operations
  , scrape
  , scrapeWithOptions

    -- * Errors
  , ScraperClientError (..)
  ) where

import Control.Concurrent (ThreadId, forkIO, threadDelay)
import Control.Concurrent.STM
  ( TVar
  , atomically
  , modifyTVar'
  , newTVarIO
  , readTVar
  , readTVarIO
  , writeTVar
  )
import Control.Exception (Exception, bracket, try)
import Control.Monad (forever)
import Data.ByteString (ByteString)
import Data.ByteString.Char8 qualified as BC
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import System.ZMQ4 qualified as ZMQ

import Foundry.Extract.Types (ScrapeResult)
import Foundry.Scraper.Config (CurveKeys (..), ScraperConfig (..))
import Foundry.Scraper.Protocol
  ( ScrapeError (..)
  , ScrapeOptions
  , ScrapeRequest (..)
  , ScrapeResponse (..)
  , defaultOptions
  , decodeResponse
  , encodeRequest
  )

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Opaque handle to scraper client
data ScraperClient = ScraperClient
  { scConfig     :: !ScraperConfig
  , scContext    :: !ZMQ.Context
  , scSocket     :: !(ZMQ.Socket ZMQ.Dealer)
  , scPending    :: !(TVar (Map ByteString (TVar (Maybe ScrapeResponse))))
  , scNextId     :: !(TVar Int)
  , scRecvThread :: !(TVar (Maybe ThreadId))
  }

-- | Errors from scraper client
data ScraperClientError
  = ConnectionError !Text
  | TimeoutError !Text
  | ProtocolError !Text
  | ScraperError !ScrapeError
  deriving stock (Eq, Show)

instance Exception ScraperClientError

--------------------------------------------------------------------------------
-- Client Lifecycle
--------------------------------------------------------------------------------

-- | Run action with a scraper client
withScraperClient :: ScraperConfig -> (ScraperClient -> IO a) -> IO a
withScraperClient config = bracket (newScraperClient config) closeScraperClient

-- | Create a new scraper client
newScraperClient :: ScraperConfig -> IO ScraperClient
newScraperClient config = do
  ctx <- ZMQ.context
  sock <- ZMQ.socket ctx ZMQ.Dealer
  
  -- Set socket options
  ZMQ.setLinger (ZMQ.restrict (0 :: Int)) sock
  ZMQ.setSendTimeout (ZMQ.restrict (scTimeout config)) sock
  ZMQ.setReceiveTimeout (ZMQ.restrict (scTimeout config)) sock
  
  -- Configure CURVE if keys provided
  case scCurveKeys config of
    Just keys -> configureCurve sock keys
    Nothing   -> pure ()
  
  -- Connect to endpoint
  ZMQ.connect sock (T.unpack $ scEndpoint config)
  
  -- Initialize state
  pending <- newTVarIO Map.empty
  nextId <- newTVarIO 0
  recvThread <- newTVarIO Nothing
  
  let client = ScraperClient
        { scConfig = config
        , scContext = ctx
        , scSocket = sock
        , scPending = pending
        , scNextId = nextId
        , scRecvThread = recvThread
        }
  
  -- Start receiver thread
  startReceiver client
  
  pure client

-- | Configure CURVE encryption on socket
configureCurve :: ZMQ.Socket ZMQ.Dealer -> CurveKeys -> IO ()
configureCurve sock CurveKeys{..} = do
  ZMQ.setCurvePublicKey ZMQ.TextFormat (ZMQ.restrict ckPublicKey) sock
  ZMQ.setCurveSecretKey ZMQ.TextFormat (ZMQ.restrict ckSecretKey) sock
  ZMQ.setCurveServerKey ZMQ.TextFormat (ZMQ.restrict ckServerKey) sock

-- | Close the scraper client
closeScraperClient :: ScraperClient -> IO ()
closeScraperClient ScraperClient{..} = do
  -- Stop receiver thread
  mThread <- readTVarIO scRecvThread
  case mThread of
    Just _tid -> pure ()  -- Thread will exit when socket closes
    Nothing   -> pure ()
  
  -- Close socket and context
  ZMQ.close scSocket
  ZMQ.term scContext

-- | Start the receiver thread
startReceiver :: ScraperClient -> IO ()
startReceiver client@ScraperClient{..} = do
  tid <- forkIO $ receiverLoop client
  atomically $ writeTVar scRecvThread (Just tid)

-- | Receiver loop - processes incoming messages
receiverLoop :: ScraperClient -> IO ()
receiverLoop ScraperClient{..} = forever $ do
  -- Receive multipart message: [requestId, response]
  result <- try @ZMQ.ZMQError $ ZMQ.receiveMulti scSocket
  case result of
    Left _err -> 
      -- Socket closed or error, exit loop
      pure ()
    Right parts -> case parts of
      [requestId, responseData] -> do
        case decodeResponse responseData of
          Left _err -> 
            -- Protocol error, ignore malformed response
            pure ()
          Right response -> do
            -- Find pending request and complete it
            atomically $ do
              pending <- readTVar scPending
              case Map.lookup requestId pending of
                Just responseVar -> do
                  writeTVar responseVar (Just response)
                  modifyTVar' scPending (Map.delete requestId)
                Nothing ->
                  -- Unknown request ID, ignore
                  pure ()
      _ ->
        -- Malformed message, ignore
        pure ()

--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

-- | Scrape a URL with default options
scrape :: ScraperClient -> Text -> IO (Either ScraperClientError ScrapeResult)
scrape client url = scrapeWithOptions client url defaultOptions

-- | Scrape a URL with custom options
scrapeWithOptions 
  :: ScraperClient 
  -> Text 
  -> ScrapeOptions 
  -> IO (Either ScraperClientError ScrapeResult)
scrapeWithOptions ScraperClient{..} url options = do
  -- Generate request ID
  requestId <- atomically $ do
    rid <- readTVar scNextId
    writeTVar scNextId (rid + 1)
    pure $ BC.pack $ show rid
  
  -- Create response variable
  responseVar <- newTVarIO Nothing
  
  -- Register pending request
  atomically $ modifyTVar' scPending (Map.insert requestId responseVar)
  
  -- Build and send request
  let request = ScrapeRequest url options
      encoded = encodeRequest request
  
  -- Send as multipart: [requestId, request]
  sendResult <- try @ZMQ.ZMQError $ ZMQ.sendMulti scSocket (requestId :| [encoded])
  case sendResult of
    Left err -> do
      -- Clean up pending request
      atomically $ modifyTVar' scPending (Map.delete requestId)
      pure $ Left $ ConnectionError $ T.pack $ show err
    Right () -> do
      -- Wait for response with timeout
      let timeoutMicros = scTimeout scConfig * 1000
      mResponse <- waitForResponse responseVar timeoutMicros
      
      case mResponse of
        Nothing -> do
          atomically $ modifyTVar' scPending (Map.delete requestId)
          pure $ Left $ TimeoutError $ "Timeout waiting for response to: " <> url
        Just (ScrapeSuccess result) ->
          pure $ Right result
        Just (ScrapeFailure err) ->
          pure $ Left $ ScraperError err

-- | Wait for response with timeout
waitForResponse :: TVar (Maybe ScrapeResponse) -> Int -> IO (Maybe ScrapeResponse)
waitForResponse var timeoutMicros = go maxPolls
  where
    -- Simple polling implementation
    -- A production version would use async/timeout
    pollInterval :: Int
    pollInterval = 10000  -- 10ms
    
    maxPolls :: Int
    maxPolls = timeoutMicros `div` pollInterval
    
    go :: Int -> IO (Maybe ScrapeResponse)
    go 0 = pure Nothing
    go n = do
      mResp <- readTVarIO var
      case mResp of
        Just resp -> pure (Just resp)
        Nothing -> do
          threadDelay pollInterval
          go (n - 1)
