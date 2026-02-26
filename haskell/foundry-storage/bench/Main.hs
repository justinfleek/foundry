{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // foundry // storage // bench
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Main
Description : Criterion benchmarks for storage operations
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Performance benchmarks for:
- HAMT insert/lookup/delete operations
- Content hashing (SHA256)
- Structure sharing efficiency

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Main (main) where

import Criterion.Main
  ( Benchmark
  , bench
  , bgroup
  , defaultMain
  , env
  , nf
  , whnf
  )
import Control.DeepSeq (NFData, force)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import System.Random (mkStdGen, randoms)

import Foundry.Storage.HAMT
  ( HAMT
  , StorageKey
  , delete
  , empty
  , insert
  , lookup
  , member
  , mkStorageKey
  , size
  )

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = defaultMain
  [ bgroup "StorageKey"
      [ bench "mkStorageKey/small (100B)" $ nf mkStorageKey smallContent
      , bench "mkStorageKey/medium (10KB)" $ nf mkStorageKey mediumContent
      , bench "mkStorageKey/large (1MB)" $ nf mkStorageKey largeContent
      ]
  , bgroup "HAMT/insert"
      [ env (pure empty) $ \h ->
          bench "insert/1" $ whnf (insert smallContent) h
      , env (buildHAMT 100) $ \h ->
          bench "insert/into-100" $ whnf (insert smallContent) h
      , env (buildHAMT 1000) $ \h ->
          bench "insert/into-1000" $ whnf (insert smallContent) h
      , env (buildHAMT 10000) $ \h ->
          bench "insert/into-10000" $ whnf (insert smallContent) h
      ]
  , bgroup "HAMT/lookup"
      [ env (buildHAMTWithKey 100) $ \(h, k) ->
          bench "lookup/in-100" $ whnf (lookup k) h
      , env (buildHAMTWithKey 1000) $ \(h, k) ->
          bench "lookup/in-1000" $ whnf (lookup k) h
      , env (buildHAMTWithKey 10000) $ \(h, k) ->
          bench "lookup/in-10000" $ whnf (lookup k) h
      ]
  , bgroup "HAMT/member"
      [ env (buildHAMTWithKey 1000) $ \(h, k) ->
          bench "member/present" $ whnf (member k) h
      , env (buildHAMT 1000) $ \h ->
          bench "member/absent" $ whnf (member (mkStorageKey "not-present")) h
      ]
  , bgroup "HAMT/delete"
      [ env (buildHAMTWithKey 100) $ \(h, k) ->
          bench "delete/from-100" $ whnf (delete k) h
      , env (buildHAMTWithKey 1000) $ \(h, k) ->
          bench "delete/from-1000" $ whnf (delete k) h
      ]
  , bgroup "HAMT/bulk"
      [ bench "bulk-insert/100" $ whnf buildHAMTForce 100
      , bench "bulk-insert/1000" $ whnf buildHAMTForce 1000
      , bench "bulk-insert/10000" $ whnf buildHAMTForce 10000
      ]
  , bgroup "HAMT/structure-sharing"
      [ env (buildHAMT 1000) $ \h ->
          bench "insert-preserves-structure" $ whnf (checkSharing h) smallContent
      ]
  ]

--------------------------------------------------------------------------------
-- Test Data
--------------------------------------------------------------------------------

smallContent :: ByteString
smallContent = BS.pack $ take 100 $ randoms (mkStdGen 42)

mediumContent :: ByteString
mediumContent = BS.pack $ take 10000 $ randoms (mkStdGen 43)

largeContent :: ByteString
largeContent = BS.pack $ take 1000000 $ randoms (mkStdGen 44)

-- | Generate n unique bytestrings
generateContents :: Int -> [ByteString]
generateContents n = 
  [ BS.pack $ take 100 $ randoms (mkStdGen (1000 + i))
  | i <- [0..n-1]
  ]

--------------------------------------------------------------------------------
-- HAMT Builders
--------------------------------------------------------------------------------

-- | Build a HAMT with n entries
buildHAMT :: Int -> IO (HAMT ByteString)
buildHAMT n = pure $ buildHAMTForce n

buildHAMTForce :: Int -> HAMT ByteString
buildHAMTForce n = foldr insert empty (generateContents n)

-- | Build a HAMT with n entries and return one key
buildHAMTWithKey :: Int -> IO (HAMT ByteString, StorageKey)
buildHAMTWithKey n = do
  let contents = generateContents n
      h = foldr insert empty contents
      -- Get the key for the first content
      k = mkStorageKey (Prelude.head contents)
  pure (h, k)

-- | Check structure sharing: inserting new content shouldn't duplicate old
checkSharing :: HAMT ByteString -> ByteString -> Int
checkSharing h content = 
  let h' = insert content h
  in size h'  -- Force evaluation
