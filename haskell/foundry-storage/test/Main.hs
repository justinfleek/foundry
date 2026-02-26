{- |
Module      : Main
Description : Test suite entry point for foundry-storage
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause
-}
module Main (main) where

import Test.Foundry.Storage.HAMT qualified as HAMT
import Test.Tasty (defaultMain, testGroup)

main :: IO ()
main =
  defaultMain $
    testGroup
      "foundry-storage"
      [ HAMT.tests
      ]
