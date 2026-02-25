{- |
Module      : Main
Description : Test suite entry point
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause
-}
module Main (main) where

import Test.Tasty (defaultMain, testGroup)

main :: IO ()
main =
  defaultMain $
    testGroup
      "metxt-core"
      [ -- Test.Metxt.Core.Agent.tests
        -- Test.Metxt.Core.Brand.tests
        -- Test.Metxt.Core.Effect.tests
      ]
