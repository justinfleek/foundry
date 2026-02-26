{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // foundry // extract // test
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Main
Description : Test suite entry point
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Main (main) where

import Test.Tasty (TestTree, defaultMain, testGroup)

import Test.Foundry.Extract.Color qualified as Color
import Test.Foundry.Extract.Compose qualified as Compose
import Test.Foundry.Extract.Spacing qualified as Spacing
import Test.Foundry.Extract.Typography qualified as Typography
import Test.Foundry.Extract.Voice qualified as Voice

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "foundry-extract"
  [ Color.tests
  , Typography.tests
  , Spacing.tests
  , Voice.tests
  , Compose.tests
  ]
