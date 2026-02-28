{- |
Module      : Main
Description : Test suite entry point
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

NORMAN STANSFIELD ENERGY - EVERYONE GETS TESTED.
-}
module Main (main) where

import Test.Foundry.Core.Agent qualified as Agent
import Test.Foundry.Core.Agent.Allocation qualified as Allocation
import Test.Foundry.Core.Brand qualified as Brand
import Test.Foundry.Core.Brand.Tagline qualified as Tagline
import Test.Foundry.Core.Brand.Editorial qualified as Editorial
import Test.Foundry.Core.Brand.Strategy qualified as Strategy
import Test.Foundry.Core.Brand.Security qualified as Security
import Test.Foundry.Core.Brand.UIElements qualified as UIElements
import Test.Foundry.Core.Brand.GraphicElements qualified as GraphicElements
import Test.Foundry.Core.Effect qualified as Effect
import Test.Tasty (defaultMain, testGroup)

main :: IO ()
main =
  defaultMain $
    testGroup
      "foundry-core"
      [ Agent.tests
      , Allocation.tests
      , Brand.tests
      , Tagline.tests
      , Editorial.tests
      , Strategy.tests
      , Security.tests
      , UIElements.tests
      , GraphicElements.tests
      , Effect.tests
      ]
