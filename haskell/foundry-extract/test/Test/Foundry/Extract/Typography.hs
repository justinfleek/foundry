{- |
Module      : Test.Foundry.Extract.Typography
Description : Property tests for typography extraction
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause
-}
module Test.Foundry.Extract.Typography (tests) where

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Foundry.Extract.Typography.Scale (detectScaleFromSizes, DetectedScale (..))

tests :: TestTree
tests = testGroup "Typography"
  [ testProperty "Scale detection produces positive base" prop_scale_positiveBase
  , testProperty "Scale detection produces positive ratio" prop_scale_positiveRatio
  , testProperty "Common ratios are detected" prop_scale_commonRatios
  ]

-- | Base size is always positive
prop_scale_positiveBase :: Property
prop_scale_positiveBase = property $ do
  sizes <- forAll $ Gen.list (Range.linear 2 10) $ 
           Gen.double (Range.constant 8 72)
  case detectScaleFromSizes sizes of
    Nothing -> success  -- Not enough data is fine
    Just ds -> assert $ dsBaseSize ds > 0

-- | Ratio is always positive
prop_scale_positiveRatio :: Property
prop_scale_positiveRatio = property $ do
  sizes <- forAll $ Gen.list (Range.linear 2 10) $ 
           Gen.double (Range.constant 8 72)
  case detectScaleFromSizes sizes of
    Nothing -> success
    Just ds -> assert $ dsRatio ds > 0

-- | Major third (1.25) is detected from 16, 20, 25, 31.25
prop_scale_commonRatios :: Property
prop_scale_commonRatios = property $ do
  let majorThirdSizes = [16, 20, 25, 31.25] :: [Double]
  case detectScaleFromSizes majorThirdSizes of
    Nothing -> failure
    Just ds -> do
      -- Ratio should be close to 1.25
      let ratio = dsRatio ds
          expected = 1.25 :: Double
      assert (abs (ratio - expected) < 0.1)
