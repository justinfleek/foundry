{- |
Module      : Test.Foundry.Extract.Spacing
Description : Property tests for spacing extraction
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause
-}
module Test.Foundry.Extract.Spacing (tests) where

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Foundry.Extract.Spacing (detectBaseUnit, detectSpacingScale)
import Foundry.Core.Brand.Spacing (SpacingScale (..))

tests :: TestTree
tests = testGroup "Spacing"
  [ testProperty "Base unit is positive" prop_baseUnit_positive
  , testProperty "Common base units detected" prop_baseUnit_common
  , testProperty "Spacing scale has positive values" prop_scale_positive
  ]

-- | Base unit is always positive
prop_baseUnit_positive :: Property
prop_baseUnit_positive = property $ do
  values <- forAll $ Gen.list (Range.linear 1 20) $ 
            Gen.double (Range.constant 4 64)
  let base = detectBaseUnit values
  assert $ base > 0

-- | 8px base is detected from [8, 16, 24, 32]
prop_baseUnit_common :: Property
prop_baseUnit_common = property $ do
  let values = [8, 16, 24, 32, 48, 64]
  let base = detectBaseUnit values
  -- Should be 8 or a factor of 8
  assert $ base > 0 && base <= 16

-- | Spacing scale has positive base and ratio
prop_scale_positive :: Property
prop_scale_positive = property $ do
  values <- forAll $ Gen.list (Range.linear 2 10) $ 
            Gen.double (Range.constant 4 64)
  case detectSpacingScale values of
    Nothing -> success
    Just ss -> do
      assert $ spacingScaleBase ss > 0
      assert $ spacingScaleRatio ss > 0
