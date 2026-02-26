{- |
Module      : Test.Foundry.Extract.Color
Description : Property tests for color extraction
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause
-}
module Test.Foundry.Extract.Color (tests) where

import Data.Text (Text, pack)
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Foundry.Extract.Color.CSS (OKLCH' (..), RGB (..), parseColorText, rgbToOKLCH)
import Foundry.Extract.Color.Cluster (oklchDistance)

tests :: TestTree
tests = testGroup "Color"
  [ testProperty "RGB to OKLCH preserves bounds" prop_rgbToOKLCH_bounds
  , testProperty "OKLCH distance is symmetric" prop_oklchDistance_symmetric
  , testProperty "OKLCH distance is non-negative" prop_oklchDistance_nonnegative
  , testProperty "Hex color parsing roundtrips" prop_hexColor_parse
  ]

-- | OKLCH lightness is always in [0, 1]
prop_rgbToOKLCH_bounds :: Property
prop_rgbToOKLCH_bounds = property $ do
  r <- forAll $ Gen.double (Range.constant 0 255)
  g <- forAll $ Gen.double (Range.constant 0 255)
  b <- forAll $ Gen.double (Range.constant 0 255)
  let oklch = rgbToOKLCH (RGB r g b 1.0)
  assert $ oklchL' oklch >= 0 && oklchL' oklch <= 1

-- | Distance is symmetric: d(a, b) = d(b, a)
prop_oklchDistance_symmetric :: Property
prop_oklchDistance_symmetric = property $ do
  c1 <- forAll genOKLCH
  c2 <- forAll genOKLCH
  oklchDistance c1 c2 === oklchDistance c2 c1

-- | Distance is non-negative
prop_oklchDistance_nonnegative :: Property
prop_oklchDistance_nonnegative = property $ do
  c1 <- forAll genOKLCH
  c2 <- forAll genOKLCH
  assert $ oklchDistance c1 c2 >= 0

-- | Hex colors can be parsed
prop_hexColor_parse :: Property
prop_hexColor_parse = property $ do
  r <- forAll $ Gen.int (Range.constant 0 255)
  g <- forAll $ Gen.int (Range.constant 0 255)
  b <- forAll $ Gen.int (Range.constant 0 255)
  let hex = "#" <> toHex r <> toHex g <> toHex b
  case parseColorText hex of
    Nothing -> failure
    Just _  -> success

toHex :: Int -> Text
toHex n = 
  let hexChars = "0123456789abcdef"
      hi = (n `div` 16) `mod` 16
      lo = n `mod` 16
  in pack [hexChars !! hi, hexChars !! lo]

genOKLCH :: Gen OKLCH'
genOKLCH = OKLCH'
  <$> Gen.double (Range.constant 0 1)
  <*> Gen.double (Range.constant 0 0.4)
  <*> Gen.double (Range.constant 0 360)
  <*> pure 1.0
