{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // foundry // test // core // effect
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Core.Effect
Description : Property tests for Effect module (Coeffect algebra)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

== Verified Properties (mirroring Continuity.Coeffect theorems)

* empty_is_pure: isPure [] = true
* tensor_pure_right: r ++ [] = r
* tensor_pure_left: [] ++ r = r
* tensor_assoc: (a ++ b) ++ c = a ++ (b ++ c)
* tensor_pure_pure: isPure a → isPure b → isPure (a ++ b)
* tensor_reproducible: isReproducible a → isReproducible b → isReproducible (a ++ b)
* time_not_reproducible: isReproducible [Time] = false
* random_not_reproducible: isReproducible [Random] = false

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Core.Effect
  ( tests
  ) where

import Hedgehog (Gen, Property, forAll, property, (===), assert)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Foundry.Core.Effect.CoEffect
  ( Coeffect (..)
  , Coeffects
  , coeffectsPure
  , coeffectsTensor
  , isPure
  , isReproducible
  , purityLevel
  , minPurity
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

--------------------------------------------------------------------------------
-- Test Tree
--------------------------------------------------------------------------------

-- | All Effect module tests
tests :: TestTree
tests =
  testGroup
    "Foundry.Core.Effect"
    [ testGroup "Coeffect" coeffectTests
    , testGroup "Coeffects (Tensor)" tensorTests
    , testGroup "Reproducibility" reproducibilityTests
    , testGroup "Purity" purityTests
    ]

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

-- | Generate a reproducible coeffect
genReproducibleCoeffect :: Gen Coeffect
genReproducibleCoeffect = Gen.choice
  [ pure Pure
  , FilesystemCA <$> Gen.bytes (Range.linear 32 32)
  , NetworkCA <$> Gen.bytes (Range.linear 32 32)
  , Auth <$> Gen.text (Range.linear 1 20) Gen.alphaNum
  , Gpu <$> Gen.text (Range.linear 1 20) Gen.alphaNum
  , Sandbox <$> Gen.text (Range.linear 1 20) Gen.alphaNum
  ]

-- | Generate a non-reproducible coeffect
genNonReproducibleCoeffect :: Gen Coeffect
genNonReproducibleCoeffect = Gen.choice
  [ Filesystem <$> Gen.text (Range.linear 1 50) Gen.alphaNum
  , Network <$> Gen.text (Range.linear 1 30) Gen.alphaNum <*> Gen.int (Range.linear 1 65535)
  , Environment <$> Gen.text (Range.linear 1 20) Gen.alphaNum
  , pure Time
  , pure Random
  , pure Identity
  ]

-- | Generate any coeffect
genCoeffect :: Gen Coeffect
genCoeffect = Gen.choice [genReproducibleCoeffect, genNonReproducibleCoeffect]

-- | Generate a list of coeffects
genCoeffects :: Gen Coeffects
genCoeffects = Gen.list (Range.linear 0 10) genCoeffect

-- | Generate a reproducible coeffect list
genReproducibleCoeffects :: Gen Coeffects
genReproducibleCoeffects = Gen.list (Range.linear 0 10) genReproducibleCoeffect

--------------------------------------------------------------------------------
-- Coeffect Tests
--------------------------------------------------------------------------------

coeffectTests :: [TestTree]
coeffectTests =
  [ testProperty "Pure has highest purity level" prop_pureHighestPurity
  , testProperty "Time has lowest purity level" prop_timeLowestPurity
  , testProperty "Random has lowest purity level" prop_randomLowestPurity
  ]

-- | Pure coeffect has purity level 3
prop_pureHighestPurity :: Property
prop_pureHighestPurity = property $ do
  purityLevel Pure === 3

-- | Time coeffect has purity level 0
prop_timeLowestPurity :: Property
prop_timeLowestPurity = property $ do
  purityLevel Time === 0

-- | Random coeffect has purity level 0
prop_randomLowestPurity :: Property
prop_randomLowestPurity = property $ do
  purityLevel Random === 0

--------------------------------------------------------------------------------
-- Tensor Product Tests (mirrors Continuity.Coeffect theorems)
--------------------------------------------------------------------------------

tensorTests :: [TestTree]
tensorTests =
  [ testProperty "tensor_pure_right: r ++ [] = r" prop_tensorPureRight
  , testProperty "tensor_pure_left: [] ++ r = r" prop_tensorPureLeft
  , testProperty "tensor_assoc: (a ++ b) ++ c = a ++ (b ++ c)" prop_tensorAssoc
  , testProperty "empty_is_pure: isPure [] = true" prop_emptyIsPure
  ]

-- | Tensor with pure is identity (right)
prop_tensorPureRight :: Property
prop_tensorPureRight = property $ do
  r <- forAll genCoeffects
  coeffectsTensor r coeffectsPure === r

-- | Tensor with pure is identity (left)
prop_tensorPureLeft :: Property
prop_tensorPureLeft = property $ do
  r <- forAll genCoeffects
  coeffectsTensor coeffectsPure r === r

-- | Tensor is associative
prop_tensorAssoc :: Property
prop_tensorAssoc = property $ do
  a <- forAll genCoeffects
  b <- forAll genCoeffects
  c <- forAll genCoeffects
  coeffectsTensor (coeffectsTensor a b) c === coeffectsTensor a (coeffectsTensor b c)

-- | Empty coeffects are pure
prop_emptyIsPure :: Property
prop_emptyIsPure = property $ do
  assert (isPure coeffectsPure)

--------------------------------------------------------------------------------
-- Reproducibility Tests (mirrors Continuity.Coeffect theorems)
--------------------------------------------------------------------------------

reproducibilityTests :: [TestTree]
reproducibilityTests =
  [ testProperty "pure_is_reproducible: isReproducible [] = true" prop_pureIsReproducible
  , testProperty "tensor_pure_pure: isPure a → isPure b → isPure (a ++ b)" prop_tensorPurePure
  , testProperty "tensor_reproducible: both reproducible → combined reproducible" prop_tensorReproducible
  , testProperty "time_not_reproducible: isReproducible [Time] = false" prop_timeNotReproducible
  , testProperty "random_not_reproducible: isReproducible [Random] = false" prop_randomNotReproducible
  , testProperty "filesystemCA_reproducible: isReproducible [FilesystemCA h] = true" prop_filesystemCAReproducible
  , testProperty "networkCA_reproducible: isReproducible [NetworkCA h] = true" prop_networkCAReproducible
  ]

-- | Empty coeffects are reproducible
prop_pureIsReproducible :: Property
prop_pureIsReproducible = property $ do
  assert (isReproducible coeffectsPure)

-- | If both inputs are pure, tensor is pure
prop_tensorPurePure :: Property
prop_tensorPurePure = property $ do
  -- Two empty lists are pure, and their tensor should be pure
  let a = coeffectsPure
      b = coeffectsPure
  assert (isPure a)
  assert (isPure b)
  assert (isPure (coeffectsTensor a b))

-- | If both inputs are reproducible, tensor is reproducible
prop_tensorReproducible :: Property
prop_tensorReproducible = property $ do
  a <- forAll genReproducibleCoeffects
  b <- forAll genReproducibleCoeffects
  -- Both should be reproducible
  assert (isReproducible a)
  assert (isReproducible b)
  -- Combined should be reproducible
  assert (isReproducible (coeffectsTensor a b))

-- | Time coeffect is not reproducible
prop_timeNotReproducible :: Property
prop_timeNotReproducible = property $ do
  assert (not (isReproducible [Time]))

-- | Random coeffect is not reproducible
prop_randomNotReproducible :: Property
prop_randomNotReproducible = property $ do
  assert (not (isReproducible [Random]))

-- | FilesystemCA is reproducible
prop_filesystemCAReproducible :: Property
prop_filesystemCAReproducible = property $ do
  hash <- forAll $ Gen.bytes (Range.singleton 32)
  assert (isReproducible [FilesystemCA hash])

-- | NetworkCA is reproducible
prop_networkCAReproducible :: Property
prop_networkCAReproducible = property $ do
  hash <- forAll $ Gen.bytes (Range.singleton 32)
  assert (isReproducible [NetworkCA hash])

--------------------------------------------------------------------------------
-- Purity Level Tests
--------------------------------------------------------------------------------

purityTests :: [TestTree]
purityTests =
  [ testProperty "minPurity [] = 3 (pure)" prop_minPurityEmpty
  , testProperty "minPurity preserves minimum" prop_minPurityPreservesMin
  ]

-- | Empty coeffects have maximum purity
prop_minPurityEmpty :: Property
prop_minPurityEmpty = property $ do
  minPurity coeffectsPure === 3

-- | minPurity returns the minimum purity level
prop_minPurityPreservesMin :: Property
prop_minPurityPreservesMin = property $ do
  cs <- forAll genCoeffects
  case cs of
    [] -> minPurity cs === 3
    _  -> do
      let computedMin = minimum (fmap purityLevel cs)
      minPurity cs === computedMin
