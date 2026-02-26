{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // foundry // test // core // brand
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Core.Brand
Description : Property tests for Brand types (Palette, Typography, etc.)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

== Verified Properties

* OKLCH invariants: L ∈ [0,1], C ∈ [0,0.4], H ∈ [0,360)
* mkOKLCH validates all constraints
* Color roles are bounded and enumerable

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Core.Brand
  ( tests
  ) where

import Hedgehog (Gen, Property, forAll, property, (===), assert)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Foundry.Core.Brand.Palette
  ( OKLCH (..)
  , ColorRole (..)
  , mkOKLCH
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

--------------------------------------------------------------------------------
-- Test Tree
--------------------------------------------------------------------------------

-- | All Brand module tests
tests :: TestTree
tests =
  testGroup
    "Foundry.Core.Brand"
    [ testGroup "OKLCH" oklchTests
    , testGroup "ColorRole" colorRoleTests
    ]

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

-- | Generate a valid lightness value [0, 1]
genLightness :: Gen Double
genLightness = Gen.double (Range.linearFrac 0.0 1.0)

-- | Generate a valid chroma value [0, 0.4]
genChroma :: Gen Double
genChroma = Gen.double (Range.linearFrac 0.0 0.4)

-- | Generate a valid hue value [0, 360)
genHue :: Gen Double
genHue = Gen.double (Range.linearFrac 0.0 359.999)

-- | Generate an invalid lightness (outside [0, 1])
genInvalidLightness :: Gen Double
genInvalidLightness = Gen.choice
  [ Gen.double (Range.linearFrac (-10.0) (-0.001))
  , Gen.double (Range.linearFrac 1.001 10.0)
  ]

-- | Generate an invalid chroma (outside [0, 0.4])
genInvalidChroma :: Gen Double
genInvalidChroma = Gen.choice
  [ Gen.double (Range.linearFrac (-10.0) (-0.001))
  , Gen.double (Range.linearFrac 0.401 10.0)
  ]

-- | Generate an invalid hue (outside [0, 360))
genInvalidHue :: Gen Double
genInvalidHue = Gen.choice
  [ Gen.double (Range.linearFrac (-360.0) (-0.001))
  , Gen.double (Range.linearFrac 360.0 720.0)
  ]

-- | Generate an arbitrary ColorRole
genColorRole :: Gen ColorRole
genColorRole = Gen.enumBounded

--------------------------------------------------------------------------------
-- OKLCH Tests
--------------------------------------------------------------------------------

oklchTests :: [TestTree]
oklchTests =
  [ testProperty "valid inputs create OKLCH" prop_validInputsCreateOKLCH
  , testProperty "invalid lightness rejected" prop_invalidLightnessRejected
  , testProperty "invalid chroma rejected" prop_invalidChromaRejected
  , testProperty "invalid hue rejected" prop_invalidHueRejected
  , testProperty "mkOKLCH preserves values" prop_mkOKLCHPreservesValues
  , testProperty "boundary values accepted" prop_boundaryValuesAccepted
  ]

-- | Valid inputs should create a Just OKLCH
prop_validInputsCreateOKLCH :: Property
prop_validInputsCreateOKLCH = property $ do
  l <- forAll genLightness
  c <- forAll genChroma
  h <- forAll genHue
  case mkOKLCH l c h of
    Nothing -> assert False  -- Should succeed
    Just _  -> assert True

-- | Invalid lightness should be rejected
prop_invalidLightnessRejected :: Property
prop_invalidLightnessRejected = property $ do
  l <- forAll genInvalidLightness
  c <- forAll genChroma
  h <- forAll genHue
  case mkOKLCH l c h of
    Nothing -> assert True
    Just _  -> assert False

-- | Invalid chroma should be rejected
prop_invalidChromaRejected :: Property
prop_invalidChromaRejected = property $ do
  l <- forAll genLightness
  c <- forAll genInvalidChroma
  h <- forAll genHue
  case mkOKLCH l c h of
    Nothing -> assert True
    Just _  -> assert False

-- | Invalid hue should be rejected
prop_invalidHueRejected :: Property
prop_invalidHueRejected = property $ do
  l <- forAll genLightness
  c <- forAll genChroma
  h <- forAll genInvalidHue
  case mkOKLCH l c h of
    Nothing -> assert True
    Just _  -> assert False

-- | mkOKLCH should preserve input values exactly
prop_mkOKLCHPreservesValues :: Property
prop_mkOKLCHPreservesValues = property $ do
  l <- forAll genLightness
  c <- forAll genChroma
  h <- forAll genHue
  case mkOKLCH l c h of
    Nothing -> assert False
    Just oklch -> do
      oklchL oklch === l
      oklchC oklch === c
      oklchH oklch === h

-- | Boundary values should be accepted
prop_boundaryValuesAccepted :: Property
prop_boundaryValuesAccepted = property $ do
  -- Test exact boundaries
  case mkOKLCH 0.0 0.0 0.0 of
    Nothing -> assert False
    Just _  -> assert True
  case mkOKLCH 1.0 0.4 359.0 of
    Nothing -> assert False
    Just _  -> assert True
  -- Hue 360 should be rejected (it's [0, 360))
  case mkOKLCH 0.5 0.2 360.0 of
    Nothing -> assert True
    Just _  -> assert False

--------------------------------------------------------------------------------
-- ColorRole Tests
--------------------------------------------------------------------------------

colorRoleTests :: [TestTree]
colorRoleTests =
  [ testProperty "all roles enumerable" prop_allRolesEnumerable
  , testProperty "roles have stable ordering" prop_rolesStableOrdering
  ]

-- | All color roles should be enumerable
prop_allRolesEnumerable :: Property
prop_allRolesEnumerable = property $ do
  let allRoles = [minBound .. maxBound] :: [ColorRole]
  -- There should be exactly 10 color roles as defined in the type
  length allRoles === 10

-- | ColorRole ordering should be stable (Ord instance)
prop_rolesStableOrdering :: Property
prop_rolesStableOrdering = property $ do
  r1 <- forAll genColorRole
  r2 <- forAll genColorRole
  -- Ord should be reflexive
  assert (r1 <= r1)
  -- If r1 <= r2 and r2 <= r1 then r1 == r2 (antisymmetry)
  case (compare r1 r2, compare r2 r1) of
    (LT, GT) -> assert True
    (GT, LT) -> assert True
    (EQ, EQ) -> assert (r1 == r2)
    _        -> assert True  -- Other cases are valid
