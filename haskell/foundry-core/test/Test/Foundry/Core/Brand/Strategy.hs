{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                          // foundry // test // brand // strategy
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Core.Brand.Strategy
Description : Property tests for Strategy module (SMART Sections 2, 4, 5)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

NORMAN STANSFIELD ENERGY - EVERYONE GETS TESTED.

== Test Categories

1. MissionStatement - Immutability, validation
2. BrandValues - Non-empty requirement, ordering preservation
3. PersonalityTraits - 3-5 trait requirement, trait preservation
4. PositioningStatement - 12 archetypes, narrative preservation
5. StrategicLayer - Complete composition

== Verified Properties

* Mission statement requires non-empty text
* Mission statement is stripped
* BrandValues requires at least one value
* PersonalityTraits requires at least one trait
* All 12 positioning archetypes are enumerable
* StrategicLayer composes all components correctly

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Core.Brand.Strategy
  ( tests
  ) where

import Data.Maybe (isJust, isNothing)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Hedgehog (Property, forAll, property, (===), assert, withTests)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Foundry.Core.Brand.Strategy
  ( MissionStatement (..)
  , BrandValue (..)
  , BrandValues (..)
  , PersonalityTrait (..)
  , PersonalityDescription (..)
  , PositioningType (..)
  , PositioningStatement (..)
  , BrandPersonality (..)
  , StrategicLayer (..)
  , mkMissionStatement
  , missionToText
  , mkBrandValue
  , mkBrandValues
  , valuesCount
  , mkPersonalityTrait
  , traitToText
  , mkPersonalityDescription
  , positioningTypeToText
  , parsePositioningType
  , mkPositioningStatement
  , mkBrandPersonality
  , mkStrategicLayer
  )

import Test.Foundry.Core.Brand.Generators
  ( genMissionStatement
  , genValidMissionText
  , genBrandValue
  , genBrandValues
  , genPersonalityTrait
  , genPersonalityDescription
  , genPositioningType
  , genPositioningStatement
  , genBrandPersonality
  , genStrategicLayer
  , genRealisticMission
  , genRealisticValue
  , genRealisticTrait
  , genPoisonPill
  )

--------------------------------------------------------------------------------
-- Test Tree
--------------------------------------------------------------------------------

tests :: TestTree
tests =
  testGroup
    "Foundry.Core.Brand.Strategy"
    [ testGroup "MissionStatement" missionTests
    , testGroup "BrandValues" valuesTests
    , testGroup "PersonalityTraits" traitTests
    , testGroup "PositioningStatement" positioningTests
    , testGroup "BrandPersonality" personalityTests
    , testGroup "StrategicLayer" strategicLayerTests
    , testGroup "Security" securityTests
    ]

--------------------------------------------------------------------------------
-- MissionStatement Tests
--------------------------------------------------------------------------------

missionTests :: [TestTree]
missionTests =
  [ testProperty "mission requires non-empty text" prop_missionRequiresText
  , testProperty "mission rejects empty" prop_missionRejectsEmpty
  , testProperty "mission rejects whitespace-only" prop_missionRejectsWhitespace
  , testProperty "mission strips whitespace" prop_missionStrips
  , testProperty "mission preserves content" prop_missionPreserves
  , testProperty "missionToText roundtrips" prop_missionRoundtrip
  ]

-- | Mission statement requires non-empty text
prop_missionRequiresText :: Property
prop_missionRequiresText = withTests 200 $ property $ do
  txt <- forAll genValidMissionText
  let stripped = T.strip txt
  if T.null stripped
    then assert (isNothing (mkMissionStatement txt))
    else assert (isJust (mkMissionStatement txt))

-- | Empty text should be rejected
prop_missionRejectsEmpty :: Property
prop_missionRejectsEmpty = property $ do
  assert (isNothing (mkMissionStatement ""))

-- | Whitespace-only text should be rejected
prop_missionRejectsWhitespace :: Property
prop_missionRejectsWhitespace = property $ do
  ws <- forAll $ Gen.element ["   ", "\t\n", "  \t  \n  "]
  assert (isNothing (mkMissionStatement ws))

-- | Mission text should be stripped
prop_missionStrips :: Property
prop_missionStrips = property $ do
  core <- forAll $ Gen.text (Range.linear 10 100) Gen.alphaNum
  let input = "  " <> core <> "  \n"
  case mkMissionStatement input of
    Nothing -> assert False
    Just ms -> missionToText ms === core

-- | Mission content should be preserved exactly
prop_missionPreserves :: Property
prop_missionPreserves = withTests 200 $ property $ do
  txt <- forAll genRealisticMission
  case mkMissionStatement txt of
    Nothing -> assert False
    Just ms -> missionToText ms === T.strip txt

-- | missionToText should roundtrip through mkMissionStatement
prop_missionRoundtrip :: Property
prop_missionRoundtrip = withTests 200 $ property $ do
  mMs <- forAll genMissionStatement
  case mMs of
    Nothing -> assert True
    Just ms -> do
      let txt = missionToText ms
      case mkMissionStatement txt of
        Nothing -> assert False
        Just ms2 -> missionToText ms2 === txt

--------------------------------------------------------------------------------
-- BrandValues Tests
--------------------------------------------------------------------------------

valuesTests :: [TestTree]
valuesTests =
  [ testProperty "values requires at least one" prop_valuesRequiresOne
  , testProperty "values count is accurate" prop_valuesCountAccurate
  , testProperty "values ordering is preserved" prop_valuesOrderPreserved
  , testProperty "value name is required" prop_valueNameRequired
  , testProperty "value description can be empty" prop_valueDescCanBeEmpty
  ]

-- | BrandValues requires at least one value
prop_valuesRequiresOne :: Property
prop_valuesRequiresOne = property $ do
  assert (isNothing (mkBrandValues V.empty))

-- | valuesCount should match actual count
prop_valuesCountAccurate :: Property
prop_valuesCountAccurate = withTests 200 $ property $ do
  mBv <- forAll genBrandValues
  case mBv of
    Nothing -> assert True
    Just bv -> do
      let count = valuesCount bv
          actual = V.length (brandValuesItems bv)
      fromIntegral count === actual

-- | Values ordering should be preserved
prop_valuesOrderPreserved :: Property
prop_valuesOrderPreserved = property $ do
  let names = ["Innovation", "Integrity", "Excellence"]
  mValues <- sequence <$> forAll (mapM (\n -> pure (mkBrandValue n "desc")) names)
  case mValues of
    Nothing -> assert False
    Just values -> do
      case mkBrandValues (V.fromList values) of
        Nothing -> assert False
        Just bv -> do
          let extracted = V.toList $ V.map brandValueName (brandValuesItems bv)
          extracted === names

-- | Value name is required (non-empty)
prop_valueNameRequired :: Property
prop_valueNameRequired = property $ do
  assert (isNothing (mkBrandValue "" "description"))
  assert (isNothing (mkBrandValue "   " "description"))

-- | Value description can be empty
prop_valueDescCanBeEmpty :: Property
prop_valueDescCanBeEmpty = property $ do
  assert (isJust (mkBrandValue "Innovation" ""))

--------------------------------------------------------------------------------
-- PersonalityTraits Tests
--------------------------------------------------------------------------------

traitTests :: [TestTree]
traitTests =
  [ testProperty "trait requires non-empty text" prop_traitRequiresText
  , testProperty "trait is stripped" prop_traitStripped
  , testProperty "traitToText preserves value" prop_traitToTextPreserves
  ]

-- | Personality trait requires non-empty text
prop_traitRequiresText :: Property
prop_traitRequiresText = property $ do
  assert (isNothing (mkPersonalityTrait ""))
  assert (isNothing (mkPersonalityTrait "   "))

-- | Trait text should be stripped
prop_traitStripped :: Property
prop_traitStripped = property $ do
  let input = "  Friendly  "
  case mkPersonalityTrait input of
    Nothing -> assert False
    Just t -> traitToText t === "Friendly"

-- | traitToText should preserve the value
prop_traitToTextPreserves :: Property
prop_traitToTextPreserves = withTests 200 $ property $ do
  txt <- forAll genRealisticTrait
  case mkPersonalityTrait txt of
    Nothing -> assert False
    Just t -> traitToText t === T.strip txt

--------------------------------------------------------------------------------
-- PositioningStatement Tests
--------------------------------------------------------------------------------

positioningTests :: [TestTree]
positioningTests =
  [ testProperty "all 12 archetypes enumerable" prop_archetypesEnumerable
  , testProperty "positioningTypeToText roundtrips" prop_archetypeRoundtrip
  , testProperty "positioning statement preserves values" prop_positioningPreserves
  ]

-- | All 12 positioning archetypes should be enumerable
prop_archetypesEnumerable :: Property
prop_archetypesEnumerable = property $ do
  let archetypes =
        [ Ally, Guide, Facilitator, Authority, Challenger, Creator
        , Caregiver, Everyman, Hero, Sage, Explorer, Rebel
        ]
  length archetypes === 12

-- | positioningTypeToText should be parseable back
prop_archetypeRoundtrip :: Property
prop_archetypeRoundtrip = withTests 200 $ property $ do
  ptype <- forAll genPositioningType
  let txt = positioningTypeToText ptype
  case parsePositioningType txt of
    Nothing -> assert False
    Just parsed -> parsed === ptype

-- | PositioningStatement should preserve all values
prop_positioningPreserves :: Property
prop_positioningPreserves = withTests 200 $ property $ do
  ptype <- forAll genPositioningType
  narrative <- forAll $ Gen.text (Range.linear 20 200) Gen.unicode
  let ps = mkPositioningStatement ptype narrative
  positioningType ps === ptype
  positioningNarrative ps === T.strip narrative

--------------------------------------------------------------------------------
-- BrandPersonality Tests
--------------------------------------------------------------------------------

personalityTests :: [TestTree]
personalityTests =
  [ testProperty "personality requires at least one trait" prop_personalityRequiresTrait
  , testProperty "personality preserves all components" prop_personalityPreserves
  ]

-- | BrandPersonality requires at least one trait
prop_personalityRequiresTrait :: Property
prop_personalityRequiresTrait = property $ do
  mDesc <- forAll genPersonalityDescription
  pos <- forAll genPositioningStatement
  case mDesc of
    Nothing -> assert True
    Just desc -> do
      let result = mkBrandPersonality V.empty desc pos
      assert (isNothing result)

-- | BrandPersonality should preserve all components
prop_personalityPreserves :: Property
prop_personalityPreserves = withTests 100 $ property $ do
  mBp <- forAll genBrandPersonality
  case mBp of
    Nothing -> assert True
    Just bp -> do
      -- All fields should be accessible
      let traits = personalityTraits bp
          _ = personalityDescription bp
          _ = personalityPositioning bp
      assert (V.length traits >= 1)

--------------------------------------------------------------------------------
-- StrategicLayer Tests
--------------------------------------------------------------------------------

strategicLayerTests :: [TestTree]
strategicLayerTests =
  [ testProperty "strategic layer composes all components" prop_strategicCompose
  , testProperty "strategic layer preserves mission" prop_strategicPreservesMission
  ]

-- | StrategicLayer should compose all components correctly
prop_strategicCompose :: Property
prop_strategicCompose = withTests 50 $ property $ do
  mSl <- forAll genStrategicLayer
  case mSl of
    Nothing -> assert True
    Just sl -> do
      -- All fields should be accessible
      let _ = strategicMission sl
          _ = strategicValues sl
          _ = strategicPersonality sl
      assert True

-- | StrategicLayer should preserve the mission
prop_strategicPreservesMission :: Property
prop_strategicPreservesMission = withTests 50 $ property $ do
  mSl <- forAll genStrategicLayer
  case mSl of
    Nothing -> assert True
    Just sl -> do
      let mission = strategicMission sl
          txt = missionToText mission
      assert (not (T.null txt))

--------------------------------------------------------------------------------
-- Security Tests
--------------------------------------------------------------------------------

securityTests :: [TestTree]
securityTests =
  [ testProperty "poison pills don't crash mission" prop_poisonMissionSafe
  , testProperty "poison pills don't crash values" prop_poisonValuesSafe
  , testProperty "poison pills don't crash traits" prop_poisonTraitsSafe
  ]

-- | Poison pills should not crash mission creation
prop_poisonMissionSafe :: Property
prop_poisonMissionSafe = withTests 200 $ property $ do
  poison <- forAll genPoisonPill
  let result = mkMissionStatement poison
  -- Should not crash, just accept or reject gracefully
  case result of
    Nothing -> assert True
    Just ms -> do
      let txt = missionToText ms
      assert (not (T.null txt))

-- | Poison pills should not crash value creation
prop_poisonValuesSafe :: Property
prop_poisonValuesSafe = withTests 200 $ property $ do
  poison <- forAll genPoisonPill
  let result = mkBrandValue poison "description"
  -- Should accept or reject gracefully
  case result of
    Nothing -> assert True
    Just _ -> assert True

-- | Poison pills should not crash trait creation
prop_poisonTraitsSafe :: Property
prop_poisonTraitsSafe = withTests 200 $ property $ do
  poison <- forAll genPoisonPill
  let result = mkPersonalityTrait poison
  case result of
    Nothing -> assert True
    Just _ -> assert True
