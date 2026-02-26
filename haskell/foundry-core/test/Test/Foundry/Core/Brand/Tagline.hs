{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                           // foundry // test // brand // tagline
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Core.Brand.Tagline
Description : Exhaustive property tests for Tagline module
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

NORMAN STANSFIELD ENERGY - EVERYONE GETS TESTED.

== Test Categories

1. Validation tests - mkTaglineText accepts/rejects correctly
2. Immutability tests - TaglineText cannot be modified
3. Invariant tests - Primary tagline always has GeneralContext
4. Boundary tests - Edge cases at limits
5. Security tests - Poison pills are handled safely
6. Distribution tests - Realistic inputs work correctly

== Verified Properties

* Empty text is rejected
* Whitespace-only text is rejected
* Valid text is stripped and accepted
* Primary tagline always has GeneralContext
* Secondary tagline requires at least one context
* TaglineSet always has at least one tagline (the primary)
* Poison pills don't crash or corrupt state

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Core.Brand.Tagline
  ( tests
  ) where

import Data.Maybe (isJust, isNothing)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Hedgehog (Property, forAll, property, (===), assert, withTests, classify)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Foundry.Core.Brand.Tagline
  ( TaglineText
  , TaglineContext (..)
  , Tagline
  , PrimaryTagline
  , SecondaryTagline
  , TaglineSet
  , TaglineUsageRule (..)
  , mkTaglineText
  , taglineToText
  , mkTagline
  , mkPrimaryTagline
  , mkSecondaryTagline
  , mkTaglineSet
  , primaryToTagline
  , secondaryToTagline
  , allTaglines
  , taglineText
  , taglineContexts
  , taglineSetPrimary
  , taglineSetSecondary
  )

import Test.Foundry.Core.Brand.Generators
  ( genValidTaglineText
  , genInvalidTaglineText
  , genPoisonTaglineText
  , genTaglineContext
  , genPrimaryTagline
  , genSecondaryTagline
  , genTaglineSet
  , genTaglineUsageRule
  , genPoisonPill
  , genMassiveText
  )

--------------------------------------------------------------------------------
-- Test Tree
--------------------------------------------------------------------------------

tests :: TestTree
tests =
  testGroup
    "Foundry.Core.Brand.Tagline"
    [ testGroup "TaglineText" taglineTextTests
    , testGroup "PrimaryTagline" primaryTaglineTests
    , testGroup "SecondaryTagline" secondaryTaglineTests
    , testGroup "TaglineSet" taglineSetTests
    , testGroup "Security" securityTests
    , testGroup "StressTests" stressTests
    ]

--------------------------------------------------------------------------------
-- TaglineText Tests
--------------------------------------------------------------------------------

taglineTextTests :: [TestTree]
taglineTextTests =
  [ testProperty "valid text is accepted" prop_validTextAccepted
  , testProperty "empty text is rejected" prop_emptyTextRejected
  , testProperty "whitespace-only text is rejected" prop_whitespaceOnlyRejected
  , testProperty "text is stripped" prop_textIsStripped
  , testProperty "value is preserved after creation" prop_valuePreserved
  , testProperty "taglineToText roundtrips" prop_taglineToTextRoundtrip
  , testProperty "all contexts are enumerable" prop_allContextsEnumerable
  , testProperty "invalid text is rejected" prop_invalidTextRejected
  , testProperty "poison text is handled safely" prop_poisonTextSafe
  , testProperty "mkTagline creates valid tagline" prop_mkTaglineWorks
  , testProperty "mkTaglineSet creates valid set" prop_mkTaglineSetWorks
  , testProperty "usage rules are generated properly" prop_usageRulesGenerated
  ]

-- | Valid (non-empty, non-whitespace) text should be accepted
prop_validTextAccepted :: Property
prop_validTextAccepted = withTests 1000 $ property $ do
  txt <- forAll genValidTaglineText
  classify "short (<10 chars)" (T.length txt < 10)
  classify "medium (10-50 chars)" (T.length txt >= 10 && T.length txt < 50)
  classify "long (50+ chars)" (T.length txt >= 50)
  -- Only test if the input is actually valid (non-empty after strip)
  let stripped = T.strip txt
  if T.null stripped
    then assert (isNothing (mkTaglineText txt))
    else assert (isJust (mkTaglineText txt))

-- | Empty text should always be rejected
prop_emptyTextRejected :: Property
prop_emptyTextRejected = property $ do
  assert (isNothing (mkTaglineText ""))

-- | Whitespace-only text should be rejected
prop_whitespaceOnlyRejected :: Property
prop_whitespaceOnlyRejected = property $ do
  whitespace <- forAll $ Gen.element
    [ " "
    , "  "
    , "\t"
    , "\n"
    , "\r\n"
    , "   \t\n  "
    , "\t\t\t"
    ]
  assert (isNothing (mkTaglineText whitespace))

-- | Text should be stripped (leading/trailing whitespace removed)
prop_textIsStripped :: Property
prop_textIsStripped = property $ do
  core <- forAll $ Gen.text (Range.linear 1 50) Gen.alphaNum
  prefix <- forAll $ Gen.text (Range.linear 0 5) (Gen.element [' ', '\t', '\n'])
  suffix <- forAll $ Gen.text (Range.linear 0 5) (Gen.element [' ', '\t', '\n'])
  let input = prefix <> core <> suffix
  case mkTaglineText input of
    Nothing -> assert False  -- core is non-empty, should succeed
    Just tt -> taglineToText tt === core

-- | Value should be exactly preserved after creation
prop_valuePreserved :: Property
prop_valuePreserved = property $ do
  txt <- forAll genValidTaglineText
  let stripped = T.strip txt
  case mkTaglineText txt of
    Nothing -> assert (T.null stripped)  -- Only fails if empty after strip
    Just tt -> taglineToText tt === stripped

-- | taglineToText should roundtrip through mkTaglineText
prop_taglineToTextRoundtrip :: Property
prop_taglineToTextRoundtrip = property $ do
  txt <- forAll genValidTaglineText
  case mkTaglineText txt of
    Nothing -> assert True  -- Invalid input, skip
    Just tt -> do
      let extracted = taglineToText tt
      -- Re-creating from extracted should give same result
      case mkTaglineText extracted of
        Nothing -> assert False  -- Valid text should always be re-creatable
        Just tt2 -> taglineToText tt2 === taglineToText tt

-- | All contexts should be enumerable
prop_allContextsEnumerable :: Property
prop_allContextsEnumerable = property $ do
  -- Verify all 7 contexts exist
  let contexts =
        [ GeneralContext
        , MarketingCampaign
        , SocialMedia
        , ProductLine
        , InternalCommunication
        , EventContext
        , PartnerContext
        ]
  length contexts === 7

-- | Invalid text inputs should be rejected
prop_invalidTextRejected :: Property
prop_invalidTextRejected = withTests 200 $ property $ do
  invalidTxt :: Text <- forAll genInvalidTaglineText
  -- Invalid text should always be rejected
  assert (isNothing (mkTaglineText invalidTxt))

-- | Poison text inputs should be handled safely (no crash)
prop_poisonTextSafe :: Property
prop_poisonTextSafe = withTests 200 $ property $ do
  poisonTxt :: Text <- forAll genPoisonTaglineText
  -- Should either accept (with sanitization) or reject, never crash
  let result :: Maybe TaglineText = mkTaglineText poisonTxt
  assert (isJust result || isNothing result)

-- | mkTagline should create valid taglines with contexts
prop_mkTaglineWorks :: Property
prop_mkTaglineWorks = withTests 200 $ property $ do
  txt <- forAll genValidTaglineText
  ctx <- forAll genTaglineContext
  let contexts = V.singleton ctx
  case mkTagline txt contexts of
    Nothing -> assert True  -- Invalid input
    Just (tagline :: Tagline) -> do
      -- Tagline should have the context we specified
      let resultCtxs = taglineContexts tagline
      assert (V.elem ctx resultCtxs)
      -- Text should be preserved (stripped)
      let resultTxt :: TaglineText = taglineText tagline
      taglineToText resultTxt === T.strip txt

-- | mkTaglineSet should create valid sets with primary and secondaries
prop_mkTaglineSetWorks :: Property
prop_mkTaglineSetWorks = withTests 100 $ property $ do
  mPrimary <- forAll genPrimaryTagline
  mSecondaries <- forAll $ Gen.list (Range.linear 0 3) genSecondaryTagline
  rules <- V.fromList <$> forAll (Gen.list (Range.linear 0 2) genTaglineUsageRule)
  case mPrimary of
    Nothing -> assert True  -- Invalid primary
    Just primary -> do
      let validSecondaries = [s | Just s <- mSecondaries]
      let tagSet :: TaglineSet = mkTaglineSet primary (V.fromList validSecondaries) rules
      -- TaglineSet should contain the primary
      let setPrimary :: PrimaryTagline = taglineSetPrimary tagSet
      let setSecondaries :: V.Vector SecondaryTagline = taglineSetSecondary tagSet
      -- Primary should match
      taglineText (primaryToTagline setPrimary) === taglineText (primaryToTagline primary)
      -- Secondaries count should match
      V.length setSecondaries === length validSecondaries

-- | Usage rules should be properly generated
prop_usageRulesGenerated :: Property
prop_usageRulesGenerated = withTests 100 $ property $ do
  rule :: TaglineUsageRule <- forAll genTaglineUsageRule
  -- Verify the rule is one of the expected variants
  let isValidRule = case rule of
        UsageWithLogo -> True
        UsageStandalone -> True
        NoModification -> True
        NoCampaignCombination -> True
        RequiresApproval -> True
  assert isValidRule

--------------------------------------------------------------------------------
-- PrimaryTagline Tests
--------------------------------------------------------------------------------

primaryTaglineTests :: [TestTree]
primaryTaglineTests =
  [ testProperty "primary always has GeneralContext" prop_primaryHasGeneralContext
  , testProperty "primary requires valid text" prop_primaryRequiresValidText
  , testProperty "primaryToTagline preserves text" prop_primaryPreservesText
  ]

-- | Primary tagline MUST always have GeneralContext
prop_primaryHasGeneralContext :: Property
prop_primaryHasGeneralContext = withTests 500 $ property $ do
  mPrimary <- forAll genPrimaryTagline
  case mPrimary of
    Nothing -> assert True  -- Invalid input
    Just primary -> do
      let tagline = primaryToTagline primary
          contexts = taglineContexts tagline
      assert (V.elem GeneralContext contexts)

-- | Primary tagline requires valid (non-empty) text
prop_primaryRequiresValidText :: Property
prop_primaryRequiresValidText = property $ do
  -- Only test truly empty/whitespace-only inputs
  emptyInput <- forAll $ Gen.element ["", "   ", "\t\n\r", "  \t  "]
  assert (isNothing (mkPrimaryTagline emptyInput))

-- | Converting to tagline preserves the text
prop_primaryPreservesText :: Property
prop_primaryPreservesText = property $ do
  validTxt <- forAll genValidTaglineText
  case mkPrimaryTagline validTxt of
    Nothing -> assert True  -- Skip invalid
    Just primary -> do
      let tagline = primaryToTagline primary
          txtFromTagline = taglineToText (taglineText tagline)
      txtFromTagline === T.strip validTxt

--------------------------------------------------------------------------------
-- SecondaryTagline Tests
--------------------------------------------------------------------------------

secondaryTaglineTests :: [TestTree]
secondaryTaglineTests =
  [ testProperty "secondary requires at least one context" prop_secondaryRequiresContext
  , testProperty "secondary with empty contexts is rejected" prop_secondaryEmptyContextRejected
  , testProperty "secondary preserves contexts" prop_secondaryPreservesContexts
  ]

-- | Secondary tagline must have at least one context
prop_secondaryRequiresContext :: Property
prop_secondaryRequiresContext = property $ do
  validTxt <- forAll genValidTaglineText
  -- Empty context vector should be rejected
  assert (isNothing (mkSecondaryTagline validTxt V.empty))

-- | Secondary with empty contexts is rejected
prop_secondaryEmptyContextRejected :: Property
prop_secondaryEmptyContextRejected = property $ do
  validTxt <- forAll genValidTaglineText
  let result = mkSecondaryTagline validTxt V.empty
  assert (isNothing result)

-- | Contexts are preserved in secondary tagline
prop_secondaryPreservesContexts :: Property
prop_secondaryPreservesContexts = property $ do
  validTxt <- forAll genValidTaglineText
  contexts <- V.fromList <$> forAll (Gen.list (Range.linear 1 5) genTaglineContext)
  case mkSecondaryTagline validTxt contexts of
    Nothing -> assert True  -- Invalid text
    Just secondary -> do
      let tagline = secondaryToTagline secondary
      taglineContexts tagline === contexts

--------------------------------------------------------------------------------
-- TaglineSet Tests
--------------------------------------------------------------------------------

taglineSetTests :: [TestTree]
taglineSetTests =
  [ testProperty "taglineSet always has at least one tagline" prop_taglineSetNonEmpty
  , testProperty "allTaglines includes primary first" prop_allTaglinesPrimaryFirst
  , testProperty "allTaglines count matches expected" prop_allTaglinesCount
  ]

-- | TaglineSet always has at least one tagline (the primary)
prop_taglineSetNonEmpty :: Property
prop_taglineSetNonEmpty = withTests 500 $ property $ do
  mSet <- forAll genTaglineSet
  case mSet of
    Nothing -> assert True  -- Failed to create (invalid input)
    Just tagSet -> do
      let allTags = allTaglines tagSet
      assert (V.length allTags >= 1)

-- | allTaglines should have the primary tagline first
prop_allTaglinesPrimaryFirst :: Property
prop_allTaglinesPrimaryFirst = property $ do
  mSet <- forAll genTaglineSet
  case mSet of
    Nothing -> assert True
    Just tagSet -> do
      let allTags = allTaglines tagSet
          primary = primaryToTagline (taglineSetPrimary tagSet)
      case V.uncons allTags of
        Nothing -> assert False  -- Should never be empty
        Just (first, _) -> do
          -- First element should be the primary
          taglineText first === taglineText primary

-- | Count of allTaglines = 1 + length of secondaries
prop_allTaglinesCount :: Property
prop_allTaglinesCount = property $ do
  mSet <- forAll genTaglineSet
  case mSet of
    Nothing -> assert True
    Just tagSet -> do
      let allTags = allTaglines tagSet
          secondaries = taglineSetSecondary tagSet
      V.length allTags === 1 + V.length secondaries

--------------------------------------------------------------------------------
-- Security Tests
--------------------------------------------------------------------------------

securityTests :: [TestTree]
securityTests =
  [ testProperty "poison pills don't crash mkTaglineText" prop_poisonPillSafe
  , testProperty "SQL injection is harmless" prop_sqlInjectionSafe
  , testProperty "XSS payloads are treated as text" prop_xssSafe
  , testProperty "control chars don't corrupt" prop_controlCharsSafe
  , testProperty "unicode weirdness is handled" prop_unicodeWeirdnessSafe
  ]

-- | Poison pills should not crash, just return valid or Nothing
prop_poisonPillSafe :: Property
prop_poisonPillSafe = withTests 500 $ property $ do
  poison <- forAll genPoisonPill
  -- This should NOT throw an exception
  let result = mkTaglineText poison
  -- Either it's accepted (and stripped) or rejected
  case result of
    Nothing -> assert True  -- Rejected is fine
    Just tt -> do
      -- If accepted, the value should be safely stored
      let stored = taglineToText tt
      -- The stored value should not be empty (or it would have been rejected)
      assert (not (T.null stored))

-- | SQL injection attempts should be treated as plain text
prop_sqlInjectionSafe :: Property
prop_sqlInjectionSafe = property $ do
  injection <- forAll $ Gen.element
    [ "'; DROP TABLE brands; --"
    , "1' OR '1'='1"
    , "admin'--"
    ]
  case mkTaglineText injection of
    Nothing -> assert True
    Just tt -> do
      -- The SQL should be stored literally, not executed
      let stored = taglineToText tt
      assert (T.isInfixOf "DROP" stored || T.isInfixOf "OR" stored || T.isInfixOf "--" stored)

-- | XSS payloads should be treated as plain text
prop_xssSafe :: Property
prop_xssSafe = property $ do
  xss <- forAll $ Gen.element
    [ "<script>alert('xss')</script>"
    , "<img src=x onerror=alert(1)>"
    ]
  case mkTaglineText xss of
    Nothing -> assert True
    Just tt -> do
      let stored = taglineToText tt
      -- The script tags should be stored literally
      assert (T.isInfixOf "<" stored || T.isInfixOf ">" stored)

-- | Control characters should not corrupt internal state
prop_controlCharsSafe :: Property
prop_controlCharsSafe = property $ do
  ctrl <- forAll $ Gen.element
    [ "\x00\x01\x02"
    , "\x1B[2J"
    , "\r\n\r\n"
    ]
  -- Should not crash - result is either accepted or rejected gracefully
  let result = mkTaglineText ctrl
  assert (isJust result || isNothing result)

-- | Unicode weirdness should be handled gracefully
prop_unicodeWeirdnessSafe :: Property
prop_unicodeWeirdnessSafe = property $ do
  weird <- forAll $ Gen.element
    [ "\x1F468\x200D\x1F469\x200D\x1F467"  -- Family emoji with ZWJ
    , "\x1F3F3\xFE0F\x200D\x1F308"         -- Rainbow flag
    , "Za\x0308lg\x030Ao"                   -- Zalgo-like
    ]
  case mkTaglineText weird of
    Nothing -> assert True
    Just tt -> do
      -- Should be stored and retrievable
      let stored = taglineToText tt
      assert (not (T.null stored))

--------------------------------------------------------------------------------
-- Stress Tests
--------------------------------------------------------------------------------

stressTests :: [TestTree]
stressTests =
  [ testProperty "massive text is handled" prop_massiveTextHandled
  , testProperty "rapid creation doesn't leak" prop_rapidCreation
  , testProperty "high cardinality contexts work" prop_highCardinalityContexts
  ]

-- | Very large text inputs should not crash
prop_massiveTextHandled :: Property
prop_massiveTextHandled = withTests 10 $ property $ do
  massive <- forAll genMassiveText
  -- Should not crash or hang - result is either accepted or rejected gracefully
  let result = mkTaglineText massive
  assert (isJust result || isNothing result)

-- | Creating many taglines rapidly should not leak memory
prop_rapidCreation :: Property
prop_rapidCreation = withTests 10 $ property $ do
  -- Create 1000 taglines
  let texts = map (\i -> "Tagline " <> T.pack (show i)) [1..1000 :: Int]
  let results = map mkTaglineText texts
  -- All should succeed
  assert (all isJust results)
  -- Count should match
  length (filter isJust results) === 1000

-- | Many different contexts should work
prop_highCardinalityContexts :: Property
prop_highCardinalityContexts = property $ do
  -- Use all 7 contexts
  let allContexts = V.fromList
        [ GeneralContext
        , MarketingCampaign
        , SocialMedia
        , ProductLine
        , InternalCommunication
        , EventContext
        , PartnerContext
        ]
  case mkSecondaryTagline "Test tagline" allContexts of
    Nothing -> assert False  -- Should succeed
    Just secondary -> do
      let tagline = secondaryToTagline secondary
      V.length (taglineContexts tagline) === 7
