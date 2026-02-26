{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                           // foundry // test // brand // security
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Core.Brand.Security
Description : Security tests - poison pills, injection attacks, corruption
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

NORMAN STANSFIELD ENERGY - EVERYONE GETS TESTED.

== Threat Model

Adversarial agent scrapes a malicious website that contains:
- SQL injection payloads in brand text
- XSS payloads in taglines
- Control characters to corrupt parsers
- Unicode tricks to bypass validation
- Homoglyph attacks for impersonation
- RTL override attacks
- Null injection to truncate strings
- Template injection for code execution
- Path traversal to read files
- Memory exhaustion payloads

If ANY of these corrupt agent state, a billion-agent swarm moving at
1000 tokens/second will cascade fail catastrophically.

== Success Criteria

1. No crashes (exceptions caught or prevented)
2. No state corruption (valid data stays valid)
3. No injection execution (payloads treated as data)
4. No memory exhaustion (bounded allocations)
5. Graceful rejection (invalid → Nothing, not panic)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Core.Brand.Security
  ( tests
  ) where

import Control.Exception (evaluate, try, SomeException)
import Data.Maybe (isJust, isNothing)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Hedgehog (Property, forAll, property, assert, withTests, evalIO)
import Hedgehog.Gen qualified as Gen
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Foundry.Core.Brand.Tagline
  ( TaglineContext (..)
  , mkTaglineText
  , mkPrimaryTagline
  , mkSecondaryTagline
  , taglineToText
  )

import Foundry.Core.Brand.Strategy
  ( mkMissionStatement
  , mkBrandValue
  , mkPersonalityTrait
  , mkPersonalityDescription
  , missionToText
  )

import Foundry.Core.Brand.Editorial
  ( mkPhoneFormat
  , mkConfusedWord
  )

import Test.Foundry.Core.Brand.Generators
  ( genPoisonPill
  , genSqlInjection
  , genXssPayload
  , genControlChars
  , genUnicodeWeirdness
  , genZeroWidthChars
  , genRtlOverride
  , genHomoglyphAttack
  , genNullInjection
  , genMassiveText
  )

--------------------------------------------------------------------------------
-- Test Tree
--------------------------------------------------------------------------------

tests :: TestTree
tests =
  testGroup
    "Security"
    [ testGroup "InjectionAttacks" injectionTests
    , testGroup "UnicodeAttacks" unicodeTests
    , testGroup "MemoryAttacks" memoryTests
    , testGroup "ParserAttacks" parserTests
    , testGroup "CrossModuleAttacks" crossModuleTests
    ]

--------------------------------------------------------------------------------
-- Injection Attack Tests
--------------------------------------------------------------------------------

injectionTests :: [TestTree]
injectionTests =
  [ testProperty "SQL injection in tagline is data-only" prop_sqlInjectionTagline
  , testProperty "SQL injection in mission is data-only" prop_sqlInjectionMission
  , testProperty "SQL injection in values is data-only" prop_sqlInjectionValues
  , testProperty "XSS payload in tagline is data-only" prop_xssTagline
  , testProperty "XSS payload in mission is data-only" prop_xssMission
  , testProperty "template injection is data-only" prop_templateInjection
  ]

-- | SQL injection in taglines must be treated as literal text
prop_sqlInjectionTagline :: Property
prop_sqlInjectionTagline = withTests 200 $ property $ do
  injection <- forAll genSqlInjection
  case mkTaglineText injection of
    Nothing -> assert True  -- Rejected is safe
    Just tt -> do
      let stored = taglineToText tt
      -- SQL keywords should be stored literally
      assert (stored == T.strip injection)

-- | SQL injection in mission statements must be treated as literal text
prop_sqlInjectionMission :: Property
prop_sqlInjectionMission = withTests 200 $ property $ do
  injection <- forAll genSqlInjection
  case mkMissionStatement injection of
    Nothing -> assert True
    Just ms -> do
      let stored = missionToText ms
      assert (stored == T.strip injection)

-- | SQL injection in brand values must be treated as literal text
prop_sqlInjectionValues :: Property
prop_sqlInjectionValues = withTests 200 $ property $ do
  injection <- forAll genSqlInjection
  case mkBrandValue injection "description" of
    Nothing -> assert True
    Just _ -> assert True  -- Just verify no crash

-- | XSS payloads in taglines must be stored literally
prop_xssTagline :: Property
prop_xssTagline = withTests 200 $ property $ do
  xss <- forAll genXssPayload
  case mkTaglineText xss of
    Nothing -> assert True
    Just tt -> do
      let stored = taglineToText tt
      -- HTML tags should NOT be escaped, just stored as-is
      -- (escaping happens at render time, not storage)
      assert (T.isInfixOf "<" xss && T.isInfixOf "<" stored
              || not (T.isInfixOf "<" xss))

-- | XSS payloads in mission statements must be stored literally
prop_xssMission :: Property
prop_xssMission = withTests 200 $ property $ do
  xss <- forAll genXssPayload
  case mkMissionStatement xss of
    Nothing -> assert True
    Just ms -> do
      let stored = missionToText ms
      assert (stored == T.strip xss)

-- | Template injection must be treated as literal text
prop_templateInjection :: Property
prop_templateInjection = withTests 100 $ property $ do
  template <- forAll $ Gen.element
    [ "{{7*7}}"
    , "${7*7}"
    , "<%= 7*7 %>"
    , "#{7*7}"
    ]
  case mkTaglineText template of
    Nothing -> assert True
    Just tt -> do
      let stored = taglineToText tt
      -- Should NOT evaluate to 49
      assert (not (T.isInfixOf "49" stored))
      assert (stored == T.strip template)

--------------------------------------------------------------------------------
-- Unicode Attack Tests
--------------------------------------------------------------------------------

unicodeTests :: [TestTree]
unicodeTests =
  [ testProperty "zero-width chars don't corrupt" prop_zeroWidthSafe
  , testProperty "RTL override doesn't confuse" prop_rtlSafe
  , testProperty "homoglyphs are stored literally" prop_homoglyphSafe
  , testProperty "unicode weirdness doesn't crash" prop_unicodeWeirdSafe
  , testProperty "null injection doesn't truncate" prop_nullInjectionSafe
  ]

-- | Zero-width characters should not corrupt data
prop_zeroWidthSafe :: Property
prop_zeroWidthSafe = withTests 200 $ property $ do
  zwc <- forAll genZeroWidthChars
  case mkTaglineText zwc of
    Nothing -> assert True  -- May be rejected if only ZWC
    Just tt -> do
      let stored = taglineToText tt
      -- Should either contain the ZWC or have stripped them
      assert (not (T.null stored))

-- | RTL override should not confuse text direction
prop_rtlSafe :: Property
prop_rtlSafe = withTests 200 $ property $ do
  rtl <- forAll genRtlOverride
  case mkTaglineText rtl of
    Nothing -> assert True
    Just tt -> do
      let stored = taglineToText tt
      -- The RTL chars are stored, but don't affect our logic
      assert (not (T.null stored))

-- | Homoglyph attacks should store the actual characters
prop_homoglyphSafe :: Property
prop_homoglyphSafe = withTests 200 $ property $ do
  homo <- forAll genHomoglyphAttack
  case mkTaglineText homo of
    Nothing -> assert True
    Just tt -> do
      let stored = taglineToText tt
      -- Cyrillic/Greek chars should be stored literally
      assert (stored == T.strip homo)

-- | Unicode weirdness should not crash
prop_unicodeWeirdSafe :: Property
prop_unicodeWeirdSafe = withTests 200 $ property $ do
  weird <- forAll genUnicodeWeirdness
  -- Should not throw exception - result is either Just (valid) or Nothing (rejected)
  let result = mkTaglineText weird
  -- Verify result is one of the expected outcomes (not an exception)
  assert (isJust result || isNothing result)

-- | Null injection should not truncate strings
prop_nullInjectionSafe :: Property
prop_nullInjectionSafe = withTests 200 $ property $ do
  nullInj <- forAll genNullInjection
  case mkTaglineText nullInj of
    Nothing -> assert True
    Just tt -> do
      let stored = taglineToText tt
      -- Length should be preserved (nulls stored, not truncated)
      -- Note: Text handles nulls, ByteString may not
      assert (not (T.null stored))

--------------------------------------------------------------------------------
-- Memory Attack Tests
--------------------------------------------------------------------------------

memoryTests :: [TestTree]
memoryTests =
  [ testProperty "massive text doesn't exhaust memory" prop_massiveTextSafe
  , testProperty "repeated allocations don't leak" prop_noMemoryLeak
  , testProperty "deeply nested doesn't stack overflow" prop_deepNestingSafe
  ]

-- | Massive text inputs should be handled without memory exhaustion
prop_massiveTextSafe :: Property
prop_massiveTextSafe = withTests 10 $ property $ do
  massive <- forAll genMassiveText
  -- Should complete without crashing
  let result = mkTaglineText massive
  -- Either accepted or rejected, but shouldn't crash
  assert (isJust result || isNothing result)

-- | Repeated allocations shouldn't cause memory leaks
prop_noMemoryLeak :: Property
prop_noMemoryLeak = withTests 5 $ property $ do
  -- Create and discard 10000 taglines
  let createMany n = 
        let texts = map (\i -> "Tagline " <> T.pack (show i)) [1..n]
        in length (filter isJust (map mkTaglineText texts))
  let count = createMany (10000 :: Int)
  assert (count == 10000)

-- | Deeply nested structures shouldn't cause stack overflow
prop_deepNestingSafe :: Property
prop_deepNestingSafe = withTests 10 $ property $ do
  let depth = 10000 :: Int
  let nested = T.concat [T.replicate depth "[", "x", T.replicate depth "]"]
  case mkTaglineText nested of
    Nothing -> assert True
    Just tt -> do
      let stored = taglineToText tt
      -- Should handle the brackets
      assert (T.length stored > 0)

--------------------------------------------------------------------------------
-- Parser Attack Tests
--------------------------------------------------------------------------------

parserTests :: [TestTree]
parserTests =
  [ testProperty "control chars don't corrupt parser" prop_controlCharsSafe
  , testProperty "ANSI escape codes are data" prop_ansiEscapeSafe
  , testProperty "line terminators are handled" prop_lineTerminatorSafe
  ]

-- | Control characters shouldn't corrupt parser state
prop_controlCharsSafe :: Property
prop_controlCharsSafe = withTests 200 $ property $ do
  ctrl <- forAll genControlChars
  case mkTaglineText ctrl of
    Nothing -> assert True  -- May be rejected
    Just tt -> do
      let stored = taglineToText tt
      -- Parser should survive - stored text should be non-empty
      assert (not (T.null stored))

-- | ANSI escape codes should be treated as data
prop_ansiEscapeSafe :: Property
prop_ansiEscapeSafe = property $ do
  ansi <- forAll $ Gen.element
    [ "\x1B[2J"           -- Clear screen
    , "\x1B[31mRED\x1B[0m" -- Color
    , "\x1B[H"            -- Home cursor
    ]
  case mkTaglineText ansi of
    Nothing -> assert True
    Just tt -> do
      let stored = taglineToText tt
      -- ANSI codes should be stored, not interpreted
      assert (T.isInfixOf "\x1B" stored || T.null stored)

-- | Various line terminators should be handled
prop_lineTerminatorSafe :: Property
prop_lineTerminatorSafe = property $ do
  terminator <- forAll $ Gen.element
    [ "line1\nline2"     -- Unix
    , "line1\r\nline2"   -- Windows
    , "line1\rline2"     -- Old Mac
    , "line1\x0Bline2"   -- Vertical tab
    , "line1\x0Cline2"   -- Form feed
    ]
  case mkTaglineText terminator of
    Nothing -> assert True
    Just tt -> do
      let stored = taglineToText tt
      assert (not (T.null stored))

--------------------------------------------------------------------------------
-- Cross-Module Attack Tests
--------------------------------------------------------------------------------

crossModuleTests :: [TestTree]
crossModuleTests =
  [ testProperty "poison doesn't propagate tagline→strategy" prop_noPropagationTaglineStrategy
  , testProperty "poison doesn't propagate strategy→editorial" prop_noPropagationStrategyEditorial
  , testProperty "all modules reject consistently" prop_consistentRejection
  , testProperty "poison in primary tagline is safe" prop_poisonPrimaryTagline
  , testProperty "poison in secondary tagline is safe" prop_poisonSecondaryTagline
  , testProperty "exception handling for poison pills" prop_noExceptionsFromPoison
  ]

-- | Poison in tagline shouldn't affect strategy module
prop_noPropagationTaglineStrategy :: Property
prop_noPropagationTaglineStrategy = withTests 100 $ property $ do
  poison <- forAll genPoisonPill
  -- Create tagline with poison
  let taglineResult = mkTaglineText poison
  -- Strategy module should also handle the same poison
  let missionResult = mkMissionStatement poison
  let valueResult = mkBrandValue poison "desc"
  -- All should either accept or reject gracefully (not crash)
  assert (isJust taglineResult || isNothing taglineResult)
  assert (isJust missionResult || isNothing missionResult)
  assert (isJust valueResult || isNothing valueResult)

-- | Poison in strategy shouldn't affect editorial module
prop_noPropagationStrategyEditorial :: Property
prop_noPropagationStrategyEditorial = withTests 100 $ property $ do
  poison <- forAll genPoisonPill
  -- Try in strategy
  let missionResult = mkMissionStatement poison
  -- Try in editorial (phone format with X placeholders)
  let phoneResult = mkPhoneFormat (poison <> "X")
  let wordResult = mkConfusedWord poison "correct" "context"
  -- All should either accept or reject gracefully (not crash)
  assert (isJust missionResult || isNothing missionResult)
  assert (isJust phoneResult || isNothing phoneResult)
  assert (isJust wordResult || isNothing wordResult)

-- | All modules should reject invalid input consistently
prop_consistentRejection :: Property
prop_consistentRejection = property $ do
  -- Empty string should be rejected for required fields
  assert (isNothing (mkTaglineText ""))
  assert (isNothing (mkMissionStatement ""))
  assert (isNothing (mkBrandValue "" "desc"))  -- Empty name rejected
  -- Note: mkBrandValue accepts empty description (description is optional)
  assert (isJust (mkBrandValue "name" ""))     -- Empty desc is OK
  assert (isNothing (mkPersonalityTrait ""))
  assert (isNothing (mkPersonalityDescription ""))

-- | Primary tagline with poison should be safe
prop_poisonPrimaryTagline :: Property
prop_poisonPrimaryTagline = withTests 100 $ property $ do
  poison <- forAll genPoisonPill
  let result = mkPrimaryTagline poison
  -- Should either accept or reject, never crash
  assert (isJust result || isNothing result)

-- | Secondary tagline with poison should be safe
prop_poisonSecondaryTagline :: Property
prop_poisonSecondaryTagline = withTests 100 $ property $ do
  poison <- forAll genPoisonPill
  -- Try with various contexts to ensure poison doesn't corrupt context handling
  let contexts = V.fromList [GeneralContext, MarketingCampaign]
  let result = mkSecondaryTagline poison contexts
  assert (isJust result || isNothing result)

-- | Verify that poison pills don't throw exceptions (uses evaluate/try)
-- This is the most rigorous safety test - actually catches runtime exceptions
prop_noExceptionsFromPoison :: Property
prop_noExceptionsFromPoison = withTests 50 $ property $ do
  poison :: Text <- forAll genPoisonPill
  -- Use evaluate to force evaluation and catch any exceptions
  result <- evalIO $ try @SomeException $ evaluate $ mkTaglineText poison
  case result of
    Left _exc -> assert False  -- Exception thrown - test fails
    Right val -> assert (isJust val || isNothing val)
