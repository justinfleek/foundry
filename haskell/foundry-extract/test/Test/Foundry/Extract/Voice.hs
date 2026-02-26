{- |
Module      : Test.Foundry.Extract.Voice
Description : Property tests for voice extraction
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause
-}
module Test.Foundry.Extract.Voice (tests) where

import Data.Text (Text)
import Data.Text qualified as T
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Foundry.Extract.Voice.NLP (TextAnalysis (..), analyzeText, formalityScore)

tests :: TestTree
tests = testGroup "Voice"
  [ testProperty "Formality score in [0, 1]" prop_formality_bounded
  , testProperty "Word count is non-negative" prop_wordCount_nonnegative
  , testProperty "Empty text has zero words" prop_emptyText_zeroWords
  ]

-- | Formality is always in [0, 1]
prop_formality_bounded :: Property
prop_formality_bounded = property $ do
  contractions <- forAll $ Gen.int (Range.constant 0 10)
  firstPerson <- forAll $ Gen.int (Range.constant 0 10)
  secondPerson <- forAll $ Gen.int (Range.constant 0 10)
  wordCount <- forAll $ Gen.int (Range.constant 1 1000)
  let score = formalityScore contractions firstPerson secondPerson wordCount
  assert $ score >= 0 && score <= 1

-- | Word count is non-negative
prop_wordCount_nonnegative :: Property
prop_wordCount_nonnegative = property $ do
  text <- forAll genText
  let analysis = analyzeText text
  assert $ taWordCount analysis >= 0

-- | Empty text has zero words
prop_emptyText_zeroWords :: Property
prop_emptyText_zeroWords = property $ do
  let analysis = analyzeText ""
  taWordCount analysis === 0

genText :: Gen Text
genText = do
  words' <- Gen.list (Range.linear 0 50) genWord
  pure $ T.intercalate " " words'

genWord :: Gen Text
genWord = Gen.text (Range.linear 1 10) Gen.alpha
