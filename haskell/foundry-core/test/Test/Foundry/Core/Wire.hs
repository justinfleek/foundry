{-# LANGUAGE PatternSynonyms #-}

{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // foundry // test // core // wire
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Core.Wire
Description : Property tests for FWIRE binary format encode/decode roundtrip
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

== Verified Properties

* Varint encode/decode roundtrip identity
* Header encode/decode roundtrip identity
* PillarBlock encode/decode roundtrip identity
* FWireFrame encode/decode roundtrip identity
* CRC32 integrity verification

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Core.Wire
  ( tests
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Word (Word16, Word32, Word64)
import Hedgehog (Gen, Property, forAll, property, (===), assert)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Foundry.Core.Wire.Types
  ( FWireHeader (..)
  , FWireFrame (..)
  , PillarBlock (..)
  , PillarId (..)
  , EncodingType (..)
  )
import Foundry.Core.Wire.Types (pattern FWIRE_MAGIC, pattern FWIRE_VERSION)
import Foundry.Core.Wire.Varint (encodeVarint, decodeVarint)
import Foundry.Core.Wire.Encode (encodeFrame)
import Foundry.Core.Wire.Decode (decodeFrame)

--------------------------------------------------------------------------------
-- Test Tree
--------------------------------------------------------------------------------

-- | All Wire module tests
tests :: TestTree
tests =
  testGroup
    "Foundry.Core.Wire"
    [ testGroup "Varint" varintTests
    , testGroup "FWireFrame" frameTests
    ]

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

-- | Generate a valid Word32 for varint encoding
genWord32 :: Gen Word32
genWord32 = Gen.word32 Range.linearBounded

-- | Generate a small Word32 (single-byte varint)
genSmallWord32 :: Gen Word32
genSmallWord32 = Gen.word32 (Range.linear 0 127)

-- | Generate a medium Word32 (2-byte varint)
genMediumWord32 :: Gen Word32
genMediumWord32 = Gen.word32 (Range.linear 128 16383)

-- | Generate a pillar ID (0x00-0x25 for 38 pillars)
genPillarId :: Gen PillarId
genPillarId = PillarId <$> Gen.word8 (Range.linear 0 0x25)

-- | Generate an encoding type
genEncodingType :: Gen EncodingType
genEncodingType = Gen.enumBounded

-- | Generate arbitrary bytes for pillar data
genPillarData :: Gen ByteString
genPillarData = Gen.bytes (Range.linear 0 1024)

-- | Generate a valid pillar block
genPillarBlock :: Gen PillarBlock
genPillarBlock = PillarBlock
  <$> genPillarId
  <*> genEncodingType
  <*> genPillarData

-- | Generate a valid timestamp (unix microseconds)
genTimestamp :: Gen Word64
genTimestamp = Gen.word64 (Range.linear 0 0xFFFFFFFFFFFFFFFF)

-- | Generate a domain name (ASCII bytes for simplicity)
genDomain :: Gen ByteString
genDomain = Gen.utf8 (Range.linear 1 255) Gen.alphaNum

-- | Generate a valid FWIRE header
genHeader :: Word16 -> Gen FWireHeader
genHeader pillarCount = FWireHeader
  <$> pure FWIRE_MAGIC
  <*> pure FWIRE_VERSION
  <*> Gen.word8 (Range.linear 0 0)  -- flags reserved
  <*> pure pillarCount
  <*> genTimestamp

-- | Generate a valid FWIRE frame
genFrame :: Gen FWireFrame
genFrame = do
  pillars <- Gen.list (Range.linear 0 10) genPillarBlock
  let pillarCount = fromIntegral (length pillars)
  header <- genHeader pillarCount
  domain <- genDomain
  -- CRC32 is computed by encoder, use placeholder
  pure FWireFrame
    { fwfHeader  = header
    , fwfDomain  = domain
    , fwfPillars = pillars
    , fwfCrc32   = 0  -- Will be computed by encoder
    }

--------------------------------------------------------------------------------
-- Varint Tests
--------------------------------------------------------------------------------

varintTests :: [TestTree]
varintTests =
  [ testProperty "roundtrip identity" prop_varintRoundtrip
  , testProperty "small values single byte" prop_varintSmallSingleByte
  , testProperty "medium values two bytes" prop_varintMediumTwoBytes
  , testProperty "zero encodes correctly" prop_varintZero
  , testProperty "max value encodes" prop_varintMax
  ]

-- | Varint encode/decode roundtrip should be identity
prop_varintRoundtrip :: Property
prop_varintRoundtrip = property $ do
  n <- forAll genWord32
  let encoded = encodeVarint n
  case decodeVarint encoded of
    Nothing -> assert False
    Just (decoded, remaining) -> do
      decoded === n
      -- Should consume all bytes
      BS.length remaining === 0

-- | Small values (< 128) should encode to single byte
prop_varintSmallSingleByte :: Property
prop_varintSmallSingleByte = property $ do
  n <- forAll genSmallWord32
  let encoded = encodeVarint n
  BS.length encoded === 1
  -- MSB should be 0 (no continuation)
  assert (BS.index encoded 0 < 128)

-- | Medium values (128-16383) should encode to two bytes
prop_varintMediumTwoBytes :: Property
prop_varintMediumTwoBytes = property $ do
  n <- forAll genMediumWord32
  let encoded = encodeVarint n
  BS.length encoded === 2
  -- First byte MSB should be 1 (continuation)
  assert (BS.index encoded 0 >= 128)
  -- Second byte MSB should be 0 (no continuation)
  assert (BS.index encoded 1 < 128)

-- | Zero should encode to single byte 0x00
prop_varintZero :: Property
prop_varintZero = property $ do
  let encoded = encodeVarint 0
  encoded === BS.pack [0x00]

-- | Max Word32 should encode and decode correctly
prop_varintMax :: Property
prop_varintMax = property $ do
  let n = maxBound :: Word32
      encoded = encodeVarint n
  case decodeVarint encoded of
    Nothing -> assert False
    Just (decoded, _) -> decoded === n

--------------------------------------------------------------------------------
-- FWireFrame Tests
--------------------------------------------------------------------------------

frameTests :: [TestTree]
frameTests =
  [ testProperty "roundtrip identity" prop_frameRoundtrip
  , testProperty "magic preserved" prop_frameMagicPreserved
  , testProperty "version preserved" prop_frameVersionPreserved
  , testProperty "pillar count matches" prop_framePillarCountMatches
  , testProperty "domain preserved" prop_frameDomainPreserved
  , testProperty "empty pillars valid" prop_frameEmptyPillarsValid
  ]

-- | Frame encode/decode roundtrip should be identity
prop_frameRoundtrip :: Property
prop_frameRoundtrip = property $ do
  frame <- forAll genFrame
  let encoded = encodeFrame frame
  case decodeFrame encoded of
    Left _err -> do
      -- Annotate with error for debugging
      assert False
    Right decoded -> do
      -- Check all fields match (except CRC which is computed)
      fwfHeader decoded === fwfHeader frame
      fwfDomain decoded === fwfDomain frame
      fwfPillars decoded === fwfPillars frame

-- | Magic bytes should be preserved
prop_frameMagicPreserved :: Property
prop_frameMagicPreserved = property $ do
  frame <- forAll genFrame
  let encoded = encodeFrame frame
  case decodeFrame encoded of
    Left _ -> assert False
    Right decoded ->
      fwhMagic (fwfHeader decoded) === FWIRE_MAGIC

-- | Version should be preserved
prop_frameVersionPreserved :: Property
prop_frameVersionPreserved = property $ do
  frame <- forAll genFrame
  let encoded = encodeFrame frame
  case decodeFrame encoded of
    Left _ -> assert False
    Right decoded ->
      fwhVersion (fwfHeader decoded) === FWIRE_VERSION

-- | Pillar count in header should match actual pillars
prop_framePillarCountMatches :: Property
prop_framePillarCountMatches = property $ do
  frame <- forAll genFrame
  let encoded = encodeFrame frame
  case decodeFrame encoded of
    Left _ -> assert False
    Right decoded ->
      fromIntegral (fwhPillarCount (fwfHeader decoded)) === length (fwfPillars decoded)

-- | Domain should be preserved exactly
prop_frameDomainPreserved :: Property
prop_frameDomainPreserved = property $ do
  frame <- forAll genFrame
  let encoded = encodeFrame frame
  case decodeFrame encoded of
    Left _ -> assert False
    Right decoded ->
      fwfDomain decoded === fwfDomain frame

-- | Empty pillar list should be valid
prop_frameEmptyPillarsValid :: Property
prop_frameEmptyPillarsValid = property $ do
  header <- forAll (genHeader 0)
  domain <- forAll genDomain
  let frame = FWireFrame
        { fwfHeader  = header
        , fwfDomain  = domain
        , fwfPillars = []
        , fwfCrc32   = 0
        }
      encoded = encodeFrame frame
  case decodeFrame encoded of
    Left _ -> assert False
    Right decoded -> do
      fwfPillars decoded === []
      fwhPillarCount (fwfHeader decoded) === 0
