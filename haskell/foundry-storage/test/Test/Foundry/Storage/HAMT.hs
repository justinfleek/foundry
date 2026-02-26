{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // foundry // test // storage // hamt
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Storage.HAMT
Description : Property tests for HAMT storage
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

== Verified Properties

* Content-addressability: same content → same key
* Idempotency: insert(x); insert(x) = insert(x)
* Lookup consistency: insert(x); lookup(key(x)) = Just x
* Delete consistency: delete(key); lookup(key) = Nothing

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Storage.HAMT
  ( tests
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as BS8
import Hedgehog (Gen, Property, forAll, property, (===), assert, withTests)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Foundry.Storage.HAMT qualified as HAMT
import Foundry.Storage.Types (mkStorageKey)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

--------------------------------------------------------------------------------
-- Test Tree
--------------------------------------------------------------------------------

-- | All HAMT tests
tests :: TestTree
tests =
  testGroup
    "Foundry.Storage.HAMT"
    [ testGroup "Construction" constructionTests
    , testGroup "Operations" operationTests
    , testGroup "Properties" propertyTests
    , testGroup "Memory" memoryTests
    , testGroup "Security" securityTests
    , testGroup "Invariants" invariantTests
    ]

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

-- | Generate arbitrary content
genContent :: Gen ByteString
genContent = Gen.bytes (Range.linear 1 1000)

-- | Generate a list of contents
genContents :: Gen [ByteString]
genContents = Gen.list (Range.linear 0 50) genContent

--------------------------------------------------------------------------------
-- Construction Tests
--------------------------------------------------------------------------------

constructionTests :: [TestTree]
constructionTests =
  [ testProperty "empty has size 0" prop_emptySize
  , testProperty "empty is null" prop_emptyNull
  , testProperty "singleton has size 1" prop_singletonSize
  ]

-- | Empty HAMT has size 0
prop_emptySize :: Property
prop_emptySize = property $ do
  HAMT.size HAMT.empty === 0

-- | Empty HAMT is null
prop_emptyNull :: Property
prop_emptyNull = property $ do
  assert (HAMT.null HAMT.empty)

-- | Singleton HAMT has size 1
prop_singletonSize :: Property
prop_singletonSize = property $ do
  content <- forAll genContent
  let (_, hamt) = HAMT.singleton content
  HAMT.size hamt === 1

--------------------------------------------------------------------------------
-- Operation Tests
--------------------------------------------------------------------------------

operationTests :: [TestTree]
operationTests =
  [ testProperty "insert-lookup consistency" prop_insertLookup
  , testProperty "insert-member consistency" prop_insertMember
  , testProperty "delete-lookup consistency" prop_deleteLookup
  , testProperty "insert is idempotent" prop_insertIdempotent
  , testProperty "bulk insert preserves all contents" prop_bulkInsert
  , testProperty "bulk insert size equals unique count" prop_bulkInsertSize
  ]

-- | Insert then lookup returns the content
prop_insertLookup :: Property
prop_insertLookup = property $ do
  content <- forAll genContent
  let (key, hamt) = HAMT.insert content HAMT.empty
  HAMT.lookup key hamt === Just content

-- | Insert then member returns True
prop_insertMember :: Property
prop_insertMember = property $ do
  content <- forAll genContent
  let (key, hamt) = HAMT.insert content HAMT.empty
  assert (HAMT.member key hamt)

-- | Delete then lookup returns Nothing
prop_deleteLookup :: Property
prop_deleteLookup = property $ do
  content <- forAll genContent
  let (key, hamt) = HAMT.insert content HAMT.empty
      hamt' = HAMT.delete key hamt
  HAMT.lookup key hamt' === Nothing

-- | Inserting same content twice is idempotent
prop_insertIdempotent :: Property
prop_insertIdempotent = property $ do
  content <- forAll genContent
  let (key1, hamt1) = HAMT.insert content HAMT.empty
      (key2, hamt2) = HAMT.insert content hamt1
  key1 === key2
  HAMT.size hamt1 === HAMT.size hamt2

-- | Bulk insert preserves all contents (all can be looked up)
prop_bulkInsert :: Property
prop_bulkInsert = property $ do
  contents <- forAll genContents
  let insertAll cs h = foldr (\c (ks, h') -> let (k, h'') = HAMT.insert c h' in (k : ks, h'')) ([], h) cs
      (keys, hamt) = insertAll contents HAMT.empty
  -- Every key should be present and return original content
  let pairs = zip keys contents
  mapM_ (\(k, c) -> HAMT.lookup k hamt === Just c) pairs

-- | Bulk insert size equals number of unique contents
prop_bulkInsertSize :: Property
prop_bulkInsertSize = property $ do
  contents <- forAll genContents
  -- Only the final HAMT matters, not the keys - use snd to discard keys
  let insertAll cs h = foldl (\h' c -> snd (HAMT.insert c h')) h cs
      hamt = insertAll contents HAMT.empty
      -- Count unique contents (content-addressed means duplicates merge)
      uniqueCount = length (foldr (\c acc -> if c `elem` acc then acc else c : acc) [] contents)
  HAMT.size hamt === uniqueCount

--------------------------------------------------------------------------------
-- Property Tests (Content-Addressability)
--------------------------------------------------------------------------------

propertyTests :: [TestTree]
propertyTests =
  [ testProperty "same content → same key" prop_contentAddressable
  , testProperty "different content → different key (usually)" prop_differentContent
  , testProperty "key matches mkStorageKey" prop_keyConsistency
  ]

-- | Same content always produces same key
prop_contentAddressable :: Property
prop_contentAddressable = property $ do
  content <- forAll genContent
  let (key1, _) = HAMT.insert content HAMT.empty
      (key2, _) = HAMT.insert content HAMT.empty
  key1 === key2

-- | Different content produces different keys (with high probability)
prop_differentContent :: Property
prop_differentContent = property $ do
  content1 <- forAll genContent
  content2 <- forAll genContent
  let (key1, _) = HAMT.insert content1 HAMT.empty
      (key2, _) = HAMT.insert content2 HAMT.empty
  -- Only assert if contents are different
  if content1 == content2
    then key1 === key2
    else assert (key1 /= key2)

-- | HAMT key matches standalone mkStorageKey
prop_keyConsistency :: Property
prop_keyConsistency = property $ do
  content <- forAll genContent
  let (hamtKey, _) = HAMT.insert content HAMT.empty
      standaloneKey = mkStorageKey content
  hamtKey === standaloneKey

--------------------------------------------------------------------------------
-- Memory Tests
--------------------------------------------------------------------------------

memoryTests :: [TestTree]
memoryTests =
  [ testProperty "large content handled" prop_largeContent
  , testProperty "many entries handled" prop_manyEntries
  , testProperty "structure sharing works" prop_structureSharing
  ]

-- | Large content should be handled without issues
prop_largeContent :: Property
prop_largeContent = withTests 10 $ property $ do
  -- Generate 100KB content
  content <- forAll $ Gen.bytes (Range.linear 50000 100000)
  let (key, hamt) = HAMT.insert content HAMT.empty
  HAMT.lookup key hamt === Just content

-- | Many entries should be handled
prop_manyEntries :: Property
prop_manyEntries = withTests 10 $ property $ do
  -- Generate 1000 unique entries
  let contents = map (\i -> BS8.pack ("content" <> show i)) [1..1000 :: Int]
  let (keys, hamt) = HAMT.fromList contents
  -- All should be retrievable
  length keys === 1000
  HAMT.size hamt === 1000

-- | Structure sharing should work (old versions remain valid)
prop_structureSharing :: Property
prop_structureSharing = property $ do
  content1 <- forAll genContent
  content2 <- forAll genContent
  let (key1, hamt1) = HAMT.insert content1 HAMT.empty
      (key2, hamt2) = HAMT.insert content2 hamt1
  -- Old version should still work
  HAMT.lookup key1 hamt1 === Just content1
  -- New version should have both
  HAMT.lookup key1 hamt2 === Just content1
  HAMT.lookup key2 hamt2 === Just content2

--------------------------------------------------------------------------------
-- Security Tests  
--------------------------------------------------------------------------------

securityTests :: [TestTree]
securityTests =
  [ testProperty "poison content is stored safely" prop_poisonContentSafe
  , testProperty "binary content preserved exactly" prop_binaryExact
  , testProperty "null bytes handled" prop_nullBytes
  ]

-- | Poison pill content should be stored and retrieved safely
prop_poisonContentSafe :: Property
prop_poisonContentSafe = withTests 100 $ property $ do
  -- Generate adversarial content
  poison <- forAll $ Gen.element
    [ "'; DROP TABLE--"
    , "<script>alert(1)</script>"
    , "null\x00byte"
    , "\x1B[2J"  -- ANSI escape
    ]
  let content = BS8.pack poison
  let (key, hamt) = HAMT.insert content HAMT.empty
  -- Should be stored and retrieved exactly
  HAMT.lookup key hamt === Just content

-- | Binary content should be preserved exactly
prop_binaryExact :: Property
prop_binaryExact = withTests 200 $ property $ do
  content <- forAll genContent
  let (key, hamt) = HAMT.insert content HAMT.empty
  case HAMT.lookup key hamt of
    Nothing -> assert False
    Just retrieved -> retrieved === content

-- | Null bytes should be handled correctly
prop_nullBytes :: Property
prop_nullBytes = property $ do
  let content = BS8.pack "before\x00after"
  let (key, hamt) = HAMT.insert content HAMT.empty
  case HAMT.lookup key hamt of
    Nothing -> assert False
    Just retrieved -> BS.length retrieved === BS.length content

--------------------------------------------------------------------------------
-- Invariant Tests
--------------------------------------------------------------------------------

invariantTests :: [TestTree]
invariantTests =
  [ testProperty "determinism: same input same key always" prop_deterministic
  , testProperty "collision resistance: different input different key" prop_collisionResistant
  , testProperty "delete is complete" prop_deleteComplete
  , testProperty "insert-delete-insert idempotent" prop_insertDeleteInsert
  ]

-- | Same input always produces same key (deterministic)
prop_deterministic :: Property
prop_deterministic = withTests 200 $ property $ do
  content <- forAll genContent
  let (key1, _) = HAMT.singleton content
      (key2, _) = HAMT.singleton content
      (key3, _) = HAMT.insert content HAMT.empty
  key1 === key2
  key2 === key3

-- | Different input produces different key (collision resistance)
prop_collisionResistant :: Property
prop_collisionResistant = withTests 500 $ property $ do
  content1 <- forAll genContent
  content2 <- forAll genContent
  if content1 == content2
    then do
      let (k1, _) = HAMT.singleton content1
          (k2, _) = HAMT.singleton content2
      k1 === k2
    else do
      let (k1, _) = HAMT.singleton content1
          (k2, _) = HAMT.singleton content2
      assert (k1 /= k2)

-- | Delete should completely remove entry
prop_deleteComplete :: Property
prop_deleteComplete = property $ do
  content <- forAll genContent
  let (key, hamt1) = HAMT.insert content HAMT.empty
      hamt2 = HAMT.delete key hamt1
  -- Should not be member
  assert (not (HAMT.member key hamt2))
  -- Lookup should return Nothing
  HAMT.lookup key hamt2 === Nothing
  -- Size should be 0
  HAMT.size hamt2 === 0

-- | Insert, delete, insert should work correctly
prop_insertDeleteInsert :: Property
prop_insertDeleteInsert = property $ do
  content <- forAll genContent
  let (key1, hamt1) = HAMT.insert content HAMT.empty
      hamt2 = HAMT.delete key1 hamt1
      (key2, hamt3) = HAMT.insert content hamt2
  -- Keys should be the same (content-addressed)
  key1 === key2
  -- Final state should have the content
  HAMT.lookup key2 hamt3 === Just content
  HAMT.size hamt3 === 1
