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
import Hedgehog (Gen, Property, forAll, property, (===), assert)
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
  let insertAll cs h = foldr (\c (_, h') -> HAMT.insert c h') (undefined, h) cs
      (_, hamt) = insertAll contents HAMT.empty
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
