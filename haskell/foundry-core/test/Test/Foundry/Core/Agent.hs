{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // foundry // test // core // agent
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Core.Agent
Description : Property tests for Agent module (Permission, Budget, Context)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

== Verified Properties

* Permission set monotonicity: granting is additive
* Budget conservation: total = spent + remaining
* Budget spending: only succeeds when sufficient funds exist

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Core.Agent
  ( tests
  ) where

import Data.Set qualified as Set
import Hedgehog (Gen, Property, forAll, property, (===), assert)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Foundry.Core.Agent.Budget
  ( Budget (..)
  , BudgetLimit (..)
  , isBudgetExhausted
  , mkBudget
  , remainingBudget
  , spendBudget
  )
import Foundry.Core.Agent.Permission
  ( Permission (..)
  , PermissionSet (..)
  , grantPermission
  , hasPermission
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

--------------------------------------------------------------------------------
-- Test Tree
--------------------------------------------------------------------------------

-- | All Agent module tests
tests :: TestTree
tests =
  testGroup
    "Foundry.Core.Agent"
    [ testGroup "Permission" permissionTests
    , testGroup "Budget" budgetTests
    ]

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

-- | Generate an arbitrary Permission
genPermission :: Gen Permission
genPermission = Gen.enumBounded

-- | Generate a list of permissions
genPermissions :: Gen [Permission]
genPermissions = Gen.list (Range.linear 0 10) genPermission

-- | Generate a BudgetLimit (positive integer in cents)
genBudgetLimit :: Gen BudgetLimit
genBudgetLimit = BudgetLimit <$> Gen.int (Range.linear 1 100000)

-- | Generate an amount to spend (positive integer in cents)
-- Used by budget spending tests via spendBudget
_genSpendAmount :: Gen Int
_genSpendAmount = Gen.int (Range.linear 0 50000)

--------------------------------------------------------------------------------
-- Permission Tests
--------------------------------------------------------------------------------

permissionTests :: [TestTree]
permissionTests =
  [ testProperty "grant adds permission" prop_grantAddsPermission
  , testProperty "grant is idempotent" prop_grantIdempotent
  , testProperty "empty set has no permissions" prop_emptySetNoPermissions
  , testProperty "grant is monotonic" prop_grantMonotonic
  ]

-- | Granting a permission makes hasPermission return True
prop_grantAddsPermission :: Property
prop_grantAddsPermission = property $ do
  p <- forAll genPermission
  let emptySet = PermissionSet Set.empty
      withPerm = grantPermission p emptySet
  assert (hasPermission p withPerm)

-- | Granting the same permission twice has no additional effect
prop_grantIdempotent :: Property
prop_grantIdempotent = property $ do
  p <- forAll genPermission
  let emptySet = PermissionSet Set.empty
      once = grantPermission p emptySet
      twice = grantPermission p once
  once === twice

-- | Empty permission set contains no permissions
prop_emptySetNoPermissions :: Property
prop_emptySetNoPermissions = property $ do
  p <- forAll genPermission
  let emptySet = PermissionSet Set.empty
  assert (not (hasPermission p emptySet))

-- | Granting permissions is monotonic (set only grows)
prop_grantMonotonic :: Property
prop_grantMonotonic = property $ do
  perms <- forAll genPermissions
  let emptySet = PermissionSet Set.empty
      sizes = scanl (\(PermissionSet s) p -> grantPermission p (PermissionSet s)) emptySet perms
      sizeList = fmap (\(PermissionSet s) -> Set.size s) sizes
  -- Verify sizes are monotonically non-decreasing
  assert (isMonotonic sizeList)
  where
    isMonotonic :: [Int] -> Bool
    isMonotonic xs = and (zipWith (<=) xs (drop 1 xs))

--------------------------------------------------------------------------------
-- Budget Tests
--------------------------------------------------------------------------------

budgetTests :: [TestTree]
budgetTests =
  [ testProperty "conservation law" prop_budgetConservation
  , testProperty "new budget has zero spent" prop_newBudgetZeroSpent
  , testProperty "spend fails on insufficient funds" prop_spendFailsInsufficient
  , testProperty "spend succeeds on sufficient funds" prop_spendSucceedsSufficient
  , testProperty "exhausted check consistent" prop_exhaustedConsistent
  ]

-- | Budget conservation: limit = spent + remaining
prop_budgetConservation :: Property
prop_budgetConservation = property $ do
  limit <- forAll genBudgetLimit
  let budget = mkBudget limit
  unBudgetLimit limit === budgetSpent budget + remainingBudget budget

-- | A new budget has zero spent
prop_newBudgetZeroSpent :: Property
prop_newBudgetZeroSpent = property $ do
  limit <- forAll genBudgetLimit
  let budget = mkBudget limit
  budgetSpent budget === 0

-- | Spending more than remaining fails
prop_spendFailsInsufficient :: Property
prop_spendFailsInsufficient = property $ do
  limit <- forAll genBudgetLimit
  let budget = mkBudget limit
      overSpend = unBudgetLimit limit + 1
  spendBudget overSpend budget === Nothing

-- | Spending within budget succeeds and updates correctly
prop_spendSucceedsSufficient :: Property
prop_spendSucceedsSufficient = property $ do
  limit <- forAll genBudgetLimit
  amount <- forAll $ Gen.int (Range.linear 0 (unBudgetLimit limit))
  let budget = mkBudget limit
  case spendBudget amount budget of
    Nothing -> assert False  -- Should succeed
    Just newBudget -> do
      budgetSpent newBudget === amount
      remainingBudget newBudget === unBudgetLimit limit - amount
      -- Conservation still holds
      unBudgetLimit limit === budgetSpent newBudget + remainingBudget newBudget

-- | isBudgetExhausted returns True iff remaining <= 0
prop_exhaustedConsistent :: Property
prop_exhaustedConsistent = property $ do
  limit <- forAll genBudgetLimit
  let budget = mkBudget limit
  isBudgetExhausted budget === (remainingBudget budget <= 0)
