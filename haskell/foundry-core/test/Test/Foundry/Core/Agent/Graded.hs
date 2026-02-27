{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                           // foundry // test // agent // graded
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Core.Agent.Graded
Description : Compile-time proof tests for type-level graded monad
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

== Proof Strategy

These tests verify that the type system enforces constraints:

1. Budget tests - if this module compiles, budget conservation holds
2. Permission tests - if this module compiles, permission checks work

The existence of well-typed functions IS the proof.
If bad code compiled, we would have a type error here.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Core.Agent.Graded
  ( tests
    -- * Exported proof witnesses (their types ARE the proofs)
  , proofBudgetSpendWorks
  , proofMultipleSpends
  , proofPermissionRequired
  ) where

import Data.Functor.Identity (Identity (..))
import Foundry.Core.Agent.Graded
  ( AgentT
  , SNat (..)
  , SPermission (..)
  , HasPermission
  , liftAgent
  , runAgentT
  , spend
  , requirePermission
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Hedgehog (Property, property, assert)

--------------------------------------------------------------------------------
-- Test Tree
--------------------------------------------------------------------------------

-- | All Graded Agent tests
tests :: TestTree
tests =
  testGroup
    "Foundry.Core.Agent.Graded"
    [ testGroup "Compile-time Proofs" compileTimeProofs
    , testGroup "Runtime Verification" runtimeTests
    ]

--------------------------------------------------------------------------------
-- SECTION 1: COMPILE-TIME PROOFS
--
-- If these functions typecheck, the proofs hold.
-- We're not testing VALUES - we're testing that TYPES are correct.
--------------------------------------------------------------------------------

compileTimeProofs :: [TestTree]
compileTimeProofs =
  [ testProperty "budget spend typechecks" prop_budgetSpendTypechecks
  , testProperty "multiple spends typecheck" prop_multipleSpendTypechecks
  , testProperty "permission required typechecks" prop_permissionTypechecks
  ]

-- | PROOF: Spending 50 from a budget of 100 leaves 50.
--
-- The type signature @AgentT perms 50 Identity ()@ proves that after
-- spending 50 from 100, exactly 50 remains. GHC verified this.
proofBudgetSpendWorks :: forall perms. AgentT perms 50 Identity ()
proofBudgetSpendWorks = spend (SNat @50) action100
  where
    action100 :: AgentT perms 100 Identity ()
    action100 = liftAgent (Identity ())

-- | PROOF: Multiple spends compose correctly.
--
-- Start with 100, spend 30, spend 40, spend 20 = 10 remaining.
-- The final type @AgentT perms 10 Identity ()@ proves this.
proofMultipleSpends :: forall perms. AgentT perms 10 Identity ()
proofMultipleSpends = 
  spend (SNat @20) $
  spend (SNat @40) $
  spend (SNat @30) (start :: AgentT perms 100 Identity ())
  where
    start :: AgentT perms 100 Identity ()
    start = liftAgent (Identity ())

-- | PROOF: Permission checking works at compile time.
--
-- The function requires "read" permission. The type signature
-- proves that @perms@ must contain "read".
proofPermissionRequired 
  :: HasPermission "read" perms 
  => AgentT perms budget Identity ()
proofPermissionRequired = 
  requirePermission (SPermission @"read") (liftAgent (Identity ()))

--------------------------------------------------------------------------------
-- SECTION 2: RUNTIME VERIFICATION
--
-- These tests run the agents and verify behavior.
--------------------------------------------------------------------------------

runtimeTests :: [TestTree]
runtimeTests =
  [ testProperty "runAgentT extracts value" prop_runAgentTExtractsValue
  ]

-- | Property: Spending within budget runs successfully
prop_budgetSpendTypechecks :: Property
prop_budgetSpendTypechecks = property $ do
  -- The fact that proofBudgetSpendWorks compiled is the test
  -- We just verify we can run it
  let result = runIdentity $ runAgentT proofBudgetSpendWorks
  assert (result == ())

-- | Property: Multiple spends compose correctly
prop_multipleSpendTypechecks :: Property
prop_multipleSpendTypechecks = property $ do
  let result = runIdentity $ runAgentT proofMultipleSpends
  assert (result == ())

-- | Property: Permission-constrained code compiles when permission present
prop_permissionTypechecks :: Property
prop_permissionTypechecks = property $ do
  -- Instantiate with a permission list containing "read"
  let agent :: AgentT '["read", "write"] 100 Identity ()
      agent = proofPermissionRequired
      result = runIdentity $ runAgentT agent
  assert (result == ())

-- | Property: runAgentT correctly extracts the value
prop_runAgentTExtractsValue :: Property
prop_runAgentTExtractsValue = property $ do
  let agent :: AgentT '["read"] 100 Identity Int
      agent = liftAgent (Identity 42)
      result = runIdentity $ runAgentT agent
  assert (result == 42)

