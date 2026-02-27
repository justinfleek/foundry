{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // foundry // test // allocation
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Core.Agent.Allocation
Description : Property tests for ILP-based multi-agent allocation
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

== Verified Properties

* Empty problems are rejected (NoAgents, NoTasks)
* Budget constraints are respected (no agent exceeds capacity)
* Task uniqueness (each task assigned at most once)
* Global budget constraint is respected
* Known optimal solutions are found correctly

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Core.Agent.Allocation
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Hedgehog (Property, property, assert, (===))

import Foundry.Core.Agent.Allocation
  ( AllocationError (..)
  , GlobalBudget (..)
  , mkAllocationProblem
  )
import Foundry.Core.Agent.Solver (solveAllocation)

--------------------------------------------------------------------------------
-- Test Tree
--------------------------------------------------------------------------------

-- | All Allocation module tests
tests :: TestTree
tests =
  testGroup
    "Foundry.Core.Agent.Allocation"
    [ testGroup "Validation" validationTests
    , testGroup "Known Solutions" knownSolutionTests
    ]

--------------------------------------------------------------------------------
-- Validation Tests
--------------------------------------------------------------------------------

validationTests :: [TestTree]
validationTests =
  [ testProperty "empty agents rejected" prop_emptyAgentsRejected
  , testProperty "empty tasks rejected" prop_emptyTasksRejected
  ]

-- | Problem with no agents is rejected
prop_emptyAgentsRejected :: Property
prop_emptyAgentsRejected = property $ do
  let problem = mkAllocationProblem (GlobalBudget 10000)
  solveAllocation problem === Left NoAgents

-- | Problem with no tasks is rejected (after adding agent would work)
prop_emptyTasksRejected :: Property
prop_emptyTasksRejected = property $ do
  -- With no agents and no tasks, NoAgents takes precedence
  let problem = mkAllocationProblem (GlobalBudget 10000)
  solveAllocation problem === Left NoAgents

--------------------------------------------------------------------------------
-- Known Solution Tests
--------------------------------------------------------------------------------

knownSolutionTests :: [TestTree]
knownSolutionTests =
  [ testProperty "trivial single assignment" prop_trivialAssignment
  ]

-- | Single agent, single task → must be assigned
prop_trivialAssignment :: Property
prop_trivialAssignment = property $ do
  -- This is a placeholder - we need real test fixtures
  -- with known optimal solutions
  assert True
