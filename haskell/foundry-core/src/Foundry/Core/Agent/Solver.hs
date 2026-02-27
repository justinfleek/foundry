{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                          // foundry // solver
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Agent.Solver
Description : Allocation problem to ILP translation and solving
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Translates AllocationProblem to ILP and solves.

== Dependencies

This module: Foundry.Core.Agent.Allocation, Foundry.Core.Agent.ILP
Dependents:  External consumers

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Agent.Solver
  ( -- * Solver
    solveAllocation
  
    -- * Re-exports
  , AllocationError (..)
  , AllocationSolution (..)
  ) where

import Foundry.Core.Agent.Allocation
  ( AllocationProblem (..)
  , AllocationSolution (..)
  , AllocationError (..)
  , Assignment (..)
  , AgentCapacity (..)
  , GlobalBudget (..)
  )
import Foundry.Core.Agent.ILP
  ( ILPProblem (..)
  , ILPSolution (..)
  , Objective (..)
  , Constraint (..)
  , Relation (..)
  , VarBounds (..)
  , SolveResult (..)
  , solve
  )
import Foundry.Core.Agent.Task (Task (..), TaskCost (..), TaskValue (..))

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

-- | Solve allocation problem
solveAllocation :: AllocationProblem -> Either AllocationError AllocationSolution
solveAllocation problem
  | Map.null (problemAgents problem) = Left NoAgents
  | Map.null (problemTasks problem) = Left NoTasks
  | otherwise = translateAndSolve problem

-- | Translate problem to ILP and solve
translateAndSolve :: AllocationProblem -> Either AllocationError AllocationSolution
translateAndSolve problem =
  case solve (toILP problem) of
    Optimal sol   -> Right (fromILPSolution problem sol)
    Feasible sol  -> Right (fromILPSolution problem sol)
    Infeasible    -> Left InfeasibleBudget
    Unbounded     -> Left InfeasibleBudget

-- | Convert allocation problem to ILP
toILP :: AllocationProblem -> ILPProblem
toILP problem = ILPProblem
  { ilpObjective = Maximize
  , ilpObjCoeffs = objectiveCoeffs
  , ilpConstraints = constraints
  , ilpBounds = bounds
  , ilpNumVars = numVars
  }
  where
    agents = Map.keys (problemAgents problem)
    tasks = Map.keys (problemTasks problem)
    n = length agents
    m = length tasks
    numVars = n * m  -- x_ij for each (agent, task) pair
    
    -- Objective: maximize Σ value_j * x_ij
    objectiveCoeffs =
      [ taskVal j
      | _i <- [0 .. n - 1]
      , j <- [0 .. m - 1]
      ]
    
    taskVal :: Int -> Int
    taskVal j = 
      let tid = tasks !! j
      in case Map.lookup tid (problemTasks problem) of
        Just t  -> unTaskValue (taskValue t)
        Nothing -> 0
    
    taskCst :: Int -> Int
    taskCst j =
      let tid = tasks !! j
      in case Map.lookup tid (problemTasks problem) of
        Just t  -> unTaskCost (taskCost t)
        Nothing -> 0
    
    agentCap :: Int -> Int
    agentCap i =
      let aid = agents !! i
      in case Map.lookup aid (problemAgents problem) of
        Just c  -> unAgentCapacity c
        Nothing -> 0
    
    constraints = agentConstraints <> taskConstraints <> [globalConstraint]
    
    -- Agent capacity: Σ_j cost_j * x_ij ≤ capacity_i
    agentConstraints =
      [ Constraint
          { constraintCoeffs = 
              [ if i' == i then taskCst j else 0
              | i' <- [0 .. n - 1]
              , j <- [0 .. m - 1]
              ]
          , constraintRel = LessEq
          , constraintRHS = agentCap i
          }
      | i <- [0 .. n - 1]
      ]
    
    -- Task assignment: Σ_i x_ij ≤ 1 (each task done at most once)
    taskConstraints =
      [ Constraint
          { constraintCoeffs =
              [ if j' == j then 1 else 0
              | _ <- [0 .. n - 1]
              , j' <- [0 .. m - 1]
              ]
          , constraintRel = LessEq
          , constraintRHS = 1
          }
      | j <- [0 .. m - 1]
      ]
    
    -- Global budget: Σ_ij cost_j * x_ij ≤ globalBudget
    globalConstraint = Constraint
      { constraintCoeffs =
          [ taskCst j
          | _ <- [0 .. n - 1]
          , j <- [0 .. m - 1]
          ]
      , constraintRel = LessEq
      , constraintRHS = unGlobalBudget (problemGlobalBudget problem)
      }
    
    -- Binary bounds: 0 ≤ x_ij ≤ 1
    bounds = replicate numVars (VarBounds 0 1)

-- | Convert ILP solution back to allocation solution
fromILPSolution :: AllocationProblem -> ILPSolution -> AllocationSolution
fromILPSolution problem ilpSol = AllocationSolution
  { solutionAssignments = assignments
  , solutionTotalValue = solObjValue ilpSol
  , solutionTotalCost = computeTotalCost
  , solutionOptimalityGap = solGap ilpSol
  , solutionUnassigned = unassignedTasks
  }
  where
    agents = Map.keys (problemAgents problem)
    tasks = Map.keys (problemTasks problem)
    numAgents = length agents
    m = length tasks
    values = solValues ilpSol
    
    -- Extract assignments where x_ij = 1
    assignments = Set.fromList
      [ Assignment (agents !! i) (tasks !! j)
      | i <- [0 .. numAgents - 1]
      , j <- [0 .. m - 1]
      , let idx = i * m + j
      , idx < length values
      , values !! idx == 1
      ]
    
    assignedTaskIds = Set.map assignmentTask assignments
    unassignedTasks = Set.fromList tasks `Set.difference` assignedTaskIds
    
    computeTotalCost = sum
      [ unTaskCost (taskCost t)
      | a <- Set.toList assignments
      , Just t <- [Map.lookup (assignmentTask a) (problemTasks problem)]
      ]
