{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // foundry // allocation
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Agent.Allocation
Description : Multi-agent task allocation via Integer Linear Programming
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Optimal task allocation for billion-agent swarms using ILP.

== The Multi-Agent Allocation Problem

Given:
  - N agents with capacities c_i and permission sets P_i
  - M tasks with costs t_j, values v_j, and required permissions R_j
  - Global budget B

Find:
  - Assignment matrix x_ij ∈ {0,1} (agent i does task j)

Maximize:
  Σ_ij v_j · x_ij              (total value delivered)

Subject to:
  Σ_j t_j · x_ij ≤ c_i  ∀i    (agent capacity constraint)
  Σ_i x_ij ≤ 1          ∀j    (task done at most once)
  Σ_ij t_j · x_ij ≤ B         (global budget constraint)
  P_i ⊇ R_j when x_ij = 1     (permission constraint)

== Complexity

This is a variant of the Generalized Assignment Problem (GAP).
GAP is NP-hard in general, but tractable for:
  - Small N (< 1000 agents per allocation batch)
  - Sparse constraint matrices
  - Branch-and-bound with good LP relaxation

For billion-agent scale, we partition into O(N/1000) subproblems.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Agent.Allocation
  ( -- * Problem types
    AllocationProblem (..)
  , AgentCapacity (..)
  , GlobalBudget (..)
  
    -- * Solution types
  , AllocationSolution (..)
  , Assignment (..)
  , AllocationError (..)
  
    -- * Problem construction
  , mkAllocationProblem
  , addAgent
  , addTask
  
    -- * Solution queries
  , assignedTasks
  , assignedAgent
  , totalValue
  , totalCost
  , isOptimal
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Foundry.Core.Agent.Budget (Budget (..), BudgetLimit (..))
import Foundry.Core.Agent.Context (AgentContext (..), AgentId (..))
import Foundry.Core.Agent.Permission (PermissionSet (..))
import Foundry.Core.Agent.Task (Task (..), TaskId (..))

-- | Global budget constraint for entire allocation
newtype GlobalBudget = GlobalBudget {unGlobalBudget :: Int}
  deriving stock (Eq, Ord, Show)

-- | Agent capacity (budget available for task assignment)
newtype AgentCapacity = AgentCapacity {unAgentCapacity :: Int}
  deriving stock (Eq, Ord, Show)

-- | The multi-agent allocation problem
data AllocationProblem = AllocationProblem
  { problemAgents      :: !(Map AgentId AgentCapacity)     -- ^ Agent capacities
  , problemPermissions :: !(Map AgentId PermissionSet)     -- ^ Agent permissions
  , problemTasks       :: !(Map TaskId Task)               -- ^ Tasks to assign
  , problemGlobalBudget :: !GlobalBudget                   -- ^ Global budget limit
  , problemDependencies :: !(Map TaskId (Set TaskId))      -- ^ Task dependencies
  }
  deriving stock (Eq, Show)

-- | An assignment of a task to an agent
data Assignment = Assignment
  { assignmentAgent :: !AgentId
  , assignmentTask  :: !TaskId
  }
  deriving stock (Eq, Ord, Show)

-- | Solution to the allocation problem
data AllocationSolution = AllocationSolution
  { solutionAssignments   :: !(Set Assignment)   -- ^ Task → Agent assignments
  , solutionTotalValue    :: !Int                -- ^ Total value achieved
  , solutionTotalCost     :: !Int                -- ^ Total cost incurred
  , solutionOptimalityGap :: !Double             -- ^ Gap from LP relaxation (0 = optimal)
  , solutionUnassigned    :: !(Set TaskId)       -- ^ Tasks that couldn't be assigned
  }
  deriving stock (Eq, Show)

-- | Errors that can occur during allocation
data AllocationError
  = NoAgents                       -- ^ No agents in problem
  | NoTasks                        -- ^ No tasks in problem
  | InfeasibleBudget               -- ^ No valid assignment within budget
  | InfeasiblePermissions          -- ^ No agent can handle some task
  | CyclicDependencies             -- ^ Task dependencies form a cycle
  | SolverTimeout                  -- ^ ILP solver timed out
  deriving stock (Eq, Show)

-- | Create an empty allocation problem
mkAllocationProblem :: GlobalBudget -> AllocationProblem
mkAllocationProblem globalBudget = AllocationProblem
  { problemAgents = Map.empty
  , problemPermissions = Map.empty
  , problemTasks = Map.empty
  , problemGlobalBudget = globalBudget
  , problemDependencies = Map.empty
  }

-- | Add an agent to the problem
addAgent :: AgentContext -> AllocationProblem -> AllocationProblem
addAgent ctx problem = problem
  { problemAgents = Map.insert agentId capacity (problemAgents problem)
  , problemPermissions = Map.insert agentId perms (problemPermissions problem)
  }
  where
    agentId = contextAgentId ctx
    capacity = AgentCapacity (unBudgetLimit (budgetLimit (contextBudget ctx)))
    perms = contextPermissions ctx

-- | Add a task to the problem
addTask :: Task -> AllocationProblem -> AllocationProblem
addTask task problem = problem
  { problemTasks = Map.insert (taskId task) task (problemTasks problem)
  , problemDependencies = Map.insert (taskId task) (taskDependsOn task) (problemDependencies problem)
  }

-- | Get all tasks assigned to an agent
assignedTasks :: AgentId -> AllocationSolution -> Set TaskId
assignedTasks agentId solution =
  Set.map assignmentTask $
    Set.filter (\a -> assignmentAgent a == agentId) (solutionAssignments solution)

-- | Get the agent assigned to a task (if any)
assignedAgent :: TaskId -> AllocationSolution -> Maybe AgentId
assignedAgent taskId solution =
  case Set.toList $ Set.filter (\a -> assignmentTask a == taskId) (solutionAssignments solution) of
    [a] -> Just (assignmentAgent a)
    _   -> Nothing

-- | Get total value of solution
totalValue :: AllocationSolution -> Int
totalValue = solutionTotalValue

-- | Get total cost of solution
totalCost :: AllocationSolution -> Int
totalCost = solutionTotalCost

-- | Check if solution is proven optimal
isOptimal :: AllocationSolution -> Bool
isOptimal solution = solutionOptimalityGap solution == 0.0
