{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                              // foundry // task
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Agent.Task
Description : Task definitions for multi-agent allocation
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Tasks represent units of work that can be assigned to agents.
Each task has a cost (budget consumption) and value (priority/importance).

== Task Properties

@
cost    :: Task → Nat         -- Resources required (USD cents)
value   :: Task → Nat         -- Priority/importance weight
requires :: Task → PermissionSet  -- Required permissions
@

== Invariants

@
∀ task. taskCost task > 0           -- Tasks must cost something
∀ task. taskValue task > 0          -- Tasks must have value
∀ task. taskId task is UUID5        -- Deterministic ID
@

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Agent.Task
  ( -- * Types
    Task (..)
  , TaskId (..)
  , TaskCost (..)
  , TaskValue (..)

    -- * Smart constructors
  , mkTask
  , mkTaskId

    -- * Queries
  , taskRequiresPermission
  ) where

import Data.ByteString qualified as BS
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text.Encoding qualified as TE
import Data.UUID (UUID)
import Data.UUID.V5 qualified as UUID5
import Foundry.Core.Agent.Permission (Permission, PermissionSet (..))

-- | Task identifier (UUID5 for determinism)
newtype TaskId = TaskId {unTaskId :: UUID}
  deriving stock (Eq, Ord, Show)

-- | Task cost in USD cents (must be positive)
newtype TaskCost = TaskCost {unTaskCost :: Int}
  deriving stock (Eq, Ord, Show)

-- | Task value/priority (must be positive)
newtype TaskValue = TaskValue {unTaskValue :: Int}
  deriving stock (Eq, Ord, Show)

-- | A unit of work assignable to an agent
data Task = Task
  { taskId          :: !TaskId           -- ^ Unique identifier (UUID5)
  , taskLabel       :: !Text             -- ^ Human-readable description
  , taskCost        :: !TaskCost         -- ^ Budget consumption (cents)
  , taskValue       :: !TaskValue        -- ^ Priority/importance weight
  , taskPermissions :: !PermissionSet    -- ^ Required permissions
  , taskDependsOn   :: !(Set TaskId)     -- ^ Tasks that must complete first
  }
  deriving stock (Eq, Show)

-- | Namespace UUID for task IDs (constant for reproducibility)
taskNamespace :: UUID
taskNamespace = UUID5.generateNamed UUID5.namespaceURL (BS.unpack $ TE.encodeUtf8 "foundry:task")

-- | Create task ID from label (deterministic via UUID5)
mkTaskId :: Text -> TaskId
mkTaskId label = TaskId (UUID5.generateNamed taskNamespace (BS.unpack $ TE.encodeUtf8 label))

-- | Create a task with validation
--
-- Returns Nothing if cost or value is non-positive.
mkTask 
  :: Text            -- ^ Label
  -> Int             -- ^ Cost (cents)
  -> Int             -- ^ Value
  -> PermissionSet   -- ^ Required permissions
  -> Set TaskId      -- ^ Dependencies
  -> Maybe Task
mkTask label cost value perms deps
  | cost <= 0 = Nothing
  | value <= 0 = Nothing
  | otherwise = Just Task
      { taskId = mkTaskId label
      , taskLabel = label
      , taskCost = TaskCost cost
      , taskValue = TaskValue value
      , taskPermissions = perms
      , taskDependsOn = deps
      }

-- | Check if task requires a specific permission
taskRequiresPermission :: Permission -> Task -> Bool
taskRequiresPermission perm task =
  Set.member perm (unPermissionSet (taskPermissions task))
