{- |
Module      : Foundry.Core.Agent.Context
Description : Agent execution context
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Execution context carrying environment requirements.
-}
module Foundry.Core.Agent.Context
  ( -- * Types
    AgentContext (..)
  , AgentId (..)

    -- * Smart constructors
  , mkAgentContext
  ) where

import Data.Text (Text)
import Data.UUID (UUID)
import Foundry.Core.Agent.Budget (Budget)
import Foundry.Core.Agent.Permission (PermissionSet)

-- | Agent identifier (UUID5)
newtype AgentId = AgentId {unAgentId :: UUID}
  deriving stock (Eq, Ord, Show)

-- | Agent execution context
data AgentContext = AgentContext
  { contextAgentId :: !AgentId
  , contextPermissions :: !PermissionSet
  , contextBudget :: !Budget
  , contextParentId :: !(Maybe AgentId)  -- ^ For hierarchical agent trees
  , contextLabel :: !Text                -- ^ Human-readable description
  }
  deriving stock (Eq, Show)

-- | Create agent context
mkAgentContext :: AgentId -> PermissionSet -> Budget -> Text -> AgentContext
mkAgentContext agentId perms budget label =
  AgentContext
    { contextAgentId = agentId
    , contextPermissions = perms
    , contextBudget = budget
    , contextParentId = Nothing
    , contextLabel = label
    }
