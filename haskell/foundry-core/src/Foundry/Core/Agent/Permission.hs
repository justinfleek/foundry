{- |
Module      : Foundry.Core.Agent.Permission
Description : Permission lattice for agent capabilities
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Permission system with lattice structure for monotonic capability tracking.
-}
module Foundry.Core.Agent.Permission
  ( -- * Types
    Permission (..)
  , PermissionSet (..)

    -- * Operations
  , hasPermission
  , grantPermission
  , revokePermission
  ) where

import Data.Set (Set)
import Data.Set qualified as Set

-- | Individual permissions
data Permission
  = ReadBrand         -- ^ Read brand data
  | WriteBrand        -- ^ Write/update brand data
  | ExecuteSkill      -- ^ Execute browser skills
  | NetworkAccess     -- ^ Make network requests
  | FileSystemRead    -- ^ Read local files
  | FileSystemWrite   -- ^ Write local files
  | DatabaseRead      -- ^ Read from database
  | DatabaseWrite     -- ^ Write to database
  | WalletSign        -- ^ Sign transactions
  | WalletSpend       -- ^ Spend funds (requires human approval)
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | Set of permissions (monotonic - can only grow)
newtype PermissionSet = PermissionSet {unPermissionSet :: (Set Permission)}
  deriving stock (Eq, Show)
  deriving newtype (Semigroup, Monoid)

-- | Check if permission is granted
hasPermission :: Permission -> PermissionSet -> Bool
hasPermission p (PermissionSet ps) = Set.member p ps

-- | Grant a permission (monotonic growth)
grantPermission :: Permission -> PermissionSet -> PermissionSet
grantPermission p (PermissionSet ps) = PermissionSet (Set.insert p ps)

-- | Revoke permission (requires elevated privileges - not available to agents)
revokePermission :: Permission -> PermissionSet -> PermissionSet
revokePermission p (PermissionSet ps) = PermissionSet (Set.delete p ps)
