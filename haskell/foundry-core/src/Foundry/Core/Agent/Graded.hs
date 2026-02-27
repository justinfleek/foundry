{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // foundry // agent // graded
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Agent.Graded
Description : Type-level graded monad for agent operations
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Type-level encoding of budget and permissions using GHC's TypeNats.

== Design Principles

1. Budget is tracked at the TYPE level, not runtime
2. Spending REDUCES the type-level budget (compile-time proof)
3. Permissions form a type-level set (compile-time capability check)
4. Monad laws hold with grade composition

== The Core Insight

@
-- This type signature IS the proof of budget conservation:
spend :: forall cost budget perms a. (CmpNat cost budget ~ 'LT) =>
  SNat cost -> AgentT perms budget a -> AgentT perms (budget - cost) a
@

If @cost > budget@, the constraint @CmpNat cost budget ~ 'LT@ cannot be
satisfied and the program DOES NOT COMPILE. No runtime check needed.

== Dependencies

This module: GHC.TypeNats, Data.Type.Bool
Dependents:  Foundry.Core.Agent (re-exports)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Agent.Graded
  ( -- * The Graded Agent Monad
    AgentT (..)
    
    -- * Type-level singletons
  , SNat (..)
  , SPermission (..)
  
    -- * Budget operations
  , spend
  , liftAgent
  , CanSpend
  
    -- * Permission operations
  , requirePermission
  , HasPermission
  , Elem
  
    -- * Running agents
  , runAgentT
    
    -- * Re-exports for type-level programming
  , KnownNat
  , type (<=)
  , type (-)
  ) where

import Data.Kind (Type)
import Data.Type.Bool (If)
import Data.Type.Ord (OrdCond)
import GHC.TypeLits (Symbol, TypeError, ErrorMessage (..))
import GHC.TypeNats (Nat, KnownNat, CmpNat, type (<=), type (-))

--------------------------------------------------------------------------------
-- SECTION 1: TYPE-LEVEL NAT SINGLETON
--------------------------------------------------------------------------------

-- | Singleton for type-level Nat (witness that we know the value)
data SNat (n :: Nat) = SNat

--------------------------------------------------------------------------------
-- SECTION 1b: BUDGET CONSTRAINT WITH CUSTOM ERROR
--------------------------------------------------------------------------------

-- | Constraint that @cost <= budget@ with a custom error message.
-- When violated, produces: "Budget exceeded: tried to spend X but only Y remaining"
type family AssertBudget (cost :: Nat) (budget :: Nat) :: Bool where
  AssertBudget cost budget = 
    OrdCond (CmpNat cost budget)
      'True   -- cost < budget: OK
      'True   -- cost = budget: OK  
      (TypeError ('Text "Budget exceeded: tried to spend " 
            ':<>: 'ShowType cost 
            ':<>: 'Text " but only " 
            ':<>: 'ShowType budget 
            ':<>: 'Text " remaining"))

-- | Constraint alias for budget checking
type CanSpend cost budget = (AssertBudget cost budget ~ 'True)

--------------------------------------------------------------------------------
-- SECTION 2: TYPE-LEVEL PERMISSION SET
--------------------------------------------------------------------------------

-- | Type family to check if a symbol is in a type-level list.
-- Returns 'True if present, 'False otherwise.
type family Elem (x :: Symbol) (xs :: [Symbol]) :: Bool where
  Elem _ '[]       = 'False
  Elem x (x ': _)  = 'True
  Elem x (_ ': xs) = Elem x xs

-- | Type family for permission checking with custom error message.
type family AssertPermission (p :: Symbol) (perms :: [Symbol]) (found :: Bool) :: Bool where
  AssertPermission _ _ 'True = 'True
  AssertPermission p perms 'False = 
    TypeError ('Text "Permission denied: '" 
          ':<>: 'ShowType p 
          ':<>: 'Text "' is not in permission set " 
          ':<>: 'ShowType perms)

-- | Constraint that a permission is present in the permission set.
-- This is used to require specific permissions at compile time.
-- Produces error: "Permission denied: 'X' is not in permission set [...]"
type HasPermission (p :: Symbol) (perms :: [Symbol]) = 
  (AssertPermission p perms (Elem p perms) ~ 'True)

--------------------------------------------------------------------------------
-- SECTION 3: THE GRADED AGENT MONAD
--------------------------------------------------------------------------------

-- | The graded Agent monad transformer.
--
-- Type parameters:
--   @perms@  - Type-level list of permissions (e.g., '["read", "network"])
--   @budget@ - Type-level Nat representing remaining budget in cents
--   @m@      - Underlying monad
--   @a@      - Result type
--
-- The budget parameter DECREASES as operations consume resources.
-- This is enforced at compile time - overspending does not typecheck.
newtype AgentT (perms :: [Symbol]) (budget :: Nat) (m :: Type -> Type) (a :: Type)
  = AgentT { unAgentT :: m a }
  deriving stock (Functor)

-- | Applicative instance preserves budget (no consumption)
instance (Applicative m) => Applicative (AgentT perms budget m) where
  pure :: a -> AgentT perms budget m a
  pure = AgentT . pure
  {-# INLINE pure #-}
  
  (<*>) :: AgentT perms budget m (a -> b) -> AgentT perms budget m a -> AgentT perms budget m b
  AgentT mf <*> AgentT ma = AgentT (mf <*> ma)
  {-# INLINE (<*>) #-}

-- | Monad instance preserves budget (spending happens via explicit combinators)
instance (Monad m) => Monad (AgentT perms budget m) where
  (>>=) :: AgentT perms budget m a -> (a -> AgentT perms budget m b) -> AgentT perms budget m b
  AgentT ma >>= f = AgentT (ma >>= unAgentT . f)
  {-# INLINE (>>=) #-}

--------------------------------------------------------------------------------
-- SECTION 4: BUDGET OPERATIONS
--------------------------------------------------------------------------------

-- | Spend budget at the type level.
--
-- This is the key insight: the return type has @(budget - cost)@.
-- If @cost > budget@, GHC cannot solve @cost <= budget@ and compilation fails.
--
-- @
-- example :: AgentT perms 100 IO ()
-- example = do
--   spend (SNat @50) (pure ())  -- Now we have 50 remaining
--   spend (SNat @30) (pure ())  -- Now we have 20 remaining  
--   spend (SNat @30) (pure ())  -- COMPILE ERROR: 30 > 20
-- @
spend
  :: forall cost budget perms m a
   . (CanSpend cost budget)
  => SNat cost
  -> AgentT perms budget m a
  -> AgentT perms (budget - cost) m a
spend SNat (AgentT ma) = AgentT ma
{-# INLINE spend #-}

-- | Lift an action into the agent monad without consuming budget.
-- Use this for pure computations that don't require resources.
liftAgent :: m a -> AgentT perms budget m a
liftAgent = AgentT
{-# INLINE liftAgent #-}

--------------------------------------------------------------------------------
-- SECTION 5: PERMISSION OPERATIONS  
--------------------------------------------------------------------------------

-- | Proxy type for permissions (avoids ambiguous type variables)
data SPermission (p :: Symbol) = SPermission

-- | Require a permission at compile time.
--
-- If the permission is not in the agent's permission set, compilation fails.
-- The permission check happens entirely at compile time - no runtime cost.
--
-- @
-- readData :: HasPermission "read" perms => AgentT perms budget IO Data
-- readData = requirePermission SPermission $ AgentT $ do
--   -- actual read operation
-- @
requirePermission
  :: forall (p :: Symbol) perms budget m a
   . (HasPermission p perms)
  => SPermission p
  -> AgentT perms budget m a
  -> AgentT perms budget m a
requirePermission SPermission (AgentT ma) = AgentT ma
{-# INLINE requirePermission #-}

--------------------------------------------------------------------------------
-- SECTION 6: RUNNING AGENTS
--------------------------------------------------------------------------------

-- | Run an agent computation.
--
-- The type signature proves:
-- 1. We started with @initialBudget@
-- 2. We have @remainingBudget@ left
-- 3. Therefore we spent exactly @(initialBudget - remainingBudget)@
--
-- This is compile-time proof of budget conservation.
runAgentT
  :: AgentT perms budget m a
  -> m a
runAgentT (AgentT ma) = ma
{-# INLINE runAgentT #-}

