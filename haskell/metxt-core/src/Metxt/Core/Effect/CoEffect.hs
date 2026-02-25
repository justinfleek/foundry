{- |
Module      : Metxt.Core.Effect.CoEffect
Description : Co-effect algebra for environment requirements
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Co-effects track what computations REQUIRE from the environment.

== Co-effect Algebra Laws

@
f(f(x)) = f(x)                    -- Idempotency
S(x) >= S(y)                      -- Monotonicity
(E₁ ∘ E₂) ∘ E₃ = E₁ ∘ (E₂ ∘ E₃)  -- Associativity
∀ mutation → Event                -- Provenance
@
-}
module Metxt.Core.Effect.CoEffect
  ( -- * Types
    CoEffect (..)
  , Requirement (..)
  ) where

import Data.Set (Set)

-- | Environment requirement
data Requirement
  = RequiresNetwork
  | RequiresFileSystem
  | RequiresDatabase
  | RequiresBrowser
  | RequiresWallet
  | RequiresHumanApproval
  deriving stock (Eq, Ord, Show, Enum, Bounded)

-- | Co-effect tracking environment requirements
class CoEffect c where
  -- | Get requirements
  requirements :: c -> Set Requirement

  -- | Compose co-effects (union of requirements)
  composeCoEffect :: c -> c -> c

  -- | Empty co-effect (no requirements)
  emptyCoEffect :: c
