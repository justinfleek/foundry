{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                // foundry // core
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core
Description : METXT Core - Graded monads and brand types
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause
Maintainer  : dev@straylight.ai
Stability   : experimental

Core types and graded monad infrastructure for the SMART Brand Ingestion Engine.

== Overview

This module re-exports the main components:

* "Foundry.Core.Brand" - Brand schema types (Identity, Palette, Typography, etc.)
* "Foundry.Core.Agent" - Graded monad with permission/budget/context tracking
* "Foundry.Core.Effect" - Co-effect algebra and graded monad laws

== Graded Monad Laws

The 'Agent' monad must satisfy:

@
return a >>= f  ≡  f a            -- Left identity
m >>= return    ≡  m              -- Right identity
(m >>= f) >>= g ≡  m >>= (λx → f x >>= g)  -- Associativity
@

== Co-effect Algebra Laws

@
f(f(x)) = f(x)                    -- Idempotency
S(x) >= S(y)                      -- Monotonicity
(E₁ ∘ E₂) ∘ E₃ = E₁ ∘ (E₂ ∘ E₃)  -- Associativity
∀ mutation → Event                -- Provenance
@

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core
  ( -- * Re-exports
    module Foundry.Core.Brand
  , module Foundry.Core.Agent
  , module Foundry.Core.Effect
  ) where

import Foundry.Core.Agent
import Foundry.Core.Brand
import Foundry.Core.Effect
