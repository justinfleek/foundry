{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // foundry // agent
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Agent
Description : Graded monad for agent operations
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

The Agent graded monad with permission, budget, and context tracking.

== Graded Monad Laws

@
return a >>= f  ≡  f a            -- Left identity
m >>= return    ≡  m              -- Right identity
(m >>= f) >>= g ≡  m >>= (λx → f x >>= g)  -- Associativity
@

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Agent
  ( -- * Re-exports
    module Foundry.Core.Agent.Permission
  , module Foundry.Core.Agent.Budget
  , module Foundry.Core.Agent.Context
  ) where

import Foundry.Core.Agent.Budget
import Foundry.Core.Agent.Context
import Foundry.Core.Agent.Permission
