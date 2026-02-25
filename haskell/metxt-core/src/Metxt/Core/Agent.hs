{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // metxt // agent
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Metxt.Core.Agent
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
module Metxt.Core.Agent
  ( -- * Re-exports
    module Metxt.Core.Agent.Permission
  , module Metxt.Core.Agent.Budget
  , module Metxt.Core.Agent.Context
  ) where

import Metxt.Core.Agent.Budget
import Metxt.Core.Agent.Context
import Metxt.Core.Agent.Permission
