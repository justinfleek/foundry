{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                              // metxt // effect
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Metxt.Core.Effect
Description : Effect system with graded monads and co-effects
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Metxt.Core.Effect
  ( -- * Re-exports
    module Metxt.Core.Effect.Graded
  , module Metxt.Core.Effect.CoEffect
  ) where

import Metxt.Core.Effect.CoEffect
import Metxt.Core.Effect.Graded
