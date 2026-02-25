{- |
Module      : Metxt.Core.Effect.Graded
Description : Graded monad implementation
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Graded monad with grade tracking for effect composition.

== Graded Monad Laws

The implementation must satisfy:

@
return a >>= f  ≡  f a                      -- Left identity
m >>= return    ≡  m                        -- Right identity
(m >>= f) >>= g ≡  m >>= (λx → f x >>= g)  -- Associativity
@

With grade composition:

@
grade (m >>= f) = grade m <> grade (f undefined)
@
-}
module Metxt.Core.Effect.Graded
  ( -- * Types
    GradedMonad (..)
  , Grade (..)
  ) where

-- | Grade for effect tracking
class (Monoid g) => Grade g where
  -- | Combine two grades
  gradeCompose :: g -> g -> g
  gradeCompose = (<>)

-- | Graded monad typeclass
class (Monad m, Grade g) => GradedMonad g m | m -> g where
  -- | Get the current grade
  getGrade :: m g

  -- | Run with specific grade requirement
  withGrade :: g -> m a -> m a
