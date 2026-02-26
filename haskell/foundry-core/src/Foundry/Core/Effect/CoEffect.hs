{- |
Module      : Foundry.Core.Effect.CoEffect
Description : Co-effect algebra for environment requirements
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Co-effects track what computations REQUIRE from the environment.

This module aligns with the Lean4 proofs in Continuity.Coeffect:
  - straylight/src/straylight/continuity/Continuity/Coeffect.lean

== Co-effect Algebra Laws (proven in Lean4)

@
empty_is_pure       : isPure []        = true
pure_is_reproducible: isReproducible []= true
tensor_pure_right   : r ++ []          = r
tensor_pure_left    : [] ++ r          = r
tensor_assoc        : (a ++ b) ++ c    = a ++ (b ++ c)
tensor_pure_pure    : isPure a → isPure b → isPure (a ++ b)
tensor_reproducible : isReproducible a → isReproducible b → isReproducible (a ++ b)
time_not_reproducible   : isReproducible [time]   = false
random_not_reproducible : isReproducible [random] = false
filesystemCA_reproducible : isReproducible [filesystemCA h] = true
networkCA_reproducible    : isReproducible [networkCA h]    = true
@

== Dependencies

Requires: (none - leaf module)
Required by: Foundry.Core.Effect.Graded, Foundry.Core.Agent

== Architecture

Effects:   what a computation DOES to the world
Coeffects: what a computation NEEDS from the world

A pure build needs nothing external (coeffects = []).
An impure build needs network, filesystem, time, random, auth, etc.
-}
module Foundry.Core.Effect.CoEffect
  ( -- * Types
    Coeffect (..)
  , Coeffects

    -- * Operations
  , coeffectsPure
  , coeffectsTensor
  , isPure
  , isReproducible
  , requiresNetwork
  , requiresAuth

    -- * Purity levels
  , purityLevel
  , minPurity
  ) where

import Data.ByteString (ByteString)
import Data.Text (Text)

--------------------------------------------------------------------------------
-- Coeffect Type (mirrors Continuity.Coeffect.Coeffect)
--------------------------------------------------------------------------------

-- | A coeffect: what a computation requires from the environment.
--
-- Mirrors the Lean4 inductive type in Continuity.Coeffect.
data Coeffect
  = Pure
    -- ^ Needs nothing
  | Filesystem !Text
    -- ^ Needs a file at path (non-content-addressed, non-reproducible)
  | FilesystemCA !ByteString
    -- ^ Needs content-addressed content by hash (reproducible)
  | Network !Text !Int
    -- ^ Needs network endpoint (host, port) - non-reproducible
  | NetworkCA !ByteString
    -- ^ Needs content-addressed content via network (reproducible)
  | Environment !Text
    -- ^ Needs environment variable (non-reproducible)
  | Time
    -- ^ Needs wall clock time (non-reproducible!)
  | Random
    -- ^ Needs entropy source (non-reproducible!)
  | Identity
    -- ^ Needs uid/gid (non-reproducible)
  | Auth !Text
    -- ^ Needs credential from provider (reproducible if handled correctly)
  | Gpu !Text
    -- ^ Needs GPU device access (deterministic if seeded)
  | Sandbox !Text
    -- ^ Needs specific sandbox environment
  deriving stock (Eq, Ord, Show)

-- | A set of coeffects (representing tensor product combination).
--
-- Mirrors Lean4: @abbrev Coeffects := List Coeffect@
type Coeffects = [Coeffect]

--------------------------------------------------------------------------------
-- Coeffect Operations (mirrors Continuity.Coeffect operations)
--------------------------------------------------------------------------------

-- | The pure coeffect set (empty).
--
-- @Coeffects.pure : Coeffects := []@
coeffectsPure :: Coeffects
coeffectsPure = []

-- | Tensor product: combine two coeffect sets.
--
-- @Coeffects.tensor (r s : Coeffects) : Coeffects := r ++ s@
coeffectsTensor :: Coeffects -> Coeffects -> Coeffects
coeffectsTensor = (++)

-- | Check if coeffects are pure (empty).
--
-- @Coeffects.isPure (r : Coeffects) : Bool := r.isEmpty@
isPure :: Coeffects -> Bool
isPure = null

-- | Check if coeffects are reproducible.
--
-- Non-reproducible coeffects: time, random, non-CA filesystem, non-CA network,
-- environment variables, identity.
--
-- Reproducible coeffects: pure, filesystemCA, networkCA, auth, gpu, sandbox.
isReproducible :: Coeffects -> Bool
isReproducible = all coeffectIsReproducible
  where
    coeffectIsReproducible :: Coeffect -> Bool
    coeffectIsReproducible = \case
      Pure           -> True
      FilesystemCA _ -> True   -- Content-addressed = reproducible
      NetworkCA _    -> True   -- Content-addressed = reproducible
      Auth _         -> True   -- OK if handled correctly
      Gpu _          -> True   -- Deterministic if seeded
      Sandbox _      -> True   -- OK
      Filesystem _   -> False  -- Non-CA filesystem = non-reproducible
      Network _ _    -> False  -- Non-CA network = non-reproducible
      Environment _  -> False  -- Ambient = non-reproducible
      Time           -> False  -- Wall clock = non-reproducible
      Random         -> False  -- Entropy = non-reproducible
      Identity       -> False  -- Ambient = non-reproducible

-- | Check if coeffects require network access.
requiresNetwork :: Coeffects -> Bool
requiresNetwork = any isNetworkCoeffect
  where
    isNetworkCoeffect :: Coeffect -> Bool
    isNetworkCoeffect = \case
      Network _ _ -> True
      NetworkCA _ -> True
      _           -> False

-- | Check if coeffects require authentication.
requiresAuth :: Coeffects -> Bool
requiresAuth = any isAuthCoeffect
  where
    isAuthCoeffect :: Coeffect -> Bool
    isAuthCoeffect = \case
      Auth _ -> True
      _      -> False

--------------------------------------------------------------------------------
-- Purity Levels (mirrors Continuity.Coeffect.purityLevel)
--------------------------------------------------------------------------------

-- | Purity level of a coeffect (higher = purer).
--
-- Level 3: Pure (needs nothing)
-- Level 2: Reproducible (CA access, auth, gpu, sandbox)
-- Level 1: Ambient (non-CA access, environment, identity)
-- Level 0: Non-reproducible (time, random)
purityLevel :: Coeffect -> Int
purityLevel = \case
  Pure           -> 3
  FilesystemCA _ -> 2
  NetworkCA _    -> 2
  Auth _         -> 2
  Gpu _          -> 2
  Sandbox _      -> 2
  Filesystem _   -> 1
  Network _ _    -> 1
  Environment _  -> 1
  Identity       -> 1
  Time           -> 0
  Random         -> 0

-- | Minimum purity level of a coeffect set.
--
-- Empty set has purity 3 (pure).
minPurity :: Coeffects -> Int
minPurity []     = 3
minPurity (c:cs) = min (purityLevel c) (minPurity cs)
