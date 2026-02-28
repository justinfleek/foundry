/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // CONTINUITY // COEFFECT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                             The Coeffect Algebra

                          straylight.software · 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    EFFECTS vs COEFFECTS:

    Effects:    what a computation DOES to the world
    Coeffects:  what a computation NEEDS from the world

A pure build needs nothing external (coeffects = ∅).
An impure build needs things like network, filesystem, time, random, auth.

The TENSOR PRODUCT (⊗) combines coeffects.
The DISCHARGE PROOF is evidence that coeffects were satisfied.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Foundry.Continuity.Crypto

namespace Foundry.Continuity.Coeffect

open Foundry.Continuity.Crypto

-- ═══════════════════════════════════════════════════════════════════════════════
-- COEFFECT TYPE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A coeffect: what a computation requires from the environment. -/
inductive Coeffect where
  | pure                                      -- Needs nothing
  | filesystem (path : String)                -- Needs a file (non-CA)
  | filesystemCA (hash : Hash)                -- Needs CA content (reproducible)
  | network (host : String) (port : Nat)      -- Needs network endpoint
  | networkCA (hash : Hash)                   -- Needs CA content via network
  | environment (varname : String)            -- Needs env var
  | time                                      -- Needs wall clock (non-reproducible!)
  | random                                    -- Needs entropy (non-reproducible!)
  | identity                                  -- Needs uid/gid
  | auth (provider : String)                  -- Needs credential
  | gpu (device : String)                     -- Needs GPU access
  | sandbox (name : String)                   -- Needs specific sandbox

-- DecidableEq axiomatized (depends on opaque Hash)
@[instance] axiom Coeffect.instDecidableEq : DecidableEq Coeffect

/-- A set of coeffects (representing ⊗ combination). -/
abbrev Coeffects := List Coeffect

-- ═══════════════════════════════════════════════════════════════════════════════
-- COEFFECT OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The pure coeffect set (empty). -/
def Coeffects.pure : Coeffects := []

/-- Tensor product: combine two coeffect sets. -/
def Coeffects.tensor (r s : Coeffects) : Coeffects := r ++ s

instance : Append Coeffects where append := Coeffects.tensor

/-- Check if coeffects are pure. -/
def Coeffects.isPure (r : Coeffects) : Bool := r.isEmpty

/-- Check if coeffects are reproducible (no time, random, or non-CA accesses). -/
def Coeffects.isReproducible (r : Coeffects) : Bool :=
  r.all fun c => match c with
    | .pure => true
    | .filesystemCA _ => true
    | .networkCA _ => true
    | .filesystem _ => false    -- Non-CA filesystem
    | .network _ _ => false     -- Non-CA network
    | .environment _ => false   -- Ambient
    | .time => false            -- Non-reproducible
    | .random => false          -- Non-reproducible
    | .identity => false        -- Ambient
    | .auth _ => true           -- OK if handled correctly
    | .gpu _ => true            -- Deterministic if seeded
    | .sandbox _ => true        -- OK

/-- Check if coeffects require network. -/
def Coeffects.requiresNetwork (r : Coeffects) : Bool :=
  r.any fun c => match c with
    | .network _ _ => true
    | .networkCA _ => true
    | _ => false

/-- Check if coeffects require auth. -/
def Coeffects.requiresAuth (r : Coeffects) : Bool :=
  r.any fun c => match c with
    | .auth _ => true
    | _ => false

-- ═══════════════════════════════════════════════════════════════════════════════
-- COEFFECT ORDERING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Coeffect purity level: how "pure" is this coeffect? -/
def Coeffect.purityLevel : Coeffect → Nat
  | .pure => 3
  | .filesystemCA _ => 2
  | .networkCA _ => 2
  | .auth _ => 2
  | .gpu _ => 2
  | .sandbox _ => 2
  | .filesystem _ => 1
  | .network _ _ => 1
  | .environment _ => 1
  | .identity => 1
  | .time => 0
  | .random => 0

/-- A coeffect set is "purer" if all coeffects have higher purity. -/
def Coeffects.minPurity (r : Coeffects) : Nat :=
  match r with
  | [] => 3  -- Pure
  | c :: cs => min c.purityLevel (Coeffects.minPurity cs)

-- ═══════════════════════════════════════════════════════════════════════════════
-- THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Empty coeffects are pure. -/
theorem empty_is_pure : Coeffects.isPure [] = true := rfl

/-- Pure coeffects are reproducible. -/
theorem pure_is_reproducible : Coeffects.isReproducible [] = true := rfl

/-- Tensor with pure is identity (right). -/
theorem tensor_pure_right (r : Coeffects) : r ++ [] = r := List.append_nil r

/-- Tensor with pure is identity (left). -/
theorem tensor_pure_left (r : Coeffects) : [] ++ r = r := rfl

/-- Tensor is associative. -/
theorem tensor_assoc (a b c : Coeffects) : (a ++ b) ++ c = a ++ (b ++ c) := 
  List.append_assoc a b c

/-- If both inputs are pure, tensor is pure. -/
theorem tensor_pure_pure (a b : Coeffects) 
    (ha : a.isPure) (hb : b.isPure) : (a ++ b).isPure := by
  simp only [Coeffects.isPure, List.isEmpty_iff] at *
  simp [ha, hb]

/-- If both inputs are reproducible, tensor is reproducible. -/
theorem tensor_reproducible (a b : Coeffects)
    (ha : a.isReproducible) (hb : b.isReproducible) : (a ++ b).isReproducible := by
  simp only [Coeffects.isReproducible, List.all_append, Bool.and_eq_true]
  exact ⟨ha, hb⟩

/-- Time coeffect is not reproducible. -/
theorem time_not_reproducible : Coeffects.isReproducible [.time] = false := rfl

/-- Random coeffect is not reproducible. -/
theorem random_not_reproducible : Coeffects.isReproducible [.random] = false := rfl

/-- CA filesystem is reproducible. -/
theorem filesystemCA_reproducible (h : Hash) : 
    Coeffects.isReproducible [.filesystemCA h] = true := rfl

/-- CA network is reproducible. -/
theorem networkCA_reproducible (h : Hash) : 
    Coeffects.isReproducible [.networkCA h] = true := rfl

end Foundry.Continuity.Coeffect
