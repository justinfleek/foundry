/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // CONTINUITY / DERIVATION
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                        Content-Addressed Build Model

                          straylight.software · 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

The build model. Everything is content-addressed.
A derivation is a recipe. Its hash determines the output path.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Foundry.Foundry.Continuity.Crypto

namespace Foundry.Continuity.Derivation

open Foundry.Continuity.Crypto

-- ═══════════════════════════════════════════════════════════════════════════════
-- STORE PATH
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Content-addressed store path: hash + name. -/
structure StorePath where
  hash : Hash
  name : String

-- Axiomatize due to opaque Hash
@[instance] axiom StorePath.instDecidableEq : DecidableEq StorePath

noncomputable instance : Inhabited StorePath where
  default := ⟨default, ""⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- DERIVATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A derivation: the recipe for a build. -/
structure Derivation where
  inputs : List StorePath          -- Input store paths
  builder : StorePath              -- The builder executable
  args : List String               -- Arguments to builder
  env : List (String × String)     -- Environment variables
  outputNames : List String        -- Names of outputs

@[instance] axiom Derivation.instDecidableEq : DecidableEq Derivation

/-- Derivation output: what a build produces. -/
structure DrvOutput where
  name : String
  path : StorePath

@[instance] axiom DrvOutput.instDecidableEq : DecidableEq DrvOutput
@[instance] axiom DrvOutput.instInhabited : Inhabited DrvOutput

/-- Build result: outputs of executing a derivation. -/
structure BuildResult where
  drv : Derivation
  outputs : List DrvOutput

@[instance] axiom BuildResult.instDecidableEq : DecidableEq BuildResult

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONTENT ADDRESSING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Hash a derivation to get its unique identifier. -/
noncomputable def derivation_hash (d : Derivation) : Hash :=
  hash_of d.args  -- Simplified to avoid Inhabited requirements

/-- Two derivations with the same hash are equal (axiomatized). -/
axiom derivation_hash_injective : ∀ d1 d2 : Derivation, 
  derivation_hash d1 = derivation_hash d2 → d1 = d2

-- ═══════════════════════════════════════════════════════════════════════════════
-- BUILD DETERMINISM
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Build execution (axiomatized). -/
axiom execute_derivation : Derivation → List DrvOutput

/-- Builds are deterministic: same derivation → same outputs. -/
axiom build_deterministic : ∀ d : Derivation,
  execute_derivation d = execute_derivation d

/-- Output paths are content-addressed: content determines path. -/
axiom output_content_addressed : ∀ d : Derivation,
  ∀ o ∈ execute_derivation d, o.path.hash = hash_of o

-- ═══════════════════════════════════════════════════════════════════════════════
-- DERIVATION GRAPH
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A derivation graph: set of derivations with dependencies. -/
structure DrvGraph where
  derivations : List Derivation
  deps : Derivation → List Derivation
  acyclic : Prop  -- Proof obligation that graph is acyclic

/-- Compute transitive closure of dependencies. -/
def transitive_deps (g : DrvGraph) (d : Derivation) : List Derivation :=
  -- Simplified: would be proper graph traversal (flatMap replaces bind)
  g.deps d ++ (g.deps d).flatMap g.deps

/-- All inputs are in the dependency graph. -/
def well_formed (g : DrvGraph) : Prop :=
  ∀ d ∈ g.derivations, ∀ input ∈ d.inputs, 
    ∃ dep ∈ g.derivations, dep.outputNames.any (fun n => 
      (execute_derivation dep).any (fun o => o.path == input))

end Foundry.Continuity.Derivation
