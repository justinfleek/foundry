/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // CONTINUITY // TOOLCHAIN
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                    Typed Toolchains and Build Equivalence

                          straylight.software · 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

No strings for targets. Real types.
Compiler + target + flags = toolchain.
Different toolchains can produce identical builds (the coset).

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Foundry.Foundry.Continuity.Derivation

namespace Foundry.Continuity.Toolchain

open Foundry.Continuity.Derivation

-- ═══════════════════════════════════════════════════════════════════════════════
-- TARGET TRIPLE COMPONENTS (NO STRINGS!)
-- ═══════════════════════════════════════════════════════════════════════════════

inductive Arch where
  | x86_64 | aarch64 | wasm32 | riscv64 | armv7
  deriving DecidableEq, Repr

inductive OS where
  | linux | darwin | wasi | windows | none_
  deriving DecidableEq, Repr

inductive ABI where
  | gnu | musl | eabi | eabihf | msvc | none_
  deriving DecidableEq, Repr

inductive Vendor where
  | unknown | pc | apple | nvidia
  deriving DecidableEq, Repr

/-- CPU microarchitecture (for -march, -mtune). -/
inductive Cpu where
  | generic | native
  -- x86_64
  | x86_64_v2 | x86_64_v3 | x86_64_v4
  | znver3 | znver4 | znver5 | sapphirerapids | alderlake
  -- aarch64 datacenter
  | neoverse_v2 | neoverse_n2
  -- aarch64 consumer
  | apple_m1 | apple_m2 | apple_m3 | apple_m4
  deriving DecidableEq, Repr

/-- GPU SM version (for CUDA -arch=sm_XX). -/
inductive Gpu where
  | none_
  | sm_80 | sm_86 | sm_87 | sm_89        -- Ampere/Orin
  | sm_90 | sm_90a                       -- Hopper
  | sm_100 | sm_100a | sm_120            -- Blackwell
  deriving DecidableEq, Repr

/-- Target triple with CPU/GPU microarchitecture. -/
structure Triple where
  arch : Arch
  vendor : Vendor
  os : OS
  abi : ABI
  cpu : Cpu
  gpu : Gpu
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPILER FLAGS (TYPED!)
-- ═══════════════════════════════════════════════════════════════════════════════

inductive OptLevel where
  | O0 | O1 | O2 | O3 | Oz | Os
  deriving DecidableEq, Repr

inductive LTOMode where
  | off | thin | fat
  deriving DecidableEq, Repr

inductive Flag where
  | optLevel : OptLevel → Flag
  | lto : LTOMode → Flag
  | debug : Bool → Flag
  | pic : Bool → Flag
  | sanitize : String → Flag
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════════════════════
-- TOOLCHAIN
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A toolchain: compiler + target + flags. -/
structure Toolchain where
  compiler : StorePath
  host : Triple
  target : Triple
  flags : List Flag
  sysroot : Option StorePath

@[instance] axiom Toolchain.instDecidableEq : DecidableEq Toolchain

/-- Toolchain closure: all transitive dependencies. -/
def toolchain_closure (t : Toolchain) : List StorePath :=
  [t.compiler] ++ (match t.sysroot with | some s => [s] | none => [])

-- ═══════════════════════════════════════════════════════════════════════════════
-- BUILD EQUIVALENCE (THE COSET)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Build outputs from a toolchain and source. -/
axiom build_outputs : Toolchain → StorePath → List DrvOutput

/-- Build equivalence: same outputs for all sources. -/
def build_equivalent (t1 t2 : Toolchain) : Prop :=
  ∀ source, build_outputs t1 source = build_outputs t2 source

theorem build_equivalent_refl : ∀ t, build_equivalent t t := by
  intro t source; rfl

theorem build_equivalent_symm : ∀ t1 t2, build_equivalent t1 t2 → build_equivalent t2 t1 := by
  intro t1 t2 h source; exact (h source).symm

theorem build_equivalent_trans : ∀ t1 t2 t3,
    build_equivalent t1 t2 → build_equivalent t2 t3 → build_equivalent t1 t3 := by
  intro t1 t2 t3 h12 h23 source
  exact Eq.trans (h12 source) (h23 source)

theorem build_equivalent_equivalence : Equivalence build_equivalent :=
  ⟨build_equivalent_refl, fun h => build_equivalent_symm _ _ h, 
   fun h1 h2 => build_equivalent_trans _ _ _ h1 h2⟩

/-- The Coset: equivalence class under build_equivalent. -/
def Coset := Quotient ⟨build_equivalent, build_equivalent_equivalence⟩

def to_coset (t : Toolchain) : Coset := Quotient.mk _ t

theorem coset_eq_iff (t1 t2 : Toolchain) :
    to_coset t1 = to_coset t2 ↔ build_equivalent t1 t2 := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

-- ═══════════════════════════════════════════════════════════════════════════════
-- CACHE KEY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Cache key is the coset, not the toolchain hash! -/
def cache_key (t : Toolchain) : Coset := to_coset t

/-- CACHE CORRECTNESS: Same coset → same outputs. -/
theorem cache_correctness (t1 t2 : Toolchain) (source : StorePath)
    (h : cache_key t1 = cache_key t2) :
    build_outputs t1 source = build_outputs t2 source := by
  have h_equiv : build_equivalent t1 t2 := (coset_eq_iff t1 t2).mp h
  exact h_equiv source

/-- Cache hit iff same coset. -/
theorem cache_hit_iff_same_coset (t1 t2 : Toolchain) :
    cache_key t1 = cache_key t2 ↔ build_equivalent t1 t2 :=
  coset_eq_iff t1 t2

end Foundry.Continuity.Toolchain
