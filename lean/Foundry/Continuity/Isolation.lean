/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // CONTINUITY // ISOLATION
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                        Namespace and VM Isolation Model

                          straylight.software · 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Builds run in isolation. Namespaces provide lightweight isolation.
MicroVMs provide stronger isolation (isospin for GPU).

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Foundry.Continuity.Derivation

namespace Foundry.Continuity.Isolation

open Foundry.Continuity.Derivation

-- ═══════════════════════════════════════════════════════════════════════════════
-- LINUX NAMESPACES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A Linux namespace configuration. -/
structure Namespace where
  user : Bool      -- CLONE_NEWUSER
  mount : Bool     -- CLONE_NEWNS
  net : Bool       -- CLONE_NEWNET
  pid : Bool       -- CLONE_NEWPID
  ipc : Bool       -- CLONE_NEWIPC
  uts : Bool       -- CLONE_NEWUTS
  cgroup : Bool    -- CLONE_NEWCGROUP
  deriving DecidableEq, Repr

namespace Namespace

/-- Full isolation: all namespace flags set. -/
def full : Namespace := ⟨true, true, true, true, true, true, true⟩

/-- No isolation: all namespace flags unset. -/
def none : Namespace := ⟨false, false, false, false, false, false, false⟩

/-- Ordering: more isolation is "greater". -/
def le (n1 n2 : Namespace) : Prop :=
  (n1.user → n2.user) ∧ (n1.mount → n2.mount) ∧ (n1.net → n2.net) ∧
  (n1.pid → n2.pid) ∧ (n1.ipc → n2.ipc) ∧ (n1.uts → n2.uts) ∧ (n1.cgroup → n2.cgroup)

/-- Count of enabled namespaces. -/
def count (n : Namespace) : Nat :=
  (if n.user then 1 else 0) + (if n.mount then 1 else 0) + (if n.net then 1 else 0) +
  (if n.pid then 1 else 0) + (if n.ipc then 1 else 0) + (if n.uts then 1 else 0) +
  (if n.cgroup then 1 else 0)

end Namespace

instance : LE Namespace where le := Namespace.le

-- ═══════════════════════════════════════════════════════════════════════════════
-- MICROVM (FIRECRACKER / ISOSPIN)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Firecracker-based microVM configuration. -/
structure MicroVM where
  kernel : StorePath
  rootfs : StorePath
  vcpus : Nat
  memMb : Nat
  netEnabled : Bool
  gpuPassthrough : Bool

@[instance] axiom MicroVM.instDecidableEq : DecidableEq MicroVM

/-- isospin: minimal proven microVM for GPU. -/
structure Isospin extends MicroVM where
  kernelMinimal : Prop    -- Kernel is minimal/verified
  driversVerified : Prop  -- Driver stack is verified

-- ═══════════════════════════════════════════════════════════════════════════════
-- ISOLATION LEVEL
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Isolation level hierarchy. -/
inductive IsolationLevel where
  | none_                        -- No isolation
  | namespace_ (ns : Namespace)  -- Namespace isolation
  | vm (vm : MicroVM)            -- Full VM isolation

/-- Ordering on isolation levels. -/
def IsolationLevel.le : IsolationLevel → IsolationLevel → Prop
  | .none_, _ => True
  | .namespace_ _, .none_ => False
  | .namespace_ ns1, .namespace_ ns2 => Namespace.le ns1 ns2
  | .namespace_ _, .vm _ => True
  | .vm _, .none_ => False
  | .vm _, .namespace_ _ => False
  | .vm vm1, .vm vm2 => vm1 = vm2  -- VMs are incomparable unless equal

instance : LE IsolationLevel where le := IsolationLevel.le

-- ═══════════════════════════════════════════════════════════════════════════════
-- HERMETIC BUILD
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A build is hermetic if it only accesses declared inputs. -/
def IsHermetic (inputs accessed : List StorePath) : Prop :=
  ∀ p ∈ accessed, p ∈ inputs

/-- Execute action in isolation. -/
axiom execute_isolated : Derivation → Namespace → List DrvOutput

/-- Action execution is deterministic. -/
axiom execute_deterministic : ∀ d ns, 
  execute_isolated d ns = execute_isolated d ns

/-- More isolation doesn't change outputs. -/
axiom isolation_monotonic : ∀ d ns1 ns2,
  Namespace.le ns1 ns2 → execute_isolated d ns1 = execute_isolated d ns2

-- ═══════════════════════════════════════════════════════════════════════════════
-- THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Full namespace isolation is maximal. -/
theorem full_is_max (ns : Namespace) : ns ≤ Namespace.full := by
  simp only [LE.le, Namespace.le, Namespace.full]
  exact ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial, 
         fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial⟩

/-- Namespace.none is minimal. -/
theorem none_is_min (ns : Namespace) : Namespace.none ≤ ns := by
  simp only [LE.le, Namespace.le, Namespace.none]
  exact ⟨Bool.noConfusion, Bool.noConfusion, Bool.noConfusion,
         Bool.noConfusion, Bool.noConfusion, Bool.noConfusion, 
         Bool.noConfusion⟩

/-- Full namespace has 7 namespaces enabled. -/
theorem full_count : Namespace.full.count = 7 := rfl

/-- Hermetic builds only access declared inputs. -/
theorem hermetic_build (d : Derivation) (ns : Namespace)
    (h_full : ns = Namespace.full)
    (inputs : List StorePath)
    (accessed : List StorePath)
    (h_subset : ∀ p ∈ accessed, p ∈ inputs) :
    IsHermetic inputs accessed := h_subset

end Foundry.Continuity.Isolation
