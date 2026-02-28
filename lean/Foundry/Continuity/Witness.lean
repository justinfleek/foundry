/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                         // CONTINUITY // WITNESS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                         eBPF Syscall-Level Witnessing

                          straylight.software · 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    "The matrix has its roots in primitive arcade games."
                                        — Neuromancer

The HTTP proxy only sees HTTP. But builds touch EVERYTHING:
  • Environment variables (getenv)
  • Files (open, read, write, stat)
  • Network (connect, sendto, recvfrom)
  • Time (clock_gettime, gettimeofday)
  • Random (getrandom, /dev/urandom)

To truly witness a build, we need eBPF-level syscall tracing.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Foundry.Continuity.Crypto
import Foundry.Continuity.Coeffect
import Foundry.Continuity.Trust

namespace Foundry.Continuity.Witness

open Foundry.Continuity.Crypto
open Foundry.Continuity.Coeffect
open Foundry.Continuity.Trust

-- ═══════════════════════════════════════════════════════════════════════════════
-- SYSCALL CLASSIFICATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Syscall classes that we trace. -/
inductive SyscallClass where
  | fileOpen      -- open, openat, openat2
  | fileRead      -- read, pread64, readv
  | fileWrite     -- write, pwrite64, writev
  | fileStat      -- stat, fstat, lstat, statx
  | fileAccess    -- access, faccessat
  | netConnect    -- connect
  | netSend       -- sendto, sendmsg
  | netRecv       -- recvfrom, recvmsg
  | netSocket     -- socket, socketpair
  | timeGet       -- clock_gettime, gettimeofday
  | randomGet     -- getrandom
  | processExec   -- execve, execveat
  | processFork   -- fork, clone
  | identityGet   -- getuid, getgid
  | envRead       -- getenv (via /proc/self/environ)
  | other
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════════════════════
-- WITNESSED EVENTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A witnessed syscall from eBPF. -/
structure WitnessedSyscall where
  class_ : SyscallClass
  nr : Nat                      -- Syscall number
  args : List Nat               -- Arguments
  ret : Int                     -- Return value
  timestamp : Nat               -- Monotonic ns
  pid : Nat                     -- Process ID
  contentHash : Option Hash     -- Hash of data if applicable

-- Axiomatize DecidableEq due to opaque Hash
@[instance] axiom WitnessedSyscall.instDecidableEq : DecidableEq WitnessedSyscall

/-- Environment variable access. -/
structure EnvAccess where
  name : String
  valueHash : Hash
  timestamp : Nat

@[instance] axiom EnvAccess.instDecidableEq : DecidableEq EnvAccess

/-- File access. -/
structure FileAccess where
  path : String
  mode : String                 -- read, write, stat, exec
  contentHash : Option Hash
  size : Option Nat
  timestamp : Nat

@[instance] axiom FileAccess.instDecidableEq : DecidableEq FileAccess

/-- Network access. -/
structure NetAccess where
  host : String
  port : Nat
  protocol : String             -- tcp, udp
  direction : String            -- connect, accept
  contentHash : Option Hash
  timestamp : Nat

@[instance] axiom NetAccess.instDecidableEq : DecidableEq NetAccess

/-- Time access. -/
structure TimeAccess where
  clockId : Nat
  value : Nat
  timestamp : Nat
  deriving DecidableEq

/-- Random access. -/
structure RandomAccess where
  source : String               -- /dev/urandom, getrandom
  bytes : Nat
  entropyHash : Hash
  timestamp : Nat

@[instance] axiom RandomAccess.instDecidableEq : DecidableEq RandomAccess

-- ═══════════════════════════════════════════════════════════════════════════════
-- DISCHARGE PROOF
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Complete discharge proof: evidence that coeffects were satisfied. -/
structure DischargeProof where
  declaredCoeffects : Coeffects
  syscallTrace : List WitnessedSyscall
  envAccesses : List EnvAccess
  fileAccesses : List FileAccess
  netAccesses : List NetAccess
  timeAccesses : List TimeAccess
  randomAccesses : List RandomAccess
  builder : HybridPublicKey
  startTime : Timestamp
  endTime : Timestamp
  derivationHash : Hash
  outputHashes : List (String × Hash)
  signature : HybridSignature

namespace DischargeProof

-- Note: message hashes the relevant parts of the proof
noncomputable def message (p : DischargeProof) : Hash :=
  hash_of p.derivationHash  -- Simplified to avoid Inhabited requirement

def wellFormed (p : DischargeProof) : Prop :=
  hybrid_verify p.builder p.message p.signature = true

def isPure (p : DischargeProof) : Bool :=
  p.envAccesses.isEmpty && 
  p.netAccesses.isEmpty && 
  p.timeAccesses.isEmpty && 
  p.randomAccesses.isEmpty

def isReproducible (p : DischargeProof) : Bool :=
  p.timeAccesses.isEmpty &&
  p.randomAccesses.isEmpty &&
  p.envAccesses.all (fun e => e.name != "USER" && e.name != "HOME") &&
  p.fileAccesses.all (fun f => f.contentHash.isSome) &&
  p.netAccesses.all (fun n => n.contentHash.isSome)

def actualCoeffects (p : DischargeProof) : Coeffects :=
  let envCoeffs := p.envAccesses.map (fun e => Coeffect.environment e.name)
  let fileCoeffs := p.fileAccesses.map (fun f => 
    match f.contentHash with
    | some h => Coeffect.filesystemCA h
    | none => Coeffect.filesystem f.path)
  let netCoeffs := p.netAccesses.map (fun n =>
    match n.contentHash with  
    | some h => Coeffect.networkCA h
    | none => Coeffect.network n.host n.port)
  let timeCoeffs := if p.timeAccesses.isEmpty then [] else [Coeffect.time]
  let randCoeffs := if p.randomAccesses.isEmpty then [] else [Coeffect.random]
  envCoeffs ++ fileCoeffs ++ netCoeffs ++ timeCoeffs ++ randCoeffs

end DischargeProof

-- ═══════════════════════════════════════════════════════════════════════════════
-- THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Pure proofs have no external coeffects. -/
theorem pure_no_coeffects (p : DischargeProof) (h : p.isPure = true) :
    p.envAccesses = [] ∧ p.netAccesses = [] ∧ 
    p.timeAccesses = [] ∧ p.randomAccesses = [] := by
  simp only [DischargeProof.isPure, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

/-- Reproducible proofs have no time or random access. -/
theorem reproducible_no_time_random (p : DischargeProof) 
    (h : p.isReproducible = true) :
    p.timeAccesses = [] ∧ p.randomAccesses = [] := by
  simp only [DischargeProof.isReproducible, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, _⟩ := h
  exact ⟨h1, h2⟩

/-- Pure implies time and random are empty (partial reproducibility). -/
theorem pure_implies_no_time_random (p : DischargeProof) 
    (h : p.isPure = true) : p.timeAccesses = [] ∧ p.randomAccesses = [] := by
  simp only [DischargeProof.isPure, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨_, _⟩, h3⟩, h4⟩ := h
  exact ⟨h3, h4⟩

end Foundry.Continuity.Witness
