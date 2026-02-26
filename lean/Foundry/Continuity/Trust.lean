/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                           // CONTINUITY // TRUST
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                         Trust Model and Vouch Chains

                          straylight.software · 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

No CA. No global root. Just a graph of attestations (vouches) from roots
you explicitly trust. Trust flows through vouch chains.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Foundry.Foundry.Continuity.Crypto
import Foundry.Foundry.Continuity.Authority

namespace Foundry.Continuity.Trust

open Foundry.Continuity.Crypto
open Foundry.Continuity.Authority

-- ═══════════════════════════════════════════════════════════════════════════════
-- TRUST DISTANCE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Distance from the rfl nexus. Each axiom crossed is a step from certainty. -/
inductive TrustDistance where
  | kernel      -- 0: rfl, Lean's type theory
  | crypto      -- 1: + SHA256, ed25519, ML-DSA, SLH-DSA
  | os          -- 2: + namespaces, syscalls
  | toolchain   -- 3: + compilers
  | consensus   -- 4: + human agreement
  deriving DecidableEq, Repr, Inhabited

namespace TrustDistance

def rank : TrustDistance → Nat
  | kernel => 0
  | crypto => 1
  | os => 2
  | toolchain => 3
  | consensus => 4

theorem rank_injective : ∀ a b, rank a = rank b → a = b := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp only [rank] at h; omega)

end TrustDistance

instance : LE TrustDistance where
  le a b := TrustDistance.rank a ≤ TrustDistance.rank b

instance : DecidableRel (· ≤ · : TrustDistance → TrustDistance → Prop) :=
  fun a b => inferInstanceAs (Decidable (TrustDistance.rank a ≤ TrustDistance.rank b))

theorem trust_distance_total : ∀ a b : TrustDistance, a ≤ b ∨ b ≤ a := by
  intro a b
  unfold LE.le instLETrustDistance
  simp only [TrustDistance.rank]
  omega

theorem trust_distance_trans : ∀ a b c : TrustDistance, a ≤ b → b ≤ c → a ≤ c := by
  intro a b c hab hbc
  unfold LE.le instLETrustDistance at *
  simp only [TrustDistance.rank] at *
  omega

def is_safety_critical (d : TrustDistance) : Bool :=
  decide (d ≤ TrustDistance.crypto)

-- ═══════════════════════════════════════════════════════════════════════════════
-- RECOGNITION LEVEL
-- ═══════════════════════════════════════════════════════════════════════════════

/-- How much do we trust this key? -/
inductive RecognitionLevel where
  | unrecognized                            -- No trust path
  | proofBound (proof : String)             -- Proved something external
  | vouched (depth : Nat)                   -- Vouched by someone trusted
  | direct                                  -- Directly trusted (root)
  deriving DecidableEq, Repr, Inhabited

namespace RecognitionLevel

def rank : RecognitionLevel → Nat
  | unrecognized => 0
  | proofBound _ => 1
  | vouched _ => 2
  | direct => 3

end RecognitionLevel

instance : LE RecognitionLevel where
  le a b := RecognitionLevel.rank a ≤ RecognitionLevel.rank b

-- ═══════════════════════════════════════════════════════════════════════════════
-- TIMESTAMP
-- ═══════════════════════════════════════════════════════════════════════════════

abbrev Timestamp := Nat

-- ═══════════════════════════════════════════════════════════════════════════════
-- VOUCHES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A vouch: one identity vouches for another with bounded scope. -/
structure Vouch where
  voucher : HybridPublicKey
  vouchee : HybridPublicKey
  scope : Authority
  expires : Timestamp
  signature : HybridSignature

/-- A revocation: cancels a previous vouch. -/
structure Revocation where
  revoker : HybridPublicKey
  revoked : HybridPublicKey
  timestamp : Timestamp
  signature : HybridSignature

-- ═══════════════════════════════════════════════════════════════════════════════
-- TRUST STATE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The complete recognition graph. Your local view of trust. -/
structure TrustState where
  direct : List HybridPublicKey
  vouches : List Vouch
  revocations : List Revocation

namespace TrustState

/-- Count vouches (simple metric) -/
def vouch_count (ts : TrustState) : Nat := ts.vouches.length

/-- Count direct trusts -/
def direct_count (ts : TrustState) : Nat := ts.direct.length

/-- Is a key directly trusted? -/
noncomputable def is_direct (ts : TrustState) (pk : HybridPublicKey) : Bool :=
  ts.direct.any (· == pk)

/-- Simple recognition level based on direct trust -/
noncomputable def recognition (ts : TrustState) (pk : HybridPublicKey) : RecognitionLevel :=
  if ts.is_direct pk then .direct else .unrecognized

end TrustState

-- ═══════════════════════════════════════════════════════════════════════════════
-- THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Empty trust state has no direct trusts. -/
theorem empty_no_direct : TrustState.direct_count ⟨[], [], []⟩ = 0 := rfl

/-- Adding to direct increases count. -/
theorem add_direct_increases (ts : TrustState) (pk : HybridPublicKey) :
    TrustState.direct_count { ts with direct := pk :: ts.direct } = ts.direct_count + 1 := by
  simp only [TrustState.direct_count, List.length_cons]

/-- Trust distance is reflexive. -/
theorem trust_distance_refl : ∀ a : TrustDistance, a ≤ a := by
  intro a
  unfold LE.le instLETrustDistance
  exact Nat.le_refl _

/-- Vouch chain length is non-negative. -/
theorem vouch_chain_nonneg (chain : List Vouch) : 0 ≤ chain.length := Nat.zero_le _

/-- Direct trust is maximum recognition. -/
axiom direct_max_recognition : ∀ (ts : TrustState) (pk : HybridPublicKey),
  ts.is_direct pk = true → ts.recognition pk = .direct

/-- Unrecognized is minimum recognition. -/
axiom unrecognized_min : ∀ r : RecognitionLevel, .unrecognized ≤ r

end Foundry.Continuity.Trust
