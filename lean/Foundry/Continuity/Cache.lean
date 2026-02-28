/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                           // CONTINUITY // CACHE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                              Cache Trust Model

                          straylight.software · 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

When can we use a cached build output?
  1. Builder is recognized (vouch chain exists)
  2. Proof signature verifies
  3. Coeffect policy is satisfied

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Foundry.Continuity.Crypto
import Foundry.Continuity.Trust
import Foundry.Continuity.Witness

namespace Foundry.Continuity.Cache

open Foundry.Continuity.Crypto
open Foundry.Continuity.Trust
open Foundry.Continuity.Witness

-- ═══════════════════════════════════════════════════════════════════════════════
-- COEFFECT POLICY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Simple coeffect policy (non-recursive for termination). -/
inductive SimplePolicy where
  | acceptAll                                    -- Trust any build
  | requirePure                                  -- Only pure builds
  | requireReproducible                          -- Only reproducible builds
  | requireProxy (proxy : HybridPublicKey)       -- Network must go through proxy
  | requireNoTime                                -- No wall clock access
  | requireNoRandom                              -- No entropy access
  deriving Inhabited

-- Axiomatize DecidableEq due to HybridPublicKey
@[instance] axiom SimplePolicy.instDecidableEq : DecidableEq SimplePolicy

/-- Combined policy is a list of simple policies. -/
def CoeffectPolicy := List SimplePolicy

/-- Check if a discharge proof satisfies a simple policy. -/
def satisfies_simple (p : DischargeProof) (policy : SimplePolicy) : Bool :=
  match policy with
  | .acceptAll => true
  | .requirePure => p.isPure
  | .requireReproducible => p.isReproducible
  | .requireProxy _ => p.netAccesses.all (fun _ => true)  -- Would check proxy sig
  | .requireNoTime => p.timeAccesses.isEmpty
  | .requireNoRandom => p.randomAccesses.isEmpty

/-- Check if a discharge proof satisfies all policies. -/
def satisfies_policy (p : DischargeProof) (policy : CoeffectPolicy) : Bool :=
  policy.all (satisfies_simple p)

-- ═══════════════════════════════════════════════════════════════════════════════
-- TRUST STATE WITH POLICY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Extended trust state with coeffect policy. -/
structure TrustStateWithPolicy extends TrustState where
  coeffectPolicy : CoeffectPolicy

-- ═══════════════════════════════════════════════════════════════════════════════
-- CACHE TRUST
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Can we trust a cached build output? -/
noncomputable def can_trust_cache (ts : TrustStateWithPolicy) (p : DischargeProof) 
    (_now : Timestamp) : Bool :=
  -- 1. Builder is recognized
  let recognized := match ts.toTrustState.recognition p.builder with
    | .unrecognized => false
    | _ => true
  -- 2. Signature verifies
  let sigValid := hybrid_verify p.builder p.message p.signature
  -- 3. Policy satisfied
  let policyOk := satisfies_policy p ts.coeffectPolicy
  recognized && sigValid && policyOk

-- ═══════════════════════════════════════════════════════════════════════════════
-- THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Unrecognized builders cannot have trusted cache entries. -/
theorem unrecognized_no_cache_trust (ts : TrustStateWithPolicy) (p : DischargeProof) 
    (now : Timestamp)
    (h_unrec : ts.toTrustState.recognition p.builder = .unrecognized) :
    can_trust_cache ts p now = false := by
  simp only [can_trust_cache]
  simp only [h_unrec, Bool.false_and]

/-- Recognized, well-formed proofs can be trusted (if policy allows). -/
theorem recognized_wellformed_can_trust (ts : TrustStateWithPolicy) (p : DischargeProof)
    (now : Timestamp)
    (h_rec : ts.toTrustState.recognition p.builder ≠ .unrecognized)
    (h_wf : p.wellFormed)
    (h_policy : satisfies_policy p ts.coeffectPolicy = true) :
    can_trust_cache ts p now = true := by
  simp only [can_trust_cache]
  simp only [DischargeProof.wellFormed] at h_wf
  have h1 : (match ts.toTrustState.recognition p.builder with
    | .unrecognized => false | _ => true) = true := by
    cases h : ts.toTrustState.recognition p.builder <;> simp_all
  simp only [h1, h_wf, h_policy, Bool.true_and, Bool.and_self]

/-- Empty policy (accept all) trusts any proof. -/
theorem empty_policy_accepts (p : DischargeProof) :
    satisfies_policy p [] = true := rfl

/-- Pure requirement rejects impure proofs. -/
theorem pure_rejects_impure (p : DischargeProof) 
    (h : p.isPure = false) :
    satisfies_policy p [.requirePure] = false := by
  simp only [satisfies_policy, List.all_cons, satisfies_simple, h, Bool.false_and]

/-- Combined policy requires all sub-policies. -/
theorem combined_all (p : DischargeProof) (policies : CoeffectPolicy) :
    satisfies_policy p policies = policies.all (satisfies_simple p) := rfl

end Foundry.Continuity.Cache
