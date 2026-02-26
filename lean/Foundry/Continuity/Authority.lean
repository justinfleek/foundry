/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                            CONTINUITY · AUTHORITY
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                      Capability Lattice and Security Levels

                          straylight.software · 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    "With great power comes great responsibility."
    "With no power comes no responsibility."
                                        — capability-based security

Authority forms a MEET-SEMILATTICE. The meet (⊓) is intersection.
Security forms a JOIN-SEMILATTICE. The join (⊔) is minimum.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Foundry.Continuity.Authority

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECURITY LEVEL (JOIN-SEMILATTICE)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Security level of cryptographic operations. Higher = better. -/
inductive SecurityLevel where
  | plain       -- Unauthenticated
  | classical   -- Classical crypto (ed25519)
  | quantum     -- Post-quantum (hybrid)
  deriving DecidableEq, Repr

namespace SecurityLevel

def rank : SecurityLevel → Nat
  | plain => 0
  | classical => 1
  | quantum => 2

theorem rank_injective : ∀ a b, rank a = rank b → a = b := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp only [rank] at h; omega)

/-- Join (⊔): the MINIMUM security level (weakest link). -/
def join (a b : SecurityLevel) : SecurityLevel :=
  if rank a ≤ rank b then a else b

end SecurityLevel

instance : LE SecurityLevel where
  le a b := SecurityLevel.rank a ≤ SecurityLevel.rank b

instance : Max SecurityLevel where
  max := SecurityLevel.join

theorem security_join_comm : ∀ a b : SecurityLevel, max a b = max b a := by
  intro a b; simp only [Max.max, SecurityLevel.join, SecurityLevel.rank]
  cases a <;> cases b <;> simp

theorem security_join_assoc : ∀ a b c : SecurityLevel, max (max a b) c = max a (max b c) := by
  intro a b c; simp only [Max.max, SecurityLevel.join, SecurityLevel.rank]
  cases a <;> cases b <;> cases c <;> simp

theorem security_join_idem : ∀ a : SecurityLevel, max a a = a := by
  intro a; simp only [Max.max, SecurityLevel.join, SecurityLevel.rank]; cases a <;> simp

-- ═══════════════════════════════════════════════════════════════════════════════
-- CAPABILITIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Individual capabilities: what you're allowed to do. -/
inductive Capability where
  | shell (user : String)
  | exec (user : String) (command : String)
  | gitUploadPack (repos : List String)
  | gitReceivePack (repos : List String)
  | portForward (ports : List (String × Nat))
  | sftp (paths : List String)
  | build (targets : List String)           -- Can build these targets
  | attest (scopes : List String)           -- Can sign attestations for these
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════════════════════
-- AUTHORITY (MEET-SEMILATTICE)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Authority: a set of capabilities. -/
structure Authority where
  capabilities : List Capability
  deriving DecidableEq, Repr

namespace Authority

def none : Authority := ⟨[]⟩

def all : Authority := ⟨[
  .shell "root", .exec "root" "*", 
  .gitUploadPack ["*"], .gitReceivePack ["*"],
  .portForward [], .sftp ["*"],
  .build ["*"], .attest ["*"]
]⟩

def has (a : Authority) (c : Capability) : Bool :=
  a.capabilities.contains c

/-- Meet (⊓): intersection of capabilities. -/
def meet (a b : Authority) : Authority :=
  ⟨a.capabilities.filter (b.capabilities.contains ·)⟩

/-- Join (⊔): union of capabilities. -/
def join (a b : Authority) : Authority :=
  ⟨a.capabilities ++ b.capabilities.filter (fun c => !a.capabilities.contains c)⟩

def subset (a b : Authority) : Prop :=
  ∀ c ∈ a.capabilities, c ∈ b.capabilities

/-- Extensionality for Authority. -/
theorem ext {a b : Authority} (h : a.capabilities = b.capabilities) : a = b := by
  cases a; cases b; simp only [Authority.mk.injEq]; exact h

end Authority

instance : Min Authority where min := Authority.meet
instance : Max Authority where max := Authority.join
instance : LE Authority where le := Authority.subset

instance : DecidableRel (· ≤ · : Authority → Authority → Prop) :=
  fun a b => inferInstanceAs (Decidable (∀ c ∈ a.capabilities, c ∈ b.capabilities))

-- ═══════════════════════════════════════════════════════════════════════════════
-- LATTICE THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════════

-- Simplified lattice theorems (structural equality proofs deferred)
-- The key property is that meet/join are well-defined operations.

theorem authority_meet_le_left : ∀ a b : Authority, min a b ≤ a := by
  intro a b
  simp only [Min.min, Authority.meet, LE.le, Authority.subset]
  intro c hc; simp only [List.mem_filter] at hc; exact hc.1

theorem authority_meet_le_right : ∀ a b : Authority, min a b ≤ b := by
  intro a b
  simp only [Min.min, Authority.meet, LE.le, Authority.subset]
  intro c hc
  simp only [List.mem_filter] at hc
  obtain ⟨_, hcb⟩ := hc
  simp only [List.contains_eq_any_beq, List.any_eq_true] at hcb
  obtain ⟨x, hxb, hcx⟩ := hcb
  simp only [beq_iff_eq] at hcx
  rw [hcx]; exact hxb

theorem authority_meet_glb : ∀ a b c : Authority, c ≤ a → c ≤ b → c ≤ min a b := by
  intro a b c hca hcb
  simp only [LE.le, Authority.subset, Min.min, Authority.meet] at *
  intro cap hcap
  simp only [List.mem_filter, List.contains_eq_any_beq, List.any_eq_true]
  constructor
  · exact hca cap hcap
  · exact ⟨cap, hcb cap hcap, by simp only [beq_self_eq_true]⟩

end Foundry.Continuity.Authority
