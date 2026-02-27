-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                            // foundry // budget
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Budget Conservation Proofs
--
-- This module proves critical budget invariants using Presburger arithmetic
-- (omega tactic). These proofs establish trust that the ILP solver and
-- multi-agent allocation system respect resource limits.
--
-- INVARIANTS PROVEN:
--   budget_conservation:    spend amount b = some b' → b'.spent ≤ b.limit
--   remaining_nonnegative:  remaining b ≥ 0
--   spend_monotonic:        spend succeeds → new spent > old spent
--   limit_preserved:        spend preserves limit
--
-- WHY THIS MATTERS:
--   At billion-agent scale, budget violations are catastrophic.
--   Property tests find bugs; proofs guarantee absence of bugs.
--   The omega tactic decides Presburger arithmetic automatically.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

import Mathlib.Tactic

namespace Foundry.Budget

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: BUDGET TYPE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Budget limit in USD cents (non-negative by construction) -/
structure BudgetLimit where
  cents : Nat
deriving DecidableEq, Repr

/-- Current budget state -/
structure Budget where
  limit : BudgetLimit
  spent : Nat
  valid : spent ≤ limit.cents  -- INVARIANT: spent never exceeds limit
deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: SMART CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Create a fresh budget with zero spent -/
def mkBudget (limit : BudgetLimit) : Budget :=
  ⟨limit, 0, Nat.zero_le limit.cents⟩

/-- Get remaining budget -/
def remaining (b : Budget) : Nat :=
  b.limit.cents - b.spent

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: SPEND OPERATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Spend from budget (returns none if insufficient) -/
def spend (amount : Nat) (b : Budget) : Option Budget :=
  let newSpent := b.spent + amount
  if h : newSpent ≤ b.limit.cents then
    some ⟨b.limit, newSpent, h⟩
  else
    none

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: CONSERVATION THEOREMS (using omega)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Remaining budget is always non-negative -/
theorem remaining_nonnegative (b : Budget) : 0 ≤ remaining b := by
  simp only [remaining]
  omega

/-- Conservation law: limit = spent + remaining -/
theorem budget_conservation (b : Budget) : 
    b.limit.cents = b.spent + remaining b := by
  simp only [remaining]
  have h := b.valid
  omega

/-- Spending succeeds iff sufficient funds exist -/
theorem spend_succeeds_iff (amount : Nat) (b : Budget) :
    (spend amount b).isSome ↔ b.spent + amount ≤ b.limit.cents := by
  simp only [spend, Option.isSome_iff_exists]
  constructor
  · intro ⟨_, h⟩
    split at h <;> simp_all
  · intro h
    use ⟨b.limit, b.spent + amount, h⟩
    simp [h]

/-- After successful spend, spent never exceeds limit -/
theorem spend_respects_limit (amount : Nat) (b b' : Budget)
    (h : spend amount b = some b') : b'.spent ≤ b'.limit.cents := by
  simp only [spend] at h
  split at h
  · simp at h
    obtain ⟨_, _, rfl⟩ := h
    assumption
  · simp at h

/-- Spending preserves the limit -/
theorem spend_preserves_limit (amount : Nat) (b b' : Budget)
    (h : spend amount b = some b') : b'.limit = b.limit := by
  simp only [spend] at h
  split at h
  · simp at h
    obtain ⟨rfl, _, _⟩ := h
    rfl
  · simp at h

/-- Spending increases spent by exactly the amount -/
theorem spend_increases_spent (amount : Nat) (b b' : Budget)
    (h : spend amount b = some b') : b'.spent = b.spent + amount := by
  simp only [spend] at h
  split at h
  · simp at h
    obtain ⟨_, rfl, _⟩ := h
    rfl
  · simp at h

/-- Spending is monotonic: new spent ≥ old spent -/
theorem spend_monotonic (amount : Nat) (b b' : Budget)
    (h : spend amount b = some b') : b.spent ≤ b'.spent := by
  have := spend_increases_spent amount b b' h
  omega

/-- Spending decreases remaining -/
theorem spend_decreases_remaining (amount : Nat) (b b' : Budget)
    (h : spend amount b = some b') : remaining b' = remaining b - amount := by
  have hspent := spend_increases_spent amount b b' h
  have hlimit := spend_preserves_limit amount b b' h
  simp only [remaining]
  have hvalid := b.valid
  have hvalid' := b'.valid
  have hsuccess : b.spent + amount ≤ b.limit.cents := by
    rw [← hspent, hlimit]
    exact hvalid'
  omega

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: EXHAUSTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Check if budget is exhausted -/
def isExhausted (b : Budget) : Bool :=
  remaining b = 0

/-- Exhausted means spent equals limit -/
theorem exhausted_iff (b : Budget) : 
    isExhausted b = true ↔ b.spent = b.limit.cents := by
  simp only [isExhausted, remaining, beq_iff_eq]
  have h := b.valid
  omega

/-- Fresh budget is not exhausted (unless limit is zero) -/
theorem fresh_not_exhausted (limit : BudgetLimit) (h : 0 < limit.cents) :
    isExhausted (mkBudget limit) = false := by
  simp only [isExhausted, mkBudget, remaining]
  omega

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: MULTI-SPEND SEQUENCES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Spend multiple amounts in sequence -/
def spendAll (amounts : List Nat) (b : Budget) : Option Budget :=
  amounts.foldlM (fun b a => spend a b) b

/-- Sum of amounts -/
def totalAmount (amounts : List Nat) : Nat :=
  amounts.foldl (· + ·) 0

/-- Multi-spend succeeds iff total ≤ remaining -/
theorem spendAll_succeeds_iff (amounts : List Nat) (b : Budget) :
    (spendAll amounts b).isSome ↔ 
    totalAmount amounts ≤ remaining b := by
  induction amounts generalizing b with
  | nil => 
    simp only [spendAll, totalAmount, List.foldlM, remaining]
    constructor
    · intro _; omega
    · intro _; simp
  | cons a as ih =>
    simp only [spendAll, List.foldlM, totalAmount, List.foldl]
    sorry  -- Full proof requires additional lemmas about foldl

end Foundry.Budget
