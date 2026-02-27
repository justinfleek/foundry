-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // foundry // timestamp
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Timestamp Ordering Proofs
--
-- This module proves that timestamps are well-ordered and that operations
-- on timestamp intervals (like duration) cannot underflow.
--
-- THE PROBLEM (from Pipeline.lean):
--   def duration (p : DischargeProof) : Nat :=
--     p.endTime.nanos - p.startTime.nanos  -- BUG: Can underflow!
--
-- THE FIX:
--   Store ordering proof in the structure, then duration is safe.
--
-- INVARIANTS PROVEN:
--   ordered_interval:       startTime ≤ endTime
--   duration_nonnegative:   duration ≥ 0 (by construction)
--   duration_correct:       duration = endTime - startTime
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

import Mathlib.Tactic

namespace Foundry.Timestamp

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: TIMESTAMP TYPE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Monotonic timestamp in nanoseconds -/
structure Timestamp where
  nanos : Nat
deriving DecidableEq, Repr, Ord

instance : LE Timestamp where
  le a b := a.nanos ≤ b.nanos

instance : LT Timestamp where
  lt a b := a.nanos < b.nanos

instance (a b : Timestamp) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.nanos ≤ b.nanos))

instance (a b : Timestamp) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.nanos < b.nanos))

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: ORDERED INTERVAL (fixes the underflow bug)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A time interval with proven ordering.
    
    This is the key type: by carrying the proof `ordered`, we guarantee
    that duration computation cannot underflow.
-/
structure TimeInterval where
  startTime : Timestamp
  endTime : Timestamp
  ordered : startTime ≤ endTime  -- THE FIX: Ordering is proven at construction

/-- Duration of an interval (safe: cannot underflow due to `ordered` proof) -/
def TimeInterval.duration (interval : TimeInterval) : Nat :=
  interval.endTime.nanos - interval.startTime.nanos

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: ORDERING PROOFS (using omega)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Duration is non-negative (trivially true for Nat, but proves our design) -/
theorem duration_nonnegative (interval : TimeInterval) : 
    0 ≤ interval.duration := by
  simp only [TimeInterval.duration]
  omega

/-- Duration equals end minus start -/
theorem duration_correct (interval : TimeInterval) :
    interval.duration = interval.endTime.nanos - interval.startTime.nanos := rfl

/-- Duration is zero iff start equals end -/
theorem duration_zero_iff (interval : TimeInterval) :
    interval.duration = 0 ↔ interval.startTime = interval.endTime := by
  simp only [TimeInterval.duration]
  have h := interval.ordered
  simp only [LE.le] at h
  constructor
  · intro hd
    have : interval.endTime.nanos = interval.startTime.nanos := by omega
    ext; exact this
  · intro heq
    simp [heq]

/-- If duration is positive, start is strictly before end -/
theorem duration_pos_iff (interval : TimeInterval) :
    0 < interval.duration ↔ interval.startTime < interval.endTime := by
  simp only [TimeInterval.duration, LT.lt]
  have h := interval.ordered
  simp only [LE.le] at h
  omega

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: INTERVAL CONSTRUCTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Create an interval, returning none if not ordered -/
def mkInterval (start finish : Timestamp) : Option TimeInterval :=
  if h : start ≤ finish then
    some ⟨start, finish, h⟩
  else
    none

/-- mkInterval succeeds iff timestamps are ordered -/
theorem mkInterval_isSome_iff (start finish : Timestamp) :
    (mkInterval start finish).isSome ↔ start ≤ finish := by
  simp only [mkInterval, Option.isSome_iff_exists]
  constructor
  · intro ⟨_, h⟩
    split at h <;> simp_all
  · intro h
    use ⟨start, finish, h⟩
    simp [h]

/-- Zero-duration interval at a point -/
def pointInterval (t : Timestamp) : TimeInterval :=
  ⟨t, t, le_refl t⟩

/-- Point interval has zero duration -/
theorem pointInterval_duration (t : Timestamp) :
    (pointInterval t).duration = 0 := by
  simp [pointInterval, TimeInterval.duration]

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: INTERVAL CONCATENATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Concatenate two adjacent intervals -/
def concat (a b : TimeInterval) (h : a.endTime = b.startTime) : TimeInterval :=
  ⟨a.startTime, b.endTime, by
    have ha := a.ordered
    have hb := b.ordered
    simp only [LE.le] at *
    omega⟩

/-- Duration of concatenated intervals is sum of durations -/
theorem concat_duration (a b : TimeInterval) (h : a.endTime = b.startTime) :
    (concat a b h).duration = a.duration + b.duration := by
  simp only [concat, TimeInterval.duration]
  have ha := a.ordered
  have hb := b.ordered
  simp only [LE.le] at *
  have heq : a.endTime.nanos = b.startTime.nanos := by
    simp [h]
  omega

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: TOTAL ORDERING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Timestamps are totally ordered -/
theorem timestamp_total (a b : Timestamp) : a ≤ b ∨ b ≤ a := by
  simp only [LE.le]
  omega

/-- Transitivity of timestamp ordering -/
theorem timestamp_trans (a b c : Timestamp) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  simp only [LE.le] at *
  omega

/-- Antisymmetry of timestamp ordering -/
theorem timestamp_antisymm (a b : Timestamp) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  simp only [LE.le] at *
  ext; omega

end Foundry.Timestamp
