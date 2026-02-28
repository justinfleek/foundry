/-
  Cornell - Verified Binary Format DSL
  
  "Cornell boxes... the man made these things. Boxes with things inside them."
  
  A box is a bidirectional codec with machine-checked round-trip correctness.
  
  This module re-exports verified boxes from Foundry.Cornell.Proofs.
  All boxes have complete proofs - no sorry, no axiom, no partial.
-/

import Foundry.Cornell.Proofs

namespace Foundry.Cornell

-- ═══════════════════════════════════════════════════════════════════════════════
-- RE-EXPORTS FROM PROOFS
-- All of these have complete, machine-checked proofs.
-- ═══════════════════════════════════════════════════════════════════════════════

-- Core types
export Foundry.Cornell.Proofs (Bytes ParseResult Box)

-- Verified primitive boxes
export Foundry.Cornell.Proofs (unit u8 u64leBitVec u32leBitVec)

-- Verified combinators  
export Foundry.Cornell.Proofs (seq isoBox)

-- ═══════════════════════════════════════════════════════════════════════════════
-- BYTES UTILITIES (convenience functions)
-- ═══════════════════════════════════════════════════════════════════════════════

instance : Repr Bytes where
  reprPrec bs _ := 
    let hex := bs.toList.map fun b => 
      let hi := b.toNat / 16
      let lo := b.toNat % 16
      let toHex := fun n => if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
      s!"{toHex hi}{toHex lo}"
    Std.Format.text s!"⟨{String.intercalate " " hex}⟩"

def Bytes.empty : Bytes := ByteArray.empty

def Bytes.length (bs : Bytes) : Nat := bs.size

def Bytes.append (a b : Bytes) : Bytes := a ++ b

instance : Append Bytes := ⟨Bytes.append⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- PARSERESULT UTILITIES
-- ═══════════════════════════════════════════════════════════════════════════════

open Foundry.Cornell.Proofs in
instance {α : Type} [Repr α] : Repr (ParseResult α) where
  reprPrec
    | .ok a _, n => Repr.addAppParen ("ParseResult.ok " ++ reprArg a ++ " <bytes>") n
    | .fail, _ => "ParseResult.fail"

open Foundry.Cornell.Proofs in
def ParseResult.isOk {α : Type} : ParseResult α → Bool
  | .ok _ _ => true
  | .fail => false

open Foundry.Cornell.Proofs in
def ParseResult.toOption {α : Type} : ParseResult α → Option (α × Bytes)
  | .ok a rest => some (a, rest)
  | .fail => none

-- ═══════════════════════════════════════════════════════════════════════════════
-- UINTXX BOXES (via isoBox from BitVec)
-- These use the verified BitVec boxes and convert via isomorphism
-- ═══════════════════════════════════════════════════════════════════════════════

open Foundry.Cornell.Proofs in
/-- Little-endian u64 (verified via isoBox from u64leBitVec) -/
def u64le : Box UInt64 := 
  isoBox u64leBitVec 
    UInt64.ofBitVec 
    UInt64.toBitVec
    (fun _ => rfl)
    (fun _ => rfl)

open Foundry.Cornell.Proofs in
/-- Little-endian u32 (verified via isoBox from u32leBitVec) -/
def u32le : Box UInt32 := 
  isoBox u32leBitVec 
    UInt32.ofBitVec 
    UInt32.toBitVec
    (fun _ => rfl)
    (fun _ => rfl)

open Foundry.Cornell.Proofs in
/-- Boolean as u64 (Nix style): 0 = false, nonzero = true 
    
    Note: This is a lossy encoding (many u64 values map to true).
    The roundtrip property still holds: parse(serialize(b)) = b
-/
def bool64 : Box Bool where
  parse bs := (u64le.parse bs).map (· != 0)
  serialize b := u64le.serialize (if b then 1 else 0)
  roundtrip b := by
    simp only [u64le, isoBox, ParseResult.map]
    cases b
    · -- false case: serialize gives 0, parse gives 0, (0 != 0) = false
      rw [u64leBitVec.roundtrip]; rfl
    · -- true case: serialize gives 1, parse gives 1, (1 != 0) = true  
      rw [u64leBitVec.roundtrip]; rfl
  consumption b extra := by
    simp only [u64le, isoBox, ParseResult.map]
    cases b
    · rw [u64leBitVec.consumption]; rfl
    · rw [u64leBitVec.consumption]; rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONVENIENCE COMBINATORS
-- ═══════════════════════════════════════════════════════════════════════════════

open Foundry.Cornell.Proofs in
/-- Map a box through an isomorphism (alias for isoBox) -/
def isoMap {α β : Type} (box : Box α) (f : α → β) (g : β → α) 
    (iso_fg : ∀ b, f (g b) = b) (iso_gf : ∀ a, g (f a) = a) : Box β := 
  isoBox box f g iso_fg iso_gf

end Foundry.Cornell
