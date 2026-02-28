/-
  Foundry.Cornell.Proofs - Verified Box Implementations
  
  This module contains Box definitions with COMPLETE proofs.
  No `sorry`, no `axiom`, no `partial`.
  
  The goal: real load-bearing proofs that guarantee roundtrip correctness.
-/

import Std.Tactic.BVDecide

namespace Foundry.Cornell.Proofs

-- ═══════════════════════════════════════════════════════════════════════════════
-- BYTES (same as Basic, but we'll use ByteArray directly for lemma access)
-- ═══════════════════════════════════════════════════════════════════════════════

abbrev Bytes := ByteArray

-- ═══════════════════════════════════════════════════════════════════════════════
-- PARSE RESULT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parse result: either failure or (value, remaining bytes) -/
inductive ParseResult (α : Type) where
  | ok : α → Bytes → ParseResult α
  | fail : ParseResult α
  deriving DecidableEq

namespace ParseResult

def map {α β : Type} (f : α → β) : ParseResult α → ParseResult β
  | ok a rest => ok (f a) rest
  | fail => fail

def bind {α β : Type} (r : ParseResult α) (f : α → Bytes → ParseResult β) : ParseResult β :=
  match r with
  | ok a rest => f a rest
  | fail => fail

-- Lemmas about ParseResult
@[simp] theorem map_ok {α β : Type} (f : α → β) (a : α) (rest : Bytes) : 
    map f (ok a rest) = ok (f a) rest := rfl

@[simp] theorem map_fail {α β : Type} (f : α → β) : 
    map f (fail : ParseResult α) = fail := rfl

@[simp] theorem bind_ok {α β : Type} (a : α) (rest : Bytes) (f : α → Bytes → ParseResult β) :
    bind (ok a rest) f = f a rest := rfl

@[simp] theorem bind_fail {α β : Type} (f : α → Bytes → ParseResult β) :
    bind (fail : ParseResult α) f = fail := rfl

end ParseResult

-- ═══════════════════════════════════════════════════════════════════════════════
-- BOX - The verified codec structure
-- ═══════════════════════════════════════════════════════════════════════════════

/-- 
A Box is a verified bidirectional codec.

Key properties:
- `roundtrip`: parsing what you serialized gives back the original value
- `consumption`: parsing consumes exactly the serialized bytes, leaving extra untouched
-/
structure Box (α : Type) where
  parse : Bytes → ParseResult α
  serialize : α → Bytes
  roundtrip : ∀ a, parse (serialize a) = ParseResult.ok a ByteArray.empty
  consumption : ∀ a extra, parse (serialize a ++ extra) = ParseResult.ok a extra

-- ═══════════════════════════════════════════════════════════════════════════════
-- UNIT BOX - The trivial case (zero bytes)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The unit box: encodes Unit as zero bytes -/
def unit : Box Unit where
  parse bs := .ok () bs
  serialize _ := ByteArray.empty
  roundtrip := by
    intro a
    -- parse (serialize ()) = parse ByteArray.empty = .ok () ByteArray.empty
    rfl
  consumption := by
    intro a extra
    -- parse (serialize () ++ extra) = parse (ByteArray.empty ++ extra) = parse extra = .ok () extra
    simp [ByteArray.empty_append]

-- ═══════════════════════════════════════════════════════════════════════════════
-- U8 BOX - Single byte
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parse a single byte -/
def parseU8 (bs : Bytes) : ParseResult UInt8 :=
  if h : bs.size > 0 then
    .ok bs[0] (bs.extract 1 bs.size)
  else 
    .fail

/-- Serialize a single byte -/
def serializeU8 (v : UInt8) : Bytes := 
  [v].toByteArray

-- Key lemma: size of a singleton ByteArray
theorem singleton_size (v : UInt8) : [v].toByteArray.size = 1 := by
  simp [List.size_toByteArray]

-- Key lemma: getting element 0 of singleton
theorem singleton_getElem (v : UInt8) : [v].toByteArray[0]'(by simp) = v := by
  simp

-- Key lemma: extracting from position 1 of a size-1 array gives empty
theorem singleton_extract_tail (v : UInt8) : 
    [v].toByteArray.extract 1 [v].toByteArray.size = ByteArray.empty := by
  simp

/-- Single byte box with verified roundtrip -/
def u8 : Box UInt8 where
  parse := parseU8
  serialize := serializeU8
  roundtrip := by
    intro v
    simp only [parseU8, serializeU8]
    -- Need to show: if h : [v].toByteArray.size > 0 then ...
    have hsize : [v].toByteArray.size > 0 := by simp
    simp only [hsize, ↓reduceDIte]
    -- Show equality by showing both components match
    have hval : [v].toByteArray[0]'hsize = v := by simp
    have hrest : [v].toByteArray.extract 1 [v].toByteArray.size = ByteArray.empty := by
      simp
    simp only [hval, hrest]
  consumption := by
    intro v extra
    simp only [parseU8, serializeU8]
    -- Size of [v].toByteArray ++ extra > 0
    have hsize : ([v].toByteArray ++ extra).size > 0 := by
      simp only [ByteArray.size_append, List.size_toByteArray, List.length_cons, List.length_nil]
      omega
    simp only [hsize, ↓reduceDIte]
    -- Show value component: ([v].toByteArray ++ extra)[0] = v
    have hval : ([v].toByteArray ++ extra)[0]'hsize = v := by
      have h0 : (0 : Nat) < [v].toByteArray.size := by simp
      rw [ByteArray.getElem_append_left h0]
      simp
    -- Show remaining component: extract 1 (size) = extra
    have hrest : ([v].toByteArray ++ extra).extract 1 ([v].toByteArray ++ extra).size = extra := by
      simp only [ByteArray.size_append]
      -- extract 1 (1 + extra.size) from ([v].toByteArray ++ extra)
      -- [v].toByteArray has size 1, so extract from position 1 gives us the second part
      rw [ByteArray.extract_append_eq_right (by simp : 1 = [v].toByteArray.size)]
      simp
    simp only [hval, hrest]

-- ═══════════════════════════════════════════════════════════════════════════════
-- SEQUENCE COMBINATOR
-- ═══════════════════════════════════════════════════════════════════════════════

/-- 
Sequence two boxes: parse A then B, serialize A then B.
If both A and B have verified roundtrip, so does (A, B).
-/
def seq {α β : Type} (boxA : Box α) (boxB : Box β) : Box (α × β) where
  parse bs := 
    boxA.parse bs |>.bind fun a rest =>
      boxB.parse rest |>.map fun b => (a, b)
  serialize ab := boxA.serialize ab.1 ++ boxB.serialize ab.2
  roundtrip := by
    intro ⟨a, b⟩
    simp only [ParseResult.bind, ParseResult.map]
    -- parse (serA a ++ serB b) 
    -- = parseA (serA a ++ serB b) >>= ...
    -- By consumption of A: parseA (serA a ++ serB b) = ok a (serB b)
    rw [boxA.consumption a (boxB.serialize b)]
    -- Simplify the match
    simp only []
    -- Now: parseB (serB b) = ok b empty
    rw [boxB.roundtrip b]
  consumption := by
    intro ⟨a, b⟩ extra
    simp only [ParseResult.bind, ParseResult.map]
    -- parse ((serA a ++ serB b) ++ extra)
    -- = parseA ((serA a ++ serB b) ++ extra) >>= ...
    -- Rewrite: (serA a ++ serB b) ++ extra = serA a ++ (serB b ++ extra)
    rw [ByteArray.append_assoc]
    -- By consumption of A: parseA (serA a ++ (serB b ++ extra)) = ok a (serB b ++ extra)
    rw [boxA.consumption a (boxB.serialize b ++ extra)]
    -- Simplify the match
    simp only []
    -- By consumption of B: parseB (serB b ++ extra) = ok b extra
    rw [boxB.consumption b extra]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ISO COMBINATOR (mapping through isomorphism)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- 
Map a box through an isomorphism.
Given Box α and bijection f : α ↔ β, get Box β.
-/
def isoBox {α β : Type} (box : Box α) (f : α → β) (g : β → α) 
    (fg : ∀ b, f (g b) = b) (_gf : ∀ a, g (f a) = a) : Box β where
  parse bs := box.parse bs |>.map f
  serialize b := box.serialize (g b)
  roundtrip := by
    intro b
    simp only [ParseResult.map]
    -- parse (serialize (g b)) = ok (g b) empty  by box.roundtrip
    rw [box.roundtrip (g b)]
    -- Simplify the match, then f (g b) = b by fg
    simp only [fg]
  consumption := by
    intro b extra
    simp only [ParseResult.map]
    rw [box.consumption (g b) extra]
    simp only [fg]

-- ═══════════════════════════════════════════════════════════════════════════════
-- U64LE BOX - 64-bit little-endian using BitVec
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Extract byte i (0-indexed from LSB) from a 64-bit value using setWidth and shift -/
def extractByte (v : BitVec 64) (i : Nat) (_hi : i < 8 := by omega) : BitVec 8 :=
  (v >>> (i * 8)).setWidth 8

/-- Combine 8 bytes into a 64-bit value (little-endian) -/
def combineBytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  -- Little-endian: b0 is LSB, b7 is MSB
  -- We build from MSB to LSB using append
  let v7 : BitVec 64 := b7.setWidth 64 <<< 56
  let v6 : BitVec 64 := b6.setWidth 64 <<< 48
  let v5 : BitVec 64 := b5.setWidth 64 <<< 40
  let v4 : BitVec 64 := b4.setWidth 64 <<< 32
  let v3 : BitVec 64 := b3.setWidth 64 <<< 24
  let v2 : BitVec 64 := b2.setWidth 64 <<< 16
  let v1 : BitVec 64 := b1.setWidth 64 <<< 8
  let v0 : BitVec 64 := b0.setWidth 64
  v7 ||| v6 ||| v5 ||| v4 ||| v3 ||| v2 ||| v1 ||| v0

/-- Parse 8 bytes as little-endian u64 -/
def parseU64le (bs : Bytes) : ParseResult (BitVec 64) :=
  if h : bs.size ≥ 8 then
    have h0 : 0 < bs.size := by omega
    have h1 : 1 < bs.size := by omega
    have h2 : 2 < bs.size := by omega
    have h3 : 3 < bs.size := by omega
    have h4 : 4 < bs.size := by omega
    have h5 : 5 < bs.size := by omega
    have h6 : 6 < bs.size := by omega
    have h7 : 7 < bs.size := by omega
    let b0 : BitVec 8 := BitVec.ofNat 8 (bs[0]).toNat
    let b1 : BitVec 8 := BitVec.ofNat 8 (bs[1]).toNat
    let b2 : BitVec 8 := BitVec.ofNat 8 (bs[2]).toNat
    let b3 : BitVec 8 := BitVec.ofNat 8 (bs[3]).toNat
    let b4 : BitVec 8 := BitVec.ofNat 8 (bs[4]).toNat
    let b5 : BitVec 8 := BitVec.ofNat 8 (bs[5]).toNat
    let b6 : BitVec 8 := BitVec.ofNat 8 (bs[6]).toNat
    let b7 : BitVec 8 := BitVec.ofNat 8 (bs[7]).toNat
    .ok (combineBytes b0 b1 b2 b3 b4 b5 b6 b7) (bs.extract 8 bs.size)
  else 
    .fail

/-- Serialize u64 as 8 bytes little-endian -/
def serializeU64le (v : BitVec 64) : Bytes :=
  let b0 := (extractByte v 0).toNat.toUInt8
  let b1 := (extractByte v 1).toNat.toUInt8
  let b2 := (extractByte v 2).toNat.toUInt8
  let b3 := (extractByte v 3).toNat.toUInt8
  let b4 := (extractByte v 4).toNat.toUInt8
  let b5 := (extractByte v 5).toNat.toUInt8
  let b6 := (extractByte v 6).toNat.toUInt8
  let b7 := (extractByte v 7).toNat.toUInt8
  [b0, b1, b2, b3, b4, b5, b6, b7].toByteArray

-- Key lemma: extractByte extracts the correct byte
theorem extractByte_toNat (v : BitVec 64) (i : Nat) (hi : i < 8) :
    (extractByte v i hi).toNat = (v.toNat >>> (i * 8)) % 256 := by
  simp only [extractByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]

-- Key lemma: size of serialized u64
theorem serializeU64le_size (v : BitVec 64) : (serializeU64le v).size = 8 := by
  simp [serializeU64le, List.size_toByteArray]

-- Helper: List of 8 elements has length 8
theorem list8_length {α : Type} (a b c d e f g h : α) : 
    [a, b, c, d, e, f, g, h].length = 8 := rfl

-- The key insight: combineBytes and extractByte are inverses.
-- This is the fundamental theorem we need for u64le roundtrip.

-- Lemma: combining bytes then extracting gives back the original bytes
-- This follows from the structure of little-endian encoding
-- We prove each case using bv_decide

theorem combineBytes_extractByte_0 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    extractByte (combineBytes b0 b1 b2 b3 b4 b5 b6 b7) 0 = b0 := by
  simp only [extractByte, combineBytes]
  bv_decide

theorem combineBytes_extractByte_1 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    extractByte (combineBytes b0 b1 b2 b3 b4 b5 b6 b7) 1 = b1 := by
  simp only [extractByte, combineBytes]
  bv_decide

theorem combineBytes_extractByte_2 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    extractByte (combineBytes b0 b1 b2 b3 b4 b5 b6 b7) 2 = b2 := by
  simp only [extractByte, combineBytes]
  bv_decide

theorem combineBytes_extractByte_3 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    extractByte (combineBytes b0 b1 b2 b3 b4 b5 b6 b7) 3 = b3 := by
  simp only [extractByte, combineBytes]
  bv_decide

theorem combineBytes_extractByte_4 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    extractByte (combineBytes b0 b1 b2 b3 b4 b5 b6 b7) 4 = b4 := by
  simp only [extractByte, combineBytes]
  bv_decide

theorem combineBytes_extractByte_5 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    extractByte (combineBytes b0 b1 b2 b3 b4 b5 b6 b7) 5 = b5 := by
  simp only [extractByte, combineBytes]
  bv_decide

theorem combineBytes_extractByte_6 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    extractByte (combineBytes b0 b1 b2 b3 b4 b5 b6 b7) 6 = b6 := by
  simp only [extractByte, combineBytes]
  bv_decide

theorem combineBytes_extractByte_7 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    extractByte (combineBytes b0 b1 b2 b3 b4 b5 b6 b7) 7 = b7 := by
  simp only [extractByte, combineBytes]
  bv_decide

-- The converse: extracting then combining reconstructs the original value
-- This is the key theorem for the serialize->parse direction
theorem extractBytes_combineBytes (v : BitVec 64) :
    combineBytes (extractByte v 0) (extractByte v 1) (extractByte v 2) (extractByte v 3)
                 (extractByte v 4) (extractByte v 5) (extractByte v 6) (extractByte v 7) = v := by
  simp only [extractByte, combineBytes]
  bv_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- U64LE BOX (complete with proofs)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Helper: UInt8 ↔ BitVec 8 roundtrip
theorem uint8_IsLt (x : UInt8) : x.toNat < 256 := by
  unfold UInt8.toNat
  exact x.toBitVec.isLt

theorem bitvec8_IsLt (b : BitVec 8) : b.toNat < 256 := b.isLt

-- Key: BitVec.ofNat 8 (x.toNat) where x : UInt8 preserves the value
theorem ofNat8_uint8_toNat (x : UInt8) : 
    (BitVec.ofNat 8 x.toNat).toNat = x.toNat := by
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (uint8_IsLt x)

-- Key: extractByte then toUInt8 then back to BitVec = extractByte
theorem extractByte_uint8_roundtrip (v : BitVec 64) (i : Nat) (hi : i < 8) :
    BitVec.ofNat 8 ((extractByte v i hi).toNat.toUInt8.toNat) = extractByte v i hi := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hlt : (extractByte v i hi).toNat < 256 := bitvec8_IsLt _
  -- toUInt8.toNat of a value < 256 is identity
  have h1 : (extractByte v i hi).toNat.toUInt8.toNat = (extractByte v i hi).toNat := by
    unfold Nat.toUInt8 UInt8.ofNat UInt8.toNat
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [h1]
  exact Nat.mod_eq_of_lt hlt

-- Serialize then get byte i gives extractByte v i
theorem serializeU64le_getElem (v : BitVec 64) (i : Nat) (hi : i < 8) :
    (serializeU64le v)[i]'(by simp [serializeU64le_size]; exact hi) = 
    (extractByte v i hi).toNat.toUInt8 := by
  simp only [serializeU64le]
  -- The serialized bytes are [b0, b1, ..., b7].toByteArray
  -- We need to show that index i gives the i-th element
  match i with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | 3 => simp
  | 4 => simp
  | 5 => simp
  | 6 => simp
  | 7 => simp

-- Combined lemma: BitVec.ofNat 8 (serializeU64le v)[i].toNat = extractByte v i _
-- This allows simp to work instead of conv
-- We prove individual instances for each index to make simp work
@[simp] theorem serializeU64le_bitvec_0 (v : BitVec 64) (h : 0 < (serializeU64le v).size := by simp) :
    BitVec.ofNat 8 (serializeU64le v)[0].toNat = extractByte v 0 (by omega) := by
  rw [serializeU64le_getElem, extractByte_uint8_roundtrip]

@[simp] theorem serializeU64le_bitvec_1 (v : BitVec 64) (h : 1 < (serializeU64le v).size := by simp) :
    BitVec.ofNat 8 (serializeU64le v)[1].toNat = extractByte v 1 (by omega) := by
  rw [serializeU64le_getElem, extractByte_uint8_roundtrip]

@[simp] theorem serializeU64le_bitvec_2 (v : BitVec 64) (h : 2 < (serializeU64le v).size := by simp) :
    BitVec.ofNat 8 (serializeU64le v)[2].toNat = extractByte v 2 (by omega) := by
  rw [serializeU64le_getElem, extractByte_uint8_roundtrip]

@[simp] theorem serializeU64le_bitvec_3 (v : BitVec 64) (h : 3 < (serializeU64le v).size := by simp) :
    BitVec.ofNat 8 (serializeU64le v)[3].toNat = extractByte v 3 (by omega) := by
  rw [serializeU64le_getElem, extractByte_uint8_roundtrip]

@[simp] theorem serializeU64le_bitvec_4 (v : BitVec 64) (h : 4 < (serializeU64le v).size := by simp) :
    BitVec.ofNat 8 (serializeU64le v)[4].toNat = extractByte v 4 (by omega) := by
  rw [serializeU64le_getElem, extractByte_uint8_roundtrip]

@[simp] theorem serializeU64le_bitvec_5 (v : BitVec 64) (h : 5 < (serializeU64le v).size := by simp) :
    BitVec.ofNat 8 (serializeU64le v)[5].toNat = extractByte v 5 (by omega) := by
  rw [serializeU64le_getElem, extractByte_uint8_roundtrip]

@[simp] theorem serializeU64le_bitvec_6 (v : BitVec 64) (h : 6 < (serializeU64le v).size := by simp) :
    BitVec.ofNat 8 (serializeU64le v)[6].toNat = extractByte v 6 (by omega) := by
  rw [serializeU64le_getElem, extractByte_uint8_roundtrip]

@[simp] theorem serializeU64le_bitvec_7 (v : BitVec 64) (h : 7 < (serializeU64le v).size := by simp) :
    BitVec.ofNat 8 (serializeU64le v)[7].toNat = extractByte v 7 (by omega) := by
  rw [serializeU64le_getElem, extractByte_uint8_roundtrip]

-- The big theorem: parsing serialized bytes reconstructs the original value
theorem parseU64le_serializeU64le (v : BitVec 64) :
    parseU64le (serializeU64le v) = ParseResult.ok v ByteArray.empty := by
  simp only [parseU64le]
  have hsize : (serializeU64le v).size ≥ 8 := by simp [serializeU64le_size]
  simp only [hsize, ↓reduceDIte]
  -- Extract goes from 8 to 8, giving empty
  have hextract : (serializeU64le v).extract 8 (serializeU64le v).size = ByteArray.empty := by
    simp [serializeU64le_size]
  -- Now show the combined value equals v and rest is empty
  -- Goal: ParseResult.ok (combineBytes ...) (extract ...) = ParseResult.ok v empty
  -- Use congr to split into showing combineBytes ... = v and extract ... = empty
  -- hextract proves the second component, so we use simp with it first
  simp only [hextract]
  -- Now just need to show combineBytes ... = v
  congr 1
  simp only [serializeU64le_bitvec_0, serializeU64le_bitvec_1, serializeU64le_bitvec_2,
             serializeU64le_bitvec_3, serializeU64le_bitvec_4, serializeU64le_bitvec_5,
             serializeU64le_bitvec_6, serializeU64le_bitvec_7]
  exact extractBytes_combineBytes v

-- Consumption: parsing serialized bytes ++ extra leaves extra
theorem parseU64le_serializeU64le_append (v : BitVec 64) (extra : Bytes) :
    parseU64le (serializeU64le v ++ extra) = ParseResult.ok v extra := by
  simp only [parseU64le]
  have hsize : (serializeU64le v ++ extra).size ≥ 8 := by 
    simp [ByteArray.size_append, serializeU64le_size]
  simp only [hsize, ↓reduceDIte]
  -- Extract from position 8 gives extra
  have hextract : (serializeU64le v ++ extra).extract 8 (serializeU64le v ++ extra).size = extra := by
    have hi : 8 = (serializeU64le v).size := by simp [serializeU64le_size]
    have hj : (serializeU64le v ++ extra).size = (serializeU64le v).size + extra.size := by
      simp [ByteArray.size_append]
    rw [hj, ByteArray.extract_append_eq_right hi rfl]
  -- Use hextract to simplify the second component
  simp only [hextract]
  -- Now just need to show combineBytes ... = v
  congr 1
  -- Same as above but with append
  have h0 : (0 : Nat) < (serializeU64le v).size := by simp [serializeU64le_size]
  have h1 : (1 : Nat) < (serializeU64le v).size := by simp [serializeU64le_size]
  have h2 : (2 : Nat) < (serializeU64le v).size := by simp [serializeU64le_size]
  have h3 : (3 : Nat) < (serializeU64le v).size := by simp [serializeU64le_size]
  have h4 : (4 : Nat) < (serializeU64le v).size := by simp [serializeU64le_size]
  have h5 : (5 : Nat) < (serializeU64le v).size := by simp [serializeU64le_size]
  have h6 : (6 : Nat) < (serializeU64le v).size := by simp [serializeU64le_size]
  have h7 : (7 : Nat) < (serializeU64le v).size := by simp [serializeU64le_size]
  simp only [ByteArray.getElem_append_left h0, ByteArray.getElem_append_left h1,
             ByteArray.getElem_append_left h2, ByteArray.getElem_append_left h3,
             ByteArray.getElem_append_left h4, ByteArray.getElem_append_left h5,
             ByteArray.getElem_append_left h6, ByteArray.getElem_append_left h7]
  simp only [serializeU64le_bitvec_0, serializeU64le_bitvec_1, serializeU64le_bitvec_2,
             serializeU64le_bitvec_3, serializeU64le_bitvec_4, serializeU64le_bitvec_5,
             serializeU64le_bitvec_6, serializeU64le_bitvec_7]
  exact extractBytes_combineBytes v

/-- The verified u64le box -/
def u64leBitVec : Box (BitVec 64) where
  parse := parseU64le
  serialize := serializeU64le
  roundtrip := parseU64le_serializeU64le
  consumption := parseU64le_serializeU64le_append

-- ═══════════════════════════════════════════════════════════════════════════════
-- U32LE BOX (32-bit little-endian, for Protobuf fixed32)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Extract byte i from a 32-bit value (little-endian) -/
def extractByte32 (v : BitVec 32) (i : Nat) (_ : i < 4 := by omega) : BitVec 8 :=
  (v >>> (i * 8)).setWidth 8

/-- Combine 4 bytes into a 32-bit value (little-endian) -/
def combineBytes32 (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  b0.setWidth 32 |||
  (b1.setWidth 32 <<< 8) |||
  (b2.setWidth 32 <<< 16) |||
  (b3.setWidth 32 <<< 24)

/-- Serialize a 32-bit value to 4 bytes -/
def serializeU32le (v : BitVec 32) : Bytes :=
  let b0 : UInt8 := (extractByte32 v 0).toNat.toUInt8
  let b1 : UInt8 := (extractByte32 v 1).toNat.toUInt8
  let b2 : UInt8 := (extractByte32 v 2).toNat.toUInt8
  let b3 : UInt8 := (extractByte32 v 3).toNat.toUInt8
  [b0, b1, b2, b3].toByteArray

/-- Parse 4 bytes as a 32-bit value -/
def parseU32le (bs : Bytes) : ParseResult (BitVec 32) :=
  if h : bs.size ≥ 4 then
    let b0 := BitVec.ofNat 8 bs[0].toNat
    let b1 := BitVec.ofNat 8 bs[1].toNat
    let b2 := BitVec.ofNat 8 bs[2].toNat
    let b3 := BitVec.ofNat 8 bs[3].toNat
    .ok (combineBytes32 b0 b1 b2 b3) (bs.extract 4 bs.size)
  else .fail

@[simp] theorem serializeU32le_size (v : BitVec 32) : (serializeU32le v).size = 4 := by
  simp [serializeU32le, List.size_toByteArray]

-- Byte extraction lemmas (bv_decide)
theorem combineBytes32_extractByte_0 (b0 b1 b2 b3 : BitVec 8) :
    extractByte32 (combineBytes32 b0 b1 b2 b3) 0 = b0 := by
  simp only [extractByte32, combineBytes32]
  bv_decide

theorem combineBytes32_extractByte_1 (b0 b1 b2 b3 : BitVec 8) :
    extractByte32 (combineBytes32 b0 b1 b2 b3) 1 = b1 := by
  simp only [extractByte32, combineBytes32]
  bv_decide

theorem combineBytes32_extractByte_2 (b0 b1 b2 b3 : BitVec 8) :
    extractByte32 (combineBytes32 b0 b1 b2 b3) 2 = b2 := by
  simp only [extractByte32, combineBytes32]
  bv_decide

theorem combineBytes32_extractByte_3 (b0 b1 b2 b3 : BitVec 8) :
    extractByte32 (combineBytes32 b0 b1 b2 b3) 3 = b3 := by
  simp only [extractByte32, combineBytes32]
  bv_decide

-- The converse: extracting all bytes and combining gives back original
theorem extractBytes32_combineBytes (v : BitVec 32) :
    combineBytes32 (extractByte32 v 0) (extractByte32 v 1) 
                   (extractByte32 v 2) (extractByte32 v 3) = v := by
  simp only [extractByte32, combineBytes32]
  bv_decide

-- UInt8 roundtrip for 32-bit
theorem extractByte32_uint8_roundtrip (v : BitVec 32) (i : Nat) (hi : i < 4) :
    BitVec.ofNat 8 ((extractByte32 v i hi).toNat.toUInt8.toNat) = extractByte32 v i hi := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hlt : (extractByte32 v i hi).toNat < 256 := bitvec8_IsLt _
  have h1 : (extractByte32 v i hi).toNat.toUInt8.toNat = (extractByte32 v i hi).toNat := by
    unfold Nat.toUInt8 UInt8.ofNat UInt8.toNat
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [h1]
  exact Nat.mod_eq_of_lt hlt

theorem serializeU32le_getElem (v : BitVec 32) (i : Nat) (hi : i < 4) :
    (serializeU32le v)[i]'(by simp [serializeU32le_size]; exact hi) = 
    (extractByte32 v i hi).toNat.toUInt8 := by
  simp only [serializeU32le]
  match i with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | 3 => simp

-- Combined simp lemmas for the proof
@[simp] theorem serializeU32le_bitvec_0 (v : BitVec 32) (h : 0 < (serializeU32le v).size := by simp) :
    BitVec.ofNat 8 (serializeU32le v)[0].toNat = extractByte32 v 0 (by omega) := by
  rw [serializeU32le_getElem, extractByte32_uint8_roundtrip]

@[simp] theorem serializeU32le_bitvec_1 (v : BitVec 32) (h : 1 < (serializeU32le v).size := by simp) :
    BitVec.ofNat 8 (serializeU32le v)[1].toNat = extractByte32 v 1 (by omega) := by
  rw [serializeU32le_getElem, extractByte32_uint8_roundtrip]

@[simp] theorem serializeU32le_bitvec_2 (v : BitVec 32) (h : 2 < (serializeU32le v).size := by simp) :
    BitVec.ofNat 8 (serializeU32le v)[2].toNat = extractByte32 v 2 (by omega) := by
  rw [serializeU32le_getElem, extractByte32_uint8_roundtrip]

@[simp] theorem serializeU32le_bitvec_3 (v : BitVec 32) (h : 3 < (serializeU32le v).size := by simp) :
    BitVec.ofNat 8 (serializeU32le v)[3].toNat = extractByte32 v 3 (by omega) := by
  rw [serializeU32le_getElem, extractByte32_uint8_roundtrip]

-- Main roundtrip theorem
theorem parseU32le_serializeU32le (v : BitVec 32) :
    parseU32le (serializeU32le v) = ParseResult.ok v ByteArray.empty := by
  simp only [parseU32le]
  have hsize : (serializeU32le v).size ≥ 4 := by simp [serializeU32le_size]
  simp only [hsize, ↓reduceDIte]
  have hextract : (serializeU32le v).extract 4 (serializeU32le v).size = ByteArray.empty := by
    simp [serializeU32le_size]
  simp only [hextract]
  congr 1
  simp only [serializeU32le_bitvec_0, serializeU32le_bitvec_1, 
             serializeU32le_bitvec_2, serializeU32le_bitvec_3]
  exact extractBytes32_combineBytes v

-- Consumption theorem
theorem parseU32le_serializeU32le_append (v : BitVec 32) (extra : Bytes) :
    parseU32le (serializeU32le v ++ extra) = ParseResult.ok v extra := by
  simp only [parseU32le]
  have hsize : (serializeU32le v ++ extra).size ≥ 4 := by 
    simp [ByteArray.size_append, serializeU32le_size]
  simp only [hsize, ↓reduceDIte]
  have hextract : (serializeU32le v ++ extra).extract 4 (serializeU32le v ++ extra).size = extra := by
    have hi : 4 = (serializeU32le v).size := by simp [serializeU32le_size]
    have hj : (serializeU32le v ++ extra).size = (serializeU32le v).size + extra.size := by
      simp [ByteArray.size_append]
    rw [hj, ByteArray.extract_append_eq_right hi rfl]
  simp only [hextract]
  congr 1
  have h0 : (0 : Nat) < (serializeU32le v).size := by simp [serializeU32le_size]
  have h1 : (1 : Nat) < (serializeU32le v).size := by simp [serializeU32le_size]
  have h2 : (2 : Nat) < (serializeU32le v).size := by simp [serializeU32le_size]
  have h3 : (3 : Nat) < (serializeU32le v).size := by simp [serializeU32le_size]
  simp only [ByteArray.getElem_append_left h0, ByteArray.getElem_append_left h1,
             ByteArray.getElem_append_left h2, ByteArray.getElem_append_left h3]
  simp only [serializeU32le_bitvec_0, serializeU32le_bitvec_1,
             serializeU32le_bitvec_2, serializeU32le_bitvec_3]
  exact extractBytes32_combineBytes v

/-- The verified u32le box -/
def u32leBitVec : Box (BitVec 32) where
  parse := parseU32le
  serialize := serializeU32le
  roundtrip := parseU32le_serializeU32le
  consumption := parseU32le_serializeU32le_append

-- ═══════════════════════════════════════════════════════════════════════════════
-- DERIVED BOXES (built from primitives)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Two bytes (u8, u8) -/
def u8pair : Box (UInt8 × UInt8) := seq u8 u8

/-- Three bytes -/
def u8triple : Box ((UInt8 × UInt8) × UInt8) := seq u8pair u8

/-- Four bytes -/
def u8quad : Box (((UInt8 × UInt8) × UInt8) × UInt8) := seq u8triple u8

-- ═══════════════════════════════════════════════════════════════════════════════
-- EXAMPLE: Using isoBox to create a wrapped type
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A wrapper type for demonstration -/
structure WrappedByte where
  val : UInt8
  deriving DecidableEq

/-- Box for WrappedByte -/
def wrappedByte : Box WrappedByte := 
  isoBox u8 
    WrappedByte.mk 
    WrappedByte.val
    (fun _ => rfl)
    (fun ⟨_⟩ => rfl)

-- ═══════════════════════════════════════════════════════════════════════════════
-- STATISTICS
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Verification Status

### Fully Verified Boxes (0 sorry):

| Box/Combinator | Roundtrip | Consumption | Status |
|----------------|-----------|-------------|--------|
| unit           | ✓ proven  | ✓ proven    | DONE   |
| u8             | ✓ proven  | ✓ proven    | DONE   |
| u32leBitVec    | ✓ proven  | ✓ proven    | DONE   |
| u64leBitVec    | ✓ proven  | ✓ proven    | DONE   |
| seq            | ✓ proven  | ✓ proven    | DONE   |
| isoBox         | ✓ proven  | ✓ proven    | DONE   |

### BitVec Lemmas (bv_decide, 0 sorry):

| Lemma | What's Proven |
|-------|---------------|
| combineBytes_extractByte_0..7 | extractByte(combine(b0..b7), i) = bi |
| combineBytes32_extractByte_0..3 | extractByte32(combine32(b0..b3), i) = bi |
| extractBytes_combineBytes | combine(extractByte(v, 0..7)) = v |
| extractBytes32_combineBytes | combine32(extractByte32(v, 0..3)) = v |
| parseU64le_serializeU64le | parse(serialize(v)) = ok v empty |
| parseU32le_serializeU32le | parse(serialize(v)) = ok v empty |

### Derived (compositionally verified):

| Box | Built From |
|-----|------------|
| u8pair | seq u8 u8 |
| u8triple | seq u8pair u8 |  
| u8quad | seq u8triple u8 |
| wrappedByte | isoBox u8 |
| u64le (UInt64) | isoBox u64leBitVec (via Basic.lean) |
| u32le (UInt32) | isoBox u32leBitVec (via Basic.lean) |
| bool64 | isoBox u64leBitVec (via Basic.lean) |

**Total: 6 primitive boxes, 50+ theorems, 0 sorry in Proofs.lean**
**Compositionally: infinite verified boxes constructible**
-/

end Foundry.Cornell.Proofs
