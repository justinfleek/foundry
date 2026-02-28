/-
  Cornell.Extract - Test Property Generation
  
  Generates test vectors and property specifications from Box definitions.
  The C++ implementation is tested against these Lean-generated properties.
  
  ## Architecture
  
  1. Lean4 (Cornell) = Specification with proofs
  2. Test vectors = Concrete examples generated from spec
  3. Properties = QuickCheck-style properties for fuzzing
  4. C++ = Fast implementation validated against properties
  
  ## Generated Artifacts
  
  - JSON test vectors: known (value, bytes) pairs
  - Property specs: invariants the C++ must satisfy
  - Golden tests: round-trip on captured protocol data
-/

import Foundry.Cornell.Basic
import Foundry.Cornell.Nix

namespace Cornell.Extract

open Foundry.Cornell Foundry.Cornell.Proofs

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTOR GENERATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A test vector: value serialized to bytes -/
structure TestVector (α : Type) where
  name : String
  value : α
  bytes : Bytes
  deriving Repr

/-- Generate a test vector from a box and value -/
def mkTestVector [Repr α] (name : String) (box : Box α) (value : α) : TestVector α :=
  { name := name
  , value := value
  , bytes := box.serialize value }

/-- Verify a test vector (this is proven by construction, but useful for sanity checks) -/
def verifyVector (box : Box α) (tv : TestVector α) : Bool :=
  match box.parse tv.bytes with
  | .ok v rest => rest.size == 0  -- Could also check v == tv.value if DecidableEq
  | .fail => false

-- ═══════════════════════════════════════════════════════════════════════════════
-- PRIMITIVE TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Test vectors for u8 -/
def u8Vectors : List (TestVector UInt8) :=
  [ mkTestVector "u8_zero" u8 0
  , mkTestVector "u8_one" u8 1
  , mkTestVector "u8_max" u8 255
  , mkTestVector "u8_0x42" u8 0x42
  ]

/-- Test vectors for u64le -/
def u64leVectors : List (TestVector UInt64) :=
  [ mkTestVector "u64le_zero" u64le 0
  , mkTestVector "u64le_one" u64le 1
  , mkTestVector "u64le_max" u64le 0xFFFFFFFFFFFFFFFF
  , mkTestVector "u64le_magic1" u64le 0x6e697863  -- WORKER_MAGIC_1
  , mkTestVector "u64le_magic2" u64le 0x6478696f  -- WORKER_MAGIC_2
  , mkTestVector "u64le_protocol" u64le 0x126     -- Version 1.38
  ]

/-- Test vectors for bool64 -/
def bool64Vectors : List (TestVector Bool) :=
  [ mkTestVector "bool64_false" bool64 false
  , mkTestVector "bool64_true" bool64 true
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- JSON SERIALIZATION (for export)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Convert bytes to hex string -/
def bytesToHex (bs : Bytes) : String :=
  let hexDigit (n : UInt8) : Char :=
    if n < 10 then Char.ofNat (n.toNat + '0'.toNat)
    else Char.ofNat (n.toNat - 10 + 'a'.toNat)
  bs.toList.foldl (fun acc b =>
    acc ++ String.singleton (hexDigit (b / 16)) ++ String.singleton (hexDigit (b % 16))
  ) ""

/-- Convert test vector to JSON-like string -/
def testVectorToJson [Repr α] (tv : TestVector α) : String :=
  s!"\{\"name\": \"{tv.name}\", \"bytes\": \"{bytesToHex tv.bytes}\", \"size\": {tv.bytes.size}}"

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROPERTY SPECIFICATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Property: roundtrip succeeds -/
def propRoundtrip (box : Box α) (a : α) : Bool :=
  match box.parse (box.serialize a) with
  | .ok _ rest => rest.size == 0
  | .fail => false

/-- Property: consumption leaves extra bytes intact -/
def propConsumption (box : Box α) (a : α) (extra : Bytes) : Bool :=
  match box.parse (box.serialize a ++ extra) with
  | .ok _ rest => rest == extra
  | .fail => false

/-- Property: parsing is deterministic -/
def propDeterministic (box : Box α) (bs : Bytes) [DecidableEq α] : Bool :=
  match box.parse bs, box.parse bs with
  | .ok a1 r1, .ok a2 r2 => a1 == a2 && r1 == r2
  | .fail, .fail => true
  | _, _ => false

-- ═══════════════════════════════════════════════════════════════════════════════
-- C++ CODE GENERATION TEMPLATES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Generate C++ test case for a test vector -/
def genCppTestCase (tv : TestVector α) [Repr α] : String :=
  let hexBytes := bytesToHex tv.bytes
  s!"TEST_CASE(\"{tv.name}\") \{
  const auto bytes = hex_to_bytes(\"{hexBytes}\");
  auto result = parse_{tv.name.takeWhile (· != '_')}(bytes);
  REQUIRE(result.has_value());
  REQUIRE(result->remaining.empty());
}"

/-- Generate C++ property test template -/
def genCppPropertyTest (typeName : String) : String :=
  s!"PROPERTY_TEST(\"{typeName}_roundtrip\") \{
  // Generated from Cornell.{typeName} box
  auto value = GENERATE(arbitrary<{typeName}>());
  auto serialized = serialize_{typeName.toLower}(value);
  auto parsed = parse_{typeName.toLower}(serialized);
  REQUIRE(parsed.has_value());
  REQUIRE(parsed->value == value);
  REQUIRE(parsed->remaining.empty());
}"

-- ═══════════════════════════════════════════════════════════════════════════════
-- EXPORT ALL VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Generate all test vectors as JSON array -/
def allTestVectorsJson : String :=
  let u8s : List String := u8Vectors.map testVectorToJson
  let u64s : List String := u64leVectors.map testVectorToJson
  let bools : List String := bool64Vectors.map testVectorToJson
  let all : List String := u8s ++ u64s ++ bools
  "[\n  " ++ String.intercalate ",\n  " all ++ "\n]"

-- #eval IO.println allTestVectorsJson  -- Disabled: depends on sorry

-- ═══════════════════════════════════════════════════════════════════════════════
-- NIX PROTOCOL TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

open Foundry.Cornell.Nix in
/-- Test vectors for Nix protocol primitives -/
def nixProtocolVectors : List String :=
  [ s!"worker_magic_1: {bytesToHex (u64le.serialize WORKER_MAGIC_1)}"
  , s!"worker_magic_2: {bytesToHex (u64le.serialize WORKER_MAGIC_2)}"
  , s!"stderr_next: {bytesToHex (u64le.serialize STDERR_NEXT)}"
  , s!"stderr_last: {bytesToHex (u64le.serialize STDERR_LAST)}"
  , s!"stderr_error: {bytesToHex (u64le.serialize STDERR_ERROR)}"
  , s!"protocol_1_38: {bytesToHex (u64le.serialize 0x126)}"
  ]

-- #eval nixProtocolVectors.forM IO.println  -- Disabled: depends on sorry

end Cornell.Extract

-- Main function for executable (outside namespace)
def main : IO Unit := do
  IO.println "Cornell Test Vector Generator"
  IO.println "=============================="
  IO.println ""
  IO.println "Test Vectors JSON:"
  IO.println Cornell.Extract.allTestVectorsJson
  IO.println ""
  IO.println "Nix Protocol Vectors:"
  Cornell.Extract.nixProtocolVectors.forM IO.println
