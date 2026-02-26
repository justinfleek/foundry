/-
  Foundry.Cornell.Protobuf - Verified Protobuf Wire Format
  
  Protobuf wire format primitives:
  - Varint: variable-length integer encoding
  - Fixed32/Fixed64: little-endian fixed-width
  - Length-delimited: length prefix + bytes
  - Tag: field_number << 3 | wire_type
  
  Wire types:
  - 0: Varint (int32, int64, uint32, uint64, sint32, sint64, bool, enum)
  - 1: 64-bit (fixed64, sfixed64, double)
  - 2: Length-delimited (string, bytes, embedded messages, packed repeated)
  - 5: 32-bit (fixed32, sfixed32, float)
  
  Reference: https://protobuf.dev/programming-guides/encoding/
-/

import Foundry.Foundry.Cornell.Basic
import Foundry.Foundry.Cornell.Proofs

namespace Foundry.Cornell.Protobuf

open Cornell Foundry.Cornell.Proofs

-- ═══════════════════════════════════════════════════════════════════════════════
-- VARINT ENCODING
-- Variable-length integer, 7 bits per byte, MSB = continuation
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Encode a natural number as varint bytes -/
def encodeVarint (n : Nat) : Bytes :=
  if n < 128 then
    ⟨#[n.toUInt8]⟩
  else
    let byte := (n % 128 + 128).toUInt8  -- Set continuation bit
    let rest := encodeVarint (n / 128)
    ⟨#[byte]⟩ ++ rest
termination_by n
decreasing_by
  simp_wf
  omega

/-- Decode varint from bytes -/
def decodeVarint (bs : Bytes) : ParseResult Nat :=
  go bs 0 0
where
  go (bs : Bytes) (acc : Nat) (shift : Nat) : ParseResult Nat :=
    if bs.size > 0 then
      let byte := bs.data[0]!
      let value := (byte.toNat &&& 0x7F) <<< shift
      let acc' := acc + value
      if byte < 128 then
        .ok acc' (bs.extract 1 bs.size)
      else if shift >= 63 then
        .fail  -- Overflow protection
      else
        go (bs.extract 1 bs.size) acc' (shift + 7)
    else
      .fail
  termination_by bs.size

/-- Varint box (partial - needs termination proof) -/
-- Note: Full proof requires showing decodeVarint ∘ encodeVarint = id
-- This is true but requires induction on the varint structure

-- ═══════════════════════════════════════════════════════════════════════════════
-- WIRE TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

inductive WireType where
  | varint          -- 0
  | fixed64         -- 1
  | lengthDelimited -- 2
  | startGroup      -- 3 (deprecated)
  | endGroup        -- 4 (deprecated)
  | fixed32         -- 5
  deriving Repr, DecidableEq

def WireType.toNat : WireType → Nat
  | .varint => 0
  | .fixed64 => 1
  | .lengthDelimited => 2
  | .startGroup => 3
  | .endGroup => 4
  | .fixed32 => 5

def WireType.fromNat : Nat → Option WireType
  | 0 => some .varint
  | 1 => some .fixed64
  | 2 => some .lengthDelimited
  | 3 => some .startGroup
  | 4 => some .endGroup
  | 5 => some .fixed32
  | _ => none

-- ═══════════════════════════════════════════════════════════════════════════════
-- FIELD TAG
-- Tag = (field_number << 3) | wire_type
-- ═══════════════════════════════════════════════════════════════════════════════

structure FieldTag where
  fieldNumber : Nat
  wireType : WireType
  deriving Repr

def encodeTag (tag : FieldTag) : Bytes :=
  encodeVarint ((tag.fieldNumber <<< 3) + tag.wireType.toNat)

def decodeTag (bs : Bytes) : ParseResult FieldTag :=
  match decodeVarint bs with
  | .ok n rest =>
    let wireTypeNum := n &&& 0x7
    let fieldNumber := n >>> 3
    match WireType.fromNat wireTypeNum with
    | some wt => .ok ⟨fieldNumber, wt⟩ rest
    | none => .fail
  | .fail => .fail

-- ═══════════════════════════════════════════════════════════════════════════════
-- FIXED-WIDTH TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- 32-bit little-endian (wire type 5) - uses verified u32leBitVec via isoBox -/
def u32le : Box UInt32 := 
  isoBox u32leBitVec 
    UInt32.ofBitVec 
    UInt32.toBitVec
    (fun _ => rfl)  -- ofBitVec ∘ toBitVec = id
    (fun _ => rfl)  -- toBitVec ∘ ofBitVec = id

def fixed32 : Box UInt32 := u32le

/-- 64-bit little-endian (wire type 1) - uses verified u64leBitVec via isoBox -/
def u64leVerified : Box UInt64 := 
  isoBox u64leBitVec 
    UInt64.ofBitVec 
    UInt64.toBitVec
    (fun _ => rfl)
    (fun _ => rfl)

def fixed64 : Box UInt64 := u64leVerified

-- ═══════════════════════════════════════════════════════════════════════════════
-- LENGTH-DELIMITED
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Length-delimited bytes: varint length + raw bytes -/
structure LengthDelimited where
  data : Bytes
  deriving Repr

def encodeLengthDelimited (ld : LengthDelimited) : Bytes :=
  encodeVarint ld.data.size ++ ld.data

def decodeLengthDelimited (bs : Bytes) : ParseResult LengthDelimited :=
  match decodeVarint bs with
  | .ok len rest =>
    if rest.size >= len then
      .ok ⟨rest.extract 0 len⟩ (rest.extract len rest.size)
    else
      .fail
  | .fail => .fail

-- ═══════════════════════════════════════════════════════════════════════════════
-- ZIGZAG ENCODING (for sint32, sint64)
-- Maps negative numbers to positive: 0 → 0, -1 → 1, 1 → 2, -2 → 3, ...
-- ═══════════════════════════════════════════════════════════════════════════════

def zigzagEncode (n : Int) : Nat :=
  if n >= 0 then
    (n.toNat <<< 1)
  else
    (((-n).toNat <<< 1) - 1)

def zigzagDecode (n : Nat) : Int :=
  if n % 2 == 0 then
    (n >>> 1 : Nat)
  else
    -((n + 1) >>> 1 : Nat)

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROTOBUF STRING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- UTF-8 string (length-delimited) -/
structure ProtoString where
  value : String
  deriving Repr

def encodeProtoString (s : ProtoString) : Bytes :=
  let utf8 := s.value.toUTF8
  encodeVarint utf8.size ++ utf8

def decodeProtoString (bs : Bytes) : ParseResult ProtoString :=
  match decodeLengthDelimited bs with
  | .ok ld rest =>
    -- Attempt UTF-8 decode
    match String.fromUTF8? ld.data with
    | some s => .ok ⟨s⟩ rest
    | none => .fail
  | .fail => .fail

-- ═══════════════════════════════════════════════════════════════════════════════
-- GRPC FRAMING
-- 1 byte: compressed flag (0 or 1)
-- 4 bytes: message length (big-endian!)
-- N bytes: message
-- ═══════════════════════════════════════════════════════════════════════════════

structure GrpcFrame where
  compressed : Bool
  message : Bytes
  deriving Repr

def encodeGrpcFrame (frame : GrpcFrame) : Bytes :=
  let flag : UInt8 := if frame.compressed then 1 else 0
  let len := frame.message.size.toUInt32
  -- Note: gRPC uses BIG-endian for length!
  let b0 := ((len >>> 24) &&& 0xFF).toUInt8
  let b1 := ((len >>> 16) &&& 0xFF).toUInt8
  let b2 := ((len >>> 8) &&& 0xFF).toUInt8
  let b3 := (len &&& 0xFF).toUInt8
  let lenBytes : Bytes := ⟨#[b0, b1, b2, b3]⟩
  ⟨#[flag]⟩ ++ lenBytes ++ frame.message

def decodeGrpcFrame (bs : Bytes) : ParseResult GrpcFrame :=
  if bs.size >= 5 then
    let compressed := bs.data[0]! != 0
    let b1 := bs.data[1]!
    let b2 := bs.data[2]!
    let b3 := bs.data[3]!
    let b4 := bs.data[4]!
    let len := (b1.toNat <<< 24) + (b2.toNat <<< 16) + (b3.toNat <<< 8) + b4.toNat
    let rest := bs.extract 5 bs.size
    if rest.size >= len then
      .ok ⟨compressed, rest.extract 0 len⟩ (rest.extract len rest.size)
    else
      .fail
  else
    .fail

-- ═══════════════════════════════════════════════════════════════════════════════
-- GRPC CALL STATE MACHINE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- gRPC call types -/
inductive CallType where
  | unary           -- Single request, single response
  | clientStreaming -- Stream of requests, single response
  | serverStreaming -- Single request, stream of responses
  | bidiStreaming   -- Stream of requests, stream of responses
  deriving Repr, DecidableEq

/-- Client-side gRPC call state -/
inductive GrpcClientState where
  | idle
  | sendingHeaders
  | sendingMessage (remaining : Nat)  -- For streaming
  | awaitingHeaders
  | receivingMessage (remaining : Nat)
  | awaitingTrailers
  | complete (status : Nat) (message : Option String)
  | failed (reason : String)
  deriving Repr

/-- Client events -/
inductive GrpcClientEvent where
  | start (callType : CallType) (method : String)
  | headersSent
  | messageSent
  | headersReceived (status : Option Nat)
  | messageReceived (data : Bytes)
  | trailersReceived (status : Nat) (message : Option String)
  | error (reason : String)
  deriving Repr

/-- Client actions -/
inductive GrpcClientAction where
  | sendHeaders (method : String) (metadata : List (String × String))
  | sendMessage (data : Bytes) (endStream : Bool)
  | sendTrailers
  | receiveHeaders
  | receiveMessage
  | receiveTrailers
  | complete (status : Nat)
  | fail (reason : String)
  deriving Repr

-- Note: Full state machine implementation would follow the same pattern
-- as the handshake state machine in StateMachine.lean

-- ═══════════════════════════════════════════════════════════════════════════════
-- DIGEST TYPE (for REAPI)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Content digest (hash + size) -/
structure Digest where
  hash : String      -- Hex-encoded hash
  sizeBytes : Nat
  deriving Repr, DecidableEq

/-- Encode Digest as protobuf (fields 1 and 2) -/
def encodeDigest (d : Digest) : Bytes :=
  -- Field 1: string hash (wire type 2)
  let hashTag := encodeTag ⟨1, .lengthDelimited⟩
  let hashValue := encodeProtoString ⟨d.hash⟩
  -- Field 2: int64 size_bytes (wire type 0)
  let sizeTag := encodeTag ⟨2, .varint⟩
  let sizeValue := encodeVarint d.sizeBytes
  hashTag ++ hashValue ++ sizeTag ++ sizeValue

-- ═══════════════════════════════════════════════════════════════════════════════
-- REAPI MESSAGES (simplified)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- FindMissingBlobsRequest (simplified) -/
structure FindMissingBlobsRequest where
  instanceName : String
  blobDigests : List Digest
  deriving Repr

/-- FindMissingBlobsResponse (simplified) -/
structure FindMissingBlobsResponse where
  missingBlobDigests : List Digest
  deriving Repr

-- Full encoding would use repeated fields (same tag, multiple values)

-- ═══════════════════════════════════════════════════════════════════════════════
-- RESET-ON-AMBIGUITY SEMANTICS
-- Following the pattern established in Foundry.Cornell.Sigil, Foundry.Cornell.Zmtp, Foundry.Cornell.Nix
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Reset-on-Ambiguity for Protobuf

Protobuf wire format has several ambiguity triggers:

1. **Varint overflow** - more than 10 continuation bytes (64-bit max)
2. **Deprecated wire types** - groups (wire types 3, 4) are deprecated
3. **Invalid wire type** - wire type 6 or 7 don't exist
4. **Length overflow** - length-delimited field exceeds remaining bytes
5. **Invalid UTF-8** - string field contains invalid UTF-8
6. **Zero field number** - field numbers must be >= 1
7. **gRPC compression flag invalid** - must be 0 or 1

When any of these occur, we must reset parsing state.
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- AMBIGUITY REASONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Reasons for ambiguity in Protobuf parsing -/
inductive AmbiguityReason where
  /-- Varint has more than 10 continuation bytes (overflow) -/
  | varintOverflow : AmbiguityReason
  /-- Deprecated wire type (startGroup = 3, endGroup = 4) -/
  | deprecatedWireType : Nat → AmbiguityReason
  /-- Invalid wire type (6 or 7) -/
  | invalidWireType : Nat → AmbiguityReason
  /-- Field number is zero (must be >= 1) -/
  | zeroFieldNumber : AmbiguityReason
  /-- Length-delimited field length exceeds available bytes -/
  | lengthOverflow : Nat → Nat → AmbiguityReason  -- claimed, available
  /-- String contains invalid UTF-8 -/
  | invalidUtf8 : AmbiguityReason
  /-- gRPC frame has invalid compression flag (not 0 or 1) -/
  | invalidCompressionFlag : UInt8 → AmbiguityReason
  /-- gRPC frame length exceeds maximum (4MB default) -/
  | grpcFrameTooLarge : Nat → AmbiguityReason
  /-- Nested message depth exceeds limit (prevent stack overflow) -/
  | nestingTooDeep : Nat → AmbiguityReason
  deriving Repr, DecidableEq

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRICT PARSE RESULT
-- ═══════════════════════════════════════════════════════════════════════════════

/--
Strict parse result with three outcomes.

- `ok`: unambiguous success
- `incomplete`: need more bytes (streaming)
- `ambiguous`: protocol violation, must reset
-/
inductive StrictParseResult (α : Type) where
  | ok : α → Bytes → StrictParseResult α
  | incomplete : Nat → StrictParseResult α  -- how many more bytes needed
  | ambiguous : AmbiguityReason → StrictParseResult α
  deriving Repr

namespace StrictParseResult

def map (f : α → β) : StrictParseResult α → StrictParseResult β
  | ok a rest => ok (f a) rest
  | incomplete n => incomplete n
  | ambiguous r => ambiguous r

def bind (r : StrictParseResult α) (f : α → Bytes → StrictParseResult β) : StrictParseResult β :=
  match r with
  | ok a rest => f a rest
  | incomplete n => incomplete n
  | ambiguous r => ambiguous r

def isOk : StrictParseResult α → Bool
  | ok _ _ => true
  | _ => false

def isIncomplete : StrictParseResult α → Bool
  | incomplete _ => true
  | _ => false

def isAmbiguous : StrictParseResult α → Bool
  | ambiguous _ => true
  | _ => false

-- Lemmas
@[simp] theorem map_ok (f : α → β) (a : α) (rest : Bytes) :
    map f (ok a rest) = ok (f a) rest := rfl

@[simp] theorem map_incomplete (f : α → β) (n : Nat) :
    map f (incomplete n : StrictParseResult α) = incomplete n := rfl

@[simp] theorem map_ambiguous (f : α → β) (r : AmbiguityReason) :
    map f (ambiguous r : StrictParseResult α) = ambiguous r := rfl

@[simp] theorem bind_ok (a : α) (rest : Bytes) (f : α → Bytes → StrictParseResult β) :
    bind (ok a rest) f = f a rest := rfl

@[simp] theorem bind_incomplete (n : Nat) (f : α → Bytes → StrictParseResult β) :
    bind (incomplete n : StrictParseResult α) f = incomplete n := rfl

@[simp] theorem bind_ambiguous (r : AmbiguityReason) (f : α → Bytes → StrictParseResult β) :
    bind (ambiguous r : StrictParseResult α) f = ambiguous r := rfl

end StrictParseResult

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRICT VARINT PARSING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Maximum varint bytes (10 for 64-bit values) -/
def maxVarintBytes : Nat := 10

/-- 
Decode varint with strict overflow detection.

Returns:
- `ok (value, bytesConsumed)` on success
- `incomplete n` if need more bytes
- `ambiguous varintOverflow` if too many continuation bytes
-/
def decodeVarintStrict (bs : Bytes) : StrictParseResult (Nat × Nat) :=
  go bs 0 0 0
where
  go (bs : Bytes) (offset : Nat) (acc : Nat) (shift : Nat) : StrictParseResult (Nat × Nat) :=
    if offset >= bs.size then
      .incomplete 1
    else if offset >= maxVarintBytes then
      .ambiguous .varintOverflow
    else
      let byte := bs.data[offset]!
      let value := (byte.toNat &&& 0x7F) <<< shift
      let acc' := acc + value
      if byte < 128 then
        -- End of varint
        .ok (acc', offset + 1) (bs.extract (offset + 1) bs.size)
      else
        go bs (offset + 1) acc' (shift + 7)
  termination_by maxVarintBytes - offset

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRICT TAG PARSING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Check if wire type is valid (not deprecated or unknown) -/
def isValidWireType (wt : Nat) : Bool :=
  wt == 0 || wt == 1 || wt == 2 || wt == 5

/-- Check if wire type is deprecated (groups) -/
def isDeprecatedWireType (wt : Nat) : Bool :=
  wt == 3 || wt == 4

/--
Decode field tag with strict validation.

Detects:
- Varint overflow
- Zero field number
- Deprecated wire types (groups)
- Invalid wire types (6, 7)
-/
def decodeTagStrict (bs : Bytes) : StrictParseResult FieldTag :=
  match decodeVarintStrict bs with
  | .ok (n, _) rest =>
    let wireTypeNum := n &&& 0x7
    let fieldNumber := n >>> 3
    -- Check field number
    if fieldNumber == 0 then
      .ambiguous .zeroFieldNumber
    -- Check wire type
    else if isDeprecatedWireType wireTypeNum then
      .ambiguous (.deprecatedWireType wireTypeNum)
    else if !isValidWireType wireTypeNum then
      .ambiguous (.invalidWireType wireTypeNum)
    else
      match WireType.fromNat wireTypeNum with
      | some wt => .ok ⟨fieldNumber, wt⟩ rest
      | none => .ambiguous (.invalidWireType wireTypeNum)
  | .incomplete n => .incomplete n
  | .ambiguous r => .ambiguous r

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRICT LENGTH-DELIMITED PARSING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Maximum length-delimited size (256 MB) -/
def maxLengthDelimitedSize : Nat := 256 * 1024 * 1024

/--
Decode length-delimited field with strict validation.

Detects:
- Varint overflow in length
- Length exceeds remaining bytes
- Length exceeds maximum
-/
def decodeLengthDelimitedStrict (bs : Bytes) : StrictParseResult LengthDelimited :=
  match decodeVarintStrict bs with
  | .ok (len, _) rest =>
    if len > maxLengthDelimitedSize then
      .ambiguous (.lengthOverflow len maxLengthDelimitedSize)
    else if rest.size < len then
      .incomplete (len - rest.size)
    else
      .ok ⟨rest.extract 0 len⟩ (rest.extract len rest.size)
  | .incomplete n => .incomplete n
  | .ambiguous r => .ambiguous r

/--
Decode string with UTF-8 validation.
-/
def decodeProtoStringStrict (bs : Bytes) : StrictParseResult ProtoString :=
  match decodeLengthDelimitedStrict bs with
  | .ok ld rest =>
    match String.fromUTF8? ld.data with
    | some s => .ok ⟨s⟩ rest
    | none => .ambiguous .invalidUtf8
  | .incomplete n => .incomplete n
  | .ambiguous r => .ambiguous r

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRICT GRPC FRAMING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Maximum gRPC frame size (4 MB default) -/
def maxGrpcFrameSize : Nat := 4 * 1024 * 1024

/--
Decode gRPC frame with strict validation.

Detects:
- Invalid compression flag (not 0 or 1)
- Frame length exceeds maximum
- Frame length exceeds available bytes
-/
def decodeGrpcFrameStrict (bs : Bytes) : StrictParseResult GrpcFrame :=
  if bs.size < 5 then
    .incomplete (5 - bs.size)
  else
    let flag := bs.data[0]!
    -- Compression flag must be 0 or 1
    if flag > 1 then
      .ambiguous (.invalidCompressionFlag flag)
    else
      let compressed := flag == 1
      -- Big-endian length
      let b1 := bs.data[1]!.toNat
      let b2 := bs.data[2]!.toNat
      let b3 := bs.data[3]!.toNat
      let b4 := bs.data[4]!.toNat
      let len := (b1 <<< 24) + (b2 <<< 16) + (b3 <<< 8) + b4
      -- Check length limits
      if len > maxGrpcFrameSize then
        .ambiguous (.grpcFrameTooLarge len)
      else
        let rest := bs.extract 5 bs.size
        if rest.size < len then
          .incomplete (len - rest.size)
        else
          .ok ⟨compressed, rest.extract 0 len⟩ (rest.extract len rest.size)

-- ═══════════════════════════════════════════════════════════════════════════════
-- PARSE STATE AND RESET
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Protobuf message parse state -/
structure ParseState where
  /-- Current nesting depth -/
  depth : Nat
  /-- Bytes consumed so far -/
  consumed : Nat
  /-- Leftover bytes from previous parse -/
  leftover : Bytes
  deriving Repr, DecidableEq

/-- Maximum nesting depth (prevent stack overflow) -/
def maxNestingDepth : Nat := 100

/-- Initial parse state -/
def initParseState : ParseState := {
  depth := 0
  consumed := 0
  leftover := ByteArray.empty
}

/-- Reset parse state -/
def resetParseState (_s : ParseState) : ParseState := initParseState

-- ═══════════════════════════════════════════════════════════════════════════════
-- RESET THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════════

/--
THEOREM 1: Reset always produces initial state.
-/
theorem reset_is_initial : ∀ s, resetParseState s = initParseState := by
  intro s
  rfl

/--
THEOREM 2: Reset is idempotent.
-/
theorem reset_idempotent : ∀ s,
    resetParseState (resetParseState s) = resetParseState s := by
  intro s
  rfl

/--
THEOREM 3: No information leakage across reset.
-/
theorem no_leakage : ∀ s₁ s₂,
    resetParseState s₁ = resetParseState s₂ := by
  intro s₁ s₂
  rfl

/--
THEOREM 4: Initial depth is zero.
-/
theorem init_depth_zero : initParseState.depth = 0 := rfl

/--
THEOREM 5: Reset clears depth.
-/
theorem reset_clears_depth : ∀ s, (resetParseState s).depth = 0 := by
  intro s
  rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- PARSING THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════════

/--
THEOREM 6: decodeVarintStrict is deterministic.
-/
theorem decodeVarintStrict_deterministic (b1 b2 : Bytes) :
    b1 = b2 → decodeVarintStrict b1 = decodeVarintStrict b2 := by
  intro h
  rw [h]

/--
THEOREM 7: Deprecated wire type 3 triggers ambiguity.
-/
theorem wireType3_ambiguous : isDeprecatedWireType 3 = true := rfl

/--
THEOREM 8: Deprecated wire type 4 triggers ambiguity.
-/
theorem wireType4_ambiguous : isDeprecatedWireType 4 = true := rfl

/--
THEOREM 9: Wire type 6 is invalid.
-/
theorem wireType6_invalid : isValidWireType 6 = false := rfl

/--
THEOREM 10: Wire type 7 is invalid.
-/
theorem wireType7_invalid : isValidWireType 7 = false := rfl

/--
THEOREM 11: Wire types 0, 1, 2, 5 are valid.
-/
theorem valid_wire_types :
    isValidWireType 0 = true ∧
    isValidWireType 1 = true ∧
    isValidWireType 2 = true ∧
    isValidWireType 5 = true := ⟨rfl, rfl, rfl, rfl⟩

/--
THEOREM 12: gRPC compression flag > 1 is ambiguous.
-/
theorem grpc_invalid_flag (flag : UInt8) (h : flag > 1) :
    ∀ bs, bs.size ≥ 5 → bs.data[0]! = flag →
    ∃ r, decodeGrpcFrameStrict bs = .ambiguous r := by
  intro bs hsize hflag
  unfold decodeGrpcFrameStrict
  have h1 : ¬(bs.size < 5) := by omega
  simp only [h1, ↓reduceIte, hflag]
  have h2 : flag > 1 := h
  simp only [h2, ↓reduceIte]
  exact ⟨.invalidCompressionFlag flag, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- VERIFICATION STATUS
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Verification Summary

### Core Reset Theorems (all proven, 0 sorry):

| Theorem | What's Proven |
|---------|---------------|
| reset_is_initial | reset always produces initParseState |
| reset_idempotent | reset(reset(s)) = reset(s) |
| no_leakage | different states reset to identical states |
| init_depth_zero | initial depth is 0 |
| reset_clears_depth | reset clears nesting depth |

### Wire Format Theorems (all proven, 0 sorry):

| Theorem | What's Proven |
|---------|---------------|
| decodeVarintStrict_deterministic | same bytes → same result |
| wireType3_ambiguous | startGroup triggers ambiguity |
| wireType4_ambiguous | endGroup triggers ambiguity |
| wireType6_invalid | wire type 6 invalid |
| wireType7_invalid | wire type 7 invalid |
| valid_wire_types | 0, 1, 2, 5 are valid |
| grpc_invalid_flag | compression flag > 1 triggers ambiguity |

### Types Defined:

| Type | Purpose |
|------|---------|
| AmbiguityReason | why ambiguity occurred |
| StrictParseResult | ok / incomplete / ambiguous |
| ParseState | message parse state |

### Key Functions:

| Function | Purpose |
|----------|---------|
| decodeVarintStrict | varint with overflow detection |
| decodeTagStrict | tag with wire type validation |
| decodeLengthDelimitedStrict | length-delimited with bounds |
| decodeProtoStringStrict | string with UTF-8 validation |
| decodeGrpcFrameStrict | gRPC frame with flag validation |
| resetParseState | return to ground state |

**Total: 12 theorems proven, 0 sorry**
-/

end Foundry.Cornell.Protobuf
