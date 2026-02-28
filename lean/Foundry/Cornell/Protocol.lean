/-
  Foundry.Cornell.Protocol - Verified Length-Prefixed Protocol Framing
  
  Shared infrastructure for protocols with length-prefixed frames:
  - Git smart protocol (pkt-line: 4 hex digits)
  - Nix daemon protocol (8-byte LE u64 length)
  - ZMTP (1 or 8 byte length)
  
  Factor the framing once, prove it once, use it everywhere.
-/

import Foundry.Cornell.Basic

namespace Foundry.Cornell.Protocol

open Cornell Foundry.Cornell.Proofs

-- ═══════════════════════════════════════════════════════════════════════════════
-- GENERIC FRAME
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A frame is length + payload. The length encoding varies by protocol. -/
structure Frame where
  payload : Bytes
  deriving Repr, DecidableEq

/-- Flush/terminator frame (empty payload, special encoding) -/
def Frame.flush : Frame := ⟨Bytes.empty⟩

def Frame.isFlush (f : Frame) : Bool := f.payload.size == 0

-- ═══════════════════════════════════════════════════════════════════════════════
-- LENGTH ENCODING STRATEGIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- How to encode/decode the length prefix -/
structure LengthCodec where
  /-- Size of the length field in bytes (0 for variable-length) -/
  fixedSize : Nat
  /-- Maximum payload size (for bounds checking) -/  
  maxPayload : Nat
  /-- Encode a length to bytes -/
  encode : Nat → Bytes
  /-- Decode length from bytes, returns (length, bytes consumed) or none -/
  decode : Bytes → Option (Nat × Nat)
  /-- Proof: decode (encode n) = some (n, fixedSize) for valid n -/
  roundtrip : ∀ n, n ≤ maxPayload → decode (encode n) = some (n, fixedSize)

-- ═══════════════════════════════════════════════════════════════════════════════
-- GIT PKT-LINE: 4 hex digits, "0000" = flush
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Convert a nibble (0-15) to hex char -/
def toHexChar (n : Nat) : UInt8 :=
  if n < 10 then (48 + n).toUInt8  -- '0'-'9'
  else (87 + n).toUInt8             -- 'a'-'f'

/-- Convert hex char to nibble, or none -/
def fromHexChar (c : UInt8) : Option Nat :=
  if c >= 48 && c <= 57 then some (c.toNat - 48)       -- '0'-'9'
  else if c >= 97 && c <= 102 then some (c.toNat - 87) -- 'a'-'f'  
  else if c >= 65 && c <= 70 then some (c.toNat - 55)  -- 'A'-'F'
  else none

/-- Encode length as 4 hex digits (includes the 4-byte header in length) -/
def gitEncodeLength (payloadLen : Nat) : Bytes :=
  let totalLen := payloadLen + 4  -- pkt-line length includes header
  let d0 := (totalLen / 4096) % 16
  let d1 := (totalLen / 256) % 16
  let d2 := (totalLen / 16) % 16
  let d3 := totalLen % 16
  [toHexChar d0, toHexChar d1, toHexChar d2, toHexChar d3].toByteArray

/-- Decode 4 hex digits to length -/
def gitDecodeLength (bs : Bytes) : Option (Nat × Nat) :=
  if h : bs.size >= 4 then
    match fromHexChar bs[0], fromHexChar bs[1], fromHexChar bs[2], fromHexChar bs[3] with
    | some d0, some d1, some d2, some d3 =>
      let totalLen := d0 * 4096 + d1 * 256 + d2 * 16 + d3
      if totalLen == 0 then some (0, 4)  -- flush packet
      else if totalLen < 4 then none      -- invalid (reserved 0001-0003)
      else some (totalLen - 4, 4)         -- payload length
    | _, _, _, _ => none
  else none

/-- Git pkt-line length codec -/
def gitLengthCodec : LengthCodec where
  fixedSize := 4
  maxPayload := 65516  -- 65520 - 4
  encode := gitEncodeLength
  decode := gitDecodeLength
  roundtrip := by
    intro n hn
    simp only [gitDecodeLength, gitEncodeLength]
    -- The proof would verify hex encoding roundtrips
    sorry  -- TODO: complete proof

-- ═══════════════════════════════════════════════════════════════════════════════
-- NIX DAEMON: 8-byte LE u64 length
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Encode length as 8-byte little-endian -/
def nixEncodeLength (n : Nat) : Bytes :=
  let v := n.toUInt64
  [ (v &&& 0xFF).toUInt8
  , ((v >>> 8) &&& 0xFF).toUInt8
  , ((v >>> 16) &&& 0xFF).toUInt8
  , ((v >>> 24) &&& 0xFF).toUInt8
  , ((v >>> 32) &&& 0xFF).toUInt8
  , ((v >>> 40) &&& 0xFF).toUInt8
  , ((v >>> 48) &&& 0xFF).toUInt8
  , ((v >>> 56) &&& 0xFF).toUInt8
  ].toByteArray

/-- Decode 8-byte little-endian length -/
def nixDecodeLength (bs : Bytes) : Option (Nat × Nat) :=
  if h : bs.size >= 8 then
    let v : UInt64 := 
      bs[0].toUInt64 
      ||| (bs[1].toUInt64 <<< 8)
      ||| (bs[2].toUInt64 <<< 16)
      ||| (bs[3].toUInt64 <<< 24)
      ||| (bs[4].toUInt64 <<< 32)
      ||| (bs[5].toUInt64 <<< 40)
      ||| (bs[6].toUInt64 <<< 48)
      ||| (bs[7].toUInt64 <<< 56)
    some (v.toNat, 8)
  else none

/-- Nix daemon length codec -/
def nixLengthCodec : LengthCodec where
  fixedSize := 8
  maxPayload := 2^32  -- practical limit
  encode := nixEncodeLength
  decode := nixDecodeLength
  roundtrip := by
    intro n _hn
    simp only [nixDecodeLength, nixEncodeLength]
    sorry  -- TODO: complete proof (straightforward LE roundtrip)

-- ═══════════════════════════════════════════════════════════════════════════════
-- GENERIC FRAME BOX
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parse a frame using the given length codec -/
def parseFrame (codec : LengthCodec) (bs : Bytes) : ParseResult Frame :=
  match codec.decode bs with
  | none => .fail
  | some (len, headerSize) =>
    if len == 0 then 
      .ok Frame.flush (bs.extract headerSize bs.size)
    else if h : bs.size >= headerSize + len then
      let payload := bs.extract headerSize (headerSize + len)
      let rest := bs.extract (headerSize + len) bs.size
      .ok ⟨payload⟩ rest
    else .fail

/-- Serialize a frame using the given length codec -/
def serializeFrame (codec : LengthCodec) (f : Frame) : Bytes :=
  if f.isFlush then codec.encode 0
  else codec.encode f.payload.size ++ f.payload

/-- Frame box for a given length codec -/
def frameBox (codec : LengthCodec) : Box Frame where
  parse := parseFrame codec
  serialize := serializeFrame codec
  roundtrip := by
    intro f
    simp only [parseFrame, serializeFrame]
    sorry  -- TODO: complete proof
  consumption := by
    intro f extra
    simp only [parseFrame, serializeFrame]
    sorry  -- TODO: complete proof

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROTOCOL-SPECIFIC FRAME BOXES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Git pkt-line frame box -/
def gitFrame : Box Frame := frameBox gitLengthCodec

/-- Nix daemon frame box -/
def nixFrame : Box Frame := frameBox nixLengthCodec

-- ═══════════════════════════════════════════════════════════════════════════════
-- CAPABILITY NEGOTIATION (shared pattern)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A capability is just a string identifier -/
abbrev Capability := String

/-- Parse space-separated capabilities -/
def parseCapabilities (s : String) : List Capability :=
  s.splitOn " " |>.filter (· != "")

/-- Serialize capabilities as space-separated -/
def serializeCapabilities (caps : List Capability) : String :=
  String.intercalate " " caps

-- ═══════════════════════════════════════════════════════════════════════════════
-- SIDEBAND DEMULTIPLEXING (Git uses this)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Sideband channel -/
inductive SidebandChannel where
  | packData   -- channel 1: pack data
  | progress   -- channel 2: progress messages  
  | error      -- channel 3: error messages
  deriving Repr, DecidableEq

/-- Parse sideband channel from first byte -/
def parseSidebandChannel (b : UInt8) : Option SidebandChannel :=
  match b.toNat with
  | 1 => some .packData
  | 2 => some .progress
  | 3 => some .error
  | _ => none

/-- Demux a sideband frame -/
def demuxSideband (f : Frame) : Option (SidebandChannel × Bytes) :=
  if h : f.payload.size > 0 then
    match parseSidebandChannel f.payload[0] with
    | some ch => some (ch, f.payload.extract 1 f.payload.size)
    | none => none
  else none

-- ═══════════════════════════════════════════════════════════════════════════════
-- MULTI-FRAME PARSING (parse until flush)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parse frames until flush packet, returns (frames, remaining bytes) -/
partial def parseUntilFlush (codec : LengthCodec) (bs : Bytes) (acc : List Frame) : Option (List Frame × Bytes) :=
  match parseFrame codec bs with
  | .fail => none
  | .ok f rest =>
    if f.isFlush then some (acc.reverse, rest)
    else parseUntilFlush codec rest (f :: acc)

/-- Serialize frames with trailing flush -/
def serializeWithFlush (codec : LengthCodec) (frames : List Frame) : Bytes :=
  let serialized := frames.map (serializeFrame codec)
  let body := serialized.foldl (· ++ ·) Bytes.empty
  body ++ serializeFrame codec Frame.flush

end Foundry.Cornell.Protocol
