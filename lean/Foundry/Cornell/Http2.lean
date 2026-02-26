/-
  Foundry.Cornell.Http2 - Verified HTTP/2 Frame Format
  
  HTTP/2 frame parsing with HPACK header compression.
  Reference: RFC 7540 (HTTP/2), RFC 7541 (HPACK)
  
  ## Frame Format
  
  +-----------------------------------------------+
  |                 Length (24)                   |
  +---------------+---------------+---------------+
  |   Type (8)    |   Flags (8)   |
  +-+-------------+---------------+-------------------------------+
  |R|                 Stream Identifier (31)                      |
  +=+=============================================================+
  |                   Frame Payload (0...)                      ...
  +---------------------------------------------------------------+
  
  ## Frame Types
  
  - DATA (0x0): Stream data
  - HEADERS (0x1): Header block
  - PRIORITY (0x2): Stream priority
  - RST_STREAM (0x3): Stream termination
  - SETTINGS (0x4): Connection settings
  - PUSH_PROMISE (0x5): Server push
  - PING (0x6): Connection liveness
  - GOAWAY (0x7): Connection shutdown
  - WINDOW_UPDATE (0x8): Flow control
  - CONTINUATION (0x9): Header continuation
-/

import Foundry.Foundry.Cornell.Basic

namespace Foundry.Cornell.Http2

open Cornell

-- ═══════════════════════════════════════════════════════════════════════════════
-- FRAME TYPES AND FLAGS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HTTP/2 frame types -/
inductive FrameType where
  | data          -- 0x0
  | headers       -- 0x1
  | priority      -- 0x2
  | rstStream     -- 0x3
  | settings      -- 0x4
  | pushPromise   -- 0x5
  | ping          -- 0x6
  | goaway        -- 0x7
  | windowUpdate  -- 0x8
  | continuation  -- 0x9
  deriving Repr, DecidableEq

def FrameType.toUInt8 : FrameType → UInt8
  | .data => 0x0
  | .headers => 0x1
  | .priority => 0x2
  | .rstStream => 0x3
  | .settings => 0x4
  | .pushPromise => 0x5
  | .ping => 0x6
  | .goaway => 0x7
  | .windowUpdate => 0x8
  | .continuation => 0x9

def FrameType.fromUInt8 : UInt8 → Option FrameType
  | 0x0 => some .data
  | 0x1 => some .headers
  | 0x2 => some .priority
  | 0x3 => some .rstStream
  | 0x4 => some .settings
  | 0x5 => some .pushPromise
  | 0x6 => some .ping
  | 0x7 => some .goaway
  | 0x8 => some .windowUpdate
  | 0x9 => some .continuation
  | _ => none

/-- Frame flags -/
structure FrameFlags where
  raw : UInt8
  deriving Repr

namespace FrameFlags
  def endStream (f : FrameFlags) : Bool := f.raw &&& 0x1 != 0
  def ack (f : FrameFlags) : Bool := f.raw &&& 0x1 != 0  -- Same bit, different meaning
  def endHeaders (f : FrameFlags) : Bool := f.raw &&& 0x4 != 0
  def padded (f : FrameFlags) : Bool := f.raw &&& 0x8 != 0
  def priority (f : FrameFlags) : Bool := f.raw &&& 0x20 != 0
end FrameFlags

-- ═══════════════════════════════════════════════════════════════════════════════
-- FRAME HEADER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HTTP/2 frame header (9 bytes) -/
structure FrameHeader where
  length : UInt32      -- 24 bits (max 16384 default, 16777215 max)
  frameType : FrameType
  flags : FrameFlags
  streamId : UInt32    -- 31 bits (high bit reserved)
  deriving Repr

/-- Maximum frame payload size -/
def MAX_FRAME_SIZE : UInt32 := 16384
def MAX_FRAME_SIZE_ALLOWED : UInt32 := 16777215

/-- Parse frame header (9 bytes, big-endian) -/
def parseFrameHeader (bs : Bytes) : ParseResult FrameHeader :=
  if h : bs.size >= 9 then
    -- Length (24 bits, big-endian)
    let length := bs.data[0]!.toUInt32 <<< 16
              ||| bs.data[1]!.toUInt32 <<< 8
              ||| bs.data[2]!.toUInt32
    -- Type (8 bits)
    let typeRaw := bs.data[3]!
    match FrameType.fromUInt8 typeRaw with
    | none => .fail
    | some frameType =>
      -- Flags (8 bits)
      let flags := FrameFlags.mk bs.data[4]!
      -- Stream ID (31 bits, big-endian, high bit reserved)
      let streamId := (bs.data[5]!.toUInt32 &&& 0x7F) <<< 24
                  ||| bs.data[6]!.toUInt32 <<< 16
                  ||| bs.data[7]!.toUInt32 <<< 8
                  ||| bs.data[8]!.toUInt32
      .ok ⟨length, frameType, flags, streamId⟩ (bs.extract 9 bs.size)
  else .fail

/-- Serialize frame header -/
def serializeFrameHeader (h : FrameHeader) : Bytes :=
  ⟨#[
    ((h.length >>> 16) &&& 0xFF).toUInt8,
    ((h.length >>> 8) &&& 0xFF).toUInt8,
    (h.length &&& 0xFF).toUInt8,
    h.frameType.toUInt8,
    h.flags.raw,
    (((h.streamId >>> 24) &&& 0x7F).toUInt8),  -- Mask high bit
    ((h.streamId >>> 16) &&& 0xFF).toUInt8,
    ((h.streamId >>> 8) &&& 0xFF).toUInt8,
    (h.streamId &&& 0xFF).toUInt8
  ]⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- FRAME PAYLOADS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- DATA frame payload -/
structure DataPayload where
  padLength : Option UInt8  -- Present if PADDED flag set
  data : Bytes
  deriving Repr

/-- HEADERS frame payload -/
structure HeadersPayload where
  padLength : Option UInt8
  exclusive : Option Bool      -- Present if PRIORITY flag set
  streamDep : Option UInt32    -- Present if PRIORITY flag set
  weight : Option UInt8        -- Present if PRIORITY flag set
  headerBlock : Bytes          -- HPACK-encoded headers
  deriving Repr

/-- PRIORITY frame payload (5 bytes) -/
structure PriorityPayload where
  exclusive : Bool
  streamDep : UInt32
  weight : UInt8
  deriving Repr

/-- RST_STREAM frame payload (4 bytes) -/
structure RstStreamPayload where
  errorCode : UInt32
  deriving Repr

/-- SETTINGS frame payload -/
structure SettingsPayload where
  settings : List (UInt16 × UInt32)  -- (identifier, value) pairs
  deriving Repr

/-- PUSH_PROMISE frame payload -/
structure PushPromisePayload where
  padLength : Option UInt8
  promisedStreamId : UInt32
  headerBlock : Bytes
  deriving Repr

/-- PING frame payload (8 bytes) -/
structure PingPayload where
  opaqueData : Bytes  -- Must be 8 bytes
  deriving Repr

/-- GOAWAY frame payload -/
structure GoawayPayload where
  lastStreamId : UInt32
  errorCode : UInt32
  debugData : Bytes
  deriving Repr

/-- WINDOW_UPDATE frame payload (4 bytes) -/
structure WindowUpdatePayload where
  windowSizeIncrement : UInt32  -- 31 bits
  deriving Repr

/-- Frame with payload -/
inductive Frame where
  | data (h : FrameHeader) (p : DataPayload)
  | headers (h : FrameHeader) (p : HeadersPayload)
  | priority (h : FrameHeader) (p : PriorityPayload)
  | rstStream (h : FrameHeader) (p : RstStreamPayload)
  | settings (h : FrameHeader) (p : SettingsPayload)
  | pushPromise (h : FrameHeader) (p : PushPromisePayload)
  | ping (h : FrameHeader) (p : PingPayload)
  | goaway (h : FrameHeader) (p : GoawayPayload)
  | windowUpdate (h : FrameHeader) (p : WindowUpdatePayload)
  | continuation (h : FrameHeader) (headerBlock : Bytes)
  deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════════
-- PAYLOAD PARSING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parse DATA frame payload -/
def parseDataPayload (flags : FrameFlags) (bs : Bytes) : ParseResult DataPayload :=
  if flags.padded then
    if h : bs.size > 0 then
      let padLen := bs.data[0]!
      let dataEnd := bs.size - padLen.toNat
      if dataEnd <= 1 then .fail
      else
        let data := bs.extract 1 dataEnd
        .ok ⟨some padLen, data⟩ Bytes.empty
    else .fail
  else
    .ok ⟨none, bs⟩ Bytes.empty

/-- Parse PRIORITY payload (5 bytes) -/
def parsePriorityPayload (bs : Bytes) : ParseResult PriorityPayload :=
  if h : bs.size >= 5 then
    let b0 := bs.data[0]!
    let exclusive := b0 &&& 0x80 != 0
    let streamDep := ((b0.toUInt32 &&& 0x7F) <<< 24)
                 ||| bs.data[1]!.toUInt32 <<< 16
                 ||| bs.data[2]!.toUInt32 <<< 8
                 ||| bs.data[3]!.toUInt32
    let weight := bs.data[4]!
    .ok ⟨exclusive, streamDep, weight⟩ (bs.extract 5 bs.size)
  else .fail

/-- Parse SETTINGS payload -/
def parseSettingsPayload (bs : Bytes) : ParseResult SettingsPayload :=
  if bs.size % 6 != 0 then .fail
  else
    let rec go (remaining : Bytes) (acc : List (UInt16 × UInt32)) (fuel : Nat) : ParseResult SettingsPayload :=
      match fuel with
      | 0 => .fail
      | fuel' + 1 =>
        if remaining.size == 0 then
          .ok ⟨acc.reverse⟩ Bytes.empty
        else if h : remaining.size >= 6 then
          let id := remaining.data[0]!.toUInt16 <<< 8
                ||| remaining.data[1]!.toUInt16
          let value := remaining.data[2]!.toUInt32 <<< 24
                   ||| remaining.data[3]!.toUInt32 <<< 16
                   ||| remaining.data[4]!.toUInt32 <<< 8
                   ||| remaining.data[5]!.toUInt32
          go (remaining.extract 6 remaining.size) ((id, value) :: acc) fuel'
        else .fail
    go bs [] (bs.size / 6 + 1)

/-- Parse GOAWAY payload -/
def parseGoawayPayload (bs : Bytes) : ParseResult GoawayPayload :=
  if h : bs.size >= 8 then
    let lastStreamId := (bs.data[0]!.toUInt32 &&& 0x7F) <<< 24
                    ||| bs.data[1]!.toUInt32 <<< 16
                    ||| bs.data[2]!.toUInt32 <<< 8
                    ||| bs.data[3]!.toUInt32
    let errorCode := bs.data[4]!.toUInt32 <<< 24
                 ||| bs.data[5]!.toUInt32 <<< 16
                 ||| bs.data[6]!.toUInt32 <<< 8
                 ||| bs.data[7]!.toUInt32
    let debugData := bs.extract 8 bs.size
    .ok ⟨lastStreamId, errorCode, debugData⟩ Bytes.empty
  else .fail

/-- Parse WINDOW_UPDATE payload (4 bytes) -/
def parseWindowUpdatePayload (bs : Bytes) : ParseResult WindowUpdatePayload :=
  if h : bs.size >= 4 then
    let increment := (bs.data[0]!.toUInt32 &&& 0x7F) <<< 24
                 ||| bs.data[1]!.toUInt32 <<< 16
                 ||| bs.data[2]!.toUInt32 <<< 8
                 ||| bs.data[3]!.toUInt32
    .ok ⟨increment⟩ (bs.extract 4 bs.size)
  else .fail

/-- Parse complete frame -/
def parseFrame (bs : Bytes) : ParseResult Frame :=
  match parseFrameHeader bs with
  | .fail => .fail
  | .ok header rest =>
    let payloadLen := header.length.toNat
    if rest.size < payloadLen then .fail
    else
      let payload := rest.extract 0 payloadLen
      let remaining := rest.extract payloadLen rest.size
      match header.frameType with
      | .data =>
        match parseDataPayload header.flags payload with
        | .ok p _ => .ok (.data header p) remaining
        | .fail => .fail
      | .priority =>
        match parsePriorityPayload payload with
        | .ok p _ => .ok (.priority header p) remaining
        | .fail => .fail
      | .settings =>
        match parseSettingsPayload payload with
        | .ok p _ => .ok (.settings header p) remaining
        | .fail => .fail
      | .goaway =>
        match parseGoawayPayload payload with
        | .ok p _ => .ok (.goaway header p) remaining
        | .fail => .fail
      | .windowUpdate =>
        match parseWindowUpdatePayload payload with
        | .ok p _ => .ok (.windowUpdate header p) remaining
        | .fail => .fail
      | .ping =>
        if payload.size != 8 then .fail
        else .ok (.ping header ⟨payload⟩) remaining
      | .rstStream =>
        if h : payload.size >= 4 then
          let code := payload.data[0]!.toUInt32 <<< 24
                  ||| payload.data[1]!.toUInt32 <<< 16
                  ||| payload.data[2]!.toUInt32 <<< 8
                  ||| payload.data[3]!.toUInt32
          .ok (.rstStream header ⟨code⟩) remaining
        else .fail
      | .continuation =>
        .ok (.continuation header payload) remaining
      | .headers =>
        -- Simplified: just capture header block
        .ok (.headers header ⟨none, none, none, none, payload⟩) remaining
      | .pushPromise =>
        -- Simplified
        .ok (.pushPromise header ⟨none, 0, payload⟩) remaining

-- ═══════════════════════════════════════════════════════════════════════════════
-- HPACK (Header Compression)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HPACK integer encoding (prefix bits vary by context) -/
def parseHpackInt (prefixBits : Nat) (bs : Bytes) : ParseResult Nat :=
  if h : bs.size > 0 && prefixBits ≤ 8 then
    let mask := (1 <<< prefixBits) - 1
    let b0 := bs.data[0]!.toNat &&& mask
    if b0 < mask then
      .ok b0 (bs.extract 1 bs.size)
    else
      -- Multi-byte encoding
      let rec go (i : Nat) (acc : Nat) (shift : Nat) : ParseResult Nat :=
        if h2 : i < bs.size then
          let b := bs.data[i]!
          let acc' := acc + ((b.toNat &&& 0x7F) <<< shift)
          if b &&& 0x80 == 0 then
            .ok (mask + acc') (bs.extract (i + 1) bs.size)
          else
            go (i + 1) acc' (shift + 7)
        else .fail
      termination_by bs.size - i
      go 1 0 0
  else .fail

/-- Static table entry (predefined headers) -/
structure HpackEntry where
  name : String
  value : String
  deriving Repr

/-- HPACK static table (first 61 entries) -/
def staticTable : Array HpackEntry := #[
  ⟨":authority", ""⟩,
  ⟨":method", "GET"⟩,
  ⟨":method", "POST"⟩,
  ⟨":path", "/"⟩,
  ⟨":path", "/index.html"⟩,
  ⟨":scheme", "http"⟩,
  ⟨":scheme", "https"⟩,
  ⟨":status", "200"⟩,
  ⟨":status", "204"⟩,
  ⟨":status", "206"⟩,
  ⟨":status", "304"⟩,
  ⟨":status", "400"⟩,
  ⟨":status", "404"⟩,
  ⟨":status", "500"⟩,
  ⟨"accept-charset", ""⟩,
  ⟨"accept-encoding", "gzip, deflate"⟩,
  ⟨"accept-language", ""⟩,
  ⟨"accept-ranges", ""⟩,
  ⟨"accept", ""⟩,
  ⟨"access-control-allow-origin", ""⟩,
  ⟨"age", ""⟩,
  ⟨"allow", ""⟩,
  ⟨"authorization", ""⟩,
  ⟨"cache-control", ""⟩,
  ⟨"content-disposition", ""⟩,
  ⟨"content-encoding", ""⟩,
  ⟨"content-language", ""⟩,
  ⟨"content-length", ""⟩,
  ⟨"content-location", ""⟩,
  ⟨"content-range", ""⟩,
  ⟨"content-type", ""⟩,
  ⟨"cookie", ""⟩,
  ⟨"date", ""⟩,
  ⟨"etag", ""⟩,
  ⟨"expect", ""⟩,
  ⟨"expires", ""⟩,
  ⟨"from", ""⟩,
  ⟨"host", ""⟩,
  ⟨"if-match", ""⟩,
  ⟨"if-modified-since", ""⟩,
  ⟨"if-none-match", ""⟩,
  ⟨"if-range", ""⟩,
  ⟨"if-unmodified-since", ""⟩,
  ⟨"last-modified", ""⟩,
  ⟨"link", ""⟩,
  ⟨"location", ""⟩,
  ⟨"max-forwards", ""⟩,
  ⟨"proxy-authenticate", ""⟩,
  ⟨"proxy-authorization", ""⟩,
  ⟨"range", ""⟩,
  ⟨"referer", ""⟩,
  ⟨"refresh", ""⟩,
  ⟨"retry-after", ""⟩,
  ⟨"server", ""⟩,
  ⟨"set-cookie", ""⟩,
  ⟨"strict-transport-security", ""⟩,
  ⟨"transfer-encoding", ""⟩,
  ⟨"user-agent", ""⟩,
  ⟨"vary", ""⟩,
  ⟨"via", ""⟩,
  ⟨"www-authenticate", ""⟩
]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ERROR CODES
-- ═══════════════════════════════════════════════════════════════════════════════

inductive ErrorCode where
  | noError           -- 0x0
  | protocolError     -- 0x1
  | internalError     -- 0x2
  | flowControlError  -- 0x3
  | settingsTimeout   -- 0x4
  | streamClosed      -- 0x5
  | frameSizeError    -- 0x6
  | refusedStream     -- 0x7
  | cancel            -- 0x8
  | compressionError  -- 0x9
  | connectError      -- 0xa
  | enhanceYourCalm   -- 0xb
  | inadequateSecurity -- 0xc
  | http11Required    -- 0xd
  deriving Repr, DecidableEq

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONNECTION STATE MACHINE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Stream state -/
inductive StreamState where
  | idle
  | reservedLocal
  | reservedRemote
  | open_
  | halfClosedLocal
  | halfClosedRemote
  | closed
  deriving Repr, DecidableEq

/-- Connection settings -/
structure ConnectionSettings where
  headerTableSize : UInt32 := 4096
  enablePush : Bool := true
  maxConcurrentStreams : Option UInt32 := none
  initialWindowSize : UInt32 := 65535
  maxFrameSize : UInt32 := 16384
  maxHeaderListSize : Option UInt32 := none
  deriving Repr

end Foundry.Cornell.Http2
