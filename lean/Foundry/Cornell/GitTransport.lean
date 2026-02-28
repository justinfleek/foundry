/-
  Foundry.Cornell.GitTransport - Verified Git Smart HTTP Protocol
  
  Implements the client side of git-upload-pack for clone/fetch.
  
  Protocol flow:
  1. GET /info/refs?service=git-upload-pack  → ref advertisement
  2. POST /git-upload-pack                    → wants/haves negotiation
  3. Receive packfile (possibly with sideband)
  
  Uses Foundry.Cornell.Protocol for pkt-line framing.
  Uses Foundry.Cornell.Git for packfile parsing.
-/

import Foundry.Cornell.Protocol
import Foundry.Cornell.Git

namespace Foundry.Cornell.GitTransport

open Cornell Foundry.Cornell.Proofs Foundry.Cornell.Protocol Foundry.Cornell.Git

-- ═══════════════════════════════════════════════════════════════════════════════
-- REFERENCE ADVERTISEMENT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A git reference (branch, tag, etc.) -/
structure Ref where
  oid : String        -- 40 hex chars (SHA-1) or 64 hex chars (SHA-256)
  name : String       -- e.g., "refs/heads/main"
  deriving Repr, DecidableEq

/-- Reference advertisement from server -/
structure RefAdvertisement where
  refs : List Ref
  capabilities : List Capability
  head : Option String  -- symref HEAD target
  deriving Repr

/-- Parse reference advertisement line: "<oid> <refname>\0<caps>" or "<oid> <refname>" -/
def parseRefLine (s : String) : Option (Ref × List Capability) :=
  -- First line has capabilities after NUL
  let parts := s.splitOn "\x00"
  let refPart := parts.headD ""
  let caps := match parts.tail? with
    | some (s :: _) => parseCapabilities s
    | _ => []
  -- Split ref part: "<oid> <refname>"
  match refPart.splitOn " " with
  | [oid, name] => some (⟨oid, name⟩, caps)
  | _ => none

/-- Convert ByteArray to String (UTF-8, unchecked) -/
def bytesToString (bs : Bytes) : String :=
  String.fromUTF8! bs

/-- Parse complete reference advertisement from frames -/
def parseRefAdvertisement (frames : List Frame) : Option RefAdvertisement :=
  match frames with
  | [] => some ⟨[], [], none⟩
  | first :: rest =>
    -- First frame might be "# service=git-upload-pack\n" header
    let payloadStr := bytesToString first.payload
    let dataFrames := if payloadStr.startsWith "#" then rest else frames
    -- Parse refs
    let parsed := dataFrames.filterMap fun f =>
      let s := bytesToString f.payload
      parseRefLine s.trimRight  -- remove trailing newline
    let refs := parsed.map Prod.fst
    let caps := match parsed.head? with
      | some (_, c) => c
      | none => []
    -- Extract HEAD symref from capabilities
    let head := caps.findSome? fun c =>
      if c.startsWith "symref=HEAD:" then some (c.drop 12)
      else none
    some ⟨refs, caps, head⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- UPLOAD REQUEST (wants/haves)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Request to upload pack -/
structure UploadRequest where
  wants : List String           -- OIDs we want
  haves : List String           -- OIDs we have (for incremental fetch)
  capabilities : List Capability
  shallow : List String         -- shallow boundaries
  deepen : Option Nat           -- depth limit
  deriving Repr

/-- Enumerate a list with indices -/
def enumerate {α : Type} (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: xs => (i, x) :: go (i + 1) xs
  go 0 xs

/-- Serialize upload request to pkt-lines -/
def serializeUploadRequest (req : UploadRequest) : List Frame :=
  let wantFrames := (enumerate req.wants).map fun (i, oid) =>
    let line := if i == 0 then
      s!"want {oid} {serializeCapabilities req.capabilities}\n"
    else
      s!"want {oid}\n"
    ⟨line.toUTF8⟩
  let haveFrames := req.haves.map fun oid =>
    ⟨s!"have {oid}\n".toUTF8⟩
  let doneFrame : Frame := ⟨"done\n".toUTF8⟩
  wantFrames ++ [Frame.flush] ++ haveFrames ++ [doneFrame]

-- ═══════════════════════════════════════════════════════════════════════════════
-- UPLOAD RESPONSE (NAK/ACK + packfile)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Server response type -/
inductive ServerResponse where
  | nak                          -- No common commits
  | ack (oid : String)           -- Common commit found
  | shallow (oid : String)       -- Shallow boundary
  | unshallow (oid : String)     -- Unshallow
  deriving Repr, DecidableEq

/-- Parse server response line -/
def parseServerResponse (s : String) : Option ServerResponse :=
  let s := s.trimRight
  if s == "NAK" then some .nak
  else if s.startsWith "ACK " then some (.ack (s.drop 4))
  else if s.startsWith "shallow " then some (.shallow (s.drop 8))
  else if s.startsWith "unshallow " then some (.unshallow (s.drop 10))
  else none

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROTOCOL STATE MACHINE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Client state for git fetch -/
inductive FetchState where
  | init                                          -- Initial state
  | awaitingRefs                                  -- Sent info/refs request
  | receivedRefs (adv : RefAdvertisement)         -- Got refs, deciding what to fetch
  | awaitingPack                                  -- Sent upload request
  | receivingPack (received : Nat)                -- Receiving packfile data
  | done (pack : List UInt8)                      -- Complete
  | error (msg : String)                          -- Error occurred
  deriving Repr

/-- Events from network -/
inductive FetchEvent where
  | refFrames (frames : List Frame)               -- Reference advertisement
  | packFrame (data : Bytes)                      -- Pack data (sideband channel 1)
  | progress (msg : String)                       -- Progress message (sideband channel 2)
  | errorMsg (msg : String)                       -- Error from server (sideband channel 3)
  | serverResponse (resp : ServerResponse)        -- NAK/ACK
  | flush                                         -- Flush packet
  | eof                                           -- Connection closed
  deriving Repr

/-- Actions to send -/
inductive FetchAction where
  | httpGet (path : String)                       -- GET request
  | httpPost (path : String) (body : Bytes)       -- POST request
  | close                                         -- Close connection
  deriving Repr

/-- State transition -/
def fetchStep (state : FetchState) (event : FetchEvent) : FetchState × List FetchAction :=
  match state, event with
  | .init, _ => 
    (.awaitingRefs, [.httpGet "/info/refs?service=git-upload-pack"])
  
  | .awaitingRefs, .refFrames frames =>
    match parseRefAdvertisement frames with
    | some adv => (.receivedRefs adv, [])
    | none => (.error "Failed to parse ref advertisement", [.close])
  
  | .receivedRefs adv, _ =>
    -- Caller should examine adv and call fetchStep with wants
    -- For now, auto-fetch HEAD
    match adv.refs.find? (·.name == "HEAD") with
    | some headRef =>
      let req : UploadRequest := {
        wants := [headRef.oid]
        haves := []
        capabilities := ["side-band-64k", "ofs-delta", "thin-pack"]
        shallow := []
        deepen := none
      }
      let frames := serializeUploadRequest req
      let body := serializeWithFlush gitLengthCodec frames
      (.awaitingPack, [.httpPost "/git-upload-pack" body])
    | none => (.error "No HEAD ref", [.close])
  
  | .awaitingPack, .serverResponse .nak =>
    (.receivingPack 0, [])
  
  | .awaitingPack, .serverResponse (.ack _) =>
    (.receivingPack 0, [])
  
  | .receivingPack n, .packFrame data =>
    (.receivingPack (n + data.size), [])
  
  | .receivingPack _, .eof =>
    (.done [], [.close])
  
  | .receivingPack _, .progress _ =>
    -- Could log progress
    (state, [])
  
  | _, .errorMsg msg =>
    (.error msg, [.close])
  
  | s, _ => (s, [])

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMMON CAPABILITIES FOR CLONE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Default capabilities for efficient clone -/
def defaultCloneCapabilities : List Capability :=
  [ "multi_ack_detailed"
  , "side-band-64k"
  , "ofs-delta"
  , "thin-pack"
  , "no-progress"
  , "include-tag"
  , "allow-tip-sha1-in-want"
  , "allow-reachable-sha1-in-want"
  ]

/-- Capabilities for shallow clone -/
def shallowCloneCapabilities : List Capability :=
  defaultCloneCapabilities ++ ["shallow", "deepen-since", "deepen-not"]

-- ═══════════════════════════════════════════════════════════════════════════════
-- URL PARSING (minimal)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Parsed git URL -/
structure GitUrl where
  scheme : String     -- "https" or "http"
  host : String
  port : Option Nat
  path : String       -- e.g., "/owner/repo.git"
  deriving Repr

/-- Parse git URL (simplified) -/
def parseGitUrl (url : String) : Option GitUrl :=
  -- Handle https://host/path or http://host/path
  let parts := url.splitOn "://"
  match parts with
  | [scheme, rest] =>
    if scheme != "https" && scheme != "http" then none
    else
      match rest.splitOn "/" with
      | [] => none
      | [_] => none  -- no path
      | hostPart :: pathParts =>
        let path := "/" ++ String.intercalate "/" pathParts
        -- Check for port in hostPart
        match hostPart.splitOn ":" with
        | [host] => some ⟨scheme, host, none, path⟩
        | [host, portStr] =>
          match portStr.toNat? with
          | some p => some ⟨scheme, host, some p, path⟩
          | none => none
        | _ => none
  | _ => none

end Foundry.Cornell.GitTransport
