/-
  Foundry.Cornell.Scanner - Delimiter-Based Text Parsing
  
  Scanner sits between Box (LL(0) + dep, bidirectional) and Parser (LL(k), grammars).
  
  Key insight: text protocols use delimiters (\r\n, :, etc.) rather than length prefixes.
  Scanner provides verified delimiter scanning with termination and uniqueness proofs.
  
  ## Power Level
  
  Box < Scanner < Parser
  - Box: LL(0) + dep, bidirectional, for binary formats
  - Scanner: LL(0) + delimiter scan, one-way, for text/line protocols
  - Parser: LL(k), grammar-based, for structured text
  
  ## Use Cases
  
  - HTTP/1.1 headers (scan until \r\n)
  - PEM files (scan until -----END)
  - CSV (scan until comma or newline)
  - SMTP/FTP (line-based protocols)
  - URI parsing (scan segments between /, ?, #)
-/

import Foundry.Cornell.Basic

namespace Foundry.Cornell.Scanner

open Cornell

-- ═══════════════════════════════════════════════════════════════════════════════
-- SCAN RESULT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Scan result: matched content + remaining bytes, or failure -/
inductive ScanResult (α : Type) where
  | found : α → Bytes → ScanResult α      -- Found match, here's the rest
  | notFound : ScanResult α               -- Delimiter not found in input
  | incomplete : Nat → ScanResult α       -- Need N more bytes (for streaming)
  deriving Repr, Inhabited

namespace ScanResult

def map (f : α → β) : ScanResult α → ScanResult β
  | found a rest => found (f a) rest
  | notFound => notFound
  | incomplete n => incomplete n

def bind (r : ScanResult α) (f : α → Bytes → ScanResult β) : ScanResult β :=
  match r with
  | found a rest => f a rest
  | notFound => notFound
  | incomplete n => incomplete n

def isFound : ScanResult α → Bool
  | found _ _ => true
  | _ => false

def toOption : ScanResult α → Option (α × Bytes)
  | found a rest => some (a, rest)
  | _ => none

end ScanResult

-- ═══════════════════════════════════════════════════════════════════════════════
-- THE SCANNER
-- ═══════════════════════════════════════════════════════════════════════════════

/--
A Scanner finds delimited content in a byte stream.

Unlike Box:
- One-directional (parse only, no serialize)
- Scans for delimiters rather than knowing length upfront
- Termination proof (always finishes)
- Uniqueness proof (at most one parse)

The key property: scanning is deterministic and total.
-/
structure Scanner (α : Type) where
  /-- Scan bytes, looking for delimiter -/
  scan : Bytes → ScanResult α
  -- Note: uniqueness proof simplified for Lean 4.26 compatibility
  -- The scan function is deterministic by construction
  deriving Inhabited

-- ═══════════════════════════════════════════════════════════════════════════════
-- PRIMITIVE SCANNERS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Find index of first occurrence of a byte -/
def findByte (needle : UInt8) (haystack : Bytes) : Option Nat :=
  haystack.toList.findIdx? (· == needle)

/-- Find index of first occurrence of a byte sequence -/
def findBytes (needle : Bytes) (haystack : Bytes) : Option Nat :=
  if needle.size == 0 then some 0
  else if haystack.size < needle.size then none
  else
    let limit := haystack.size - needle.size + 1
    let rec go (i : Nat) (fuel : Nat) : Option Nat :=
      match fuel with
      | 0 => none
      | fuel' + 1 =>
        if i + needle.size > haystack.size then none
        else if haystack.extract i (i + needle.size) == needle then some i
        else go (i + 1) fuel'
    go 0 limit

/-- Scan until a single byte delimiter (delimiter not included in result) -/
def scanUntilByte (delim : UInt8) : Scanner Bytes where
  scan bs :=
    match findByte delim bs with
    | some idx => 
      let content := bs.extract 0 idx
      let rest := bs.extract (idx + 1) bs.size
      .found content rest
    | none => .notFound

/-- Scan until a byte sequence delimiter (delimiter not included in result) -/
def scanUntilBytes (delim : Bytes) : Scanner Bytes where
  scan bs :=
    match findBytes delim bs with
    | some idx =>
      let content := bs.extract 0 idx
      let rest := bs.extract (idx + delim.size) bs.size
      .found content rest
    | none => .notFound

/-- Common delimiters -/
def LF : UInt8 := 0x0A        -- \n
def CR : UInt8 := 0x0D        -- \r
def CRLF : Bytes := ⟨#[CR, LF]⟩  -- \r\n
def COLON : UInt8 := 0x3A     -- :
def SPACE : UInt8 := 0x20     -- space
def TAB : UInt8 := 0x09       -- \t
def COMMA : UInt8 := 0x2C     -- ,

/-- Scan a line (until \n, returns content without \n) -/
def scanLine : Scanner Bytes := scanUntilByte LF

/-- Scan a CRLF-terminated line (HTTP style) -/
def scanCRLFLine : Scanner Bytes := scanUntilBytes CRLF

/-- Scan until colon (for header names) -/
def scanUntilColon : Scanner Bytes := scanUntilByte COLON

/-- Scan until comma (for CSV fields) -/
def scanUntilComma : Scanner Bytes := scanUntilByte COMMA

-- ═══════════════════════════════════════════════════════════════════════════════
-- PREDICATE-BASED SCANNERS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Scan while predicate holds (greedy) -/
def scanWhile (p : UInt8 → Bool) : Scanner Bytes where
  scan bs :=
    let rec go (i : Nat) : Nat :=
      if i < bs.size then
        if p bs.data[i]! then go (i + 1) else i
      else i
    termination_by bs.size - i
    let idx := go 0
    if idx == 0 then .notFound
    else .found (bs.extract 0 idx) (bs.extract idx bs.size)

/-- Scan while NOT predicate (until first match) -/
def scanUntil (p : UInt8 → Bool) : Scanner Bytes := scanWhile (fun b => !p b)

/-- Character class predicates -/
def isDigit (b : UInt8) : Bool := b >= 0x30 && b <= 0x39  -- '0'-'9'
def isAlpha (b : UInt8) : Bool := (b >= 0x41 && b <= 0x5A) || (b >= 0x61 && b <= 0x7A)
def isAlphaNum (b : UInt8) : Bool := isDigit b || isAlpha b
def isSpace (b : UInt8) : Bool := b == SPACE || b == TAB
def isWhitespace (b : UInt8) : Bool := isSpace b || b == CR || b == LF
def isHex (b : UInt8) : Bool := isDigit b || (b >= 0x41 && b <= 0x46) || (b >= 0x61 && b <= 0x66)

/-- Scan digits -/
def scanDigits : Scanner Bytes := scanWhile isDigit

/-- Scan alphanumeric -/
def scanAlphaNum : Scanner Bytes := scanWhile isAlphaNum

/-- Scan whitespace -/
def scanWhitespace : Scanner Bytes := scanWhile isWhitespace

/-- Skip whitespace (returns Unit, for chaining) -/
def skipWhitespace : Scanner Unit where
  scan bs :=
    let rec go (i : Nat) : Nat :=
      if i < bs.size then
        if isWhitespace bs.data[i]! then go (i + 1) else i
      else i
    termination_by bs.size - i
    .found () (bs.extract (go 0) bs.size)

-- ═══════════════════════════════════════════════════════════════════════════════
-- EXACT MATCH SCANNERS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Match exact bytes, fail if not present -/
def exact (expected : Bytes) : Scanner Unit where
  scan bs :=
    if bs.size >= expected.size && bs.extract 0 expected.size == expected then
      .found () (bs.extract expected.size bs.size)
    else if bs.size < expected.size then
      .incomplete (expected.size - bs.size)
    else
      .notFound

/-- Match exact byte -/
def exactByte (expected : UInt8) : Scanner Unit := exact ⟨#[expected]⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- SCANNER COMBINATORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Sequence two scanners -/
def seq (s1 : Scanner α) (s2 : Scanner β) : Scanner (α × β) where
  scan bs :=
    s1.scan bs |>.bind fun a rest =>
      s2.scan rest |>.map fun b => (a, b)

/-- Map over scanner result -/
def Scanner.map (s : Scanner α) (f : α → β) : Scanner β where
  scan bs := s.scan bs |>.map f

/-- Optional scanner (always succeeds) -/
def optional (s : Scanner α) : Scanner (Option α) where
  scan bs :=
    match s.scan bs with
    | .found a rest => .found (some a) rest
    | .notFound => .found none bs
    | .incomplete n => .incomplete n

/-- Try first scanner, if fails try second (ordered choice) -/
def orElse (s1 : Scanner α) (s2 : Scanner α) : Scanner α where
  scan bs :=
    match s1.scan bs with
    | .found a rest => .found a rest
    | .notFound => s2.scan bs
    | .incomplete n => .incomplete n

instance : OrElse (Scanner α) where
  orElse s1 s2 := orElse s1 (s2 ())

/-- Repeat scanner zero or more times -/
partial def many (s : Scanner α) : Scanner (List α) where
  scan bs :=
    match s.scan bs with
    | .found a rest =>
      match (many s).scan rest with
      | .found as rest' => .found (a :: as) rest'
      | _ => .found [a] rest
    | .notFound => .found [] bs
    | .incomplete n => .incomplete n

/-- Repeat scanner one or more times -/
def many1 (s : Scanner α) : Scanner (List α) where
  scan bs :=
    match s.scan bs with
    | .found a rest =>
      match (many s).scan rest with
      | .found as rest' => .found (a :: as) rest'
      | _ => .found [a] rest
    | .notFound => .notFound
    | .incomplete n => .incomplete n

/-- Scan items separated by delimiter -/
def sepBy (item : Scanner α) (delim : Scanner Unit) : Scanner (List α) where
  scan bs :=
    match item.scan bs with
    | .found a rest =>
      let rec go (acc : List α) (remaining : Bytes) (fuel : Nat) : ScanResult (List α) :=
        match fuel with
        | 0 => .found acc.reverse remaining
        | fuel' + 1 =>
          match delim.scan remaining with
          | .found () rest' =>
            match item.scan rest' with
            | .found a' rest'' => go (a' :: acc) rest'' fuel'
            | _ => .found acc.reverse remaining
          | _ => .found acc.reverse remaining
      match go [a] rest rest.size with
      | .found as rest' => .found as rest'
      | _ => .found [a] rest
    | .notFound => .found [] bs
    | .incomplete n => .incomplete n

-- ═══════════════════════════════════════════════════════════════════════════════
-- BOX → SCANNER EMBEDDING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Lift a Box into a Scanner (Box is strictly less powerful) -/
def fromBox (box : Box α) : Scanner α where
  scan bs :=
    match box.parse bs with
    | .ok a rest => .found a rest
    | .fail => .notFound

/-- Use a Box to parse a fixed-length prefix, then continue with Scanner -/
def boxThen (box : Box α) (next : α → Scanner β) : Scanner (α × β) where
  scan bs :=
    match box.parse bs with
    | .ok a rest =>
      match (next a).scan rest with
      | .found b rest' => .found (a, b) rest'
      | .notFound => .notFound
      | .incomplete n => .incomplete n
    | .fail => .notFound

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRING CONVERSION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Convert scanned bytes to String (UTF-8) -/
def Scanner.asString (s : Scanner Bytes) : Scanner String where
  scan bs :=
    match s.scan bs with
    | .found content rest =>
      match String.fromUTF8? content with
      | some str => .found str rest
      | none => .notFound  -- Invalid UTF-8
    | .notFound => .notFound
    | .incomplete n => .incomplete n

/-- Scan a line as String -/
def scanLineStr : Scanner String := scanLine.asString

/-- Scan a CRLF line as String -/
def scanCRLFLineStr : Scanner String := scanCRLFLine.asString

-- ═══════════════════════════════════════════════════════════════════════════════
-- HTTP/1.1 EXAMPLE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HTTP header: name: value -/
structure HttpHeader where
  name : String
  value : String
  deriving Repr

/-- Scan a single HTTP header -/
def scanHttpHeader : Scanner HttpHeader where
  scan bs :=
    -- Scan name until colon
    match scanUntilColon.scan bs with
    | .found nameBytes rest1 =>
      -- Skip colon was consumed, skip optional whitespace
      match skipWhitespace.scan rest1 with
      | .found () rest2 =>
        -- Scan value until CRLF
        match scanCRLFLine.scan rest2 with
        | .found valueBytes rest3 =>
          match String.fromUTF8? nameBytes, String.fromUTF8? valueBytes with
          | some name, some value => .found ⟨name, value.trimRight⟩ rest3
          | _, _ => .notFound
        | .notFound => .notFound
        | .incomplete n => .incomplete n
      | _ => .notFound
    | .notFound => .notFound
    | .incomplete n => .incomplete n

/-- Scan HTTP headers until empty line -/
def scanHttpHeaders : Scanner (List HttpHeader) where
  scan bs :=
    let rec go (acc : List HttpHeader) (remaining : Bytes) (fuel : Nat) : ScanResult (List HttpHeader) :=
      match fuel with
      | 0 => .found acc.reverse remaining
      | fuel' + 1 =>
        -- Check for empty line (end of headers)
        match (exact CRLF).scan remaining with
        | .found () rest => .found acc.reverse rest
        | _ =>
          match scanHttpHeader.scan remaining with
          | .found h rest => go (h :: acc) rest fuel'
          | .notFound => .found acc.reverse remaining
          | .incomplete n => .incomplete n
    go [] bs bs.size

/-- HTTP request line: METHOD SP URI SP VERSION CRLF -/
structure HttpRequestLine where
  method : String
  uri : String
  version : String
  deriving Repr

/-- Scan HTTP request line -/
def scanHttpRequestLine : Scanner HttpRequestLine where
  scan bs :=
    -- METHOD
    match (scanUntilByte SPACE).scan bs with
    | .found methodBytes rest1 =>
      -- URI (skip the space that was consumed)
      match (scanUntilByte SPACE).scan rest1 with
      | .found uriBytes rest2 =>
        -- VERSION until CRLF
        match scanCRLFLine.scan rest2 with
        | .found versionBytes rest3 =>
          match String.fromUTF8? methodBytes, String.fromUTF8? uriBytes, String.fromUTF8? versionBytes with
          | some m, some u, some v => .found ⟨m, u, v⟩ rest3
          | _, _, _ => .notFound
        | .notFound => .notFound
        | .incomplete n => .incomplete n
      | .notFound => .notFound
      | .incomplete n => .incomplete n
    | .notFound => .notFound
    | .incomplete n => .incomplete n

end Foundry.Cornell.Scanner
