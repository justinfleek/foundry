/-
  Cornell - Verified Parsing at Three Power Levels
  
  Named after Joseph Cornell's shadow boxes from Count Zero.
  
  ## Parser Power Hierarchy
  
  ```
  Box < Scanner < Parser
  ```
  
  - **Box** (LL(0) + dep): Bidirectional codecs for binary formats
    - Roundtrip proof: `parse (serialize a) = a`
    - Consumption proof: `parse (serialize a ++ extra) = (a, extra)`
    - Use for: Git pack, protobuf, Nix wire, binary formats
  
  - **Scanner** (LL(0) + delimiters): One-way parsing for text protocols
    - Delimiter-based: scan until `\r\n`, `:`, etc.
    - Uniqueness proof: at most one parse result
    - Use for: HTTP/1.1, PEM, CSV, line protocols
  
  - **Parser** (LL(k)): Grammar-based parsing for structured text
    - Explicit lookahead, ordered choice
    - Unambiguity proof, FIRST/FOLLOW analysis
    - Use for: JSON, YAML, config files, DSLs
  
  ## Embedding
  
  Each level can embed the one below:
  - `Scanner.fromBox`: Use a Box within a Scanner
  - `Parser.fromScanner`: Use a Lexer (Scanner) to produce tokens
  
  ## Modules
  
  - `Cornell.Basic`: Box primitives and combinators
  - `Cornell.Scanner`: Delimiter-based text scanning
  - `Cornell.Parser`: LL(k) grammar parsing
  - `Cornell.Protocol`: Length-prefixed framing (shared by Git, Nix)
  - `Cornell.Nix`: Nix daemon wire format
  - `Cornell.Git`: Git pack/index format
  - `Cornell.GitTransport`: Git smart HTTP protocol
  - `Cornell.Protobuf`: Protobuf/gRPC wire format
  - `Cornell.StateMachine`: Verified protocol state machines
-/

import Foundry.Cornell.Basic
import Foundry.Cornell.Scanner
import Foundry.Cornell.Parser
import Foundry.Cornell.Protocol
import Foundry.Cornell.Nix
import Foundry.Cornell.Git
import Foundry.Cornell.GitTransport
import Foundry.Cornell.Protobuf
import Foundry.Cornell.StateMachine

-- The imports above bring all Cornell.* namespaces into scope.
-- Users can access types via:
--   - Cornell.Bytes, Cornell.Box (from Cornell.Proofs via Cornell.Basic)
--   - Cornell.Scanner.* 
--   - Cornell.Parser.*
--   - Cornell.StateMachine.*
-- etc.
