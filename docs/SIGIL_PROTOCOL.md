# SIGIL Protocol Specification

**Streaming Inference Grammar Interface Language**

SIGIL is the attestation layer for AI infrastructure - a verified wire format for streaming LLM tokens with semantic mode tracking. This document describes the protocol design, wire format, and reset-on-ambiguity semantics.

## Design Philosophy

SIGIL enforces a strict discipline: **ambiguity must reset the connection**. When parsing upstream data (SSE, JSON, tool calls), any ambiguity triggers a full state reset rather than "best effort" parsing.

Why this matters:
1. **Trustworthy AI** - malformed input cannot corrupt reasoning chains
2. **Epistemic hygiene** - if parse is ambiguous, you don't know what you thought
3. **Future memory systems** - corrupted parse leads to corrupted memory leads to corrupted identity

## Wire Format

### Byte Encoding

SIGIL uses a compact byte encoding optimized for LLM token streams:

```
0xxxxxxx  = hot token (ID in lower 7 bits, 0x00-0x7E)
10xxxxxx  = extended token (varint follows)
1100xxxx  = stream control (0xC0-0xCF)
```

### Hot Tokens (0x00-0x7E)

The 127 most frequent tokens get single-byte encoding. These are typically common words, punctuation, and whitespace. The token ID is the byte value directly.

### Extended Tokens (0x80-0xBF)

Less frequent tokens use a two-part encoding:
1. Marker byte (0x80-0xBF) - upper 6 bits are part of the token ID
2. LEB128 varint - remaining bits of the token ID

This allows token IDs up to 2^32 while keeping common tokens compact.

### Control Opcodes (0xC0-0xCF)

| Opcode | Byte | Description |
|--------|------|-------------|
| CHUNK_END | 0xC0 | End of semantic chunk |
| TOOL_CALL_START | 0xC1 | Begin tool call block |
| TOOL_CALL_END | 0xC2 | End tool call block |
| THINK_START | 0xC3 | Begin thinking block |
| THINK_END | 0xC4 | End thinking block |
| CODE_BLOCK_START | 0xC5 | Begin code block |
| CODE_BLOCK_END | 0xC6 | End code block |
| FLUSH | 0xC7 | Flush (chunk incomplete) |
| Reserved | 0xC8-0xCE | Reserved for future use |
| STREAM_END | 0xCF | End of stream |

## Parse Modes

The decoder tracks semantic context through parse modes:

| Mode | Description |
|------|-------------|
| `text` | Normal text output (default) |
| `think` | Thinking/reasoning block (may be hidden from user) |
| `toolCall` | Tool call JSON (must parse as valid JSON) |
| `codeBlock` | Code block content |

### Mode Transitions

Valid transitions:
- `text` → any other mode (via START opcode)
- any mode → `text` (via matching END opcode)

Invalid transitions trigger reset:
- Starting a mode while not in `text` (nested modes)
- Ending a mode you're not in (unmatched end)

## Reset-on-Ambiguity

### StrictParseResult

Unlike binary ok/fail parsing, SIGIL uses a three-way result:

```lean
inductive StrictParseResult (α : Type) where
  | ok : α → Bytes → StrictParseResult α        -- Unambiguous success
  | incomplete : StrictParseResult α             -- Need more bytes
  | ambiguous : AmbiguityReason → StrictParseResult α  -- Reset required
```

The key insight: `incomplete` is fine (wait for more data), but `ambiguous` must trigger a full state reset.

### Ambiguity Reasons

```lean
inductive AmbiguityReason where
  | unmatchedModeEnd : ParseMode → AmbiguityReason      -- End without matching start
  | nestedModeStart : ParseMode → ParseMode → AmbiguityReason  -- Mode in non-text
  | reservedOpcode : UInt8 → AmbiguityReason            -- Reserved opcode used
  | varintOverflow : AmbiguityReason                     -- Token ID > 2^32
  | jsonStructural : String → AmbiguityReason            -- Bad JSON in tool call
  | sseFraming : String → AmbiguityReason                -- SSE framing error
  | upstreamError : String → AmbiguityReason             -- In-band error signal
```

### The Ground State

The `initDecodeState` is the unique ground state:

```lean
def initDecodeState : DecodeState := {
  parseMode := .text
  buffer := []
  leftover := ByteArray.empty
}
```

Reset always produces this exact state - no information leaks across ambiguity boundaries.

## Verified Properties

Cornell proves 18 theorems about SIGIL with 0 sorry (unproven assumptions):

### Core Reset Theorems

| Theorem | Property |
|---------|----------|
| `reset_is_ground` | Reset always produces `initDecodeState` |
| `ground_unique` | All resets produce the same state |
| `reset_idempotent` | `reset(reset(s)) = reset(s)` |
| `no_leakage` | Different states reset to identical states |
| `reset_erases_mode` | Mode is `text` after reset |
| `reset_erases_buffer` | Buffer is empty after reset |
| `reset_erases_leftover` | Leftover is empty after reset |

### Mode Transition Theorems

| Theorem | Property |
|---------|----------|
| `nested_start_ambiguous` | Nested mode starts are detected |
| `mismatched_end_ambiguous` | Mismatched mode ends are detected |

### handleControl Theorems

| Theorem | Property |
|---------|----------|
| `handleControl_reserved_resets` | Reserved opcodes reset to init |
| `handleControl_toolCallStart_think_resets` | toolCallStart in think mode resets |
| `handleControl_toolCallStart_toolCall_resets` | toolCallStart in toolCall mode resets |
| `handleControl_toolCallStart_codeBlock_resets` | toolCallStart in codeBlock mode resets |
| `handleControl_toolCallEnd_text_resets` | toolCallEnd in text mode resets |
| `handleControl_toolCallEnd_think_resets` | toolCallEnd in think mode resets |
| `handleControl_toolCallEnd_codeBlock_resets` | toolCallEnd in codeBlock mode resets |
| `handleControl_ambiguity_is_ground` | Ambiguity always produces ground state |

## Code Generation

Cornell generates verified implementations:

### C++ (evring/sigil.h)

```cpp
#include "straylight/evring/sigil.h"

// Satisfies evring::machine concept
static_assert(evring::machine<evring::sigil::sigil_machine>);

// Use the machine
evring::sigil::sigil_machine decoder;
auto [new_state, ops] = decoder.step(state, byte_event);
```

### Haskell (Evring/Sigil.hs)

```haskell
import Evring.Sigil (SigilMachine, initSigilState, stepSigil)

-- Machine instance
instance Machine SigilMachine

-- Use the machine
let (newState, ops) = stepSigil state byteEvent
```

## Example: Decoding a Stream

```
Input bytes: [0x48, 0x65, 0x6C, 0x6C, 0x6F, 0xC3, 0x01, 0x02, 0xC4, 0xC0]
             "H"   "e"   "l"   "l"   "o"   THINK  tok   tok   /THINK CHUNK

Decode trace:
  state: text, buffer: []
  0x48 → text, buffer: [72]
  0x65 → text, buffer: [72, 101]
  0x6C → text, buffer: [72, 101, 108]
  0x6C → text, buffer: [72, 101, 108, 108]
  0x6F → text, buffer: [72, 101, 108, 108, 111]
  0xC3 → think, buffer: [], emit: Chunk{text: [72,101,108,108,111], complete: false}
  0x01 → think, buffer: [1]
  0x02 → think, buffer: [1, 2]
  0xC4 → text, buffer: [], emit: Chunk{think: [1, 2], complete: true}
  0xC0 → text, buffer: [], emit: Chunk{text: [], complete: true}
```

## Example: Ambiguity Reset

```
Input bytes: [0x48, 0xC3, 0x01, 0xC1, ...]
             "H"   THINK  tok   TOOL_START  ← nested mode!

Decode trace:
  state: text, buffer: []
  0x48 → text, buffer: [72]
  0xC3 → think, buffer: [], emit: Chunk{text: [72], complete: false}
  0x01 → think, buffer: [1]
  0xC1 → AMBIGUITY: nestedModeStart(think, toolCall)
         Reset to initDecodeState
         emit: Chunk{ambiguityReset: nestedModeStart(think, toolCall)}
```

## Integration with Agentic Systems

SIGIL is designed for agentic LLM systems where:

1. **Tool calls must be trustworthy** - JSON in toolCall mode is parsed; structural errors reset
2. **Thinking may be private** - think blocks can be filtered before presenting to user
3. **Streaming is first-class** - incomplete parses wait for more data
4. **Ambiguity is fatal** - corrupted state cannot propagate

The reset-on-ambiguity discipline ensures that an agent can trust its own reasoning chain. If parsing ever becomes ambiguous, the agent returns to a known-good state rather than proceeding with potentially corrupted data.
