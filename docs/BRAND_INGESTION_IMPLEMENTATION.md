━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // foundry // brand // implementation
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# BRAND INGESTION IMPLEMENTATION PLAN

**Status:** PLANNING
**Last Updated:** 2026-03-04
**Depends On:** libevring, slide, weapon-server-hs, trinity-engine-hs

────────────────────────────────────────────────────────────────────────────────
                                                              // table of contents
────────────────────────────────────────────────────────────────────────────────

1. Architecture Overview
2. Wire Format Specification
3. Machine Definition
4. Extension Integration
5. DuckDB Integration
6. Implementation Phases

────────────────────────────────────────────────────────────────────────────────
                                                                      // end toc
────────────────────────────────────────────────────────────────────────────────

## 1. Architecture Overview

### Data Flow

```
Chrome Extension (foundry-extension)
  │
  │ Binary wire format (NOT JSON)
  ▼
File: ~/.local/state/foundry/inbox/<domain>/<timestamp>.fwire
  │
  │ io_uring read via libevring
  ▼
BrandIngestMachine (Mealy machine, pure)
  │
  │ step :: State × Event → State × [Operation]
  ▼
DuckDB write via io_uring
  │
  ▼
File: ~/.local/state/foundry/brands/<domain>.duckdb
```

### Key Constraints

- **NO JSON in hot path** - Binary wire format only
- **Pure state machines** - No IO in step/generate functions
- **io_uring for all I/O** - Via libevring Machine pattern
- **weapon-server untouched** - We consume its APIs, not modify

### Repository Dependencies

| Repo | Purpose | Branch |
|------|---------|--------|
| `straylight-software/libevring` | io_uring Haskell bindings | main |
| `straylight-software/slide` | SIGIL wire format reference | main |
| `straylight-software/trinity-engine-hs` | io_uring runner | main |
| `straylight-software/weapon-server-hs` | API server (read-only) | main |

────────────────────────────────────────────────────────────────────────────────
                                                           // wire format spec
────────────────────────────────────────────────────────────────────────────────

## 2. Wire Format Specification (FWIRE)

Modeled after SIGIL wire format from slide. Optimized for 38-pillar brand data.

### Byte Layout

```
Header (16 bytes):
  [4 bytes] Magic: 0x46 0x57 0x49 0x52 ("FWIR")
  [1 byte]  Version: 0x01
  [1 byte]  Flags: reserved
  [2 bytes] Pillar count (uint16 BE)
  [8 bytes] Timestamp (uint64 BE, unix micros)

Domain Block:
  [2 bytes] Domain length (uint16 BE)
  [N bytes] Domain UTF-8 bytes

Pillar Blocks (repeated):
  [1 byte]  Pillar ID (0x00-0x25 for 38 pillars)
  [1 byte]  Encoding type:
              0x00 = raw bytes
              0x01 = varint-prefixed
              0x02 = nested pillar block
  [varint]  Data length
  [N bytes] Pillar data (pillar-specific encoding)
  
Footer:
  [4 bytes] CRC32 of all preceding bytes
```

### Pillar IDs

```
0x00 = color        0x0D = haptic       0x1A = brush
0x01 = dimension    0x0E = audio        0x1B = navigation
0x02 = geometry     0x0F = spatial      0x1C = brand
0x03 = typography   0x10 = accessibility 0x1D = scheduling
0x04 = surface      0x11 = sensation    0x1E = attestation
0x05 = elevation    0x12 = physics      0x1F = identity
0x06 = motion       0x13 = weather      0x20 = numeric
0x07 = temporal     0x14 = engineering  0x21 = element
0x08 = reactive     0x15 = physical     0x22 = canvas
0x09 = gestural     0x16 = game         0x23 = compute
0x0A = network      0x17 = epistemic    0x24 = gpu
0x0B = storage      0x18 = graph        0x25 = tensor
0x0C = media        0x19 = text
```

### Varint Encoding

Same as SIGIL/protobuf:
- 7 bits per byte, MSB = continuation flag
- Little-endian

### Color Pillar Data (0x00)

```
[1 byte]  Color count
Per color:
  [1 byte]  Role: 0=background, 1=foreground, 2=border, 3=accent
  [1 byte]  Space: 0=sRGB, 1=P3, 2=OKLCH, 3=LAB
  [4 bytes] Component 1 (float32 BE)
  [4 bytes] Component 2 (float32 BE)
  [4 bytes] Component 3 (float32 BE)
  [4 bytes] Alpha (float32 BE)
```

### Typography Pillar Data (0x03)

```
[1 byte]  Font count
Per font:
  [varint]  Family name length
  [N bytes] Family name UTF-8
  [2 bytes] Weight (uint16 BE, 100-900)
  [4 bytes] Size in px (float32 BE)
  [4 bytes] Line height ratio (float32 BE)
```

────────────────────────────────────────────────────────────────────────────────
                                                         // machine definition
────────────────────────────────────────────────────────────────────────────────

## 3. Machine Definition

Following the libevring/trinity-engine-hs pattern.

### BrandIngestMachine

```haskell
-- | Pure state machine for brand ingestion
data BrandIngestMachine = BrandIngestMachine
  { bimInboxDir  :: !FilePath
  , bimBrandDir  :: !FilePath
  }

-- | Machine state
data BrandIngestState
  = Scanning              -- Looking for new .fwire files
  | Reading !Handle !Int  -- Reading file, bytes remaining
  | Parsing !ByteString   -- Parsing complete file
  | Writing !Handle       -- Writing to DuckDB
  | Done
  deriving stock (Eq, Show)

instance Machine BrandIngestMachine where
  type State BrandIngestMachine = BrandIngestState
  
  initial _ = Scanning
  
  step machine state event = case state of
    Scanning -> handleScanResult machine event
    Reading h remaining -> handleReadResult machine h remaining event
    Parsing bytes -> handleParseResult machine bytes
    Writing h -> handleWriteResult machine h event
    Done -> StepResult Done []
  
  done _ Done = True
  done _ _    = False
```

### Operations Emitted

```haskell
-- Scanning phase
makeOpenat dirFd ".fwire" O_RDONLY

-- Reading phase  
makeRead fd buffer offset length

-- Writing phase (DuckDB)
makeOpenat dbDir "domain.duckdb" O_WRONLY
makeWrite dbFd encodedRow offset length
makeFsync dbFd
makeClose dbFd
```

### Replay Testing

```haskell
-- Deterministic replay for testing
testIngest :: [Event] -> BrandIngestState
testIngest events = replay brandMachine events

-- Property: same events → same final state
prop_deterministic :: [Event] -> Bool
prop_deterministic events = 
  replay m events == replay m events
  where m = BrandIngestMachine "/inbox" "/brands"
```

────────────────────────────────────────────────────────────────────────────────
                                                      // extension integration
────────────────────────────────────────────────────────────────────────────────

## 4. Extension Integration

The Chrome extension writes FWIRE binary files directly to disk.

### File Location

```
~/.local/state/foundry/inbox/<domain>/<timestamp>.fwire

Example:
~/.local/state/foundry/inbox/linear.app/1709571234567890.fwire
```

### JavaScript Encoder

Location: `purescript/foundry-extension/extension/extraction/fwire.js`

```javascript
// FWIRE encoder for Chrome extension
export function encodeFWIRE(extraction) {
  const encoder = new FWIREEncoder();
  
  // Header
  encoder.writeBytes([0x46, 0x57, 0x49, 0x52]); // Magic
  encoder.writeUint8(0x01);                      // Version
  encoder.writeUint8(0x00);                      // Flags
  encoder.writeUint16BE(extraction.pillarCount);
  encoder.writeUint64BE(Date.now() * 1000);      // Micros
  
  // Domain
  encoder.writeLengthPrefixedUTF8(extraction.domain);
  
  // Pillars
  for (const [id, data] of extraction.pillars) {
    encoder.writeUint8(id);
    encoder.writeUint8(0x01);  // varint-prefixed
    encoder.writeVarintPrefixedBytes(data);
  }
  
  // Footer CRC32
  encoder.writeCRC32();
  
  return encoder.toArrayBuffer();
}
```

### Native Messaging (Future)

For direct io_uring integration, use Chrome Native Messaging:

```
Extension → Native Host (Haskell) → io_uring write
```

But MVP: Extension uses `chrome.downloads.download()` or 
`navigator.storage` to write to known location.

────────────────────────────────────────────────────────────────────────────────
                                                         // duckdb integration
────────────────────────────────────────────────────────────────────────────────

## 5. DuckDB Integration

DuckDB is embedded - no server, direct file I/O via io_uring.

### Schema

```sql
-- Atoms table (colors, fonts, spacing primitives)
CREATE TABLE atoms (
  id UUID PRIMARY KEY,           -- UUID5 from domain:pillar:hash
  domain TEXT NOT NULL,
  pillar_id UINT8 NOT NULL,      -- 0x00-0x25
  atom_type TEXT NOT NULL,
  data BLOB NOT NULL,            -- Binary pillar data
  created_at TIMESTAMP DEFAULT NOW()
);

-- Elements table (DOM elements with pillar refs)  
CREATE TABLE elements (
  id UUID PRIMARY KEY,
  domain TEXT NOT NULL,
  selector TEXT NOT NULL,
  parent_id UUID,
  depth UINT16 NOT NULL,
  atom_ids UUID[] NOT NULL,      -- References to atoms
  created_at TIMESTAMP DEFAULT NOW()
);

-- Brands table (complete brand extractions)
CREATE TABLE brands (
  id UUID PRIMARY KEY,           -- UUID5 from domain
  domain TEXT NOT NULL UNIQUE,
  extraction_count UINT32,
  last_extracted TIMESTAMP,
  fwire_hash BLOB NOT NULL       -- SHA256 of latest .fwire
);

CREATE INDEX idx_atoms_domain ON atoms(domain);
CREATE INDEX idx_elements_domain ON elements(domain);
```

### Write Path

```haskell
-- DuckDB write via io_uring (through libevring)
writeBrandToDuckDB :: Handle -> CompleteBrand -> [Operation]
writeBrandToDuckDB dbFd brand =
  [ makeWrite dbFd atomsPage 0 atomsLen
  , makeWrite dbFd elementsPage atomsLen elementsLen
  , makeFsync dbFd
  ]
```

### Read Path (for COMPASS export)

```haskell
-- Read brand for export
readBrandFromDuckDB :: Handle -> Domain -> [Operation]
readBrandFromDuckDB dbFd domain =
  [ makeRead dbFd buffer 0 pageSize ]
```

────────────────────────────────────────────────────────────────────────────────
                                                      // implementation phases
────────────────────────────────────────────────────────────────────────────────

## 6. Implementation Phases

### Phase 1: FWIRE Format (1-2 days)

- [ ] Define FWIRE types in `foundry-core`
- [ ] Implement encoder in JS (`fwire.js`)
- [ ] Implement decoder in Haskell
- [ ] Property tests: encode → decode = identity

Files:
```
haskell/foundry-core/src/Foundry/Core/Wire/
  Types.hs      -- FWIRE types
  Encode.hs     -- Binary encoding
  Decode.hs     -- Binary decoding
  Varint.hs     -- Varint codec

purescript/foundry-extension/extension/extraction/
  fwire.js      -- JS encoder
```

### Phase 2: Machine Definition (1-2 days)

- [ ] Define `BrandIngestMachine` 
- [ ] Implement state transitions
- [ ] Wire to libevring operations
- [ ] Replay tests

Files:
```
haskell/foundry-core/src/Foundry/Core/Machine/
  BrandIngest.hs   -- Machine definition
  
haskell/foundry-core/test/Test/Foundry/Core/Machine/
  BrandIngestSpec.hs  -- Replay tests
```

### Phase 3: Extension Output (1 day)

- [ ] Integrate FWIRE encoder into extraction pipeline
- [ ] Write to `~/.local/state/foundry/inbox/`
- [ ] Test on real sites

Files:
```
purescript/foundry-extension/extension/extraction/
  index.js    -- Add FWIRE output path
  fwire.js    -- Encoder implementation
```

### Phase 4: DuckDB Storage (2-3 days)

- [ ] Create DuckDB schema
- [ ] Implement write operations
- [ ] Wire through io_uring
- [ ] Integration tests

Files:
```
haskell/foundry-storage/src/Foundry/Storage/
  DuckDB.hs       -- Replace stubs with real impl
  DuckDB/
    Schema.hs     -- DDL
    Write.hs      -- io_uring writes
    Read.hs       -- io_uring reads
```

### Phase 5: End-to-End (1 day)

- [ ] Run full pipeline: extension → FWIRE → machine → DuckDB
- [ ] Test with 4 golden sites (linear, coca-cola, etc.)
- [ ] Performance benchmarks

### Phase 6: JSON Purge (2-3 days)

- [ ] Remove 671 Aeson instances from foundry-*
- [ ] Replace with binary serialization
- [ ] Update all tests

────────────────────────────────────────────────────────────────────────────────
                                                                    // summary
────────────────────────────────────────────────────────────────────────────────

**Total Estimate:** 8-12 days

**Critical Path:**
1. FWIRE format must be stable before extension work
2. Machine definition must be pure (no IO in step)
3. DuckDB writes must go through io_uring

**Non-Goals:**
- JSON anywhere in hot path
- Modifying weapon-server-hs
- Server-side scraping (extension only)

────────────────────────────────────────────────────────────────────────────────
                                                          // foundry // 2026-03-04
────────────────────────────────────────────────────────────────────────────────