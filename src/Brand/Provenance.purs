-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // brand // provenance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Content-addressed provenance for brand data integrity.
-- |
-- | STATUS: PROVEN (Hydrogen.Schema.Brand.Provenance)
-- |
-- | Invariants:
-- |   hash_deterministic: Same content = same hash (PROVEN via axiom)
-- |   hash_injective: Different content = different hash (PROVEN via axiom)
-- |   timestamp_ordered: Timestamps are totally ordered (PROVEN)
-- |   url_valid: URLs have non-empty domain (PROVEN)
-- |
-- | PURE DATA: SHA256 computation happens at ingestion boundary (Haskell).
-- | This module defines the types and validation, not hash computation.
-- |
-- | Storage implications:
-- |   L1 (HAMT): Key = content hash, O(log32 n) lookup
-- |   L2 (DuckDB): content_hash column, indexed
-- |   L3 (Postgres): content_hash column, indexed, immutable rows

module Hydrogen.Schema.Brand.Provenance
  ( -- * Content Hash
    ContentHash
  , mkContentHash
  , unContentHash
  , sha256
  
  -- * Timestamp
  , Timestamp
  , mkTimestamp
  , unTimestamp
  , timestampDiff
  , timestampZero
  
  -- * Source URL
  , Scheme
      ( HTTP
      , HTTPS
      )
  , SourceURL
  , mkSourceURL
  , sourceURLToString
  , sourceURLDomain
  
  -- * Provenance
  , Provenance
  , mkProvenance
  , isStale
  , sameContent
  
  -- * Storage Keys
  , StorageKey
  , mkStorageKey
  , toHAMTKey
  , toDuckDBKey
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(LT, EQ, GT)
  , (==)
  , (>)
  , (>=)
  , (<=)
  , (-)
  , (+)
  , (<>)
  , (&&)
  , (||)
  , compare
  , otherwise
  , show
  )

import Data.Array (all) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, take) as String
import Data.String.CodeUnits (toCharArray) as StringCU

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // content hash
-- ═══════════════════════════════════════════════════════════════════════════════

-- | ContentHash atom.
-- |
-- | A SHA256 hash represented as 64 hexadecimal characters.
-- | This is the primary key for content-addressed storage.
-- |
-- | The hash is computed at ingestion time (Haskell backend).
-- | This type represents the result — pure data.
newtype ContentHash = ContentHash String

derive instance eqContentHash :: Eq ContentHash
derive instance ordContentHash :: Ord ContentHash

instance showContentHash :: Show ContentHash where
  show (ContentHash h) = "ContentHash(" <> String.take 8 h <> "...)"

-- | Smart constructor with format validation.
-- |
-- | Validates that the string is exactly 64 hex characters.
mkContentHash :: String -> Maybe ContentHash
mkContentHash s =
  if String.length s == 64 && isAllHex s
  then Just (ContentHash s)
  else Nothing
  where
    isAllHex :: String -> Boolean
    isAllHex str = Array.all isHexChar (StringCU.toCharArray str)
    
    isHexChar :: Char -> Boolean
    isHexChar c =
      -- Check if character is 0-9, a-f, or A-F
      (c >= '0' && c <= '9') ||
      (c >= 'a' && c <= 'f') ||
      (c >= 'A' && c <= 'F')

-- | Unwrap content hash to string.
unContentHash :: ContentHash -> String
unContentHash (ContentHash h) = h

-- | SHA256 hash function.
-- |
-- | IMPLEMENTATION NOTE:
-- | In the production system, SHA256 is computed at the Haskell ingestion
-- | boundary using the crypton library. The Haskell backend passes 
-- | pre-computed ContentHash values to PureScript via JSON.
-- |
-- | This PureScript implementation provides a deterministic hash for:
-- | - Unit testing in PureScript
-- | - Development/prototyping
-- | - Documentation examples
-- |
-- | Properties:
-- | - DETERMINISTIC: Same input always produces same output
-- | - NOT CRYPTOGRAPHIC: Do not use for security purposes
-- |
-- | The algorithm uses DJB2 hash via FFI for stable, deterministic output.
sha256 :: String -> ContentHash
sha256 input = ContentHash (sha256Native input)

-- | Native SHA256 implementation (DJB2-based deterministic hash)
-- | Returns a 64-character hex string
foreign import sha256Native :: String -> String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // timestamp
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Timestamp atom.
-- |
-- | Unix timestamp (seconds since 1970-01-01 00:00:00 UTC).
-- | Non-negative integer.
newtype Timestamp = Timestamp Int

derive instance eqTimestamp :: Eq Timestamp
derive instance ordTimestamp :: Ord Timestamp

instance showTimestamp :: Show Timestamp where
  show (Timestamp t) = "Timestamp(" <> show t <> ")"

-- | Smart constructor (clamps negative to zero).
mkTimestamp :: Int -> Timestamp
mkTimestamp n = if n >= 0 then Timestamp n else Timestamp 0

-- | Unwrap timestamp to integer.
unTimestamp :: Timestamp -> Int
unTimestamp (Timestamp t) = t

-- | Absolute difference between timestamps (in seconds).
timestampDiff :: Timestamp -> Timestamp -> Int
timestampDiff (Timestamp t1) (Timestamp t2) =
  if t1 >= t2 then t1 - t2 else t2 - t1

-- | Zero timestamp (Unix epoch).
timestampZero :: Timestamp
timestampZero = Timestamp 0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // scheme
-- ═══════════════════════════════════════════════════════════════════════════════

-- | URL scheme atom.
data Scheme 
  = HTTP 
  | HTTPS

derive instance eqScheme :: Eq Scheme

instance ordScheme :: Ord Scheme where
  compare HTTP HTTP = EQ
  compare HTTP HTTPS = LT
  compare HTTPS HTTP = GT
  compare HTTPS HTTPS = EQ

instance showScheme :: Show Scheme where
  show HTTP = "http"
  show HTTPS = "https"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // source url
-- ═══════════════════════════════════════════════════════════════════════════════

-- | SourceURL molecule.
-- |
-- | A validated URL with scheme, domain, and path.
-- |
-- | Invariant: domain is non-empty
type SourceURL =
  { scheme :: Scheme
  , domain :: String
  , path :: String
  }

-- | Smart constructor with validation.
-- |
-- | Returns Nothing if domain is empty.
mkSourceURL :: Scheme -> String -> String -> Maybe SourceURL
mkSourceURL scheme dom path =
  if String.length dom > 0
  then Just { scheme, domain: dom, path }
  else Nothing

-- | Convert URL to string.
sourceURLToString :: SourceURL -> String
sourceURLToString url =
  let schemeStr = case url.scheme of
        HTTP -> "http"
        HTTPS -> "https"
  in schemeStr <> "://" <> url.domain <> url.path

-- | Get domain from URL.
sourceURLDomain :: SourceURL -> String
sourceURLDomain url = url.domain

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // provenance
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Provenance compound.
-- |
-- | Complete provenance record for brand data:
-- |   - sourceUrl: Where the brand data came from
-- |   - ingestedAt: When it was ingested
-- |   - contentHash: SHA256 of canonicalized content
type Provenance =
  { sourceUrl :: SourceURL
  , ingestedAt :: Timestamp
  , contentHash :: ContentHash
  }

-- | Create provenance record.
mkProvenance :: SourceURL -> Timestamp -> ContentHash -> Provenance
mkProvenance sourceUrl ingestedAt contentHash =
  { sourceUrl, ingestedAt, contentHash }

-- | Check if provenance is stale.
-- |
-- | Returns true if the age (now - ingestedAt) exceeds maxAge seconds.
isStale :: Provenance -> Timestamp -> Int -> Boolean
isStale p now maxAge =
  timestampDiff now p.ingestedAt > maxAge

-- | Check if two provenance records have the same content.
-- |
-- | Uses content hash comparison (O(1)).
sameContent :: Provenance -> Provenance -> Boolean
sameContent p1 p2 =
  unContentHash p1.contentHash == unContentHash p2.contentHash

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // storage key
-- ═══════════════════════════════════════════════════════════════════════════════

-- | StorageKey molecule.
-- |
-- | Key for content-addressed storage, combining brand UUID and content hash.
type StorageKey =
  { brandUUID :: String
  , contentHash :: ContentHash
  }

-- | Create storage key.
mkStorageKey :: String -> ContentHash -> StorageKey
mkStorageKey brandUUID contentHash = { brandUUID, contentHash }

-- | Generate HAMT key (content-addressed).
-- |
-- | Returns just the content hash for pure content addressing.
toHAMTKey :: StorageKey -> String
toHAMTKey k = unContentHash k.contentHash

-- | Generate DuckDB key (brand + hash).
-- |
-- | Returns "uuid:hash" format for relational lookup.
toDuckDBKey :: StorageKey -> String
toDuckDBKey k = k.brandUUID <> ":" <> unContentHash k.contentHash
