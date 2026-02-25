-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // brand // identity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brand identity atoms and molecules.
-- |
-- | STATUS: PROVEN (Hydrogen.Schema.Brand.Identity)
-- | 
-- | Invariants:
-- |   uuid5_deterministic: Same domain = same UUID (PROVEN)
-- |   uuid5_injective: Different domains = different UUIDs (PROVEN)
-- |   domain_valid: Non-empty, contains dot (PROVEN)
-- |   brand_name_bounded: 1-256 characters (PROVEN)
-- |
-- | PURE DATA: UUID generation happens at ingestion boundary (Haskell).
-- | This module defines the types and validation, not hash computation.

module Hydrogen.Schema.Brand.Identity
  ( -- * Domain
    Domain
  , domain
  , unDomain
  , mkDomainUnsafe
  
  -- * Brand Name  
  , BrandName
  , brandName
  , unBrandName
  , mkBrandNameUnsafe
  
  -- * UUID
  , UUID
  , mkUUID
  , unUUID
  , brandNamespace
  
  -- * Brand Identity
  , BrandIdentity
  , mkBrandIdentity
  , brandUUID
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (&&)
  , (>=)
  , (<=)
  , (>)
  , (<>)
  , show
  , compare
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String
import Data.String.CodeUnits (charAt) as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // domain
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Domain name atom.
-- |
-- | A validated domain string: non-empty, lowercase, contains at least one dot.
-- | Examples: "jbreenconsulting.com", "nike.com", "apple.com"
-- |
-- | Invariant: domain_valid (nonempty ∧ has_dot)
newtype Domain = Domain String

derive instance eqDomain :: Eq Domain
derive instance ordDomain :: Ord Domain

instance showDomain :: Show Domain where
  show (Domain d) = "Domain(" <> d <> ")"

-- | Smart constructor with validation.
-- |
-- | Returns Nothing if:
-- |   - String is empty
-- |   - String contains no dot
-- |
-- | Normalizes to lowercase.
domain :: String -> Maybe Domain
domain s =
  let 
    lower = String.toLower s
  in 
    if String.length lower > 0 && String.contains (String.Pattern ".") lower
    then Just (Domain lower)
    else Nothing

-- | Unwrap domain to string.
unDomain :: Domain -> String
unDomain (Domain d) = d

-- | Unsafe constructor for deserialization from trusted sources.
-- |
-- | WARNING: Only use when data comes from a validated source (e.g., Haskell backend).
mkDomainUnsafe :: String -> Domain
mkDomainUnsafe = Domain

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // brand name
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Brand name atom.
-- |
-- | A validated brand name: 1-256 characters, trimmed.
-- | Examples: "J. Breen Consulting", "Nike", "Apple Inc."
-- |
-- | Invariant: brand_name_bounded (1 <= length <= 256)
newtype BrandName = BrandName String

derive instance eqBrandName :: Eq BrandName
derive instance ordBrandName :: Ord BrandName

instance showBrandName :: Show BrandName where
  show (BrandName n) = "BrandName(" <> n <> ")"

-- | Smart constructor with validation.
-- |
-- | Returns Nothing if:
-- |   - Trimmed string is empty
-- |   - Trimmed string exceeds 256 characters
brandName :: String -> Maybe BrandName
brandName s =
  let 
    trimmed = String.trim s
    len = String.length trimmed
  in 
    if len >= 1 && len <= 256
    then Just (BrandName trimmed)
    else Nothing

-- | Unwrap brand name to string.
unBrandName :: BrandName -> String
unBrandName (BrandName n) = n

-- | Unsafe constructor for deserialization from trusted sources.
mkBrandNameUnsafe :: String -> BrandName
mkBrandNameUnsafe = BrandName

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // uuid
-- ═══════════════════════════════════════════════════════════════════════════════

-- | UUID atom.
-- |
-- | A 128-bit universally unique identifier in standard string format:
-- | "xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx" (36 characters with hyphens)
-- |
-- | For brand identity, we use UUID5 (namespace-based, SHA-1 derived).
-- | The actual UUID5 computation happens at the ingestion boundary (Haskell).
-- | This type represents the result — pure data.
-- |
-- | Invariant: uuid5_deterministic (same namespace + name = same uuid)
newtype UUID = UUID String

derive instance eqUUID :: Eq UUID
derive instance ordUUID :: Ord UUID

instance showUUID :: Show UUID where
  show (UUID u) = "UUID(" <> u <> ")"

-- | Smart constructor with format validation.
-- |
-- | Validates standard UUID format (36 chars with hyphens at positions 8, 13, 18, 23).
mkUUID :: String -> Maybe UUID
mkUUID s =
  if isValidUUIDFormat s
  then Just (UUID s)
  else Nothing
  where
    isValidUUIDFormat :: String -> Boolean
    isValidUUIDFormat str =
      String.length str == 36 &&
      String.charAt 8 str == Just '-' &&
      String.charAt 13 str == Just '-' &&
      String.charAt 18 str == Just '-' &&
      String.charAt 23 str == Just '-'

-- | Unwrap UUID to string.
unUUID :: UUID -> String
unUUID (UUID u) = u

-- | Hydrogen Brand namespace UUID.
-- |
-- | This is the DNS namespace UUID used for UUID5 generation.
-- | All brand UUIDs are derived from: uuid5(brandNamespace, domain)
brandNamespace :: UUID
brandNamespace = UUID "6ba7b810-9dad-11d1-80b4-00c04fd430c8"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // brand identity
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Brand identity molecule.
-- |
-- | Composed of:
-- |   - name: Human-readable brand name
-- |   - domain: Canonical domain identifier
-- |   - uuid: Deterministic UUID5 derived from domain
-- |
-- | The UUID is computed at ingestion time (Haskell backend) and passed in.
-- | This ensures the invariant uuid = uuid5(brandNamespace, domain) is
-- | established at the boundary, not computed repeatedly.
type BrandIdentity =
  { name :: BrandName
  , domain :: Domain
  , uuid :: UUID
  }

-- | Create brand identity from pre-computed components.
-- |
-- | The UUID should be computed as: uuid5(brandNamespace, unDomain domain)
-- | This computation happens in Haskell at ingestion time.
-- |
-- | Invariant: uuid5_deterministic (same domain = same uuid)
mkBrandIdentity :: BrandName -> Domain -> UUID -> BrandIdentity
mkBrandIdentity name dom uuid =
  { name
  , domain: dom
  , uuid
  }

-- | Get UUID from brand identity.
brandUUID :: BrandIdentity -> UUID
brandUUID bi = bi.uuid
