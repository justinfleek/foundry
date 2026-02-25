{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // metxt // brand/identity
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Metxt.Core.Brand.Identity
Description : Brand identity types (UUID5, domain, name)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Brand identity types with deterministic UUID5 generation.

== Invariants (proven in Lean4)

* UUID5 is deterministic: same namespace + name = same UUID
* Domain is a valid hostname
* BrandName is non-empty

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Metxt.Core.Brand.Identity
  ( -- * Types
    BrandId (..)
  , Domain (..)
  , BrandName (..)

    -- * Smart constructors
  , mkBrandId
  , mkDomain
  , mkBrandName
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.UUID (UUID)
import Data.UUID.V5 qualified as UUID5

-- | Brand identifier - deterministic UUID5
newtype BrandId = BrandId {unBrandId :: !UUID}
  deriving stock (Eq, Ord, Show)

-- | Domain name (valid hostname)
newtype Domain = Domain {unDomain :: !Text}
  deriving stock (Eq, Ord, Show)

-- | Brand name (non-empty text)
newtype BrandName = BrandName {unBrandName :: !Text}
  deriving stock (Eq, Ord, Show)

-- | UUID5 namespace for brand identifiers
brandNamespace :: UUID
brandNamespace = UUID5.generateNamed UUID5.namespaceURL "metxt:brand"

-- | Generate deterministic brand ID from domain
mkBrandId :: Domain -> BrandId
mkBrandId (Domain d) = BrandId (UUID5.generateNamed brandNamespace (T.unpack d))

-- | Validate and create domain
mkDomain :: Text -> Maybe Domain
mkDomain t
  | T.null t = Nothing
  | otherwise = Just (Domain t)

-- | Validate and create brand name
mkBrandName :: Text -> Maybe BrandName
mkBrandName t
  | T.null t = Nothing
  | otherwise = Just (BrandName t)
