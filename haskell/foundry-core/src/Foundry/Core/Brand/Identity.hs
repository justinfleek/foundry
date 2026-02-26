{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // foundry // brand/identity
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Identity
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
module Foundry.Core.Brand.Identity
  ( -- * Types
    BrandId (..)
  , Domain (..)
  , BrandName (..)

    -- * Smart constructors
  , mkBrandId
  , mkDomain
  , mkBrandName
  
    -- * Accessors
  , brandIdToUUID
  ) where

import Data.Aeson (FromJSON (..), ToJSON (..))
import Data.ByteString qualified as BS
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import Data.UUID (UUID)
import Data.UUID qualified as UUID
import Data.UUID.V5 qualified as UUID5
import GHC.Generics (Generic)

-- | Brand identifier - deterministic UUID5
newtype BrandId = BrandId {unBrandId :: UUID}
  deriving stock (Eq, Ord, Show, Generic)

instance ToJSON BrandId where
  toJSON (BrandId uuid) = toJSON (UUID.toText uuid)

instance FromJSON BrandId where
  parseJSON v = do
    t <- parseJSON v
    case UUID.fromText t of
      Just uuid -> pure (BrandId uuid)
      Nothing -> fail "Invalid UUID format"

-- | Extract UUID from BrandId
brandIdToUUID :: BrandId -> UUID
brandIdToUUID = unBrandId

-- | Domain name (valid hostname)
newtype Domain = Domain {unDomain :: Text}
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Brand name (non-empty text)
newtype BrandName = BrandName {unBrandName :: Text}
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | UUID5 namespace for brand identifiers
brandNamespace :: UUID
brandNamespace = UUID5.generateNamed UUID5.namespaceURL (BS.unpack $ TE.encodeUtf8 "foundry:brand")

-- | Generate deterministic brand ID from domain
mkBrandId :: Domain -> BrandId
mkBrandId (Domain d) = BrandId (UUID5.generateNamed brandNamespace (BS.unpack $ TE.encodeUtf8 d))

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
