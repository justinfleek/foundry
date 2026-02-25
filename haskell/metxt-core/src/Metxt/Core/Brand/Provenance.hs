{- |
Module      : Metxt.Core.Brand.Provenance
Description : Content provenance tracking
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

SHA256 content hashing and source tracking for audit trails.
-}
module Metxt.Core.Brand.Provenance
  ( -- * Types
    ContentHash (..)
  , SourceURL (..)
  , Timestamp (..)
  , Provenance (..)
  ) where

import Data.ByteString (ByteString)
import Data.Text (Text)
import Data.Time (UTCTime)

-- | SHA256 content hash (deterministic)
newtype ContentHash = ContentHash {unContentHash :: !ByteString}
  deriving stock (Eq, Ord, Show)

-- | Source URL for ingested content
newtype SourceURL = SourceURL {unSourceURL :: !Text}
  deriving stock (Eq, Show)

-- | Timestamp for provenance tracking
newtype Timestamp = Timestamp {unTimestamp :: !UTCTime}
  deriving stock (Eq, Ord, Show)

-- | Complete provenance record
data Provenance = Provenance
  { provenanceHash :: !ContentHash
  , provenanceSource :: !SourceURL
  , provenanceTimestamp :: !Timestamp
  }
  deriving stock (Eq, Show)
