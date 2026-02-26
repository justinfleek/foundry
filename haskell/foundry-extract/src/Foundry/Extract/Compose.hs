{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // foundry // extract // compose
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Compose
Description : Brand composition from extracted components
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Composes a complete Brand from extracted components.

== Pipeline

1. Run all extractors (Color, Typography, Spacing, Voice)
2. Generate Identity (UUID5 from domain)
3. Compute Provenance (SHA256 of content)
4. Compose into complete Brand

== Design Notes

The composer is the final step in the extraction pipeline. It validates
all extracted components and combines them into a single Brand value.

== Dependencies

Requires: Foundry.Extract.Color, Foundry.Extract.Typography, 
          Foundry.Extract.Spacing, Foundry.Extract.Voice
Required by: (none - top-level entry point)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Compose
  ( -- * Composition
    composeBrand
  , BrandExtractionResult (..)

    -- * Components
  , ExtractionComponents (..)
  ) where

import Crypto.Hash (Digest, SHA256, hash)
import Data.ByteString (ByteString)
import Data.Time (UTCTime)

import Foundry.Core.Text (bshow)

import Foundry.Core.Brand
  ( BrandId
  , BrandName
  , BrandPalette
  , BrandVoice
  , ContentHash (..)
  , Domain
  , Provenance (..)
  , SourceURL (..)
  , SpacingScale
  , Timestamp (..)
  , Typography
  , mkBrandId
  , mkBrandName
  , mkDomain
  )
import Foundry.Extract.Color (ColorExtractionResult (..), extractPalette)
import Foundry.Extract.Spacing (SpacingExtractionResult (..), extractSpacing)
import Foundry.Extract.Types
  ( ExtractionError (..)
  , ExtractionWarning (..)
  , ScrapeResult (..)
  , TextContent (..)
  )
import Foundry.Extract.Typography (TypographyExtractionResult (..), extractTypography)
import Foundry.Extract.Voice (VoiceExtractionResult (..), extractVoice)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Complete brand extraction result
data BrandExtractionResult = BrandExtractionResult
  { berIdentity    :: !BrandId
    -- ^ Brand identity (UUID5)
  , berDomain      :: !Domain
    -- ^ Source domain
  , berName        :: !(Maybe BrandName)
    -- ^ Brand name (if detected)
  , berPalette     :: !BrandPalette
    -- ^ Color palette
  , berTypography  :: !Typography
    -- ^ Typography specification
  , berSpacing     :: !SpacingScale
    -- ^ Spacing scale
  , berVoice       :: !BrandVoice
    -- ^ Brand voice
  , berProvenance  :: !Provenance
    -- ^ Content provenance
  , berComponents  :: !ExtractionComponents
    -- ^ Detailed extraction results
  , berWarnings    :: ![ExtractionWarning]
    -- ^ All warnings from extraction
  }
  deriving stock (Show)

-- | Detailed extraction component results
data ExtractionComponents = ExtractionComponents
  { ecColor      :: !ColorExtractionResult
  , ecTypography :: !TypographyExtractionResult
  , ecSpacing    :: !SpacingExtractionResult
  , ecVoice      :: !VoiceExtractionResult
  }
  deriving stock (Show)

--------------------------------------------------------------------------------
-- Composition
--------------------------------------------------------------------------------

-- | Compose a complete Brand from scrape result
composeBrand :: UTCTime -> ScrapeResult -> Either ExtractionError BrandExtractionResult
composeBrand timestamp sr = do
  -- Validate domain
  domain <- case mkDomain (srDomain sr) of
    Just d  -> Right d
    Nothing -> Left ErrNoDomain
  
  -- Generate identity
  let brandId = mkBrandId domain
  
  -- Extract color palette
  colorResult <- extractPalette sr
  
  -- Extract typography
  typoResult <- extractTypography sr
  
  -- Extract spacing (infallible)
  let spacingResult = extractSpacing sr
  
  -- Extract voice (infallible)
  let voiceResult = extractVoice sr
  
  -- Compute provenance
  let contentHash = computeContentHash (srRawHTML sr)
      provenance = Provenance
        { provenanceHash = contentHash
        , provenanceSource = SourceURL (srURL sr)
        , provenanceTimestamp = Timestamp timestamp
        }
  
  -- Collect all warnings
  let allWarnings = cerWarnings colorResult
                 ++ terWarnings typoResult
                 ++ serWarnings spacingResult
                 ++ verWarnings voiceResult
  
  -- Build components record
  let components = ExtractionComponents
        { ecColor = colorResult
        , ecTypography = typoResult
        , ecSpacing = spacingResult
        , ecVoice = voiceResult
        }
  
  -- Compose result
  Right $ BrandExtractionResult
    { berIdentity = brandId
    , berDomain = domain
    , berName = extractBrandName sr
    , berPalette = cerPalette colorResult
    , berTypography = terTypography typoResult
    , berSpacing = serSpacing spacingResult
    , berVoice = verVoice voiceResult
    , berProvenance = provenance
    , berComponents = components
    , berWarnings = allWarnings
    }

-- | Compute SHA256 content hash
--
-- Uses bshow from Foundry.Core.Text following the Hydrogen Show debug convention.
-- The digest's Show instance produces a hex string representation.
computeContentHash :: ByteString -> ContentHash
computeContentHash content =
  let digest :: Digest SHA256
      digest = hash content
  in ContentHash (bshow digest)

-- | Extract brand name from title or domain
extractBrandName :: ScrapeResult -> Maybe BrandName
extractBrandName sr = case srTextContent sr of
  tc -> case tcTitle tc of
    Just title -> mkBrandName (cleanTitle title)
    Nothing    -> mkBrandName (srDomain sr)
  where
    -- Clean up title (remove " - Website" etc.)
    cleanTitle t = t  -- Note: Title cleaning should be implemented based on domain patterns
