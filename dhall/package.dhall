{- package.dhall

   METXT Dhall package - re-exports all build configuration types.

   ARCHITECTURE:
     This package provides typed build specifications for the brand ingestion
     pipeline. It follows sensenet's Dhall conventions:
       - Coeffect algebra via Resource.dhall
       - Discharge proofs via DischargeProof.dhall
       - Toolchain specifications via Toolchain.dhall
       - Build targets via Build.dhall
       - Pipeline stages via Pipeline.dhall

   DEPENDENCIES:
     - sensenet/dhall (upstream Dhall library)

   USAGE:
     let Metxt = ./package.dhall
     in  Metxt.Pipeline.scrapeStage
-}

let Resource = ./Resource.dhall
let DischargeProof = ./DischargeProof.dhall
let Pipeline = ./Pipeline.dhall

in  { -- Coeffect algebra
      Resource
      -- Discharge proofs (evidence of coeffect satisfaction)
    , DischargeProof
      -- Brand ingestion pipeline stages
    , Pipeline
    }
