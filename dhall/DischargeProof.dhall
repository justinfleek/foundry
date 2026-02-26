{- DischargeProof.dhall

   Evidence that coeffects were satisfied during pipeline execution.

   WHAT IS A DISCHARGE PROOF:
     A DischargeProof is cryptographically-signed evidence that:
     1. The declared coeffects were actually required
     2. The runtime environment provided them
     3. The outputs are content-addressed (reproducible)

   This follows Continuity's witness pattern from straylight.

   STRUCTURE:
     - Declared coeffects (what the stage claimed to need)
     - Network accesses (witnessed by MITM proxy)
     - Sandbox evidence (witnessed by gVisor/Bubblewrap hooks)
     - Database accesses (witnessed by connection pools)
     - Output hashes (content addresses of results)
     - Cryptographic signature (optional, for trust propagation)

   STATUS: PRODUCTION
-}

let Resource = ./Resource.dhall

-- ════════════════════════════════════════════════════════════════════════════════
-- WITNESS TYPES
-- ════════════════════════════════════════════════════════════════════════════════

let NetworkAccess
    : Type
    = { url : Text
      , method : Text
      , statusCode : Natural
      , contentHash : Text
      , timestamp : Text
      }

let SandboxAccess
    : Type
    = { sandboxName : Text
      , sandboxType : Text
      , processId : Natural
      , syscallsWitnessed : Natural
      , startTime : Text
      , endTime : Text
      }

let DatabaseAccess
    : Type
    = { database : Text
      , operation : < Read | Write | Query >
      , rowsAffected : Natural
      , contentHash : Optional Text
      , timestamp : Text
      }

let ZmqAccess
    : Type
    = { endpoint : Text
      , messageType : < Request | Response | Push | Pull >
      , messageHash : Text
      , timestamp : Text
      }

-- ════════════════════════════════════════════════════════════════════════════════
-- DISCHARGE PROOF TYPE
-- ════════════════════════════════════════════════════════════════════════════════

let DischargeProof
    : Type
    = { -- What coeffects were declared
        coeffects : Resource.Resources

        -- Evidence of network access (from witness proxy)
      , networkAccess : List NetworkAccess

        -- Evidence of sandbox execution (from sandbox hooks)
      , sandboxAccess : List SandboxAccess

        -- Evidence of database access (from connection pools)
      , databaseAccess : List DatabaseAccess

        -- Evidence of ZMQ messaging (from broker)
      , zmqAccess : List ZmqAccess

        -- Build metadata
      , stageId : Text
      , stageName : Text
      , inputHash : Text
      , outputHash : Text
      , startTime : Text
      , endTime : Text

        -- Optional cryptographic signature
        -- Signs: sha256(stageId ++ inputHash ++ outputHash ++ evidenceHashes)
      , signature : Optional { publicKey : Text, sig : Text }
      }

-- ════════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ════════════════════════════════════════════════════════════════════════════════

let pureProof
    : { stageId : Text
      , stageName : Text
      , inputHash : Text
      , outputHash : Text
      , startTime : Text
      , endTime : Text
      } ->
        DischargeProof
    = \(meta :
          { stageId : Text
          , stageName : Text
          , inputHash : Text
          , outputHash : Text
          , startTime : Text
          , endTime : Text
          }
        ) ->
        { coeffects = Resource.pure
        , networkAccess = [] : List NetworkAccess
        , sandboxAccess = [] : List SandboxAccess
        , databaseAccess = [] : List DatabaseAccess
        , zmqAccess = [] : List ZmqAccess
        , stageId = meta.stageId
        , stageName = meta.stageName
        , inputHash = meta.inputHash
        , outputHash = meta.outputHash
        , startTime = meta.startTime
        , endTime = meta.endTime
        , signature = None { publicKey : Text, sig : Text }
        }

-- ════════════════════════════════════════════════════════════════════════════════
-- PREDICATES
-- ════════════════════════════════════════════════════════════════════════════════

let isPure
    : DischargeProof -> Bool
    = \(p : DischargeProof) -> Resource.isPure p.coeffects

let hasNetworkEvidence
    : DischargeProof -> Bool
    = \(p : DischargeProof) ->
        merge
          { None = False
          , Some = \(_ : NetworkAccess) -> True
          }
          (List/head NetworkAccess p.networkAccess)

let hasSandboxEvidence
    : DischargeProof -> Bool
    = \(p : DischargeProof) ->
        merge
          { None = False
          , Some = \(_ : SandboxAccess) -> True
          }
          (List/head SandboxAccess p.sandboxAccess)

let isSigned
    : DischargeProof -> Bool
    = \(p : DischargeProof) ->
        merge
          { None = False
          , Some = \(_ : { publicKey : Text, sig : Text }) -> True
          }
          p.signature

-- ════════════════════════════════════════════════════════════════════════════════
-- EXPORTS
-- ════════════════════════════════════════════════════════════════════════════════

in  { -- Witness types
      NetworkAccess
    , SandboxAccess
    , DatabaseAccess
    , ZmqAccess
      -- Main type
    , DischargeProof
      -- Constructors
    , pureProof
      -- Predicates
    , isPure
    , hasNetworkEvidence
    , hasSandboxEvidence
    , isSigned
    }
