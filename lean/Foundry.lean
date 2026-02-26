-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                              // foundry // root
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- METXT - SMART Brand Ingestion Engine
--
-- Lean4 proof layer for brand ingestion pipeline.
--
-- ARCHITECTURE:
--   Foundry provides the INGESTION PIPELINE proofs:
--     - Graded monad laws for effect tracking
--     - Co-effect algebra for requirement tracking
--     - Pipeline stage composition proofs
--     - Cornell: Verified wire formats (SIGIL, ZMTP, Protobuf)
--     - Continuity: Coeffect algebra and isolation proofs
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- Foundry Pipeline proofs (graded monads, co-effect algebra)
import Foundry.Pipeline

-- Foundry Brand proofs (local - not dependent on external Hydrogen)
import Foundry.Brand

-- NOTE: Cornell and Continuity are available but have complex dependencies
-- Import them individually as needed:
--   import Foundry.Cornell
--   import Foundry.Continuity
