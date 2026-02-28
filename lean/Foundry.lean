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

-- Cornell: Verified wire formats (SIGIL, ZMTP, Protobuf)
-- Core modules have complete proofs, some theorems deferred with sorry.
import Foundry.Cornell

-- NOTE: The following modules depend on external packages not yet configured:
-- - Foundry.Brand (requires Hydrogen)
-- - Foundry.Budget (requires Mathlib)
-- - Foundry.Timestamp (requires Mathlib)
-- - Foundry.Cornell.SSP (3000+ line file with crypto, needs significant work)
-- - Foundry.Continuity (full coeffect algebra)
-- Import them individually once dependencies are added to lakefile.lean
