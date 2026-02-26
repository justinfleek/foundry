-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                              // foundry // root
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- METXT - SMART Brand Ingestion Engine
--
-- Lean4 proof layer for brand ingestion pipeline.
--
-- ARCHITECTURE:
--   This package DEPENDS on Hydrogen.Schema.Brand for core brand type proofs.
--   Foundry adds the INGESTION PIPELINE proofs:
--     - Graded monad laws for effect tracking
--     - Co-effect algebra for requirement tracking
--     - Pipeline stage composition proofs
--
-- PRODUCTION CODE DEPENDENCIES:
--   Hydrogen.Schema.Brand.Identity   - UUID5 determinism, domain validation
--   Hydrogen.Schema.Brand.Palette    - OKLCH gamut bounds, semantic roles
--   Hydrogen.Schema.Brand.Typography - Type scale monotonicity
--   Hydrogen.Schema.Brand.Spacing    - Positive spacing invariants
--   Hydrogen.Schema.Brand.Voice      - Non-empty traits, vocabulary disjointness
--   Hydrogen.Schema.Brand.Provenance - Content hash validity
--   Hydrogen.Schema.Brand.Brand      - Compound type with proof fields
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- Re-export Hydrogen.Schema.Brand (production code)
import Hydrogen.Schema.Brand.Identity
import Hydrogen.Schema.Brand.Palette
import Hydrogen.Schema.Brand.Typography
import Hydrogen.Schema.Brand.Spacing
import Hydrogen.Schema.Brand.Voice
import Hydrogen.Schema.Brand.Provenance
import Hydrogen.Schema.Brand.Brand

-- Foundry Pipeline proofs (our contribution)
import Foundry.Pipeline
