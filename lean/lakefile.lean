-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                              // foundry // lean
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- SMART Brand Ingestion Engine - Lean4 Proofs
--
-- This package DEPENDS on Hydrogen.Schema.Brand for core proofs.
-- Foundry adds ingestion pipeline proofs on top of the proven brand types.
--
-- ARCHITECTURE:
--   hydrogen/proofs/Hydrogen/Schema/Brand/* - Core brand type proofs (PRODUCTION)
--   foundry/lean/Foundry/Pipeline/*             - Ingestion pipeline proofs
--
-- Build: lake build
-- Test:  lake test
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

import Lake
open Lake DSL

package foundry where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- DEPENDENCIES
-- ═══════════════════════════════════════════════════════════════════════════════

-- Hydrogen: Production-grade Brand proofs (Identity, Palette, Typography, etc.)
-- This is the CTO's code - we use it directly instead of duplicating
require hydrogen from git
  "https://github.com/straylight-software/hydrogen" @ "main"

-- Straylight Continuity: Coeffect algebra proofs
-- Provides: Coeffect types, tensor product, purity/reproducibility theorems
-- Used for proving the ingestion pipeline respects coeffect constraints
require continuity from git
  "https://github.com/straylight-software/straylight" @ "main" / "src/examples/lean-continuity"

-- Mathlib: Mathematical foundations (pulled transitively via hydrogen/continuity)
-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4"

-- ═══════════════════════════════════════════════════════════════════════════════
-- LIBRARIES
-- ═══════════════════════════════════════════════════════════════════════════════

-- Main entry point
@[default_target]
lean_lib Foundry where
  srcDir := "."

-- Pipeline effect proofs (graded monads, co-effect algebra)
-- This is foundry's contribution: proving the INGESTION PIPELINE is correct
lean_lib «Foundry.Pipeline» where
  srcDir := "Foundry/Pipeline"
