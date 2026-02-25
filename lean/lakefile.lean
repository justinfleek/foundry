-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                              // metxt // lean
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- SMART Brand Ingestion Engine - Lean4 Proofs
--
-- This package contains:
--   - Brand schema invariant definitions
--   - Pipeline effect proofs
--   - Graded monad laws verification
--
-- Build: lake build
-- Test:  lake test
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

import Lake
open Lake DSL

package metxt where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Main library
@[default_target]
lean_lib Metxt where
  srcDir := "."

-- Brand schema proofs
lean_lib «Metxt.Brand» where
  srcDir := "Metxt/Brand"

-- Pipeline effect proofs
lean_lib «Metxt.Pipeline» where
  srcDir := "Metxt/Pipeline"

-- Dependencies
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"
