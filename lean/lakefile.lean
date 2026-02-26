-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                              // foundry // lean
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- SMART Brand Ingestion Engine - Lean4 Proofs
--
-- ARCHITECTURE:
--   Foundry.Pipeline   - Ingestion pipeline proofs (graded monads, co-effects)
--   Foundry.Cornell    - Verified wire formats (SIGIL, ZMTP, Protobuf)
--   Foundry.Continuity - Coeffect algebra and isolation proofs
--   Foundry.Brand      - Brand type proofs
--
-- All modules are vendored locally to avoid external git dependencies.
-- Original sources:
--   - Cornell: straylight/continuity/Cornell
--   - Continuity: straylight/continuity/Continuity
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
-- LIBRARIES (all local - no external git dependencies)
-- ═══════════════════════════════════════════════════════════════════════════════

-- Main entry point - imports all submodules
@[default_target]
lean_lib Foundry where
  srcDir := "."
  roots := #[`Foundry]
