-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // foundry // brand
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Brand Schema - Re-export from Hydrogen (PRODUCTION CODE)
--
-- ARCHITECTURE:
--   The brand type proofs live in Hydrogen.Schema.Brand.* (CTO's code).
--   We re-export them here for convenience. DO NOT DUPLICATE.
--
-- INVARIANTS PROVEN (in Hydrogen):
--   Identity:   uuid5_deterministic, uuid5_injective, domain_valid
--   Palette:    palette_has_primary, roles_unique, colors_in_gamut
--   Typography: typography_monotonic, base_positive
--   Spacing:    spacing_positive, ratio_gt_one
--   Voice:      traits_nonempty, vocabulary_disjoint
--   Provenance: content_hash_valid, timestamp_ordered
--   Brand:      same_domain_same_uuid, compound_valid
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- Production code from Hydrogen (CTO's proofs)
import Hydrogen.Schema.Brand.Identity
import Hydrogen.Schema.Brand.Palette
import Hydrogen.Schema.Brand.Typography
import Hydrogen.Schema.Brand.Spacing
import Hydrogen.Schema.Brand.Voice
import Hydrogen.Schema.Brand.Provenance
import Hydrogen.Schema.Brand.Brand

-- Strategy and Editorial are SMART-specific extensions
-- These build on top of Hydrogen's Brand
import Hydrogen.Schema.Brand.Strategy
import Hydrogen.Schema.Brand.Editorial
import Hydrogen.Schema.Brand.Logo
