-- ════════════════════════════════════════════════════════════════════════════════
-- MODULE IMPORTS (must be first!)
-- ════════════════════════════════════════════════════════════════════════════════

import Foundry.Continuity.Crypto
import Foundry.Continuity.Authority
import Foundry.Continuity.Trust
import Foundry.Continuity.Coeffect
import Foundry.Continuity.Witness
import Foundry.Continuity.Derivation
import Foundry.Continuity.Toolchain
import Foundry.Continuity.Cache
import Foundry.Continuity.Isolation
import Foundry.Continuity.Parametricity
import Foundry.Continuity.Protocol
import Foundry.Continuity.Main

-- CodeGen IR (emitters have issues, disabled for now)
import Foundry.Continuity.CodeGen
-- import Foundry.Continuity.CodeGen.Haskell
-- import Foundry.Continuity.CodeGen.Cpp
-- import Foundry.Continuity.CodeGen.Rust
-- import Foundry.Continuity.CodeGen.Extract

/-!
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                         THE CONTINUITY PROJECT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

          Formal Verification of a Post-Quantum, Capability-Based
                    Content-Addressed Build System

                       razorgirl / Straylight / 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

This file proves that content-addressed builds with capability-based trust
form a coherent system where:

  1. TRUST FLOWS THROUGH VOUCHES — Recognition chains establish trust
     between principals, with distance tracking attacker bounds

  2. AUTHORITY FORMS A LATTICE — Capabilities compose via meet-semilattice,
     security levels via join-semilattice (defense in depth)

  3. COEFFECTS WITNESS PURITY — eBPF syscall traces prove builds are
     hermetic and reproducible

  4. POST-QUANTUM CRYPTO — Hybrid ed25519 + ML-DSA + SLH-DSA signatures
     require breaking ALL to forge (defense in depth)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

/-!
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
     // reading this file
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

This is a Lean 4 file. Lean is a proof assistant: a programming
language where you can state mathematical theorems and the compiler
verifies your proofs are correct. If this file compiles, every
theorem is true.

THE CONTINUITY MODEL:

  Principal ─────vouches────▶ Principal
      │                           │
      │ holds                     │ holds
      ▼                           ▼
  Capability ◀───delegates───  Capability
      │                           │
      │ authorizes                │ authorizes
      ▼                           ▼
  Derivation ─────input──────▶ Derivation
      │                           │
      │ produces                  │ produces
      ▼                           ▼
  StorePath ◀────content────── StorePath
      │                           │
      │ witnessed by              │ witnessed by
      ▼                           ▼
  DischargeProof ◀──attests── DischargeProof

TRUST TOPOLOGY:

  - Vouches form a directed graph between principals
  - TrustDistance tracks minimum path length (attacker bound)
  - RecognitionLevel encodes strength: Unknown < Recognized < Vouched < Mutual
  - Revocation invalidates entire subtrees of the trust graph

SECURITY MODEL:

  - SecurityLevel: join-semilattice (security degrades to minimum)
  - Authority: meet-semilattice (authority narrows to intersection)
  - Hybrid crypto: ALL algorithms must verify (defense in depth)
  - Coeffects: witnessed syscalls prove hermeticity

AXIOM BUDGET:

  Cryptographic primitives are axiomatized at trust distance 1.
  We trust the mathematical properties of:
    - SHA-256 (collision resistance, preimage resistance)
    - Ed25519 (EUF-CMA security)
    - ML-DSA-65 (post-quantum EUF-CMA, NIST FIPS 204)
    - SLH-DSA-128s (hash-based signatures, NIST FIPS 205)
    - ML-KEM-768 (IND-CCA2 security, NIST FIPS 203)

  Everything else is proven from first principles.

-/

namespace Continuity

/-!
All modules are imported above and available under their namespaces:
  - Continuity.Crypto
  - Continuity.Authority
  - Continuity.Trust
  - Continuity.Coeffect
  - Continuity.Witness
  - Continuity.Derivation
  - Continuity.Toolchain
  - Continuity.Cache
  - Continuity.Isolation
  - Continuity.Parametricity
  - Continuity.Protocol
  - Continuity.Main
  - Continuity.CodeGen
-/

end Continuity
