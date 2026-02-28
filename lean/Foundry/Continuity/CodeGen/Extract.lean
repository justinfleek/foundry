import Foundry.Continuity.CodeGen
import Foundry.Continuity.CodeGen.Haskell
import Foundry.Continuity.CodeGen.Cpp
import Foundry.Continuity.CodeGen.Rust

/-!
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                         // CONTINUITY // TYPES
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

              Convert Continuity Lean Types → CodeGen IR

                          Straylight / 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

This module defines the extraction from verified Continuity types to
the language-agnostic CodeGen IR. Each type is manually specified here
to ensure correct correspondence.

Future: Use Lean4 metaprogramming to derive extractions automatically.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/


namespace Foundry.Continuity.CodeGen.Extract

open Foundry.Continuity.CodeGen

-- ════════════════════════════════════════════════════════════════════════════════
-- §0 CRYPTO TYPES
-- ════════════════════════════════════════════════════════════════════════════════

def hash256Def : TypeDef := .newtype "Hash256" [] (.fixedArray .u8 32)

def signatureDef : TypeDef := .enum "Signature" [] [
  { name := "Ed25519", fields := [⟨"bytes", .fixedArray .u8 64, some "64-byte Ed25519 signature"⟩] },
  { name := "MLDSA65", fields := [⟨"bytes", .prim .bytes, some "ML-DSA-65 signature (~3309 bytes)"⟩] },
  { name := "SLHDSA128s", fields := [⟨"bytes", .prim .bytes, some "SLH-DSA-128s signature (~7856 bytes)"⟩] }
]

def hybridSigDef : TypeDef := .struct "HybridSignature" [] [
  ⟨"ed25519", .named "Signature", some "Classical signature"⟩,
  ⟨"mldsa", .named "Signature", some "Post-quantum lattice signature"⟩,
  ⟨"slhdsa", .named "Signature", some "Hash-based backup signature"⟩
]

def publicKeyDef : TypeDef := .enum "PublicKey" [] [
  { name := "Ed25519", fields := [⟨"bytes", .fixedArray .u8 32, none⟩] },
  { name := "MLDSA65", fields := [⟨"bytes", .prim .bytes, some "~1952 bytes"⟩] },
  { name := "SLHDSA128s", fields := [⟨"bytes", .prim .bytes, some "~32 bytes"⟩] },
  { name := "X25519", fields := [⟨"bytes", .fixedArray .u8 32, none⟩] },
  { name := "MLKEM768", fields := [⟨"bytes", .prim .bytes, some "~1184 bytes"⟩] }
]

def hybridPublicKeyDef : TypeDef := .struct "HybridPublicKey" [] [
  ⟨"signing_ed25519", .named "PublicKey", none⟩,
  ⟨"signing_mldsa", .named "PublicKey", none⟩,
  ⟨"signing_slhdsa", .named "PublicKey", none⟩,
  ⟨"kex_x25519", .named "PublicKey", none⟩,
  ⟨"kex_mlkem", .named "PublicKey", none⟩
]

-- ════════════════════════════════════════════════════════════════════════════════
-- §1 TRUST TYPES
-- ════════════════════════════════════════════════════════════════════════════════

def principalDef : TypeDef := .struct "Principal" [] [
  ⟨"id", .named "Hash256", some "SHA-256 of public key"⟩,
  ⟨"public_key", .named "HybridPublicKey", some "Hybrid PQ public key"⟩
]

def trustDistanceDef : TypeDef := .enum "TrustDistance" [] [
  { name := "Self_", fields := [], doc := some "Distance 0 - self" },
  { name := "Direct", fields := [], doc := some "Distance 1 - direct vouch" },
  { name := "Transitive", fields := [⟨"hops", .prim .u32, some "Number of hops > 1"⟩], doc := some "Distance > 1" },
  { name := "Unknown", fields := [], doc := some "No trust path known" }
]

def recognitionLevelDef : TypeDef := .enum "RecognitionLevel" [] [
  { name := "Unknown", fields := [] },
  { name := "Recognized", fields := [], doc := some "Seen but not vouched" },
  { name := "Vouched", fields := [], doc := some "One-way vouch" },
  { name := "Mutual", fields := [], doc := some "Bidirectional vouches" }
]

def vouchDef : TypeDef := .struct "Vouch" [] [
  ⟨"from_", .named "Principal", some "Vouching principal"⟩,
  ⟨"to", .named "Principal", some "Vouched principal"⟩,
  ⟨"level", .named "RecognitionLevel", none⟩,
  ⟨"timestamp", .prim .u64, some "Unix timestamp"⟩,
  ⟨"signature", .named "HybridSignature", none⟩
]

-- ════════════════════════════════════════════════════════════════════════════════
-- §2 AUTHORITY TYPES
-- ════════════════════════════════════════════════════════════════════════════════

def securityLevelDef : TypeDef := .enum "SecurityLevel" [] [
  { name := "Unclassified", fields := [] },
  { name := "Confidential", fields := [] },
  { name := "Secret", fields := [] },
  { name := "TopSecret", fields := [] }
]

def capabilityDef : TypeDef := .struct "Capability" [] [
  ⟨"resource", .prim .string, some "Resource identifier"⟩,
  ⟨"actions", .array (.prim .string), some "Permitted actions"⟩,
  ⟨"constraints", .optional (.prim .string), some "Optional constraints"⟩,
  ⟨"expiry", .optional (.prim .u64), some "Optional expiry timestamp"⟩
]

-- ════════════════════════════════════════════════════════════════════════════════
-- §3 COEFFECT TYPES
-- ════════════════════════════════════════════════════════════════════════════════

def coeffectDef : TypeDef := .enum "Coeffect" [] [
  { name := "Pure", fields := [], doc := some "No external dependencies" },
  { name := "FileRead", fields := [⟨"path", .prim .string, none⟩] },
  { name := "FileWrite", fields := [⟨"path", .prim .string, none⟩] },
  { name := "EnvVar", fields := [⟨"name", .prim .string, none⟩] },
  { name := "Network", fields := [⟨"host", .prim .string, none⟩, ⟨"port", .prim .u16, none⟩] },
  { name := "Time", fields := [] },
  { name := "Random", fields := [] },
  { name := "Subprocess", fields := [⟨"cmd", .prim .string, none⟩] }
]

def syscallClassDef : TypeDef := .enum "SyscallClass" [] [
  { name := "FileIO", fields := [] },
  { name := "NetworkIO", fields := [] },
  { name := "ProcessControl", fields := [] },
  { name := "Memory", fields := [] },
  { name := "IPC", fields := [] },
  { name := "Time", fields := [] },
  { name := "Random", fields := [] }
]

def witnessedSyscallDef : TypeDef := .struct "WitnessedSyscall" [] [
  ⟨"syscall_nr", .prim .u32, some "Linux syscall number"⟩,
  ⟨"class_", .named "SyscallClass", none⟩,
  ⟨"args", .fixedArray .u64 6, some "Syscall arguments"⟩,
  ⟨"return_value", .prim .i64, none⟩,
  ⟨"timestamp_ns", .prim .u64, none⟩
]

def dischargeProofDef : TypeDef := .struct "DischargeProof" [] [
  ⟨"derivation_hash", .named "Hash256", some "What was built"⟩,
  ⟨"output_hash", .named "Hash256", some "Build output hash"⟩,
  ⟨"syscalls", .array (.named "WitnessedSyscall"), some "eBPF witness trace"⟩,
  ⟨"coeffects", .array (.named "Coeffect"), some "Derived coeffect set"⟩,
  ⟨"builder_signature", .named "HybridSignature", some "Builder attestation"⟩
]

-- ════════════════════════════════════════════════════════════════════════════════
-- §4 DERIVATION TYPES
-- ════════════════════════════════════════════════════════════════════════════════

def storePathDef : TypeDef := .struct "StorePath" [] [
  ⟨"hash", .named "Hash256", some "Content hash"⟩,
  ⟨"name", .prim .string, some "Human-readable name"⟩
]

def derivationDef : TypeDef := .struct "Derivation" [] [
  ⟨"outputs", .array (.named "StorePath"), none⟩,
  ⟨"inputs", .array (.named "StorePath"), none⟩,
  ⟨"builder", .prim .string, some "Builder executable"⟩,
  ⟨"args", .array (.prim .string), some "Builder arguments"⟩,
  ⟨"env", .array (.tuple [.prim .string, .prim .string]), some "Environment variables"⟩,
  ⟨"system", .prim .string, some "Target system"⟩
]

-- ════════════════════════════════════════════════════════════════════════════════
-- §5 TOOLCHAIN TYPES
-- ════════════════════════════════════════════════════════════════════════════════

def archDef : TypeDef := .enum "Arch" [] [
  { name := "X86_64", fields := [] },
  { name := "Aarch64", fields := [] },
  { name := "Riscv64", fields := [] },
  { name := "Wasm32", fields := [] }
]

def osDef : TypeDef := .enum "OS" [] [
  { name := "Linux", fields := [] },
  { name := "Darwin", fields := [] },
  { name := "FreeBSD", fields := [] },
  { name := "None_", fields := [], doc := some "Bare metal / freestanding" }
]

def abiDef : TypeDef := .enum "ABI" [] [
  { name := "GNU", fields := [] },
  { name := "Musl", fields := [] },
  { name := "MSVC", fields := [] },
  { name := "Eabi", fields := [] },
  { name := "None_", fields := [] }
]

def tripleDef : TypeDef := .struct "Triple" [] [
  ⟨"arch", .named "Arch", none⟩,
  ⟨"os", .named "OS", none⟩,
  ⟨"abi", .named "ABI", none⟩
]

-- ════════════════════════════════════════════════════════════════════════════════
-- §6 PROTOCOL TYPES (SSP)
-- ════════════════════════════════════════════════════════════════════════════════

def handshakeStateDef : TypeDef := .enum "HandshakeState" [] [
  { name := "Initial", fields := [] },
  { name := "SentClientHello", fields := [] },
  { name := "ReceivedServerHello", fields := [] },
  { name := "SentClientFinish", fields := [] },
  { name := "Established", fields := [] },
  { name := "Failed", fields := [⟨"reason", .prim .string, none⟩] }
]

def channelStateDef : TypeDef := .enum "ChannelState" [] [
  { name := "Open", fields := [] },
  { name := "HalfClosed", fields := [] },
  { name := "Closed", fields := [] }
]

def capabilityCertDef : TypeDef := .struct "CapabilityCert" [] [
  ⟨"issuer", .named "Principal", some "Who issued this cert"⟩,
  ⟨"subject", .named "Principal", some "Who holds this capability"⟩,
  ⟨"capability", .named "Capability", some "What they can do"⟩,
  ⟨"valid_from", .prim .u64, none⟩,
  ⟨"valid_until", .prim .u64, none⟩,
  ⟨"signature", .named "HybridSignature", some "Issuer's signature"⟩
]

-- ════════════════════════════════════════════════════════════════════════════════
-- §7 STATE MACHINE DEFINITIONS
-- ════════════════════════════════════════════════════════════════════════════════

def sspHandshakeMachine : StateMachine := {
  name := "SSPHandshake"
  doc := some "SSP protocol handshake state machine"
  states := [
    { name := "Initial", isInitial := true },
    { name := "AwaitingServerHello" },
    { name := "AwaitingClientFinish" },
    { name := "Established", isTerminal := true },
    { name := "Failed", isTerminal := true }
  ]
  events := [
    { name := "SendClientHello", payload := [⟨"ephemeral_pk", .named "HybridPublicKey", none⟩] },
    { name := "RecvServerHello", payload := [⟨"ephemeral_pk", .named "HybridPublicKey", none⟩, ⟨"cert", .named "CapabilityCert", none⟩] },
    { name := "SendClientFinish", payload := [⟨"cert", .named "CapabilityCert", none⟩] },
    { name := "RecvClientFinish", payload := [⟨"cert", .named "CapabilityCert", none⟩] },
    { name := "Error", payload := [⟨"reason", .prim .string, none⟩] }
  ]
  actions := [
    { name := "EmitClientHello" },
    { name := "EmitServerHello" },
    { name := "EmitClientFinish" },
    { name := "DeriveSessionKey" },
    { name := "LogError", payload := [⟨"msg", .prim .string, none⟩] }
  ]
  transitions := [
    { from_ := "Initial", event := "SendClientHello", to := "AwaitingServerHello", actions := ["EmitClientHello"] },
    { from_ := "Initial", event := "RecvClientHello", to := "AwaitingClientFinish", actions := ["EmitServerHello"] },
    { from_ := "AwaitingServerHello", event := "RecvServerHello", to := "Established", actions := ["DeriveSessionKey", "EmitClientFinish"] },
    { from_ := "AwaitingClientFinish", event := "RecvClientFinish", to := "Established", actions := ["DeriveSessionKey"] },
    { from_ := "AwaitingServerHello", event := "Error", to := "Failed", actions := ["LogError"] },
    { from_ := "AwaitingClientFinish", event := "Error", to := "Failed", actions := ["LogError"] }
  ]
}

-- ════════════════════════════════════════════════════════════════════════════════
-- §8 COMPLETE MODULE
-- ════════════════════════════════════════════════════════════════════════════════

/-- All Continuity types as a CodeGen IR module -/
def continuityModule : Module := {
  name := "Continuity"
  doc := some "Post-quantum, capability-based, content-addressed build system types.\nGenerated from verified Lean4 specifications."
  imports := []
  types := [
    -- Crypto
    hash256Def,
    signatureDef,
    hybridSigDef,
    publicKeyDef,
    hybridPublicKeyDef,
    -- Trust
    principalDef,
    trustDistanceDef,
    recognitionLevelDef,
    vouchDef,
    -- Authority
    securityLevelDef,
    capabilityDef,
    -- Coeffect
    coeffectDef,
    syscallClassDef,
    witnessedSyscallDef,
    dischargeProofDef,
    -- Derivation
    storePathDef,
    derivationDef,
    -- Toolchain
    archDef,
    osDef,
    abiDef,
    tripleDef,
    -- Protocol
    handshakeStateDef,
    channelStateDef,
    capabilityCertDef
  ]
  functions := []
  machines := [sspHandshakeMachine]
  codecs := []
}

-- ════════════════════════════════════════════════════════════════════════════════
-- §9 EMIT TO ALL TARGETS
-- ════════════════════════════════════════════════════════════════════════════════

/-- Generate Haskell module -/
def toHaskell : String := 
  Haskell.emitModule { continuityModule with name := "Foundry.Continuity.Types" }

/-- Generate C++23 header -/
def toCpp : String := 
  Cpp.emitHeader continuityModule

/-- Generate Rust module -/
def toRust : String := 
  Rust.emitModule continuityModule

end Foundry.Continuity.CodeGen.Extract
