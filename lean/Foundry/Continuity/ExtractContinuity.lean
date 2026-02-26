import Foundry.Foundry.Continuity.CodeGen.Extract

/-!
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // CONTINUITY // CODE GENERATOR
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                  Generate Haskell / C++ / Rust Code

                         straylight / 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Usage:
  continuity_gen haskell   # Output Haskell to stdout
  continuity_gen cpp       # Output C++23 to stdout
  continuity_gen rust      # Output Rust to stdout
  continuity_gen all       # Output all (separated by markers)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

open Foundry.Continuity.CodeGen.Extract

def usage : String := 
"continuity_gen - Generate code from verified Continuity specifications

Usage:
  continuity_gen <target>

Targets:
  haskell    Generate Haskell module (Continuity.Types)
  cpp        Generate C++23 header (continuity.hpp)
  rust       Generate Rust module (continuity.rs)
  all        Generate all targets with file markers

Examples:
  continuity_gen haskell > src/Continuity/Types.hs
  continuity_gen cpp > include/continuity.hpp
  continuity_gen rust > src/continuity.rs
"

def main (args : List String) : IO Unit := do
  match args with
  | ["haskell"] => IO.println toHaskell
  | ["cpp"] => IO.println toCpp
  | ["rust"] => IO.println toRust
  | ["all"] => do
    IO.println "// ═══════════════════════════════════════════════════════════════════════"
    IO.println "// FILE: Continuity/Types.hs (Haskell)"
    IO.println "// ═══════════════════════════════════════════════════════════════════════"
    IO.println ""
    IO.println toHaskell
    IO.println ""
    IO.println "// ═══════════════════════════════════════════════════════════════════════"
    IO.println "// FILE: continuity.hpp (C++23)"
    IO.println "// ═══════════════════════════════════════════════════════════════════════"
    IO.println ""
    IO.println toCpp
    IO.println ""
    IO.println "// ═══════════════════════════════════════════════════════════════════════"
    IO.println "// FILE: continuity.rs (Rust)"
    IO.println "// ═══════════════════════════════════════════════════════════════════════"
    IO.println ""
    IO.println toRust
  | _ => IO.eprintln usage
