{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                              // foundry // gpu
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.GPU
Description : GPU command infrastructure for billion-agent rendering
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Re-exports GPU command types and serialization.

== Architecture

The GPU module provides the binary wire format between:

  Haskell Backend → Binary Commands → WebGPU Interpreter (Hydrogen)

Key design points:

  * Fixed-size commands for predictable bandwidth
  * Little-endian for native GPU compatibility
  * Deterministic serialization for caching/dedup
  * GPUStorable typeclass with Lean4 roundtrip proofs

== Dependencies

Requires: (none)
Required by: Hydrogen WebGPU interpreter, agent rendering pipelines

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.GPU
  ( -- * Re-exports
    module Foundry.Core.GPU.Command
  , module Foundry.Core.GPU.Identified
  , module Foundry.Core.GPU.Patch
  , module Foundry.Core.GPU.Renderer
  ) where

import Foundry.Core.GPU.Command
import Foundry.Core.GPU.Identified
import Foundry.Core.GPU.Patch
import Foundry.Core.GPU.Renderer
