{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // foundry // brand
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand
Description : Brand schema types re-exports
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Re-exports all brand schema types.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand
  ( -- * Re-exports
    module Foundry.Core.Brand.Identity
  , module Foundry.Core.Brand.Palette
  , module Foundry.Core.Brand.Typography
  , module Foundry.Core.Brand.Spacing
  , module Foundry.Core.Brand.Voice
  , module Foundry.Core.Brand.Strategy
  , module Foundry.Core.Brand.Editorial
  , module Foundry.Core.Brand.Provenance
  ) where

import Foundry.Core.Brand.Editorial
import Foundry.Core.Brand.Identity
import Foundry.Core.Brand.Palette
import Foundry.Core.Brand.Provenance
import Foundry.Core.Brand.Spacing
import Foundry.Core.Brand.Strategy
import Foundry.Core.Brand.Typography
import Foundry.Core.Brand.Voice
