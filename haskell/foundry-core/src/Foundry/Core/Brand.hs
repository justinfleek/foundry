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
    
    -- ** Identity (Section 1)
    module Foundry.Core.Brand.Identity
  , module Foundry.Core.Brand.Overview
    
    -- ** Strategic Layer (Sections 2-8)
  , module Foundry.Core.Brand.Strategy
  , module Foundry.Core.Brand.Tagline
  , module Foundry.Core.Brand.Voice
  , module Foundry.Core.Brand.Editorial
  , module Foundry.Core.Brand.Customer
    
    -- ** Execution Layer (Sections 9-25)
  , module Foundry.Core.Brand.Logo
  , module Foundry.Core.Brand.Color
  , module Foundry.Core.Brand.Palette
  , module Foundry.Core.Brand.Gradient
  , module Foundry.Core.Brand.Typography
  , module Foundry.Core.Brand.Spacing
    
    -- ** Provenance
  , module Foundry.Core.Brand.Provenance
  ) where

-- Strategic Layer
import Foundry.Core.Brand.Customer
import Foundry.Core.Brand.Editorial
import Foundry.Core.Brand.Identity
import Foundry.Core.Brand.Overview
import Foundry.Core.Brand.Strategy
import Foundry.Core.Brand.Tagline
import Foundry.Core.Brand.Voice

-- Execution Layer
import Foundry.Core.Brand.Color
import Foundry.Core.Brand.Gradient
import Foundry.Core.Brand.Logo
import Foundry.Core.Brand.Palette
import Foundry.Core.Brand.Spacing
import Foundry.Core.Brand.Typography

-- Provenance
import Foundry.Core.Brand.Provenance
