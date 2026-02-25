{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // metxt // brand
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Metxt.Core.Brand
Description : Brand schema types re-exports
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Re-exports all brand schema types.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Metxt.Core.Brand
  ( -- * Re-exports
    module Metxt.Core.Brand.Identity
  , module Metxt.Core.Brand.Palette
  , module Metxt.Core.Brand.Typography
  , module Metxt.Core.Brand.Spacing
  , module Metxt.Core.Brand.Voice
  , module Metxt.Core.Brand.Strategy
  , module Metxt.Core.Brand.Editorial
  , module Metxt.Core.Brand.Provenance
  ) where

import Metxt.Core.Brand.Editorial
import Metxt.Core.Brand.Identity
import Metxt.Core.Brand.Palette
import Metxt.Core.Brand.Provenance
import Metxt.Core.Brand.Spacing
import Metxt.Core.Brand.Strategy
import Metxt.Core.Brand.Typography
import Metxt.Core.Brand.Voice
