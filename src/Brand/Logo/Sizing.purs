-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // brand // logo // sizing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Logo clear space and minimum sizing specifications.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | DEPENDENCIES:
-- |   - None (foundational module)
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Logo (main logo module)

module Hydrogen.Schema.Brand.Logo.Sizing
  ( -- * Clear Space Rule
    ClearSpaceRule
  , mkClearSpaceRule
  , clearSpaceReference
  , clearSpaceMultiplier
  , clearSpaceDescription
  
  -- * Minimum Size
  , MinimumSize
  , mkMinimumSize
  , minSizePrintInches
  , minSizeDigitalWidth
  , minSizeDigitalHeight
  
  -- * Lockup Sizing
  , LockupSizing
  , mkLockupSizing
  , lockupSizingName
  , lockupSizingMinPrint
  , lockupSizingMinDigital
  ) where

import Prelude
  ( class Eq
  , (>=)
  , (>)
  , (&&)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length) as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // clear space rule
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Clear space rule defines minimum buffer around logo.
type ClearSpaceRule =
  { referenceElement :: String   -- What element is used for measurement
  , multiplier :: Number         -- How many times the reference
  , description :: String        -- Full rule description
  }

-- | Create clear space rule.
mkClearSpaceRule :: String -> Number -> String -> Maybe ClearSpaceRule
mkClearSpaceRule ref mult desc =
  if String.length ref >= 1 && mult > 0.0 && String.length desc >= 1
    then Just
      { referenceElement: ref
      , multiplier: mult
      , description: desc
      }
    else Nothing

-- | Get reference element.
clearSpaceReference :: ClearSpaceRule -> String
clearSpaceReference csr = csr.referenceElement

-- | Get multiplier.
clearSpaceMultiplier :: ClearSpaceRule -> Number
clearSpaceMultiplier csr = csr.multiplier

-- | Get description.
clearSpaceDescription :: ClearSpaceRule -> String
clearSpaceDescription csr = csr.description

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // minimum size
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Minimum size specification for a lockup.
type MinimumSize =
  { printInches :: Number     -- Minimum height in inches for print
  , digitalWidth :: Int       -- Minimum width in pixels
  , digitalHeight :: Int      -- Minimum height in pixels
  }

-- | Create minimum size.
mkMinimumSize :: Number -> Int -> Int -> Maybe MinimumSize
mkMinimumSize printIn digW digH =
  if printIn > 0.0 && digW >= 1 && digH >= 1
    then Just
      { printInches: printIn
      , digitalWidth: digW
      , digitalHeight: digH
      }
    else Nothing

-- | Get print minimum in inches.
minSizePrintInches :: MinimumSize -> Number
minSizePrintInches ms = ms.printInches

-- | Get digital minimum width.
minSizeDigitalWidth :: MinimumSize -> Int
minSizeDigitalWidth ms = ms.digitalWidth

-- | Get digital minimum height.
minSizeDigitalHeight :: MinimumSize -> Int
minSizeDigitalHeight ms = ms.digitalHeight

-- | Sizing specification for a specific lockup.
type LockupSizing =
  { lockupName :: String
  , minPrint :: Number        -- Minimum height in inches
  , minDigital :: MinimumSize
  }

-- | Create lockup sizing.
mkLockupSizing :: String -> Number -> MinimumSize -> Maybe LockupSizing
mkLockupSizing name printMin digital =
  if String.length name >= 1 && printMin > 0.0
    then Just
      { lockupName: name
      , minPrint: printMin
      , minDigital: digital
      }
    else Nothing

-- | Get lockup name.
lockupSizingName :: LockupSizing -> String
lockupSizingName ls = ls.lockupName

-- | Get minimum print size.
lockupSizingMinPrint :: LockupSizing -> Number
lockupSizingMinPrint ls = ls.minPrint

-- | Get minimum digital size.
lockupSizingMinDigital :: LockupSizing -> MinimumSize
lockupSizingMinDigital ls = ls.minDigital
