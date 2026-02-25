{- |
Module      : Metxt.Core.Brand.Logo.Sizing
Description : Logo clear space and minimum sizing specifications
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Logo clear space rules and minimum sizing for print and digital contexts.
Mirrors Hydrogen.Schema.Brand.Logo.Sizing from PureScript.

DEPENDENCIES:
  - None (foundational module)

DEPENDENTS:
  - Metxt.Core.Brand.Logo (main logo module)
-}
module Metxt.Core.Brand.Logo.Sizing
  ( -- * Clear Space Rule
    ClearSpaceRule (..)
  , mkClearSpaceRule
  
    -- * Minimum Size
  , MinimumSize (..)
  , mkMinimumSize
  
    -- * Lockup Sizing
  , LockupSizing (..)
  , mkLockupSizing
  ) where

import Data.Text (Text)
import Data.Text qualified as T

-- | Clear space rule defines minimum buffer around logo.
data ClearSpaceRule = ClearSpaceRule
  { clearSpaceReference   :: !Text    -- ^ What element is used for measurement
  , clearSpaceMultiplier  :: !Double  -- ^ How many times the reference
  , clearSpaceDescription :: !Text    -- ^ Full rule description
  }
  deriving stock (Eq, Show)

-- | Create clear space rule with validation.
mkClearSpaceRule 
  :: Text    -- ^ Reference element
  -> Double  -- ^ Multiplier
  -> Text    -- ^ Description
  -> Maybe ClearSpaceRule
mkClearSpaceRule ref mult desc
  | T.length ref >= 1 && mult > 0.0 && T.length desc >= 1 =
      Just ClearSpaceRule
        { clearSpaceReference = ref
        , clearSpaceMultiplier = mult
        , clearSpaceDescription = desc
        }
  | otherwise = Nothing

-- | Minimum size specification for a lockup.
data MinimumSize = MinimumSize
  { minSizePrintInches   :: !Double  -- ^ Minimum height in inches for print
  , minSizeDigitalWidth  :: !Int     -- ^ Minimum width in pixels
  , minSizeDigitalHeight :: !Int     -- ^ Minimum height in pixels
  }
  deriving stock (Eq, Show)

-- | Create minimum size with validation.
mkMinimumSize 
  :: Double  -- ^ Print minimum in inches
  -> Int     -- ^ Digital width in pixels
  -> Int     -- ^ Digital height in pixels
  -> Maybe MinimumSize
mkMinimumSize printIn digW digH
  | printIn > 0.0 && digW >= 1 && digH >= 1 =
      Just MinimumSize
        { minSizePrintInches = printIn
        , minSizeDigitalWidth = digW
        , minSizeDigitalHeight = digH
        }
  | otherwise = Nothing

-- | Sizing specification for a specific lockup.
data LockupSizing = LockupSizing
  { lockupSizingName      :: !Text         -- ^ Which lockup this applies to
  , lockupSizingMinPrint  :: !Double       -- ^ Minimum height in inches
  , lockupSizingMinDigital :: !MinimumSize -- ^ Minimum digital dimensions
  }
  deriving stock (Eq, Show)

-- | Create lockup sizing with validation.
mkLockupSizing 
  :: Text        -- ^ Lockup name
  -> Double      -- ^ Minimum print size in inches
  -> MinimumSize -- ^ Minimum digital size
  -> Maybe LockupSizing
mkLockupSizing name printMin digital
  | T.length name >= 1 && printMin > 0.0 =
      Just LockupSizing
        { lockupSizingName = name
        , lockupSizingMinPrint = printMin
        , lockupSizingMinDigital = digital
        }
  | otherwise = Nothing
