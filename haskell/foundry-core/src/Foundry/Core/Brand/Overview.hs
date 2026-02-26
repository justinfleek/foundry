{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // foundry // brand/overview
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Overview
Description : SMART Framework Brand Overview (Section 1)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Foundational brand narrative - origin story, purpose, perception.

== SMART Framework Section 1: Brand Overview

"The foundational narrative. Every brand has an origin story, a reason for 
existing, and a way it wants to be perceived."

Fields to capture:
- Brand Name
- Parent Organization / Ecosystem (if applicable)
- Industry / Category
- One-Line Description — What the brand does in a single sentence.
- Brand Promise — The core commitment to the user/customer.
- Founding Context — Why this brand was created and what problem it solves.

DEPENDENCIES:
  - Foundry.Core.Brand.Identity (for BrandName, Domain)

DEPENDENTS:
  - Foundry.Core.Brand (compound type)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Overview
  ( -- * Brand Overview
    BrandOverview (..)
  , mkBrandOverview
  
    -- * Industry
  , Industry (..)
  , mkIndustry
  ) where

import Data.Text (Text)
import Data.Text qualified as T

--------------------------------------------------------------------------------
-- Industry
--------------------------------------------------------------------------------

-- | Industry or category classification
newtype Industry = Industry { unIndustry :: Text }
  deriving stock (Eq, Ord, Show)

-- | Create industry with validation (non-empty)
mkIndustry :: Text -> Maybe Industry
mkIndustry t
  | T.length (T.strip t) >= 1 = Just (Industry (T.strip t))
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Brand Overview
--------------------------------------------------------------------------------

-- | Complete brand overview - the foundational narrative
data BrandOverview = BrandOverview
  { overviewParentOrg     :: !(Maybe Text)  -- ^ Parent organization/ecosystem
  , overviewIndustry      :: !Industry      -- ^ Industry/category
  , overviewOneLiner      :: !Text          -- ^ What the brand does (one sentence)
  , overviewPromise       :: !Text          -- ^ Core commitment to customer
  , overviewFoundingCtx   :: !Text          -- ^ Why created, what problem solved
  }
  deriving stock (Eq, Show)

-- | Create brand overview with validation
mkBrandOverview
  :: Maybe Text  -- ^ Parent org (optional)
  -> Industry    -- ^ Industry
  -> Text        -- ^ One-liner
  -> Text        -- ^ Promise
  -> Text        -- ^ Founding context
  -> Maybe BrandOverview
mkBrandOverview parent industry oneLiner promise founding
  | T.length (T.strip oneLiner) >= 1
  , T.length (T.strip promise) >= 1
  , T.length (T.strip founding) >= 1 = Just BrandOverview
      { overviewParentOrg = fmap T.strip parent
      , overviewIndustry = industry
      , overviewOneLiner = T.strip oneLiner
      , overviewPromise = T.strip promise
      , overviewFoundingCtx = T.strip founding
      }
  | otherwise = Nothing
