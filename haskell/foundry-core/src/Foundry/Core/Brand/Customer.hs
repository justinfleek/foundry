{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // foundry // brand/customer
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Customer
Description : SMART Framework Target Customers (Section 8)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Target customer psychographic profiles for content calibration.

== SMART Framework Section 8: Target Customers

"Psychographic profiles of the brand's intended audience. These inform tone 
calibration and content strategy."

For each customer segment, define:
- Segment Name: A descriptive label
- Description: Who they are and what drives them
- Key Motivations: What attracts them to brands in this category

"Target customer profiles help calibrate language complexity, assumed 
knowledge, and emotional framing. An AI generating content for 
'privacy-conscious users' will write differently than for 'gamers seeking 
immersive experiences.'"

DEPENDENCIES:
  - None (base types)

DEPENDENTS:
  - Foundry.Core.Brand (compound type)
  - Foundry.Extract.Voice (tone calibration)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Customer
  ( -- * Customer Segment
    CustomerSegment (..)
  , mkCustomerSegment
  ) where

import Data.Text (Text)
import Data.Text qualified as T

--------------------------------------------------------------------------------
-- Customer Segment
--------------------------------------------------------------------------------

-- | A target customer segment with psychographic profile
data CustomerSegment = CustomerSegment
  { segmentName        :: !Text   -- ^ Descriptive label (e.g., "Early Adopters")
  , segmentDescription :: !Text   -- ^ Who they are and what drives them
  , segmentMotivations :: ![Text] -- ^ What attracts them to this category
  }
  deriving stock (Eq, Show)

-- | Create customer segment with validation
mkCustomerSegment :: Text -> Text -> [Text] -> Maybe CustomerSegment
mkCustomerSegment name desc motivations
  | T.length (T.strip name) >= 1
  , T.length (T.strip desc) >= 1 = Just CustomerSegment
      { segmentName = T.strip name
      , segmentDescription = T.strip desc
      , segmentMotivations = motivations
      }
  | otherwise = Nothing
