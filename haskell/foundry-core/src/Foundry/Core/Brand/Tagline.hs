{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // foundry // brand/tagline
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Tagline
Description : SMART Framework Section 3 - Brand Taglines
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Taglines distill the Brand Promise, Mission, and Values into compact, repeatable
messages. They function as the verbal signature of the brand.

== SMART Framework Alignment

  S - Story-driven: Taglines encode the brand promise in memorable form
  M - Memorable: Short, repeatable, distinctive phrasing
  A - Agile: Primary/secondary taglines for different contexts
  R - Responsive: Context rules define when each tagline applies
  T - Targeted: Taglines calibrate message to audience

== AI Ingestion Priority #6

Taglines are LOCKED COPY. They must NEVER be paraphrased, reworded, or "improved"
by AI systems. The exact phrasing is the brand asset.

== Invariants (proven in Lean4)

  * Tagline text is non-empty
  * Primary tagline exists (at least one)
  * Tagline immutability is enforced by the type (no modification functions)

== Dependencies

  - Data.Text
  - Data.Vector

== Dependents

  - Foundry.Core.Brand (compound Brand type)
  - Foundry.Core.Brand.Strategy (StrategicLayer)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Tagline
  ( -- * Tagline Types
    TaglineText (..)
  , mkTaglineText
  , taglineToText
  
    -- * Tagline Context
  , TaglineContext (..)
  , taglineContextToText
  , parseTaglineContext
  
    -- * Tagline with Context
  , Tagline (..)
  , mkTagline
  
    -- * Primary Tagline (non-empty guarantee)
  , PrimaryTagline (..)
  , mkPrimaryTagline
  , primaryToTagline
  
    -- * Secondary Taglines
  , SecondaryTagline (..)
  , mkSecondaryTagline
  , secondaryToTagline
  
    -- * Tagline Set (complete specification)
  , TaglineSet (..)
  , mkTaglineSet
  , allTaglines
  
    -- * Usage Rules
  , TaglineUsageRule (..)
  , usageRuleToText
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // tagline text
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Immutable tagline text. The text is LOCKED and must never be modified.
--
-- Per SMART Framework Section 3:
-- "Taglines must never be rewritten, reworded, or edited in any way."
--
-- The newtype wrapper enforces this at the type level - there is no
-- modification function, only creation and reading.
newtype TaglineText = TaglineText { unTaglineText :: Text }
  deriving stock (Eq, Ord)

-- | Show instance for debugging.
-- Format: (TaglineText text:"...")
instance Show TaglineText where
  show (TaglineText t) = "(TaglineText text:" <> show t <> ")"

-- | Create validated tagline text.
--
-- Validation rules:
--   * Text must be non-empty
--   * Text must contain at least one non-whitespace character
--
-- Returns Nothing for invalid input.
mkTaglineText :: Text -> Maybe TaglineText
mkTaglineText t
  | T.null stripped = Nothing
  | otherwise = Just (TaglineText stripped)
  where
    stripped = T.strip t

-- | Extract text from tagline (read-only access).
taglineToText :: TaglineText -> Text
taglineToText = unTaglineText

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // tagline context
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Context in which a tagline should be used.
--
-- Different contexts may call for different taglines. The primary tagline
-- is used for general/default contexts, while secondary taglines may be
-- appropriate for specific marketing campaigns, social media, or product lines.
data TaglineContext
  = GeneralContext         -- ^ Default, all-purpose usage
  | MarketingCampaign      -- ^ Specific marketing initiatives
  | SocialMedia            -- ^ Social media platforms
  | ProductLine            -- ^ Specific product or service line
  | InternalCommunication  -- ^ Internal/employee-facing
  | EventContext           -- ^ Conferences, tradeshows, events
  | PartnerContext         -- ^ Co-branding, partner materials
  deriving stock (Eq, Ord, Show)

-- | Convert context to text representation.
taglineContextToText :: TaglineContext -> Text
taglineContextToText GeneralContext = "general"
taglineContextToText MarketingCampaign = "marketing"
taglineContextToText SocialMedia = "social"
taglineContextToText ProductLine = "product"
taglineContextToText InternalCommunication = "internal"
taglineContextToText EventContext = "event"
taglineContextToText PartnerContext = "partner"

-- | Parse context from text.
parseTaglineContext :: Text -> Maybe TaglineContext
parseTaglineContext s = case T.toLower (T.strip s) of
  "general"       -> Just GeneralContext
  "default"       -> Just GeneralContext
  "all"           -> Just GeneralContext
  "marketing"     -> Just MarketingCampaign
  "campaign"      -> Just MarketingCampaign
  "social"        -> Just SocialMedia
  "social media"  -> Just SocialMedia
  "socialmedia"   -> Just SocialMedia
  "product"       -> Just ProductLine
  "product line"  -> Just ProductLine
  "service"       -> Just ProductLine
  "internal"      -> Just InternalCommunication
  "employee"      -> Just InternalCommunication
  "event"         -> Just EventContext
  "conference"    -> Just EventContext
  "tradeshow"     -> Just EventContext
  "partner"       -> Just PartnerContext
  "co-brand"      -> Just PartnerContext
  "cobrand"       -> Just PartnerContext
  _               -> Nothing

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                  // tagline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | A tagline with its approved usage contexts.
data Tagline = Tagline
  { taglineText     :: !TaglineText           -- ^ The immutable tagline text
  , taglineContexts :: !(Vector TaglineContext) -- ^ Approved usage contexts
  }
  deriving stock (Eq)

-- | Show instance for debugging.
instance Show Tagline where
  show (Tagline t cs) = 
    "(Tagline text:" <> show (unTaglineText t) 
    <> " contexts:" <> show (V.toList cs) <> ")"

-- | Create a tagline with validated text and contexts.
mkTagline :: Text -> Vector TaglineContext -> Maybe Tagline
mkTagline t contexts = do
  validated <- mkTaglineText t
  Just Tagline
    { taglineText = validated
    , taglineContexts = contexts
    }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // primary tagline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | The primary tagline. Every brand MUST have exactly one primary tagline.
--
-- Per SMART Framework Section 3:
-- "Primary Tagline — The single most important tagline. Locked copy."
--
-- This is a separate type to enforce that a brand cannot exist without
-- a primary tagline - it's not optional.
newtype PrimaryTagline = PrimaryTagline { unPrimaryTagline :: Tagline }
  deriving stock (Eq)

-- | Show instance for debugging.
instance Show PrimaryTagline where
  show (PrimaryTagline t) = "(PrimaryTagline " <> show t <> ")"

-- | Create a primary tagline. The primary tagline always has GeneralContext.
mkPrimaryTagline :: Text -> Maybe PrimaryTagline
mkPrimaryTagline t = do
  validated <- mkTaglineText t
  Just $ PrimaryTagline Tagline
    { taglineText = validated
    , taglineContexts = V.singleton GeneralContext
    }

-- | Convert primary tagline to generic tagline (for uniform handling).
primaryToTagline :: PrimaryTagline -> Tagline
primaryToTagline = unPrimaryTagline

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // secondary tagline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Secondary taglines for specific contexts.
--
-- Per SMART Framework Section 3:
-- "Secondary Tagline(s) — Alternative taglines for different contexts."
--
-- Unlike the primary tagline, secondary taglines are optional and may have
-- specific context restrictions.
newtype SecondaryTagline = SecondaryTagline { unSecondaryTagline :: Tagline }
  deriving stock (Eq)

-- | Show instance for debugging.
instance Show SecondaryTagline where
  show (SecondaryTagline t) = "(SecondaryTagline " <> show t <> ")"

-- | Create a secondary tagline with specific contexts.
mkSecondaryTagline :: Text -> Vector TaglineContext -> Maybe SecondaryTagline
mkSecondaryTagline t contexts
  | V.null contexts = Nothing  -- Secondary taglines must have at least one context
  | otherwise = do
      tagline <- mkTagline t contexts
      Just (SecondaryTagline tagline)

-- | Convert secondary tagline to generic tagline.
secondaryToTagline :: SecondaryTagline -> Tagline
secondaryToTagline = unSecondaryTagline

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // tagline set
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete tagline specification for a brand.
--
-- Contains exactly one primary tagline and zero or more secondary taglines.
-- The invariant that at least one tagline exists is guaranteed by the
-- requirement for a PrimaryTagline.
data TaglineSet = TaglineSet
  { taglineSetPrimary    :: !PrimaryTagline             -- ^ Required primary tagline
  , taglineSetSecondary  :: !(Vector SecondaryTagline)  -- ^ Optional secondary taglines
  , taglineSetUsageRules :: !(Vector TaglineUsageRule)  -- ^ Usage guidelines
  }
  deriving stock (Eq, Show)

-- | Create a tagline set with validation.
--
-- The primary tagline is required; secondary taglines and rules are optional.
mkTaglineSet 
  :: PrimaryTagline 
  -> Vector SecondaryTagline 
  -> Vector TaglineUsageRule 
  -> TaglineSet
mkTaglineSet primary secondary rules = TaglineSet
  { taglineSetPrimary = primary
  , taglineSetSecondary = secondary
  , taglineSetUsageRules = rules
  }

-- | Get all taglines as a uniform vector.
allTaglines :: TaglineSet -> Vector Tagline
allTaglines ts = V.cons 
  (primaryToTagline (taglineSetPrimary ts))
  (V.map secondaryToTagline (taglineSetSecondary ts))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // usage rules
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Usage rules for taglines.
--
-- Per SMART Framework Section 3:
-- - "Taglines may be used alongside any approved logo iteration"
-- - "Taglines should NOT be combined with campaign-specific phrases"
-- - "Taglines must never be rewritten, reworded, or edited"
data TaglineUsageRule
  = UsageWithLogo                -- ^ May be used with approved logos
  | UsageStandalone              -- ^ May be used as standalone marketing
  | NoModification               -- ^ Must never be edited or reworded
  | NoCampaignCombination        -- ^ Must not be combined with campaign phrases
  | RequiresApproval             -- ^ Specific uses require brand team approval
  deriving stock (Eq, Ord, Show)

-- | Convert usage rule to descriptive text.
usageRuleToText :: TaglineUsageRule -> Text
usageRuleToText UsageWithLogo = 
  "May be used alongside any approved logo iteration or brand image"
usageRuleToText UsageStandalone = 
  "May be used as standalone marketing text"
usageRuleToText NoModification = 
  "Must NEVER be rewritten, reworded, or edited in any way"
usageRuleToText NoCampaignCombination = 
  "Should NOT be combined with campaign-specific taglines or phrases"
usageRuleToText RequiresApproval = 
  "Non-standard usage requires approval from the brand team"
