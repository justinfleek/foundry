{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // foundry // extract // types/motion
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Types.Motion
Description : Animation and transition types for brand motion language
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Types for representing ALL motion/animation data from brand assets.

== Coverage

This module supports extraction of:
  - CSS @keyframes animations
  - CSS transitions
  - Timing functions (easing)
  - Animation properties
  - Reduced motion preferences

== Design Notes

Modern brands have motion guidelines. Slack, Linear, Stripe all define
specific easing curves and animation durations that are part of their
brand identity.

== Dependencies

Requires: aeson, text, vector
Required by: Foundry.Extract.Types, Foundry.Extract.Motion

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Types.Motion
  ( -- * Timing Functions
    TimingFunction (..)
  , CubicBezier (..)
  , StepPosition (..)
  
    -- * Keyframes
  , Keyframe (..)
  , KeyframeBlock (..)
  , KeyframeAnimation (..)
  
    -- * Transitions
  , TransitionData (..)
  
    -- * Animation Properties
  , AnimationData (..)
  , AnimationDirection (..)
  , AnimationFillMode (..)
  , AnimationPlayState (..)
  , AnimationIterations (..)
  
    -- * Motion Data (Aggregate)
  , MotionData (..)
  ) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Text (Text)
import Data.Vector (Vector)
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Timing Functions
--------------------------------------------------------------------------------

-- | Cubic bezier control points
data CubicBezier = CubicBezier
  { cbX1 :: !Double  -- ^ P1 x coordinate (0-1)
  , cbY1 :: !Double  -- ^ P1 y coordinate (can exceed 0-1 for overshoot)
  , cbX2 :: !Double  -- ^ P2 x coordinate (0-1)
  , cbY2 :: !Double  -- ^ P2 y coordinate
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON CubicBezier
instance ToJSON CubicBezier

-- | Step function position
data StepPosition
  = StepJumpStart   -- ^ First jump at 0%
  | StepJumpEnd     -- ^ Last jump at 100% (default)
  | StepJumpNone    -- ^ No jump at either end
  | StepJumpBoth    -- ^ Jump at both ends
  | StepStart       -- ^ Alias for jump-start
  | StepEnd         -- ^ Alias for jump-end
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON StepPosition
instance ToJSON StepPosition

-- | CSS timing function (easing)
data TimingFunction
  = TfEase          -- ^ cubic-bezier(0.25, 0.1, 0.25, 1)
  | TfEaseIn        -- ^ cubic-bezier(0.42, 0, 1, 1)
  | TfEaseOut       -- ^ cubic-bezier(0, 0, 0.58, 1)
  | TfEaseInOut     -- ^ cubic-bezier(0.42, 0, 0.58, 1)
  | TfLinear        -- ^ linear
  | TfStepStart     -- ^ steps(1, start)
  | TfStepEnd       -- ^ steps(1, end)
  | TfCubicBezier !CubicBezier  -- ^ Custom cubic-bezier
  | TfSteps !Int !StepPosition  -- ^ steps(n, position)
  deriving stock (Eq, Show, Generic)

instance FromJSON TimingFunction
instance ToJSON TimingFunction

--------------------------------------------------------------------------------
-- Keyframes
--------------------------------------------------------------------------------

-- | Single keyframe in an animation
data Keyframe = Keyframe
  { kfOffset     :: !Double        -- ^ Position 0-100 (percent)
  , kfProperties :: !(Vector Text) -- ^ CSS property declarations
  , kfTiming     :: !(Maybe TimingFunction)  -- ^ Per-keyframe easing
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON Keyframe
instance ToJSON Keyframe

-- | A @keyframes block
data KeyframeBlock = KeyframeBlock
  { kbName      :: !Text            -- ^ Animation name
  , kbKeyframes :: !(Vector Keyframe) -- ^ Keyframes
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON KeyframeBlock
instance ToJSON KeyframeBlock

-- | Complete keyframe animation data
data KeyframeAnimation = KeyframeAnimation
  { kaBlock     :: !KeyframeBlock     -- ^ The @keyframes block
  , kaUsedBy    :: !(Vector Text)     -- ^ Selectors using this animation
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON KeyframeAnimation
instance ToJSON KeyframeAnimation

--------------------------------------------------------------------------------
-- Transitions
--------------------------------------------------------------------------------

-- | CSS transition data
data TransitionData = TransitionData
  { tdProperty  :: !Text              -- ^ Property being transitioned ("all", "opacity", etc.)
  , tdDuration  :: !Double            -- ^ Duration in milliseconds
  , tdTiming    :: !TimingFunction    -- ^ Easing function
  , tdDelay     :: !Double            -- ^ Delay in milliseconds
  , tdSelector  :: !Text              -- ^ Selector where defined
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON TransitionData
instance ToJSON TransitionData

--------------------------------------------------------------------------------
-- Animation Properties
--------------------------------------------------------------------------------

-- | Animation direction
data AnimationDirection
  = DirNormal           -- ^ Plays forward
  | DirReverse          -- ^ Plays backward
  | DirAlternate        -- ^ Alternates forward/backward
  | DirAlternateReverse -- ^ Alternates backward/forward
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON AnimationDirection
instance ToJSON AnimationDirection

-- | Animation fill mode
data AnimationFillMode
  = FillNone      -- ^ No fill
  | FillForwards  -- ^ Retain final keyframe
  | FillBackwards -- ^ Apply first keyframe during delay
  | FillBoth      -- ^ Both forwards and backwards
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON AnimationFillMode
instance ToJSON AnimationFillMode

-- | Animation play state
data AnimationPlayState
  = PlayRunning
  | PlayPaused
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON AnimationPlayState
instance ToJSON AnimationPlayState

-- | Animation iteration count
data AnimationIterations
  = Iterations !Int   -- ^ Specific count
  | Infinite          -- ^ Infinite loop
  deriving stock (Eq, Show, Generic)

instance FromJSON AnimationIterations
instance ToJSON AnimationIterations

-- | Complete animation data
data AnimationData = AnimationData
  { adName       :: !Text                  -- ^ Animation name
  , adDuration   :: !Double                -- ^ Duration in ms
  , adTiming     :: !TimingFunction        -- ^ Easing function
  , adDelay      :: !Double                -- ^ Delay in ms
  , adIterations :: !AnimationIterations   -- ^ Iteration count
  , adDirection  :: !AnimationDirection    -- ^ Direction
  , adFillMode   :: !AnimationFillMode     -- ^ Fill mode
  , adPlayState  :: !AnimationPlayState    -- ^ Play state
  , adSelector   :: !Text                  -- ^ Where applied
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON AnimationData
instance ToJSON AnimationData

--------------------------------------------------------------------------------
-- Motion Data (Aggregate)
--------------------------------------------------------------------------------

-- | All motion data from a scrape
data MotionData = MotionData
  { mdKeyframes      :: !(Vector KeyframeAnimation)
    -- ^ All @keyframes animations
  , mdAnimations     :: !(Vector AnimationData)
    -- ^ Animation property usage
  , mdTransitions    :: !(Vector TransitionData)
    -- ^ Transition property usage
  , mdHasReducedMotion :: !Bool
    -- ^ Has prefers-reduced-motion media query
  , mdCommonDurations :: !(Vector Double)
    -- ^ Most common duration values (ms)
  , mdCommonTimings  :: !(Vector TimingFunction)
    -- ^ Most common easing functions
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON MotionData
instance ToJSON MotionData
