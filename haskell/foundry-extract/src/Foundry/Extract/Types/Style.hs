{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // foundry // extract // types/style
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Types.Style
Description : Extended CSS style types for TOTAL brand ingestion
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Types for representing ALL CSS style data including:
  - Gradients (linear, radial, conic)
  - CSS Custom Properties (design tokens)
  - Box shadows and text shadows
  - Border radii
  - Extended computed styles

== Design Notes

Modern brands define their design system via CSS custom properties.
Extracting these gives us the authoritative color/spacing tokens.

== Dependencies

Requires: aeson, text, vector
Required by: Foundry.Extract.Types, Foundry.Extract.Color

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Types.Style
  ( -- * CSS Custom Properties (Design Tokens)
    CSSVariable (..)
  , CSSScope (..)
  , TokenCategory (..)
  
    -- * Gradients
  , GradientData (..)
  , GradientType (..)
  , GradientDirection (..)
  , GradientStop (..)
  , ColorHint (..)
  
    -- * Shadows
  , BoxShadow (..)
  , TextShadow (..)
  
    -- * Borders
  , BorderRadius (..)
  , BorderRadiusCorner (..)
  
    -- * Extended CSS Value
  , CSSValueExtended (..)
  
    -- * Extended Computed Style
  , ComputedStyleExtended (..)
  ) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Text (Text)
import Data.Vector (Vector)
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- CSS Custom Properties (Design Tokens)
--------------------------------------------------------------------------------

-- | CSS custom property (CSS variable / design token)
--
-- Custom properties define a brand's design tokens:
--   --color-primary: #0066cc;
--   --spacing-md: 1rem;
--   --font-heading: "Inter", sans-serif;
data CSSVariable = CSSVariable
  { cvName       :: !Text
    -- ^ Variable name (e.g., "--color-primary")
  , cvValue      :: !Text
    -- ^ Raw value (e.g., "#0066cc")
  , cvScope      :: !CSSScope
    -- ^ Where defined (:root, .dark-mode, @media)
  , cvCategory   :: !(Maybe TokenCategory)
    -- ^ Inferred category
  , cvFallback   :: !(Maybe Text)
    -- ^ Fallback value if specified
  , cvUsageCount :: !Int
    -- ^ How many times referenced
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON CSSVariable
instance ToJSON CSSVariable

-- | Scope where CSS variable is defined
data CSSScope
  = ScopeRoot            -- ^ :root (global)
  | ScopeMedia !Text     -- ^ Inside @media query
  | ScopeSelector !Text  -- ^ On specific selector (e.g., ".dark-mode")
  | ScopeSupports !Text  -- ^ Inside @supports
  | ScopeLayer !Text     -- ^ Inside @layer
  deriving stock (Eq, Show, Generic)

instance FromJSON CSSScope
instance ToJSON CSSScope

-- | Category of design token (inferred from name/value)
data TokenCategory
  = TokenColor        -- ^ Color value
  | TokenSpacing      -- ^ Spacing/dimension
  | TokenTypography   -- ^ Font-related
  | TokenShadow       -- ^ Shadow definition
  | TokenBorderRadius -- ^ Border radius
  | TokenAnimation    -- ^ Animation timing
  | TokenZIndex       -- ^ Z-index value
  | TokenBreakpoint   -- ^ Media query breakpoint
  | TokenOther        -- ^ Other/unknown
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON TokenCategory
instance ToJSON TokenCategory

--------------------------------------------------------------------------------
-- Gradients
--------------------------------------------------------------------------------

-- | Gradient type
data GradientType
  = GradientLinear           -- ^ linear-gradient()
  | GradientRadial           -- ^ radial-gradient()
  | GradientConic            -- ^ conic-gradient()
  | GradientRepeatingLinear  -- ^ repeating-linear-gradient()
  | GradientRepeatingRadial  -- ^ repeating-radial-gradient()
  | GradientRepeatingConic   -- ^ repeating-conic-gradient()
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance FromJSON GradientType
instance ToJSON GradientType

-- | Gradient direction/angle
data GradientDirection
  = DirAngle !Double        -- ^ Angle in degrees (0-360)
  | DirToTop                -- ^ to top (0deg)
  | DirToBottom             -- ^ to bottom (180deg)
  | DirToLeft               -- ^ to left (270deg)
  | DirToRight              -- ^ to right (90deg)
  | DirToTopLeft            -- ^ to top left
  | DirToTopRight           -- ^ to top right
  | DirToBottomLeft         -- ^ to bottom left
  | DirToBottomRight        -- ^ to bottom right
  | DirFromAngle !Double    -- ^ from <angle> (conic)
  | DirAtPosition !Text     -- ^ at <position> (radial)
  | DirEllipse !Text        -- ^ ellipse <size> at <position>
  | DirCircle !Text         -- ^ circle <size> at <position>
  deriving stock (Eq, Show, Generic)

instance FromJSON GradientDirection
instance ToJSON GradientDirection

-- | Color hint (midpoint) in gradient
data ColorHint = ColorHint
  { chPosition :: !Double  -- ^ Position as percentage (0-100)
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON ColorHint
instance ToJSON ColorHint

-- | Gradient color stop
data GradientStop = GradientStop
  { gsColor      :: !Text
    -- ^ Color value (any CSS color)
  , gsPosition   :: !(Maybe Double)
    -- ^ Position as percentage (0-100)
  , gsHint       :: !(Maybe ColorHint)
    -- ^ Color hint after this stop
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON GradientStop
instance ToJSON GradientStop

-- | Complete gradient data
data GradientData = GradientData
  { gdType       :: !GradientType
    -- ^ Type of gradient
  , gdDirection  :: !(Maybe GradientDirection)
    -- ^ Direction (linear/conic) or shape (radial)
  , gdStops      :: !(Vector GradientStop)
    -- ^ Color stops
  , gdRaw        :: !Text
    -- ^ Original CSS string (for debugging)
  , gdSelector   :: !Text
    -- ^ Where found
  , gdProperty   :: !Text
    -- ^ Which property (background, background-image, etc.)
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON GradientData
instance ToJSON GradientData

--------------------------------------------------------------------------------
-- Shadows
--------------------------------------------------------------------------------

-- | Box shadow
data BoxShadow = BoxShadow
  { bsOffsetX  :: !Double   -- ^ Horizontal offset (px)
  , bsOffsetY  :: !Double   -- ^ Vertical offset (px)
  , bsBlur     :: !Double   -- ^ Blur radius (px)
  , bsSpread   :: !Double   -- ^ Spread radius (px)
  , bsColor    :: !Text     -- ^ Shadow color
  , bsInset    :: !Bool     -- ^ Is inset shadow
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON BoxShadow
instance ToJSON BoxShadow

-- | Text shadow
data TextShadow = TextShadow
  { tsOffsetX  :: !Double   -- ^ Horizontal offset (px)
  , tsOffsetY  :: !Double   -- ^ Vertical offset (px)
  , tsBlur     :: !Double   -- ^ Blur radius (px)
  , tsColor    :: !Text     -- ^ Shadow color
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON TextShadow
instance ToJSON TextShadow

--------------------------------------------------------------------------------
-- Border Radius
--------------------------------------------------------------------------------

-- | Single corner border radius
data BorderRadiusCorner = BorderRadiusCorner
  { brcHorizontal :: !Double  -- ^ Horizontal radius (px)
  , brcVertical   :: !Double  -- ^ Vertical radius (px, for elliptical)
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON BorderRadiusCorner
instance ToJSON BorderRadiusCorner

-- | Complete border radius (all four corners)
data BorderRadius = BorderRadius
  { brTopLeft     :: !BorderRadiusCorner
  , brTopRight    :: !BorderRadiusCorner
  , brBottomRight :: !BorderRadiusCorner
  , brBottomLeft  :: !BorderRadiusCorner
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON BorderRadius
instance ToJSON BorderRadius

--------------------------------------------------------------------------------
-- Extended CSS Value
--------------------------------------------------------------------------------

-- | Extended CSS value types
--
-- Extends the base CSSValue with gradient, variable, and function support.
data CSSValueExtended
  = CVColor !Text
    -- ^ Color value
  | CVLength !Double !Text
    -- ^ Length with unit
  | CVGradient !GradientData
    -- ^ Gradient value
  | CVVariable !Text !(Maybe Text)
    -- ^ var(--name, fallback)
  | CVCalc !Text
    -- ^ calc() expression
  | CVClamp !Text !Text !Text
    -- ^ clamp(min, preferred, max)
  | CVMin !Text
    -- ^ min() function
  | CVMax !Text
    -- ^ max() function
  | CVUrl !Text
    -- ^ url() reference
  | CVKeyword !Text
    -- ^ Keyword value
  | CVNumber !Double
    -- ^ Unitless number
  | CVRaw !Text
    -- ^ Unparsed value
  deriving stock (Eq, Show, Generic)

instance FromJSON CSSValueExtended
instance ToJSON CSSValueExtended

--------------------------------------------------------------------------------
-- Extended Computed Style
--------------------------------------------------------------------------------

-- | Extended computed style with ALL relevant properties
--
-- Captures every property needed for TOTAL brand extraction.
data ComputedStyleExtended = ComputedStyleExtended
  { -- Color properties
    cseColor              :: !(Maybe Text)
  , cseBackgroundColor    :: !(Maybe Text)
  , cseBorderTopColor     :: !(Maybe Text)
  , cseBorderRightColor   :: !(Maybe Text)
  , cseBorderBottomColor  :: !(Maybe Text)
  , cseBorderLeftColor    :: !(Maybe Text)
  , cseOutlineColor       :: !(Maybe Text)
  , cseTextDecorationColor :: !(Maybe Text)
  , cseCaretColor         :: !(Maybe Text)
  , cseAccentColor        :: !(Maybe Text)
  
    -- Typography properties
  , cseFontFamily         :: !(Maybe Text)
  , cseFontSize           :: !(Maybe Double)
  , cseFontWeight         :: !(Maybe Int)
  , cseFontStyle          :: !(Maybe Text)
  , cseFontStretch        :: !(Maybe Text)
  , cseLineHeight         :: !(Maybe Double)
  , cseLetterSpacing      :: !(Maybe Double)
  , cseWordSpacing        :: !(Maybe Double)
  , cseTextTransform      :: !(Maybe Text)
  , cseTextAlign          :: !(Maybe Text)
  , cseTextIndent         :: !(Maybe Double)
  
    -- Spacing properties
  , cseMarginTop          :: !(Maybe Double)
  , cseMarginRight        :: !(Maybe Double)
  , cseMarginBottom       :: !(Maybe Double)
  , cseMarginLeft         :: !(Maybe Double)
  , csePaddingTop         :: !(Maybe Double)
  , csePaddingRight       :: !(Maybe Double)
  , csePaddingBottom      :: !(Maybe Double)
  , csePaddingLeft        :: !(Maybe Double)
  , cseGap                :: !(Maybe Double)
  , cseRowGap             :: !(Maybe Double)
  , cseColumnGap          :: !(Maybe Double)
  
    -- Border properties
  , cseBorderTopWidth     :: !(Maybe Double)
  , cseBorderRightWidth   :: !(Maybe Double)
  , cseBorderBottomWidth  :: !(Maybe Double)
  , cseBorderLeftWidth    :: !(Maybe Double)
  , cseBorderTopStyle     :: !(Maybe Text)
  , cseBorderRadius       :: !(Maybe BorderRadius)
  
    -- Shadow properties
  , cseBoxShadow          :: !(Maybe (Vector BoxShadow))
  , cseTextShadow         :: !(Maybe (Vector TextShadow))
  
    -- Layout properties
  , cseDisplay            :: !(Maybe Text)
  , csePosition           :: !(Maybe Text)
  , cseZIndex             :: !(Maybe Int)
  , cseFlexDirection      :: !(Maybe Text)
  , cseJustifyContent     :: !(Maybe Text)
  , cseAlignItems         :: !(Maybe Text)
  , cseGridTemplateColumns :: !(Maybe Text)
  , cseGridTemplateRows   :: !(Maybe Text)
  
    -- Transform properties
  , cseTransform          :: !(Maybe Text)
  , cseTransformOrigin    :: !(Maybe Text)
  
    -- Transition/Animation
  , cseTransition         :: !(Maybe Text)
  , cseAnimation          :: !(Maybe Text)
  
    -- Background
  , cseBackgroundImage    :: !(Maybe Text)
  , cseBackgroundSize     :: !(Maybe Text)
  , cseBackgroundPosition :: !(Maybe Text)
  , cseBackgroundRepeat   :: !(Maybe Text)
  
    -- Other visual
  , cseOpacity            :: !(Maybe Double)
  , cseCursor             :: !(Maybe Text)
  , cseOverflow           :: !(Maybe Text)
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON ComputedStyleExtended
instance ToJSON ComputedStyleExtended
