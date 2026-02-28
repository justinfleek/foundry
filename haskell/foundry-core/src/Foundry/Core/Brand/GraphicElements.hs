{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                      // foundry // core // brand // graphicelements
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.GraphicElements
Description : Graphic elements (patterns, textures, logo-derived motifs)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

SMART Framework Graphic Elements Layer: Patterns, textures, and
logo-derived visual motifs.

Supplementary visual assets derived from the brand identity that add
texture, pattern, and visual interest to compositions. These weave
aspects of the logo or brand motifs into a consistent visual language.

== SMART Framework

  S - Story-driven: Elements derive from logo/brand symbolism
  M - Memorable: Consistent patterns create recognition
  A - Agile: Adapts to different contexts (dark bg, apparel, print)
  R - Responsive: Scales from digital to physical
  T - Targeted: Context-specific usage rules

== Dependencies

Requires: vector, text, aeson
Required by: Foundry.Core.Brand.Complete

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.GraphicElements
  ( -- * Element Type
    GraphicElementType (..)
  , graphicElementTypeToText
  , parseGraphicElementType

    -- * Derivation Source
  , DerivationSource (..)
  , derivationSourceToText
  , parseDerivationSource

    -- * Usage Context
  , GraphicUsageContext (..)
  , graphicUsageContextToText
  , parseGraphicUsageContext

    -- * Color Treatment
  , GraphicColorTreatment (..)
  , mkGraphicColorTreatment

    -- * Modification Allowed
  , ModificationAllowed (..)
  , modificationAllowedToText
  , parseModificationAllowed

    -- * Graphic Element
  , GraphicElement (..)
  , mkGraphicElement

    -- * Complete Specification
  , GraphicElementsSpecification (..)
  , mkGraphicElementsSpecification
  , defaultGraphicElementsSpecification
  ) where

import Data.Aeson
  ( FromJSON (..)
  , ToJSON (..)
  , object
  , withObject
  , withText
  , (.:)
  , (.=)
  )
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Graphic Element Type
--------------------------------------------------------------------------------

-- | Type of graphic element.
data GraphicElementType
  = Pattern             -- ^ Repeating visual pattern
  | Texture             -- ^ Surface texture/grain
  | StrokeShape         -- ^ Outlined shape (rounded rect, circle, pill)
  | LogoDerivedPattern  -- ^ Pattern derived from logo geometry
  | Motif               -- ^ Recurring design element
  | Ornament            -- ^ Decorative accent
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

-- | Convert element type to text.
graphicElementTypeToText :: GraphicElementType -> Text
graphicElementTypeToText Pattern            = "pattern"
graphicElementTypeToText Texture            = "texture"
graphicElementTypeToText StrokeShape        = "stroke-shape"
graphicElementTypeToText LogoDerivedPattern = "logo-derived-pattern"
graphicElementTypeToText Motif              = "motif"
graphicElementTypeToText Ornament           = "ornament"

-- | Parse element type from text.
parseGraphicElementType :: Text -> Maybe GraphicElementType
parseGraphicElementType t = case T.toLower t of
  "pattern"              -> Just Pattern
  "texture"              -> Just Texture
  "stroke-shape"         -> Just StrokeShape
  "stroke"               -> Just StrokeShape
  "shape"                -> Just StrokeShape
  "logo-derived-pattern" -> Just LogoDerivedPattern
  "logo-pattern"         -> Just LogoDerivedPattern
  "motif"                -> Just Motif
  "ornament"             -> Just Ornament
  "decoration"           -> Just Ornament
  _                      -> Nothing

instance ToJSON GraphicElementType where
  toJSON = toJSON . graphicElementTypeToText

instance FromJSON GraphicElementType where
  parseJSON = withText "GraphicElementType" $ \t ->
    case parseGraphicElementType t of
      Just et -> pure et
      Nothing -> fail $ "Invalid graphic element type: " <> T.unpack t

--------------------------------------------------------------------------------
-- Derivation Source
--------------------------------------------------------------------------------

-- | Source from which graphic element is derived.
data DerivationSource
  = FromLogo        -- ^ Derived from logo/icon
  | FromIcon        -- ^ Derived from icon specifically
  | FromPalette     -- ^ Derived from color palette
  | FromTypography  -- ^ Derived from type treatment
  | FromGeometry    -- ^ Derived from brand geometry
  | Original        -- ^ Original creation (not derived)
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

-- | Convert derivation source to text.
derivationSourceToText :: DerivationSource -> Text
derivationSourceToText FromLogo       = "logo"
derivationSourceToText FromIcon       = "icon"
derivationSourceToText FromPalette    = "palette"
derivationSourceToText FromTypography = "typography"
derivationSourceToText FromGeometry   = "geometry"
derivationSourceToText Original       = "original"

-- | Parse derivation source from text.
parseDerivationSource :: Text -> Maybe DerivationSource
parseDerivationSource t = case T.toLower t of
  "logo"       -> Just FromLogo
  "icon"       -> Just FromIcon
  "palette"    -> Just FromPalette
  "colors"     -> Just FromPalette
  "typography" -> Just FromTypography
  "type"       -> Just FromTypography
  "geometry"   -> Just FromGeometry
  "geometric"  -> Just FromGeometry
  "original"   -> Just Original
  "new"        -> Just Original
  _            -> Nothing

instance ToJSON DerivationSource where
  toJSON = toJSON . derivationSourceToText

instance FromJSON DerivationSource where
  parseJSON = withText "DerivationSource" $ \t ->
    case parseDerivationSource t of
      Just ds -> pure ds
      Nothing -> fail $ "Invalid derivation source: " <> T.unpack t

--------------------------------------------------------------------------------
-- Graphic Usage Context
--------------------------------------------------------------------------------

-- | Context where graphic element is used.
data GraphicUsageContext
  = DarkBackgrounds   -- ^ On dark backgrounds
  | LightBackgrounds  -- ^ On light backgrounds
  | AppAndMerch       -- ^ Apparel and merchandise
  | PrintMaterials    -- ^ Print collateral
  | DigitalMedia      -- ^ Digital/web use
  | LargeFormat       -- ^ Large format (billboards, banners)
  | Packaging         -- ^ Product packaging
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

-- | Convert usage context to text.
graphicUsageContextToText :: GraphicUsageContext -> Text
graphicUsageContextToText DarkBackgrounds  = "dark-backgrounds"
graphicUsageContextToText LightBackgrounds = "light-backgrounds"
graphicUsageContextToText AppAndMerch      = "apparel-merch"
graphicUsageContextToText PrintMaterials   = "print"
graphicUsageContextToText DigitalMedia     = "digital"
graphicUsageContextToText LargeFormat      = "large-format"
graphicUsageContextToText Packaging        = "packaging"

-- | Parse usage context from text.
parseGraphicUsageContext :: Text -> Maybe GraphicUsageContext
parseGraphicUsageContext t = case T.toLower t of
  "dark-backgrounds"  -> Just DarkBackgrounds
  "dark"              -> Just DarkBackgrounds
  "light-backgrounds" -> Just LightBackgrounds
  "light"             -> Just LightBackgrounds
  "apparel-merch"     -> Just AppAndMerch
  "apparel"           -> Just AppAndMerch
  "merch"             -> Just AppAndMerch
  "merchandise"       -> Just AppAndMerch
  "print"             -> Just PrintMaterials
  "digital"           -> Just DigitalMedia
  "web"               -> Just DigitalMedia
  "large-format"      -> Just LargeFormat
  "billboard"         -> Just LargeFormat
  "packaging"         -> Just Packaging
  _                   -> Nothing

instance ToJSON GraphicUsageContext where
  toJSON = toJSON . graphicUsageContextToText

instance FromJSON GraphicUsageContext where
  parseJSON = withText "GraphicUsageContext" $ \t ->
    case parseGraphicUsageContext t of
      Just ctx -> pure ctx
      Nothing  -> fail $ "Invalid usage context: " <> T.unpack t

--------------------------------------------------------------------------------
-- Color Treatment
--------------------------------------------------------------------------------

-- | Color treatment for graphic element.
data GraphicColorTreatment = GraphicColorTreatment
  { gctBackgroundType :: !Text
    -- ^ Background type (e.g., "plain", "gradient", "image")
  , gctPrimaryColor   :: !Text
    -- ^ Primary color (hex)
  , gctOpacity        :: !Double
    -- ^ Opacity (0.0 to 1.0)
  }
  deriving stock (Eq, Show, Generic)

-- | Create color treatment with validation.
mkGraphicColorTreatment :: Text -> Text -> Double -> Maybe GraphicColorTreatment
mkGraphicColorTreatment bgType primary opacity
  | T.length bgType >= 1
  , T.length primary >= 4
  , opacity >= 0
  , opacity <= 1
  = Just GraphicColorTreatment
      { gctBackgroundType = bgType
      , gctPrimaryColor   = primary
      , gctOpacity        = opacity
      }
  | otherwise = Nothing

instance ToJSON GraphicColorTreatment where
  toJSON GraphicColorTreatment{..} = object
    [ "backgroundType" .= gctBackgroundType
    , "primaryColor"   .= gctPrimaryColor
    , "opacity"        .= gctOpacity
    ]

instance FromJSON GraphicColorTreatment where
  parseJSON = withObject "GraphicColorTreatment" $ \o -> do
    gctBackgroundType <- o .: "backgroundType"
    gctPrimaryColor   <- o .: "primaryColor"
    gctOpacity        <- o .: "opacity"
    pure GraphicColorTreatment{..}

--------------------------------------------------------------------------------
-- Modification Allowed
--------------------------------------------------------------------------------

-- | Level of modification allowed for element.
data ModificationAllowed
  = NoModification    -- ^ Element is locked
  | ScaleOnly         -- ^ Can only scale (no color/shape change)
  | ColorChange       -- ^ Can change colors within palette
  | ApprovalRequired  -- ^ Changes require approval
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

-- | Convert modification allowed to text.
modificationAllowedToText :: ModificationAllowed -> Text
modificationAllowedToText NoModification   = "none"
modificationAllowedToText ScaleOnly        = "scale-only"
modificationAllowedToText ColorChange      = "color-change"
modificationAllowedToText ApprovalRequired = "approval-required"

-- | Parse modification allowed from text.
parseModificationAllowed :: Text -> Maybe ModificationAllowed
parseModificationAllowed t = case T.toLower t of
  "none"              -> Just NoModification
  "locked"            -> Just NoModification
  "no"                -> Just NoModification
  "scale-only"        -> Just ScaleOnly
  "scale"             -> Just ScaleOnly
  "color-change"      -> Just ColorChange
  "color"             -> Just ColorChange
  "approval-required" -> Just ApprovalRequired
  "approval"          -> Just ApprovalRequired
  _                   -> Nothing

instance ToJSON ModificationAllowed where
  toJSON = toJSON . modificationAllowedToText

instance FromJSON ModificationAllowed where
  parseJSON = withText "ModificationAllowed" $ \t ->
    case parseModificationAllowed t of
      Just ma -> pure ma
      Nothing -> fail $ "Invalid modification allowed: " <> T.unpack t

--------------------------------------------------------------------------------
-- Graphic Element
--------------------------------------------------------------------------------

-- | A graphic element definition.
data GraphicElement = GraphicElement
  { geName             :: !Text
    -- ^ Element identifier/name
  , geType             :: !GraphicElementType
    -- ^ Type of graphic element
  , geDescription      :: !Text
    -- ^ Visual description
  , geDerivation       :: !DerivationSource
    -- ^ Source from which element is derived
  , geUsageContexts    :: !(Vector GraphicUsageContext)
    -- ^ Contexts where element can be used
  , geColorTreatment   :: !GraphicColorTreatment
    -- ^ Color treatment specification
  , geModificationRule :: !ModificationAllowed
    -- ^ What modifications are allowed
  }
  deriving stock (Eq, Show, Generic)

-- | Create graphic element with validation.
mkGraphicElement
  :: Text                          -- ^ Name
  -> GraphicElementType            -- ^ Type
  -> Text                          -- ^ Description
  -> DerivationSource              -- ^ Derivation source
  -> Vector GraphicUsageContext    -- ^ Usage contexts
  -> GraphicColorTreatment         -- ^ Color treatment
  -> ModificationAllowed           -- ^ Modification rule
  -> Maybe GraphicElement
mkGraphicElement name gType desc derivation contexts treatment modRule
  | T.length name >= 1
  , T.length desc >= 1
  = Just GraphicElement
      { geName             = name
      , geType             = gType
      , geDescription      = desc
      , geDerivation       = derivation
      , geUsageContexts    = contexts
      , geColorTreatment   = treatment
      , geModificationRule = modRule
      }
  | otherwise = Nothing

instance ToJSON GraphicElement where
  toJSON GraphicElement{..} = object
    [ "name"             .= geName
    , "type"             .= geType
    , "description"      .= geDescription
    , "derivation"       .= geDerivation
    , "usageContexts"    .= geUsageContexts
    , "colorTreatment"   .= geColorTreatment
    , "modificationRule" .= geModificationRule
    ]

instance FromJSON GraphicElement where
  parseJSON = withObject "GraphicElement" $ \o -> do
    geName             <- o .: "name"
    geType             <- o .: "type"
    geDescription      <- o .: "description"
    geDerivation       <- o .: "derivation"
    geUsageContexts    <- o .: "usageContexts"
    geColorTreatment   <- o .: "colorTreatment"
    geModificationRule <- o .: "modificationRule"
    pure GraphicElement{..}

--------------------------------------------------------------------------------
-- Graphic Elements Specification
--------------------------------------------------------------------------------

-- | Complete graphic elements specification for a brand.
data GraphicElementsSpecification = GraphicElementsSpecification
  { gesElements    :: !(Vector GraphicElement)
    -- ^ All defined graphic elements
  , gesGlobalNotes :: !Text
    -- ^ Global usage notes
  }
  deriving stock (Eq, Show, Generic)

-- | Create specification with validation.
mkGraphicElementsSpecification
  :: Vector GraphicElement
  -> Text
  -> Maybe GraphicElementsSpecification
mkGraphicElementsSpecification elements notes
  | V.length elements >= 1
  = Just GraphicElementsSpecification
      { gesElements    = elements
      , gesGlobalNotes = notes
      }
  | otherwise = Nothing

-- | Default specification for brands without explicit graphic elements.
defaultGraphicElementsSpecification :: GraphicElementsSpecification
defaultGraphicElementsSpecification = GraphicElementsSpecification
  { gesElements = V.singleton GraphicElement
      { geName             = "default-pattern"
      , geType             = Pattern
      , geDescription      = "Simple repeating pattern derived from brand geometry"
      , geDerivation       = FromGeometry
      , geUsageContexts    = V.fromList [DigitalMedia, PrintMaterials]
      , geColorTreatment   = GraphicColorTreatment
          { gctBackgroundType = "plain"
          , gctPrimaryColor   = "#000000"
          , gctOpacity        = 0.1
          }
      , geModificationRule = ColorChange
      }
  , gesGlobalNotes = "Graphic elements should complement, not compete with, primary content."
  }

instance ToJSON GraphicElementsSpecification where
  toJSON GraphicElementsSpecification{..} = object
    [ "elements"    .= gesElements
    , "globalNotes" .= gesGlobalNotes
    ]

instance FromJSON GraphicElementsSpecification where
  parseJSON = withObject "GraphicElementsSpecification" $ \o -> do
    gesElements    <- o .: "elements"
    gesGlobalNotes <- o .: "globalNotes"
    pure GraphicElementsSpecification{..}
