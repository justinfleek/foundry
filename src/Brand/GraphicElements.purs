-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // brand // graphicelements
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SMART Framework Graphic Elements Layer: Patterns, textures, and
-- | logo-derived visual motifs.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | Supplementary visual assets derived from the brand identity that add
-- | texture, pattern, and visual interest to compositions. These weave
-- | aspects of the logo or brand motifs into a consistent visual language.
-- |
-- | SMART FRAMEWORK:
-- |   S - Story-driven: Elements derive from logo/brand symbolism
-- |   M - Memorable: Consistent patterns create recognition
-- |   A - Agile: Adapts to different contexts (dark bg, apparel, print)
-- |   R - Responsive: Scales from digital to physical
-- |   T - Targeted: Context-specific usage rules
-- |
-- | DEPENDENCIES:
-- |   - None (foundational module)
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Brand (compound Brand type)

module Hydrogen.Schema.Brand.GraphicElements
  ( -- * Element Type
    GraphicElementType
      ( Pattern
      , Texture
      , StrokeShape
      , LogoDerivedPattern
      , Motif
      , Ornament
      )
  , elementTypeToString
  , parseElementType
  
  -- * Derivation Source
  , DerivationSource
      ( FromLogo
      , FromIcon
      , FromPalette
      , FromTypography
      , FromGeometry
      , Original
      )
  , derivationSourceToString
  , parseDerivationSource
  
  -- * Usage Context
  , GraphicUsageContext
      ( DarkBackgrounds
      , LightBackgrounds
      , AppAndMerch
      , PrintMaterials
      , DigitalMedia
      , LargeFormat
      , Packaging
      )
  , graphicUsageContextToString
  , parseGraphicUsageContext
  
  -- * Color Treatment
  , GraphicColorTreatment
  , mkGraphicColorTreatment
  , treatmentBackgroundType
  , treatmentPrimaryColor
  , treatmentOpacity
  
  -- * Modification Rule
  , ModificationAllowed
      ( NoModification
      , ScaleOnly
      , ColorChange
      , ApprovalRequired
      )
  , modificationAllowedToString
  , parseModificationAllowed
  
  -- * Graphic Element
  , GraphicElement
  , mkGraphicElement
  , elementName
  , elementType
  , elementDescription
  , elementDerivation
  , elementUsageContexts
  , elementColorTreatment
  , elementModificationRule
  
  -- * Complete Graphic Elements Specification
  , GraphicElementsSpecification
  , mkGraphicElementsSpecification
  , specElements
  , specGlobalNotes
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>=)
  , (>)
  , (&&)
  , (<=)
  , (<>)
  , show
  , compare
  )

import Data.Array (length) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, toLower) as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // element type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Type of graphic element.
data GraphicElementType
  = Pattern             -- Repeating visual pattern
  | Texture             -- Surface texture/grain
  | StrokeShape         -- Outlined shape (rounded rect, circle, pill)
  | LogoDerivedPattern  -- Pattern from logo geometry
  | Motif               -- Recurring design element
  | Ornament            -- Decorative accent

derive instance eqGraphicElementType :: Eq GraphicElementType

instance ordGraphicElementType :: Ord GraphicElementType where
  compare t1 t2 = compare (typeToInt t1) (typeToInt t2)
    where
      typeToInt :: GraphicElementType -> Int
      typeToInt Pattern = 0
      typeToInt Texture = 1
      typeToInt StrokeShape = 2
      typeToInt LogoDerivedPattern = 3
      typeToInt Motif = 4
      typeToInt Ornament = 5

instance showGraphicElementType :: Show GraphicElementType where
  show = elementTypeToString

-- | Convert element type to string.
elementTypeToString :: GraphicElementType -> String
elementTypeToString Pattern = "pattern"
elementTypeToString Texture = "texture"
elementTypeToString StrokeShape = "stroke-shape"
elementTypeToString LogoDerivedPattern = "logo-derived-pattern"
elementTypeToString Motif = "motif"
elementTypeToString Ornament = "ornament"

-- | Parse element type from string.
parseElementType :: String -> Maybe GraphicElementType
parseElementType s = case String.toLower s of
  "pattern" -> Just Pattern
  "texture" -> Just Texture
  "stroke-shape" -> Just StrokeShape
  "stroke" -> Just StrokeShape
  "shape" -> Just StrokeShape
  "logo-derived-pattern" -> Just LogoDerivedPattern
  "logo-pattern" -> Just LogoDerivedPattern
  "motif" -> Just Motif
  "ornament" -> Just Ornament
  "decoration" -> Just Ornament
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // derivation source
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Source from which graphic element is derived.
data DerivationSource
  = FromLogo           -- Derived from logo/icon
  | FromIcon           -- Derived from icon specifically
  | FromPalette        -- Derived from color palette
  | FromTypography     -- Derived from type treatment
  | FromGeometry       -- Derived from brand geometry
  | Original           -- Original creation (not derived)

derive instance eqDerivationSource :: Eq DerivationSource

instance ordDerivationSource :: Ord DerivationSource where
  compare d1 d2 = compare (deriveToInt d1) (deriveToInt d2)
    where
      deriveToInt :: DerivationSource -> Int
      deriveToInt FromLogo = 0
      deriveToInt FromIcon = 1
      deriveToInt FromPalette = 2
      deriveToInt FromTypography = 3
      deriveToInt FromGeometry = 4
      deriveToInt Original = 5

instance showDerivationSource :: Show DerivationSource where
  show = derivationSourceToString

-- | Convert derivation source to string.
derivationSourceToString :: DerivationSource -> String
derivationSourceToString FromLogo = "logo"
derivationSourceToString FromIcon = "icon"
derivationSourceToString FromPalette = "palette"
derivationSourceToString FromTypography = "typography"
derivationSourceToString FromGeometry = "geometry"
derivationSourceToString Original = "original"

-- | Parse derivation source from string.
parseDerivationSource :: String -> Maybe DerivationSource
parseDerivationSource s = case String.toLower s of
  "logo" -> Just FromLogo
  "icon" -> Just FromIcon
  "palette" -> Just FromPalette
  "colors" -> Just FromPalette
  "typography" -> Just FromTypography
  "type" -> Just FromTypography
  "geometry" -> Just FromGeometry
  "geometric" -> Just FromGeometry
  "original" -> Just Original
  "new" -> Just Original
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // graphic usage context
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Context where graphic element is used.
data GraphicUsageContext
  = DarkBackgrounds    -- On dark backgrounds
  | LightBackgrounds   -- On light backgrounds
  | AppAndMerch        -- Apparel and merchandise
  | PrintMaterials     -- Print collateral
  | DigitalMedia       -- Digital/web use
  | LargeFormat        -- Large format (billboards, banners)
  | Packaging          -- Product packaging

derive instance eqGraphicUsageContext :: Eq GraphicUsageContext

instance ordGraphicUsageContext :: Ord GraphicUsageContext where
  compare c1 c2 = compare (ctxToInt c1) (ctxToInt c2)
    where
      ctxToInt :: GraphicUsageContext -> Int
      ctxToInt DarkBackgrounds = 0
      ctxToInt LightBackgrounds = 1
      ctxToInt AppAndMerch = 2
      ctxToInt PrintMaterials = 3
      ctxToInt DigitalMedia = 4
      ctxToInt LargeFormat = 5
      ctxToInt Packaging = 6

instance showGraphicUsageContext :: Show GraphicUsageContext where
  show = graphicUsageContextToString

-- | Convert graphic usage context to string.
graphicUsageContextToString :: GraphicUsageContext -> String
graphicUsageContextToString DarkBackgrounds = "dark-backgrounds"
graphicUsageContextToString LightBackgrounds = "light-backgrounds"
graphicUsageContextToString AppAndMerch = "apparel-merch"
graphicUsageContextToString PrintMaterials = "print"
graphicUsageContextToString DigitalMedia = "digital"
graphicUsageContextToString LargeFormat = "large-format"
graphicUsageContextToString Packaging = "packaging"

-- | Parse graphic usage context from string.
parseGraphicUsageContext :: String -> Maybe GraphicUsageContext
parseGraphicUsageContext s = case String.toLower s of
  "dark-backgrounds" -> Just DarkBackgrounds
  "dark" -> Just DarkBackgrounds
  "light-backgrounds" -> Just LightBackgrounds
  "light" -> Just LightBackgrounds
  "apparel-merch" -> Just AppAndMerch
  "apparel" -> Just AppAndMerch
  "merch" -> Just AppAndMerch
  "merchandise" -> Just AppAndMerch
  "print" -> Just PrintMaterials
  "digital" -> Just DigitalMedia
  "web" -> Just DigitalMedia
  "large-format" -> Just LargeFormat
  "billboard" -> Just LargeFormat
  "packaging" -> Just Packaging
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // color treatment
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Color treatment for graphic element.
type GraphicColorTreatment =
  { backgroundType :: String     -- e.g., "plain", "gradient", "image"
  , primaryColor :: String       -- Primary color hex
  , opacity :: Number            -- Opacity 0.0 to 1.0
  }

-- | Create graphic color treatment.
mkGraphicColorTreatment :: String -> String -> Number -> Maybe GraphicColorTreatment
mkGraphicColorTreatment bgType primary opacity =
  if String.length bgType >= 1 
     && String.length primary >= 4 
     && opacity >= 0.0 
     && opacity <= 1.0
    then Just
      { backgroundType: bgType
      , primaryColor: primary
      , opacity: opacity
      }
    else Nothing

-- | Get background type.
treatmentBackgroundType :: GraphicColorTreatment -> String
treatmentBackgroundType gct = gct.backgroundType

-- | Get primary color.
treatmentPrimaryColor :: GraphicColorTreatment -> String
treatmentPrimaryColor gct = gct.primaryColor

-- | Get opacity.
treatmentOpacity :: GraphicColorTreatment -> Number
treatmentOpacity gct = gct.opacity

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // modification allowed
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Level of modification allowed.
data ModificationAllowed
  = NoModification      -- Element is locked
  | ScaleOnly           -- Can only scale (no color/shape change)
  | ColorChange         -- Can change colors within palette
  | ApprovalRequired    -- Changes require approval

derive instance eqModificationAllowed :: Eq ModificationAllowed

instance ordModificationAllowed :: Ord ModificationAllowed where
  compare m1 m2 = compare (modToInt m1) (modToInt m2)
    where
      modToInt :: ModificationAllowed -> Int
      modToInt NoModification = 0
      modToInt ScaleOnly = 1
      modToInt ColorChange = 2
      modToInt ApprovalRequired = 3

instance showModificationAllowed :: Show ModificationAllowed where
  show = modificationAllowedToString

-- | Convert modification allowed to string.
modificationAllowedToString :: ModificationAllowed -> String
modificationAllowedToString NoModification = "none"
modificationAllowedToString ScaleOnly = "scale-only"
modificationAllowedToString ColorChange = "color-change"
modificationAllowedToString ApprovalRequired = "approval-required"

-- | Parse modification allowed from string.
parseModificationAllowed :: String -> Maybe ModificationAllowed
parseModificationAllowed s = case String.toLower s of
  "none" -> Just NoModification
  "locked" -> Just NoModification
  "no" -> Just NoModification
  "scale-only" -> Just ScaleOnly
  "scale" -> Just ScaleOnly
  "color-change" -> Just ColorChange
  "color" -> Just ColorChange
  "approval-required" -> Just ApprovalRequired
  "approval" -> Just ApprovalRequired
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // graphic element
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A graphic element definition.
type GraphicElement =
  { name :: String                             -- Element identifier
  , gType :: GraphicElementType
  , description :: String                      -- Visual description
  , derivation :: DerivationSource
  , usageContexts :: Array GraphicUsageContext
  , colorTreatment :: GraphicColorTreatment
  , modificationRule :: ModificationAllowed
  }

-- | Create graphic element.
mkGraphicElement
  :: String
  -> GraphicElementType
  -> String
  -> DerivationSource
  -> Array GraphicUsageContext
  -> GraphicColorTreatment
  -> ModificationAllowed
  -> Maybe GraphicElement
mkGraphicElement name gType desc derivation contexts treatment mod =
  if String.length name >= 1 && String.length desc >= 1
    then Just
      { name: name
      , gType: gType
      , description: desc
      , derivation: derivation
      , usageContexts: contexts
      , colorTreatment: treatment
      , modificationRule: mod
      }
    else Nothing

-- | Get element name.
elementName :: GraphicElement -> String
elementName ge = ge.name

-- | Get element type.
elementType :: GraphicElement -> GraphicElementType
elementType ge = ge.gType

-- | Get element description.
elementDescription :: GraphicElement -> String
elementDescription ge = ge.description

-- | Get derivation source.
elementDerivation :: GraphicElement -> DerivationSource
elementDerivation ge = ge.derivation

-- | Get usage contexts.
elementUsageContexts :: GraphicElement -> Array GraphicUsageContext
elementUsageContexts ge = ge.usageContexts

-- | Get color treatment.
elementColorTreatment :: GraphicElement -> GraphicColorTreatment
elementColorTreatment ge = ge.colorTreatment

-- | Get modification rule.
elementModificationRule :: GraphicElement -> ModificationAllowed
elementModificationRule ge = ge.modificationRule

-- ═══════════════════════════════════════════════════════════════════════════════
--                                             // graphic elements specification
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete graphic elements specification for a brand.
type GraphicElementsSpecification =
  { elements :: Array GraphicElement
  , globalNotes :: String                -- Global usage notes
  }

-- | Create graphic elements specification.
mkGraphicElementsSpecification
  :: Array GraphicElement
  -> String
  -> Maybe GraphicElementsSpecification
mkGraphicElementsSpecification elements notes =
  if Array.length elements >= 1
    then Just { elements: elements, globalNotes: notes }
    else Nothing

-- | Get all elements.
specElements :: GraphicElementsSpecification -> Array GraphicElement
specElements ges = ges.elements

-- | Get global notes.
specGlobalNotes :: GraphicElementsSpecification -> String
specGlobalNotes ges = ges.globalNotes
