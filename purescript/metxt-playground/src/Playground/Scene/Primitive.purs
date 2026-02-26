-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // playground // scene // primitive
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scene primitives — the vocabulary of visual elements.
-- |
-- | A scene is built from these primitives. Each primitive is PURE DATA
-- | describing what to render. The GPU pipeline interprets this data.
-- |
-- | No DOM, no CSS, no JavaScript — just typed descriptions.

module Playground.Scene.Primitive
  ( -- * Fill Types
    Fill(..)
  , solidFill
  , gradientFill
  , noFill
  
  -- * Stroke Types
  , Stroke
  , mkStroke
  , noStroke
  
  -- * Text Rendering
  , TextAnchor(..)
  , TextBaseline(..)
  , TextSpec
  , mkTextSpec
  
  -- * Primitives
  , Primitive(..)
  
  -- * Primitive Constructors
  , rectangle
  , roundedRectangle
  , circle
  , line
  , bezierCurve
  , text
  , group
  
  -- * Primitive Properties
  , primitiveBounds
  ) where

import Prelude
  ( class Eq
  , class Show
  , (==)
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , show
  , map
  , min
  , max
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(..))

import Playground.Render.Geometry
  ( Vec2
  , mkVec2
  , Rect
  , mkRect
  , RoundedRect
  , mkRoundedRect
  , CubicBezier
  , Transform2D
  , identityTransform
  , rectUnion
  , rectWidth
  , rectHeight
  )

import Playground.Render.Color (LinearRGBA, transparentLinear)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // fill
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Fill specification for shapes.
data Fill
  = NoFill
  | SolidFill LinearRGBA
  | LinearGradient
      { start :: Vec2
      , end :: Vec2
      , stops :: Array GradientStop
      }
  | RadialGradient
      { center :: Vec2
      , radius :: Number
      , stops :: Array GradientStop
      }

-- | Gradient color stop.
type GradientStop =
  { offset :: Number      -- 0 to 1
  , color :: LinearRGBA
  }

derive instance eqFill :: Eq Fill

-- | Solid color fill.
solidFill :: LinearRGBA -> Fill
solidFill = SolidFill

-- | Linear gradient fill.
gradientFill :: Vec2 -> Vec2 -> Array GradientStop -> Fill
gradientFill start end stops = LinearGradient { start, end, stops }

-- | No fill (transparent).
noFill :: Fill
noFill = NoFill

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // stroke
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Stroke specification for shapes and lines.
type Stroke =
  { color :: LinearRGBA
  , width :: Number         -- In logical units (> 0)
  , lineCap :: LineCap
  , lineJoin :: LineJoin
  }

-- | Line cap style.
data LineCap = ButtCap | RoundCap | SquareCap

derive instance eqLineCap :: Eq LineCap

-- | Line join style.
data LineJoin = MiterJoin | RoundJoin | BevelJoin

derive instance eqLineJoin :: Eq LineJoin

-- | Create a stroke.
mkStroke :: LinearRGBA -> Number -> Stroke
mkStroke color width =
  { color
  , width: max 0.0 width
  , lineCap: RoundCap
  , lineJoin: RoundJoin
  }

-- | No stroke.
noStroke :: Maybe Stroke
noStroke = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // text
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Text horizontal anchor.
data TextAnchor = AnchorStart | AnchorMiddle | AnchorEnd

derive instance eqTextAnchor :: Eq TextAnchor

-- | Text vertical baseline.
data TextBaseline = BaselineTop | BaselineMiddle | BaselineBottom

derive instance eqTextBaseline :: Eq TextBaseline

-- | Text rendering specification.
-- |
-- | Font family comes from brand typography — it's an atom.
type TextSpec =
  { content :: String
  , fontFamily :: String    -- Font family name
  , fontSize :: Number      -- In logical units
  , fontWeight :: Int       -- 100-900
  , anchor :: TextAnchor
  , baseline :: TextBaseline
  , fill :: Fill
  }

-- | Create text spec with defaults.
mkTextSpec :: String -> String -> Number -> TextSpec
mkTextSpec content fontFamily fontSize =
  { content
  , fontFamily
  , fontSize
  , fontWeight: 400
  , anchor: AnchorStart
  , baseline: BaselineTop
  , fill: SolidFill { r: 1.0, g: 1.0, b: 1.0, a: 1.0 }
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // primitive
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A renderable primitive.
-- |
-- | This is the atomic unit of the scene graph.
-- | Primitives compose into groups, groups compose into scenes.
data Primitive
  = RectPrimitive
      { bounds :: Rect
      , fill :: Fill
      , stroke :: Maybe Stroke
      }
  | RoundedRectPrimitive
      { bounds :: RoundedRect
      , fill :: Fill
      , stroke :: Maybe Stroke
      }
  | CirclePrimitive
      { center :: Vec2
      , radius :: Number
      , fill :: Fill
      , stroke :: Maybe Stroke
      }
  | LinePrimitive
      { start :: Vec2
      , end :: Vec2
      , stroke :: Stroke
      }
  | BezierPrimitive
      { curve :: CubicBezier
      , stroke :: Stroke
      }
  | TextPrimitive
      { position :: Vec2
      , spec :: TextSpec
      }
  | GroupPrimitive
      { children :: Array Primitive
      , transform :: Transform2D
      }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // primitive constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a rectangle primitive.
rectangle :: Rect -> Fill -> Maybe Stroke -> Primitive
rectangle bounds fill stroke = RectPrimitive { bounds, fill, stroke }

-- | Create a rounded rectangle primitive.
roundedRectangle :: Rect -> Number -> Fill -> Maybe Stroke -> Primitive
roundedRectangle bounds radius fill stroke =
  RoundedRectPrimitive
    { bounds: mkRoundedRect bounds radius
    , fill
    , stroke
    }

-- | Create a circle primitive.
circle :: Vec2 -> Number -> Fill -> Maybe Stroke -> Primitive
circle center radius fill stroke =
  CirclePrimitive { center, radius: max 0.0 radius, fill, stroke }

-- | Create a line primitive.
line :: Vec2 -> Vec2 -> Stroke -> Primitive
line start end stroke = LinePrimitive { start, end, stroke }

-- | Create a bezier curve primitive.
bezierCurve :: CubicBezier -> Stroke -> Primitive
bezierCurve curve stroke = BezierPrimitive { curve, stroke }

-- | Create a text primitive.
text :: Vec2 -> TextSpec -> Primitive
text position spec = TextPrimitive { position, spec }

-- | Create a group of primitives with transform.
group :: Array Primitive -> Transform2D -> Primitive
group children transform = GroupPrimitive { children, transform }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // primitive properties
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compute axis-aligned bounding box of a primitive.
primitiveBounds :: Primitive -> Rect
primitiveBounds prim = case prim of
  RectPrimitive { bounds } -> bounds
  
  RoundedRectPrimitive { bounds } -> bounds.bounds
  
  CirclePrimitive { center, radius } ->
    mkRect 
      (center.x - radius) (center.y - radius)
      (center.x + radius) (center.y + radius)
  
  LinePrimitive { start, end } ->
    mkRect start.x start.y end.x end.y
  
  BezierPrimitive { curve } ->
    -- Conservative: bounding box of control points
    mkRect
      (min4 curve.p0.x curve.p1.x curve.p2.x curve.p3.x)
      (min4 curve.p0.y curve.p1.y curve.p2.y curve.p3.y)
      (max4 curve.p0.x curve.p1.x curve.p2.x curve.p3.x)
      (max4 curve.p0.y curve.p1.y curve.p2.y curve.p3.y)
  
  TextPrimitive { position, spec } ->
    -- Approximate: assumes text goes right and down from position
    mkRect position.x position.y 
           (position.x + estimateTextWidth spec)
           (position.y + spec.fontSize)
  
  GroupPrimitive { children } ->
    case children of
      [] -> mkRect 0.0 0.0 0.0 0.0
      _ -> foldl rectUnion (primitiveBounds (unsafeHead children)) 
                           (map primitiveBounds (unsafeTail children))

-- | Min of four numbers.
min4 :: Number -> Number -> Number -> Number -> Number
min4 a b c d = min (min a b) (min c d)

-- | Max of four numbers.
max4 :: Number -> Number -> Number -> Number -> Number
max4 a b c d = max (max a b) (max c d)

-- | Estimate text width (very rough — real measurement needs font metrics).
estimateTextWidth :: TextSpec -> Number
estimateTextWidth spec =
  -- Rough estimate: 0.6 * fontSize * character count
  0.6 * spec.fontSize * toNumber (stringLength spec.content)

foreign import stringLength :: String -> Int
foreign import toNumber :: Int -> Number
foreign import unsafeHead :: forall a. Array a -> a
foreign import unsafeTail :: forall a. Array a -> Array a
