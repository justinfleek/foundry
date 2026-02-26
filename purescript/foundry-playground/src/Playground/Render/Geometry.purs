-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // playground // render // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Geometry primitives for WebGPU rendering.
-- |
-- | This module defines PURE DATA types that describe geometry.
-- | No rendering happens here — these are inputs to the GPU pipeline.
-- |
-- | Everything is bounded, everything composes.

module Playground.Render.Geometry
  ( -- * 2D Points and Vectors
    Vec2
  , mkVec2
  , vec2X
  , vec2Y
  , vec2Add
  , vec2Sub
  , vec2Scale
  , vec2Length
  , vec2Normalize
  
  -- * 3D Points and Vectors (for depth/z-order)
  , Vec3
  , mkVec3
  , vec3X
  , vec3Y
  , vec3Z
  
  -- * 4D Vectors (for colors, transforms)
  , Vec4
  , mkVec4
  
  -- * Rectangles
  , Rect
  , mkRect
  , rectContains
  , rectIntersects
  , rectUnion
  , rectCenter
  , rectWidth
  , rectHeight
  
  -- * Rounded Rectangles
  , RoundedRect
  , mkRoundedRect
  , cornerRadius
  
  -- * Bezier Curves
  , CubicBezier
  , mkCubicBezier
  , bezierStart
  , bezierEnd
  , bezierEvaluate
  
  -- * Transform Matrices
  , Transform2D
  , identityTransform
  , translateTransform
  , scaleTransform
  , rotateTransform
  , composeTransform
  , applyTransform
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
  , (&&)
  , (>=)
  , (<=)
  , show
  , min
  , max
  , negate
  )

import Data.Number (sqrt, sin, cos)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // vec2
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 2D vector / point.
-- |
-- | Used for positions, sizes, offsets.
-- | Components are unbounded Numbers (WebGPU uses f32).
type Vec2 =
  { x :: Number
  , y :: Number
  }

-- | Create a Vec2.
mkVec2 :: Number -> Number -> Vec2
mkVec2 x y = { x, y }

-- | Get X component.
vec2X :: Vec2 -> Number
vec2X v = v.x

-- | Get Y component.
vec2Y :: Vec2 -> Number
vec2Y v = v.y

-- | Vector addition.
vec2Add :: Vec2 -> Vec2 -> Vec2
vec2Add a b = { x: a.x + b.x, y: a.y + b.y }

-- | Vector subtraction.
vec2Sub :: Vec2 -> Vec2 -> Vec2
vec2Sub a b = { x: a.x - b.x, y: a.y - b.y }

-- | Scalar multiplication.
vec2Scale :: Number -> Vec2 -> Vec2
vec2Scale s v = { x: s * v.x, y: s * v.y }

-- | Vector length.
vec2Length :: Vec2 -> Number
vec2Length v = sqrt (v.x * v.x + v.y * v.y)

-- | Normalize to unit length.
vec2Normalize :: Vec2 -> Vec2
vec2Normalize v =
  let len = vec2Length v
  in if len == 0.0 then { x: 0.0, y: 0.0 } else vec2Scale (1.0 / len) v

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // vec3
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 3D vector.
-- |
-- | Used for z-ordering, depth, 3D transforms.
type Vec3 =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Create a Vec3.
mkVec3 :: Number -> Number -> Number -> Vec3
mkVec3 x y z = { x, y, z }

-- | Get X.
vec3X :: Vec3 -> Number
vec3X v = v.x

-- | Get Y.
vec3Y :: Vec3 -> Number
vec3Y v = v.y

-- | Get Z.
vec3Z :: Vec3 -> Number
vec3Z v = v.z

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // vec4
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 4D vector.
-- |
-- | Used for RGBA colors, homogeneous coordinates.
type Vec4 =
  { x :: Number
  , y :: Number
  , z :: Number
  , w :: Number
  }

-- | Create a Vec4.
mkVec4 :: Number -> Number -> Number -> Number -> Vec4
mkVec4 x y z w = { x, y, z, w }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // rect
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Axis-aligned rectangle.
-- |
-- | Defined by min corner and max corner (not position + size).
-- | This representation makes union/intersection natural.
type Rect =
  { minX :: Number
  , minY :: Number
  , maxX :: Number
  , maxY :: Number
  }

-- | Create a Rect from min/max corners.
-- |
-- | Normalizes so min <= max.
mkRect :: Number -> Number -> Number -> Number -> Rect
mkRect x0 y0 x1 y1 =
  { minX: min x0 x1
  , minY: min y0 y1
  , maxX: max x0 x1
  , maxY: max y0 y1
  }

-- | Check if point is inside rect.
rectContains :: Rect -> Vec2 -> Boolean
rectContains r p =
  p.x >= r.minX && p.x <= r.maxX &&
  p.y >= r.minY && p.y <= r.maxY

-- | Check if two rects intersect.
rectIntersects :: Rect -> Rect -> Boolean
rectIntersects a b =
  a.minX <= b.maxX && a.maxX >= b.minX &&
  a.minY <= b.maxY && a.maxY >= b.minY

-- | Union of two rects (bounding box).
rectUnion :: Rect -> Rect -> Rect
rectUnion a b =
  { minX: min a.minX b.minX
  , minY: min a.minY b.minY
  , maxX: max a.maxX b.maxX
  , maxY: max a.maxY b.maxY
  }

-- | Center point of rect.
rectCenter :: Rect -> Vec2
rectCenter r =
  { x: (r.minX + r.maxX) / 2.0
  , y: (r.minY + r.maxY) / 2.0
  }

-- | Width of rect.
rectWidth :: Rect -> Number
rectWidth r = r.maxX - r.minX

-- | Height of rect.
rectHeight :: Rect -> Number
rectHeight r = r.maxY - r.minY

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // rounded rect
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Rounded rectangle.
-- |
-- | A rect with corner radii. All four corners use the same radius.
-- | Radius is clamped to half the smaller dimension.
type RoundedRect =
  { bounds :: Rect
  , radius :: Number    -- Corner radius (bounded)
  }

-- | Create a rounded rect.
-- |
-- | Radius is clamped to valid range.
mkRoundedRect :: Rect -> Number -> RoundedRect
mkRoundedRect bounds r =
  let
    maxRadius = min (rectWidth bounds) (rectHeight bounds) / 2.0
    clampedRadius = max 0.0 (min r maxRadius)
  in
    { bounds, radius: clampedRadius }

-- | Get corner radius.
cornerRadius :: RoundedRect -> Number
cornerRadius rr = rr.radius

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // cubic bezier
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Cubic bezier curve.
-- |
-- | Four control points: start, control1, control2, end.
-- | Used for smooth connections between nodes.
type CubicBezier =
  { p0 :: Vec2    -- Start point
  , p1 :: Vec2    -- Control point 1
  , p2 :: Vec2    -- Control point 2
  , p3 :: Vec2    -- End point
  }

-- | Create a cubic bezier.
mkCubicBezier :: Vec2 -> Vec2 -> Vec2 -> Vec2 -> CubicBezier
mkCubicBezier p0 p1 p2 p3 = { p0, p1, p2, p3 }

-- | Get start point.
bezierStart :: CubicBezier -> Vec2
bezierStart b = b.p0

-- | Get end point.
bezierEnd :: CubicBezier -> Vec2
bezierEnd b = b.p3

-- | Evaluate bezier at parameter t (0 to 1).
-- |
-- | Uses De Casteljau's algorithm.
bezierEvaluate :: CubicBezier -> Number -> Vec2
bezierEvaluate b t =
  let
    t2 = t * t
    t3 = t2 * t
    mt = 1.0 - t
    mt2 = mt * mt
    mt3 = mt2 * mt
    
    x = mt3 * b.p0.x + 3.0 * mt2 * t * b.p1.x + 3.0 * mt * t2 * b.p2.x + t3 * b.p3.x
    y = mt3 * b.p0.y + 3.0 * mt2 * t * b.p1.y + 3.0 * mt * t2 * b.p2.y + t3 * b.p3.y
  in
    { x, y }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // transform
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 2D affine transform (3x3 matrix, bottom row always [0,0,1]).
-- |
-- | Stored as 6 components: a, b, c, d, e, f
-- | Matrix form:
-- |   | a c e |
-- |   | b d f |
-- |   | 0 0 1 |
type Transform2D =
  { a :: Number    -- scale x / rotate
  , b :: Number    -- skew y / rotate
  , c :: Number    -- skew x / rotate
  , d :: Number    -- scale y / rotate
  , e :: Number    -- translate x
  , f :: Number    -- translate y
  }

-- | Identity transform.
identityTransform :: Transform2D
identityTransform =
  { a: 1.0, b: 0.0
  , c: 0.0, d: 1.0
  , e: 0.0, f: 0.0
  }

-- | Translation transform.
translateTransform :: Number -> Number -> Transform2D
translateTransform tx ty =
  { a: 1.0, b: 0.0
  , c: 0.0, d: 1.0
  , e: tx, f: ty
  }

-- | Scale transform.
scaleTransform :: Number -> Number -> Transform2D
scaleTransform sx sy =
  { a: sx, b: 0.0
  , c: 0.0, d: sy
  , e: 0.0, f: 0.0
  }

-- | Rotation transform (angle in radians).
rotateTransform :: Number -> Transform2D
rotateTransform angle =
  let
    c = cos angle
    s = sin angle
  in
    { a: c, b: s
    , c: negate s, d: c
    , e: 0.0, f: 0.0
    }

-- | Compose two transforms (matrix multiplication).
-- |
-- | composeTransform a b = apply a then b
composeTransform :: Transform2D -> Transform2D -> Transform2D
composeTransform t1 t2 =
  { a: t1.a * t2.a + t1.c * t2.b
  , b: t1.b * t2.a + t1.d * t2.b
  , c: t1.a * t2.c + t1.c * t2.d
  , d: t1.b * t2.c + t1.d * t2.d
  , e: t1.a * t2.e + t1.c * t2.f + t1.e
  , f: t1.b * t2.e + t1.d * t2.f + t1.f
  }

-- | Apply transform to point.
applyTransform :: Transform2D -> Vec2 -> Vec2
applyTransform t p =
  { x: t.a * p.x + t.c * p.y + t.e
  , y: t.b * p.x + t.d * p.y + t.f
  }
