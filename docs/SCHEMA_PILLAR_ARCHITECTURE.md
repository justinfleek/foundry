# Hydrogen Schema Pillar Architecture

## Compositing System Reference

> **The purest motion graphics language ever created.**
>
> Every element is a composition. Every composition is deterministic.
> Same data = same pixels. Always.

---

## Executive Summary

The Hydrogen Schema provides a **complete motion graphics compositing system** distributed across 38 pillars with 1,114+ files. The architecture follows an atoms → molecules → compounds composition pattern, with full support for:

- **Layers** — 56 typed layer variants with content, blend modes, track mattes
- **Timelines** — Frame-based animation with time remapping and keyframes
- **Effects** — Full effect chain with blur, distortion, glow, stylize
- **Triggers** — Interactive relationships, gestures, and easter eggs
- **Identity** — UUID5 deterministic identity for all elements
- **CoEffects** — Graded monads tracking resource requirements
- **Bounded primitives** — NaN/Infinity-safe foundation

---

## Core Compositing Stack

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Motion.Composition                                     │
│   CompositionSettings: width, height, fps, duration, colorSpace, bitDepth    │
│   CompositionId: UUID5 deterministic identity                                 │
└──────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌──────────────────────────────────────────────────────────────────────────────┐
│                        Motion.Layer (56 LAYER TYPES)                          │
│                                                                               │
│  Media:      LTImage, LTVideo, LTAudio, LTSolid                              │
│  Content:    LTText, LTShape, LTPath                                         │
│  3D:         LTCamera, LTLight, LTMesh, LTEnvironment, LTVolume              │
│  Effects:    LTAdjustment, LTEffect                                          │
│  Comp:       LTPreComp, LTGroup, LTNestedComp                                │
│  Vector:     LTSVG, LTLottie, LTRive, LTVectorGraphic                        │
│  Audio:      LTWaveform, LTSpectrogram, LTMIDI                               │
│  Data:       LTCSV, LTJSON, LTGeoJSON                                        │
│  Tracking:   LTTracker, LTPlanarTracking, LTStabilizer                       │
│  Utility:    LTReference, LTGrid, LTGuide, LTMask, LTRoto                    │
│                                                                               │
│  LayerBase: id, name, visible, locked, solo, shy, startFrame, endFrame,      │
│             inPoint, outPoint, stretch, parentId, blendMode, opacity,        │
│             motionBlur, is3D, trackMatteMode                                 │
└──────────────────────────────────────────────────────────────────────────────┘
                                    │
         ┌──────────────────────────┼──────────────────────────┐
         ▼                          ▼                          ▼
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│  Motion.Timeline│    │  Motion.Keyframe│    │  Motion.Effects │
│                 │    │                 │    │                 │
│  - FrameRate    │    │  - KeyframeId   │    │  - 12 categories│
│  - totalFrames  │    │  - Frames pos   │    │  - blur, distort│
│  - layers[]     │    │  - KeyframeValue│    │  - glow, stylize│
│  - looping      │    │  - Interpolation│    │  - time, noise  │
│  - timeRemap    │    │  - Tangent      │    │  - keying, matte│
└─────────────────┘    └─────────────────┘    └─────────────────┘
```

---

## Layer Architecture

### The Layer Mental Model

Think of this like a motion graphics compositor working in After Effects:

```
     Z-Index ↑
         │
         │   ┌─────────────────────────────────────────┐
         │   │  Layer 5: Particle System               │ ← Physics.Particle
         │   │  (sparks on hover, trails on drag)      │   Temporal.Keyframe
         │   └─────────────────────────────────────────┘
         │   ┌─────────────────────────────────────────┐
         │   │  Layer 4: Fluid Simulation              │ ← Physics.Fluid
         │   │  (responds to phone tilt via Gestural)  │   Gestural.Tilt
         │   └─────────────────────────────────────────┘
         │   ┌─────────────────────────────────────────┐
         │   │  Layer 3: Lottie/Motion Path            │ ← Motion.Path
         │   │  (animated icon, entrance/exit)         │   Motion.Lottie
         │   └─────────────────────────────────────────┘
         │   ┌─────────────────────────────────────────┐
         │   │  Layer 2: Glow/Shadow/Elevation         │ ← Elevation.Shadow
         │   │  (3D depth, light response)             │   Color.Glow
         │   └─────────────────────────────────────────┘
         │   ┌─────────────────────────────────────────┐
         │   │  Layer 1: Material (clipped by shape)   │ ← Surface.Fill
         │   │  (gradient, noise, texture)             │   Surface.Material
         │   └─────────────────────────────────────────┘
         │   ┌─────────────────────────────────────────┐
         │   │  Layer 0: Shape Mask                    │ ← Geometry.Shape
         │   │  (corner radii, bezier, clip path)      │   Geometry.Path
         │   └─────────────────────────────────────────┘
         │
         ▼ Z = 0
```

Each layer has:

| Property | Type | Description |
|----------|------|-------------|
| `id` | `UUID5` | Deterministic identity |
| `zIndex` | `ZIndex` | Bounded Int (0-9999) |
| `material` | `Material` | What fills the layer |
| `mask` | `Shape` | What clips the material |
| `timeline` | `Timeline` | Start, end, keyframes |
| `motionPath` | `MotionPath` | Position/scale/rotation curves |
| `effects` | `Array Effect` | Post-process effects |
| `triggers` | `Array Trigger` | What activates animations |
| `coEffects` | `CoEffectSet` | What this layer NEEDS |

### LayerType Variants (56 Types)

```purescript
data LayerType
  -- Media
  = LTImage | LTVideo | LTAudio | LTSolid
  
  -- Content
  | LTText | LTShape | LTNull
  
  -- 3D
  | LTCamera | LTLight | LTMesh | LTEnvironment | LTVolume
  
  -- Effects
  | LTAdjustment | LTEffect
  
  -- Composition
  | LTPreComp | LTGroup | LTNestedComp
  
  -- Vector
  | LTSVG | LTLottie | LTRive | LTVectorGraphic
  
  -- Audio
  | LTWaveform | LTSpectrogram | LTMIDI
  
  -- Data
  | LTCSV | LTJSON | LTGeoJSON
  
  -- Tracking
  | LTTracker | LTPlanarTracking | LTStabilizer
  
  -- Utility
  | LTReference | LTGrid | LTGuide | LTMask | LTRoto
  
  -- ... and more
```

### LayerBase Record

```purescript
type LayerBase =
  { layerId            :: LayerId
  , layerName          :: String
  , layerType          :: LayerType
  -- Visibility
  , layerVisible       :: Boolean
  , layerLocked        :: Boolean
  , layerSolo          :: Boolean
  , layerShy           :: Boolean
  -- Timing
  , layerStartFrame    :: Frames
  , layerEndFrame      :: Frames
  , layerInPoint       :: Frames
  , layerOutPoint      :: Frames
  , layerStretch       :: Number
  -- Hierarchy
  , layerParentId      :: Maybe LayerId
  , layerTrackMatteMode :: TrackMatteMode
  , layerTrackMatteLayerId :: Maybe LayerId
  -- Rendering
  , layerBlendMode     :: BlendMode
  , layerOpacity       :: Opacity
  , layerMotionBlur    :: Boolean
  , layerIs3D          :: Boolean
  }
```

---

## Blend Modes (28 Porter-Duff/SVG)

```purescript
data BlendMode
  -- Standard
  = BMNormal | BMMultiply | BMScreen | BMOverlay
  
  -- Darken
  | BMDarken | BMColorBurn | BMLinearBurn | BMDarkerColor
  
  -- Lighten
  | BMLighten | BMColorDodge | BMLinearDodge | BMLighterColor
  
  -- Contrast
  | BMHardLight | BMSoftLight | BMVividLight | BMLinearLight
  | BMPinLight | BMHardMix
  
  -- Inversion
  | BMDifference | BMExclusion | BMSubtract | BMDivide
  
  -- Component
  | BMHue | BMSaturation | BMColor | BMLuminosity
  
  -- Arithmetic
  | BMAdd | BMDissolve
```

### Track Matte Modes

```purescript
data TrackMatteMode
  = TMNone
  | TMAlpha
  | TMAlphaInverted
  | TMLuma
  | TMLumaInverted
```

---

## Timeline System

### Motion.Timeline

```purescript
type Timeline =
  { fps         :: FrameRate
  , totalFrames :: Frames
  , layers      :: Array TimelineLayer
  , looping     :: LoopMode
  }

type TimelineLayer =
  { layerId     :: LayerId
  , startFrame  :: Frames
  , endFrame    :: Frames
  , inPoint     :: Frames
  , outPoint    :: Frames
  , timeRemap   :: Maybe (Array Keyframe)
  }
```

### Frame Rate Presets

```purescript
fps24  :: FrameRate  -- Film
fps25  :: FrameRate  -- PAL
fps30  :: FrameRate  -- NTSC
fps48  :: FrameRate  -- HFR
fps60  :: FrameRate  -- Games/UI
fps120 :: FrameRate  -- High refresh
customFps :: Number -> FrameRate
```

### Timeline Operations

```purescript
globalToLocal :: Frames -> TimelineLayer -> Frames
localToGlobal :: Frames -> TimelineLayer -> Frames
layerTimeAtFrame :: Frames -> TimelineLayer -> Frames
frameAtLayerTime :: Frames -> TimelineLayer -> Frames

-- Playback modes
clampFrame    :: Frames -> Timeline -> Frames
wrapFrame     :: Frames -> Timeline -> Frames
pingPongFrame :: Frames -> Timeline -> Frames

-- Full frame evaluation
evaluateFrame :: Frames -> Timeline -> FrameState
```

### Temporal.Timeline (Recursive Composition)

```purescript
data Timeline a
  = Single (Animation a)
  | Sequence (Array (Timeline a))
  | Parallel (Array (Timeline a))
  | Stagger Delay (Array (Timeline a))
  | Absolute (Array { offset :: Duration, animation :: Animation a })
```

---

## Keyframe System

### Motion.Keyframe

```purescript
type Keyframe =
  { keyframeId    :: KeyframeId
  , position      :: Frames
  , value         :: KeyframeValue
  , interpolation :: InterpolationType
  , tangentIn     :: Maybe Tangent
  , tangentOut    :: Maybe Tangent
  }

data KeyframeValue
  = NumberValue Number
  | Vec2Value { x :: Number, y :: Number }
  | Vec3Value { x :: Number, y :: Number, z :: Number }
  | ColorValue RGB
  | AngleValue Degrees
  | PercentValue Percent

data InterpolationType
  = Linear
  | Bezier
  | Hold
  | Auto
```

### Tangent Handles

```purescript
type Tangent =
  { x :: Number  -- Time influence
  , y :: Number  -- Value influence
  }
```

---

## Easing System

### 30+ Easing Presets

```purescript
-- Basic
ease, easeIn, easeOut, easeInOut :: Easing

-- Sine
easeInSine, easeOutSine, easeInOutSine :: Easing

-- Quadratic
easeInQuad, easeOutQuad, easeInOutQuad :: Easing

-- Cubic
easeInCubic, easeOutCubic, easeInOutCubic :: Easing

-- Quartic
easeInQuart, easeOutQuart, easeInOutQuart :: Easing

-- Quintic
easeInQuint, easeOutQuint, easeInOutQuint :: Easing

-- Exponential
easeInExpo, easeOutExpo, easeInOutExpo :: Easing

-- Circular
easeInCirc, easeOutCirc, easeInOutCirc :: Easing

-- Back (overshoot)
easeInBack, easeOutBack, easeInOutBack :: Easing

-- Elastic
easeInElastic, easeOutElastic, easeInOutElastic :: Easing

-- Bounce
easeInBounce, easeOutBounce, easeInOutBounce :: Easing
```

### Cubic Bezier

```purescript
type CubicBezier =
  { x1 :: Number  -- 0-1
  , y1 :: Number  -- Can exceed 0-1 for overshoot
  , x2 :: Number  -- 0-1
  , y2 :: Number  -- Can exceed 0-1 for overshoot
  }

-- CSS-style definition
cubicBezier :: Number -> Number -> Number -> Number -> Easing
```

### Spring Physics

```purescript
type SpringConfig =
  { mass      :: Mass       -- kg
  , stiffness :: Stiffness  -- N/m
  , damping   :: Damping    -- Ns/m
  , velocity  :: Velocity   -- m/s initial
  }

criticalDamping :: Mass -> Stiffness -> Damping
criticalDamping m k = 2.0 * sqrt (m * k)
```

---

## Mask System

### Motion.Mask

```purescript
type LayerMask =
  { maskRef    :: MaskRef
  , path       :: Path
  , mode       :: MaskMode
  , opacity    :: MaskOpacity      -- 0-100%
  , feather    :: { x :: Pixels, y :: Pixels }  -- Separate X/Y!
  , expansion  :: Pixels
  , inverted   :: Boolean
  , rotoBezier :: Boolean
  , locked     :: Boolean
  }

data MaskMode
  = MMNone
  | MMAdd
  | MMSubtract
  | MMIntersect
  | MMDifference
  | MMLighten
  | MMDarken

type MaskGroup = Array LayerMask  -- Compositing order
```

### Geometry.Mask

```purescript
data MaskSource
  = ShapeSource Shape
  | LinearGradientSource LinearGradient
  | RadialGradientSource RadialGradient
  | ImageSource ImageRef
  | SolidSource RGB

data MaskMode
  = AlphaMode
  | LuminanceMode
  | InverseLuminanceMode

data MaskComposite
  = MultiplyMasks
  | IntersectMasks
  | SubtractMasks
  | AddMasks
```

### Geometry.ClipPath

```purescript
data ClipPath
  = ClipNone
  | ClipPath Path
  | ClipCircle { cx :: Percent, cy :: Percent, r :: Percent }
  | ClipEllipse { cx :: Percent, cy :: Percent, rx :: Percent, ry :: Percent }
  | ClipPolygon (Array Point)
  | ClipInset { top :: Pixels, right :: Pixels, bottom :: Pixels, left :: Pixels }

-- Presets
clipCircleCenter :: ClipPath
clipOval :: ClipPath
clipTriangle :: ClipPath
clipHexagon :: ClipPath
clipStar5 :: ClipPath
```

---

## Effects System

### Effect Categories (12)

```purescript
data EffectCategory
  = ECBlurSharpen
  | ECColorCorrection
  | ECDistort
  | ECGenerate
  | ECKeying
  | ECMatte
  | ECNoiseGrain
  | ECPerspective
  | ECStylize
  | ECTime
  | ECTransition
  | ECUtility
```

### Effect Parameter Types

```purescript
data EffectParameterType
  = EPTNumber
  | EPTColor
  | EPTPoint
  | EPTPoint3D
  | EPTAngle
  | EPTCheckbox
  | EPTDropdown
  | EPTLayer
  | EPTString
  | EPTCurve
  | EPTData
```

### Blur Effects

```purescript
data BlurDimension
  = BlurHorizontal
  | BlurVertical
  | BlurBoth

data RadialBlurType
  = RadialSpin
  | RadialZoom

data AntialiasingQuality
  = AALow
  | AAMedium
  | AAHigh
```

### Distortion Effects

```purescript
data WarpStyle
  = WarpArc
  | WarpArch
  | WarpBulge
  | WarpShellLower
  | WarpShellUpper
  | WarpFlag
  | WarpWave
  | WarpFish
  | WarpRise
  | WarpFisheye
  | WarpInflate
  | WarpSqueeze
  | WarpTwist
  | WarpSpherize
  | WarpDisplace

data DisplacementChannel
  = DisplaceRed
  | DisplaceGreen
  | DisplaceBlue
  | DisplaceAlpha
  | DisplaceLuminance

data EdgeBehavior
  = EdgeWrap
  | EdgeClamp
  | EdgeMirror
```

### Glow Effects

```purescript
data GlowCompositeMode
  = GlowAdd
  | GlowScreen
  | GlowSoftLight

data FalloffMode
  = FalloffLinear
  | FalloffExponential
  | FalloffGaussian

data BloomBlendMode
  = BloomAdditive
  | BloomScreen
  | BloomSoftLight
```

### Stylize Effects

```purescript
data HalftoneColorMode
  = HalftoneMono
  | HalftoneCMYK
  | HalftoneRGB

data DitherMethod
  = DitherOrdered
  | DitherFloydSteinberg
  | DitherAtkinson
  | DitherBayer

data PixelSortDirection
  = SortHorizontal
  | SortVertical
  | SortDiagonal
```

---

## Trigger System

### Gestural.Trigger

```purescript
data TriggerCondition
  = HoverFor Duration
  | HoverWhile
  | ClickCount Int
  | KeyPattern (Array KeyCode)
  | GesturePattern GestureSequence
  | ProximityEnter Distance
  | ProximityExit Distance
  | HoldFor Duration
  | ScrollTo Progress
  | IdleFor Duration
  | VisitCount Int
  | TimeWindow { start :: Time, end :: Time }
  | CustomCondition String

data TriggerEffect
  = Reveal
  | Hide
  | Morph
  | Animate
  | Navigate
  | PlaySound
  | TriggerHaptic
  | ShowToast
  | Confetti
  | Unlock
  | Achievement
  | CustomEffect String

data TriggerTarget
  = TargetSelf
  | TargetElement ElementId
  | TargetGroup GroupId
  | TargetGlobal

type TriggerTiming =
  { delay    :: Duration
  , duration :: Duration
  , cooldown :: Duration
  , repeat   :: Maybe Int
  }

type TriggerDef =
  { condition :: TriggerCondition
  , effect    :: TriggerEffect
  , target    :: TriggerTarget
  , timing    :: TriggerTiming
  }
```

### Easter Egg Presets

```purescript
konamiCode :: SequenceTrigger
konamiCode = keySequence
  [ KeyUp, KeyUp, KeyDown, KeyDown
  , KeyLeft, KeyRight, KeyLeft, KeyRight
  , KeyB, KeyA
  ]

secretSequence :: Array KeyCode -> TriggerEffect -> TriggerDef
secretTaps :: Int -> Duration -> TriggerEffect -> TriggerDef
cornerGesture :: Corner -> TriggerEffect -> TriggerDef
```

---

## Z-Index / Elevation System

### Elevation.ZIndex

```purescript
data ZIndex
  = ZIndexAuto
  | ZIndexValue Int  -- Bounded

-- Smart constructors
z :: Int -> ZIndex
auto :: ZIndex
negative :: Int -> ZIndex

-- Operations
above :: ZIndex -> ZIndex
below :: ZIndex -> ZIndex
increment :: ZIndex -> ZIndex
decrement :: ZIndex -> ZIndex
```

### Elevation.Depth

```purescript
type ParallaxLayer =
  { content :: Element
  , depth   :: Depth      -- 0 = foreground, 1 = background
  , scale   :: Number     -- Movement multiplier
  }

type DepthStack =
  { layers  :: Array DepthLayer
  , spacing :: Pixels
  }

type FloatingUI =
  { content  :: Element
  , elevation :: SemanticElevation
  , backdrop :: Maybe Backdrop
  }

type Backdrop =
  { blur    :: BlurRadius
  , opacity :: Opacity
  , color   :: Maybe RGB
  }
```

### Semantic Elevation

```purescript
data SemanticElevation
  = Flat        -- 0dp
  | Raised      -- 2dp
  | Floating    -- 8dp
  | Modal       -- 24dp
  | Toast       -- 6dp
  | Dropdown    -- 8dp
  | Drawer      -- 16dp
  | Dialog      -- 24dp
```

---

## Shadow System

### Elevation.Shadow

```purescript
type BoxShadow =
  { offsetX :: Pixels
  , offsetY :: Pixels
  , blur    :: Pixels
  , spread  :: Pixels
  , color   :: RGBA
  , inset   :: Boolean
  }

type DropShadow =
  { offsetX :: Pixels
  , offsetY :: Pixels
  , blur    :: Pixels
  , color   :: RGBA
  }

type LayeredShadow = Array BoxShadow  -- Multiple shadows compose

type TextShadow =
  { offsetX :: Pixels
  , offsetY :: Pixels
  , blur    :: Pixels
  , color   :: RGBA
  }
```

---

## Surface / Material System

### Surface.Fill

```purescript
data Fill
  = FillNone
  | FillSolid RGB
  | FillGradient Gradient
  | FillPattern Pattern
  | FillNoise FBM

type Pattern =
  { source     :: ImageRef
  , repeatMode :: PatternRepeat
  , width      :: Pixels
  , height     :: Pixels
  }

data PatternRepeat
  = RepeatBoth
  | RepeatX
  | RepeatY
  | NoRepeat
```

### Procedural Noise

```purescript
type FBM =
  { noiseType   :: NoiseType
  , octaves     :: NoiseOctaves      -- 1-8
  , persistence :: NoisePersistence  -- 0-1
  , lacunarity  :: NoiseLacunarity   -- 1-4
  , frequency   :: NoiseFrequency
  , amplitude   :: NoiseAmplitude
  , seed        :: NoiseSeed
  }

data NoiseType
  = PerlinNoise
  | SimplexNoise
  | WorleyNoise
  | ValueNoise
```

### Filter Chain

```purescript
type FilterChain = Array Filter

data Filter
  = FilterBrightness Number      -- -100 to 100
  | FilterContrast Number        -- -100 to 100
  | FilterExposure Number        -- -5 to 5
  | FilterFade Number            -- 0 to 100
  | FilterGrain Number           -- 0 to 100
  | FilterGrayscale Number       -- 0 to 100
  | FilterHighlights Number      -- -100 to 100
  | FilterHueRotate Degrees      -- 0 to 360
  | FilterInvert Number          -- 0 to 100
  | FilterSaturation Number      -- -100 to 100
  | FilterSepia Number           -- 0 to 100
  | FilterShadows Number         -- -100 to 100
  | FilterSharpen Number         -- 0 to 100
  | FilterTemperature Number     -- -100 to 100
  | FilterTint Number            -- -100 to 100
  | FilterVignette Number        -- 0 to 100
```

### Glass Effects

```purescript
type GlassEffect =
  { blur      :: BlurRadius
  , opacity   :: Opacity
  , saturation :: Number
  , tint      :: Maybe RGBA
  }

type Neumorphism =
  { lightShadow :: BoxShadow
  , darkShadow  :: BoxShadow
  , background  :: RGB
  }

type Frosted =
  { blur       :: BlurRadius
  , opacity    :: Opacity
  , noiseLevel :: Number
  }
```

---

## Identity System

### Attestation.UUID5

All compositing elements use **deterministic UUID5** identity:

```purescript
-- Namespaces for compositing elements
nsLayer       :: Namespace
nsComposition :: Namespace
nsEffect      :: Namespace
nsKeyframe    :: Namespace
nsMask        :: Namespace
nsProperty    :: Namespace

-- 3D elements
nsCamera   :: Namespace
nsLight    :: Namespace
nsMaterial :: Namespace
nsTexture  :: Namespace
nsShader   :: Namespace

-- Animation state
nsFrameState     :: Namespace
nsAnimationState :: Namespace
nsSpringState    :: Namespace

-- Compute
nsRenderEffect  :: Namespace
nsComputeKernel :: Namespace
```

### UUID5 Generation

```purescript
-- Same namespace + same name = same UUID (forever, everywhere)
uuid5 :: Namespace -> String -> UUID5

-- Examples
layerId = uuid5 nsLayer "main-background"
effectId = uuid5 nsEffect "blur-entrance"
keyframeId = uuid5 nsKeyframe "opacity-0-to-100"
```

### Identity.Temporal

```purescript
type Generation = Int  -- Monotonically increasing

type Identified a =
  { id         :: UUID5
  , generation :: Generation
  , value      :: a
  }

type CacheKey =
  { uuid       :: UUID5
  , generation :: Generation
  }

-- Cache validity
sameIdentity :: Identified a -> Identified a -> Boolean
isNewerThan :: Identified a -> Identified a -> Boolean
```

---

## CoEffect System

### Physics.Projective.Domain

CoEffects track what operations **NEED** (Orchard-style graded monads):

```purescript
data DomainCoEffect
  = CoEffectNone
  | CoEffectNeighborDomain    -- Needs data from adjacent domain
  | CoEffectGlobalState       -- Needs full system state
  | CoEffectConstraints       -- Needs constraint data
  | CoEffectMemory Int        -- Memory bound (bytes)
  | CoEffectCPUCores Int      -- CPU cores needed
  | CoEffectComposite (Array DomainCoEffect)

-- Semigroup: compose requirements
instance Semigroup DomainCoEffect where
  append CoEffectNone b = b
  append a CoEffectNone = a
  append (CoEffectMemory a) (CoEffectMemory b) = CoEffectMemory (a + b)
  append (CoEffectCPUCores a) (CoEffectCPUCores b) = CoEffectCPUCores (max a b)
  append a b = CoEffectComposite [a, b]

-- Monoid: identity is no requirements
instance Monoid DomainCoEffect where
  mempty = CoEffectNone
```

### Physics.Fluid.Core

```purescript
data FluidCoEffect
  = CoEffectNone
  | CoEffectNeighbors     -- Needs spatial neighbor lookup
  | CoEffectGrid          -- Needs Eulerian grid
  | CoEffectGPU           -- Benefits from GPU acceleration
  | CoEffectMemory Int    -- Memory bound (bytes)
  | CoEffectBandwidth Int -- Bandwidth bound (bytes/sec)
  | CoEffectComposite (Array FluidCoEffect)
```

### Numeric.Grade

```purescript
-- Error tracking grade
newtype Grade = Grade Number  -- Non-negative

instance Semigroup Grade where
  append (Grade a) (Grade b) = Grade (a + b)

instance Monoid Grade where
  mempty = Grade 0.0

-- Graded monad for forward error
newtype ForwardError (epsilon :: Grade) a = ForwardError a

-- Sensitivity tracking
newtype Sensitive (k :: Number) a = Sensitive a
```

---

## Color System

### Color Spaces

```purescript
-- Standard
RGB, SRGB, LinearRGB :: Type
HSL, HSLA, HSV, HWB :: Type
CMYK :: Type

-- Perceptual
LAB, LCH, LCHA :: Type
OKLAB, OKLCH :: Type

-- Wide Gamut
P3A, WideGamut :: Type

-- Video
XYZ, YUV :: Type
```

### Color Atoms

```purescript
newtype Channel = Channel Int      -- 0-255, clamps
newtype Channel16 = Channel16 Int  -- 0-65535, clamps
newtype Alpha = Alpha Number       -- 0-1, clamps
newtype Hue = Hue Number           -- 0-359, wraps
newtype Saturation = Saturation Number  -- 0-100, clamps
newtype Lightness = Lightness Number    -- 0-100, clamps
newtype Kelvin = Kelvin Number     -- 1000-40000, clamps
```

### Professional Color Grading

```purescript
-- ASC Color Decision List
type CDL =
  { slope  :: { r :: Number, g :: Number, b :: Number }
  , offset :: { r :: Number, g :: Number, b :: Number }
  , power  :: { r :: Number, g :: Number, b :: Number }
  , saturation :: Number
  }

-- Lift/Gamma/Gain (Color Wheels)
type LiftGammaGain =
  { lift  :: RGB  -- Shadows
  , gamma :: RGB  -- Midtones
  , gain  :: RGB  -- Highlights
  }

-- Tonal Curves
type Curves =
  { master :: Array Point  -- Luminance curve
  , red    :: Array Point  -- Red channel
  , green  :: Array Point  -- Green channel
  , blue   :: Array Point  -- Blue channel
  }
```

### Color.Glow

```purescript
type Glow =
  { color     :: RGB
  , intensity :: Number     -- 0-10
  , radius    :: Pixels     -- Blur radius
  , composite :: GlowCompositeMode
  }
```

---

## Composition Example

A **Button** is just a Composition with stacked layers:

```purescript
type Button =
  { geometry   :: ButtonGeometry    -- WHERE (size, padding, shape)
  , appearance :: ButtonAppearance  -- HOW IT LOOKS (fill, shadow)
  , behavior   :: ButtonBehavior    -- HOW IT RESPONDS (haptic, audio)
  , semantics  :: ButtonSemantics   -- WHAT IT MEANS (purpose, a11y)
  }

-- Each layer composes atoms from Schema pillars:

ButtonGeometry =
  { width, height     -- Dimension
  , padding           -- Geometry.Spacing
  , cornerRadii       -- Geometry.CornerRadii
  }

ButtonAppearance =
  { fill              -- Surface.Fill
  , shadow            -- Elevation.LayeredShadow
  , borderWidth       -- Dimension
  , borderColor       -- Color.RGB
  , opacity           -- Color.Opacity
  }

ButtonBehavior =
  { hapticOnPress     -- Haptic.ImpactFeedback
  , hapticOnRelease   -- Haptic.ImpactFeedback
  , audioOnClick      -- Audio.AudioCue
  , longPressMs       -- Temporal.Duration
  }

ButtonSemantics =
  { purpose           -- Reactive.ButtonPurpose
  , label             -- String
  , toggleState       -- Reactive.ToggleState
  , disabled          -- Boolean
  }
```

---

## Pillar Reference

### File Counts by Pillar

| # | Pillar | Files | Primary Focus |
|---|--------|-------|---------------|
| 1 | Motion | 46 | Layers, compositions, timelines, keyframes, effects |
| 2 | Temporal | 39 | Animation, springs, duration, progress, easing |
| 3 | Surface | 45 | Fills, patterns, filters, procedural textures |
| 4 | Elevation | 10 | Z-index, shadows, depth, perspective |
| 5 | Geometry | 49 | Shapes, masks, paths, transforms, curves |
| 6 | Reactive | 23 | State flags, data state, presence, media state |
| 7 | Gestural | 21 | Triggers, gestures, pointer, touch, keyboard |
| 8 | Physics | 8 | CoEffects, fluid simulation, forces |
| 9 | Spatial | 43 | Camera, lights, PBR materials, scene graph |
| 10 | Color | 55 | Color spaces, gradients, blending, grading |
| 11 | Haptic | 4 | Vibration, feedback, patterns |
| 12 | Audio | 31 | Triggers, automation, effects, MIDI |
| 13 | Media | 6 | Video state, playback, buffering |
| 14 | Brand | 18 | Brand identity, palettes, provenance |
| 15 | Element | 3+ | UI compounds (Button, Playhead) |
| 16 | Brush | 36 | Dry/wet mediums, digital tools, presets |
| 17 | Graph | 7 | Node graphs, connections, viewports |
| 18 | Tensor | 5 | Shapes, dtypes, broadcasting |
| 19 | GPU | 3 | Storable, Landauer entropy |
| 20 | Compute | 4 | Compute graphs, operations, dispatch |
| 21 | Numeric | 4 | Graded monads, error tracking |
| 22 | Storage | 4 | Clipboard, IndexedDB, local/session |
| 23 | Identity | 2 | UUID5, generations, cache keys |
| 24 | Network | 6 | HTTP, WebSocket, SSE |
| 25 | Accessibility | 7 | WAI-ARIA 1.2, roles, states |
| 26 | Text | 6 | Rich text, code, selection |
| 27 | Weather | 7 | Precipitation, wind, atmosphere |
| 28 | Game | 18 | Entities, timers, temporal integrity |
| 29 | Phone | 10 | Phone number handling |
| 30 | Scheduling | 8 | Calendar events, recurrence |
| 31 | Engineering | 6 | CAD primitives, section views |
| 32 | Physical | 6 | Periodic elements, materials |
| 33 | Epistemic | 6 | Confidence, uncertainty, coherence |
| 34 | Attestation | 12 | UUID5, provenance, cryptography |
| 35 | Sensation | 9 | Proprioceptive, contact, environment |
| 36 | Navigation | 3 | History, pagination |
| 37 | Dimension | 36 | Points, sizes, transforms, temporal |
| 38 | Bounded | 1 | Foundation: bounds, clamp, wrap |

**Total: 1,114+ files across 38 pillars**

---

## Key Source Files

### Motion Pillar (Compositing Core)

```
hydrogen/src/Hydrogen/Schema/Motion/
├── Composition.purs      -- 474 lines - CompositionSettings, BlendMode
├── Layer.purs            -- 233 lines - LayerType, LayerBase
├── LayerContent.purs     -- 848 lines - 56 content types
├── Timeline.purs         -- 663 lines - Timeline, FrameRate
├── Keyframe.purs         -- Keyframe, InterpolationType
├── Easing.purs           -- 30+ easing presets
├── Effects.purs          -- 241 lines - Effect system
├── Mask.purs             -- LayerMask, MaskMode
├── Path.purs             -- MotionPath
└── Effects/
    ├── Blur.purs
    ├── Distort.purs
    ├── Glow.purs
    ├── Stylize.purs
    └── Time.purs
```

### Temporal Pillar (Animation)

```
hydrogen/src/Hydrogen/Schema/Temporal/
├── Timeline.purs         -- Recursive Timeline composition
├── Animation.purs        -- Transition, Keyframe, Spring, Physics
├── Duration.purs         -- Duration, Delay, Frames
├── Progress.purs         -- Progress (0-1)
├── Easing.purs           -- Easing curves
├── Spring.purs           -- Spring physics
└── PlayState.purs        -- Running, Paused, Finished
```

### Gestural Pillar (Triggers)

```
hydrogen/src/Hydrogen/Schema/Gestural/
├── Trigger.purs          -- 619 lines - Complete trigger system
├── Gesture.purs          -- Tap, swipe, pan, pinch
├── Pointer.purs          -- Mouse, touch, pen
├── Keyboard.purs         -- Key codes, shortcuts
└── Easter.purs           -- Konami code, secret sequences
```

### Attestation Pillar (Identity)

```
hydrogen/src/Hydrogen/Schema/Attestation/
├── UUID5.purs            -- Deterministic UUID generation
├── Namespace.purs        -- nsLayer, nsComposition, nsEffect, ...
├── Provenance.purs       -- Source, timestamp, hash
└── Signature.purs        -- Cryptographic signatures
```

---

## Guarantees

1. **Deterministic** — Same composition data = same rendered output
2. **Bounded** — All values have explicit bounds, NaN/Infinity-safe
3. **Typed** — 56 layer types, 28 blend modes, 12 effect categories
4. **Traceable** — UUID5 identity for every element
5. **Composable** — Graded monoids track requirements
6. **Complete** — No stubs, no TODOs, no placeholders

---

*// hydrogen // schema // pillar // architecture*
*// straylight/2026*
