# Brand Schema

The canonical structure for brand exports from COMPASS.

Based on professional brand guide methodology refined over 25 years of strategic
brand consulting for enterprise clients.

## Overview

A brand is not a logo. A brand is a *system* — a coherent set of decisions that
express a singular identity across every touchpoint. This schema captures that
system in a machine-readable, type-safe format.

## Structure

```
Brand
├── 1. FOUNDATION (Strategic Core)
│   ├── Mission      — Why we exist
│   ├── Vision       — Where we're going
│   ├── Values []    — What we believe
│   ├── Taglines     — How we summarize ourselves
│   └── Audience     — Who we serve (psychographics)
│
├── 2. NARRATIVE (Symbol & Story)
│   ├── BrandStory       — Origin and purpose narrative
│   ├── SymbolMeaning    — Why this mark = this message
│   └── VisualMetaphors  — Recurring visual themes
│
├── 3. VOICE (Personality & Tone)
│   ├── PersonalityTraits []   — "Friendly. Intelligent. Helpful."
│   ├── VoiceAttributes []     — IS / IS NOT pairs
│   └── StyleGuide
│       ├── Headlines      — Case, punctuation, font rules
│       ├── Grammar        — Oxford comma, exclamation rules
│       ├── Formatting     — Alignment defaults
│       └── Conventions    — Dates, times, contact formats
│
├── 4. LOGO (Mark System)
│   ├── Components    — Icon, wordmark, tagline
│   ├── Lockups []    — Horizontal, vertical, stacked
│   ├── Variants []   — Color, grayscale, knockout
│   ├── ClearSpace    — Self-referential ratio (e.g., "2× the N")
│   ├── MinimumSizes  — Digital (px) and print (inches)
│   └── Constraints   — DO / DON'T rules as types
│
├── 5. COLOR (Palette System)
│   ├── PrimaryColors []      — Full specs (hex, rgb, pantone, cmyk)
│   ├── TintProgression       — Ratio-based tint scale
│   ├── Neutrals              — Brand black, brand white (never true #000)
│   ├── Gradients []          — Approved gradient combinations
│   ├── BackgroundAdaptation  — Luminance → logo treatment mapping
│   └── ContrastRules         — Minimum contrast ratios
│
├── 6. TYPOGRAPHY (Type System)
│   ├── FontSources
│   │   ├── SystemFonts []    — Enumerable (Arial, Georgia, etc.)
│   │   └── CustomFonts []    — With import config (Google, Adobe, self-hosted)
│   ├── TypeScale             — Base size + ratio (e.g., 23.04px, Major Third)
│   ├── Hierarchy []          — Level → TypeStyle mapping
│   └── TypeStyle
│       ├── FontFamily
│       ├── FontWeight
│       ├── TextTransform
│       ├── LetterSpacing
│       └── LineHeight
│
├── 7. LAYOUT (Spatial System)
│   ├── GridSystem        — Portrait (8 col) / Landscape (16 col)
│   ├── ContentZones []   — Named regions with purposes
│   ├── SpacingScale      — Ratio-based spacing
│   └── Breakpoints []    — Responsive thresholds
│
├── 8. MATERIAL (Surface & Depth)
│   ├── LightSource       — Direction (always from above for consistency)
│   ├── ElevationScale    — Depth levels with shadow specs
│   ├── GlowTreatment     — Intensity, color, usage rules
│   ├── NeumorphicRules   — Gradient direction, stroke requirements
│   └── ShadowSystem      — Soft, hard, colored variants
│
├── 9. IMAGERY (Visual Content)
│   ├── ContentThemes []      — Brand-specific visual motifs
│   ├── PhotographyGuidelines — Sharpness, faces, text overlay rules
│   ├── ColorGrading          — 3-point grading to match palette
│   └── Illustrations         — Style, stroke, fill rules
│
└── 10. THEMES (Mode Variants)
    ├── LightMode         — Default / corporate / professional
    ├── DarkMode          — Modern / alternative (only after brand established)
    └── ContextRules      — When to use which mode
```

## Voice Attributes Pattern

The IS / IS NOT pattern constrains content at the type level:

```purescript
type VoiceAttribute =
  { name :: String
  , is :: Array String        -- "knowledgeable, trusted, confident"
  , isNot :: Array String     -- "overbearing, pompous, condescending"
  }

-- Example
authoritative :: VoiceAttribute
authoritative =
  { name: "Authoritative"
  , is: [ "knowledgeable", "trusted", "confident", "expert" ]
  , isNot: [ "overbearing", "pompous", "condescending", "preachy" ]
  }
```

## Color Specification

Colors are multi-format molecules — the same color expressed for different media:

```purescript
type BrandColor =
  { name :: String           -- "Sentience_P1"
  , hex :: HexCode           -- #ffe3ef
  , rgb :: RGB               -- RGB 255 237 239
  , pantone :: Maybe String  -- "Pantone 7436 C"
  , cmyk :: Maybe CMYK       -- CMYK 0 13 0 0
  , role :: ColorRole        -- Primary | Tint | Neutral | Accent
  }
```

## Logo Constraints as Types

Invalid logo usage should be *unrepresentable*:

```purescript
-- These combinations are type errors, not runtime errors:
data LogoVariant = FullColor | Grayscale | Knockout
data BackgroundLuminance = Light | Medium | Dark

-- Valid combinations only
logoForBackground :: BackgroundLuminance -> LogoVariant
logoForBackground Light  = FullColor
logoForBackground Medium = FullColor  -- or Knockout depending on exact value
logoForBackground Dark   = Knockout

-- Constraints encoded:
-- ❌ DarkLogo on DarkBackground — impossible by construction
-- ❌ True black (#000000) anywhere — BrandBlack newtype prevents it
-- ❌ Distorted proportions — Logo is opaque, not composable from parts
```

## Self-Referential Measurements

Proportions derived from the mark itself scale correctly at any size:

```purescript
-- Clear space = 2× the height of the "N" in the wordmark
clearSpace :: LogoHeight -> Spacing
clearSpace height = height * clearSpaceRatio
  where clearSpaceRatio = 0.4  -- derived from mark geometry

-- This scales correctly whether the logo is 50px or 500px
```

## Typography Hierarchy

Type hierarchy maps semantic levels to compound TypeStyles:

```purescript
type TypeHierarchy =
  { hl :: TypeStyle    -- Hero/display
  , h1 :: TypeStyle
  , h2 :: TypeStyle
  , h3 :: TypeStyle
  , h4 :: TypeStyle
  , h5 :: TypeStyle
  , h6 :: TypeStyle
  , body :: TypeStyle
  , small :: TypeStyle
  , footnote :: TypeStyle
  }

-- Example from Sentience brand:
-- HL-H3: Archivo, ExtraBold, UPPERCASE, tracking 25, line-height 1.3
-- H4-H6: Poppins, Bold, Normal, tracking 40, line-height 1.3
-- Body:  Poppins, Regular, Normal, tracking 40, line-height 1.6
```

## Gradient Rules

Gradients have direction and approved color stop combinations:

```purescript
type BrandGradient =
  { name :: String
  , angle :: Degrees        -- -90° = dark to light (top to bottom)
  , stops :: Array ColorStop
  , usage :: GradientUsage  -- Background | Overlay | Text
  }

-- Rule: High resolution to avoid banding
-- Rule: No noise/grain to hide banding — use proper resolution
```

## Theme Context

Themes are not just color swaps — they carry semantic meaning:

```purescript
data ThemeContext
  = CorporateProfessional  -- Light mode, default
  | ModernAlternative      -- Dark mode, requires brand establishment first

themeUsageRule :: ThemeContext -> String
themeUsageRule CorporateProfessional = "Default for all initial touchpoints"
themeUsageRule ModernAlternative = "Only after primary brand is established"
```

## Reference Implementation

See `brand/Sentience/brand44/` for annotated screenshots of a complete brand guide
following this structure. Files are named by section:

```
01_cover_welcome.png
02_foundation_intent.png
03_foundation_brand_tagline.png
...
30a_typography_scale_hierarchy.png
30b_typography_scale_values.png
...
44_back_cover.png
```

---

This schema becomes the export format for COMPASS brand configuration. When an
agent or human builds a brand, the output is a complete, type-safe instantiation
of this structure — compilable PureScript that encodes every brand decision.
