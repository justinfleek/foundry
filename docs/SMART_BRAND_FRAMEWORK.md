# SMART Brand Ingestion Framework

> **S**tory-driven, **M**emorable, **A**gile, **R**esponsive, **T**argeted
> A universal framework for parsing and encoding brand style guides into machine-readable specifications.
> Developed by Justin / Weyl.ai — 25 years of strategic brand consulting & motion graphics production.

---

## How to Use This Framework

This document defines the structure, categories, and fields required to fully ingest any brand's style guide into a format that AI systems can interpret, enforce, and generate from. Each section represents a core pillar of brand identity. When ingesting a new brand, populate each section with the brand's specific values.

The framework is organized into two tiers:

1. **Strategic Layer** — The story, personality, voice, and values that drive all creative decisions.
2. **Execution Layer** — The concrete specs (colors, type, logo rules, sizing) that enforce the strategy visually.

---

# STRATEGIC LAYER

---

## 1. Brand Overview

The foundational narrative. Every brand has an origin story, a reason for existing, and a way it wants to be perceived. This section captures the high-level identity.

### Fields to Capture:

- **Brand Name**
- **Parent Organization / Ecosystem** (if applicable)
- **Industry / Category**
- **One-Line Description** — What the brand does in a single sentence.
- **Brand Promise** — The core commitment to the user/customer.
- **Founding Context** — Why this brand was created and what problem it solves.

---

## 2. Mission Statement

A concise declaration of the brand's purpose and intended impact.

### Fields to Capture:

- **Mission Statement** — The full, canonical mission text. This should be treated as locked copy; do not paraphrase or reword.

---

## 3. Taglines

Taglines distill the Brand Promise, Mission, and Values into a compact, repeatable message. They function as the verbal signature of the brand.

### Fields to Capture:

- **Primary Tagline** — The single most important tagline. Locked copy.
- **Secondary Tagline(s)** — Alternative taglines for different contexts. Locked copy.

### Tagline Usage Rules:

- Taglines may be used alongside any approved logo iteration or brand image as standalone marketing.
- Taglines should NOT be combined with campaign-specific taglines or phrases.
- Taglines must never be rewritten, reworded, or edited in any way.

---

## 4. Brand Values

The core principles that inform every decision, design, and communication.

### Fields to Capture:

- **Values List** — An ordered list of the brand's stated values (e.g., Innovation, Security, Accessibility, etc.)

---

## 5. Brand Personality

How the brand would behave if it were a person. This drives tone, visual style, and interaction design.

### Fields to Capture:

- **Core Personality Traits** — Typically 3–5 adjectives (e.g., "Friendly. Intelligent. Helpful.")
- **Personality Description** — A narrative explanation of how these traits manifest across touchpoints.
- **Positioning Statement** — How the brand positions itself relative to users (e.g., ally, guide, facilitator, authority).

---

## 6. Voice & Tone

The way a brand looks is only part of the equation. How it sounds is equally important. This section defines the verbal identity.

### Fields to Capture:

- **Voice Summary** — The overarching principle (e.g., "cohesive, consistent, relevant across all touchpoints").

### Tone of Voice Definitions

For each tone attribute, capture BOTH what it IS and what it is NOT. This dual-constraint format is essential for AI systems — the "NOT" definitions create guardrails that prevent drift.

#### Template per Tone Attribute:

| Attribute | IS | NOT |
|-----------|----|----|
| [e.g., Authoritative] | [e.g., knowledgeable, trusted, confident, credible] | [e.g., overbearing, pompous, condescending] |
| [e.g., Approachable] | [e.g., friendly, engaging, warm, conversational] | [e.g., overly casual, unprofessional, patronizing] |
| [e.g., Innovative] | [e.g., creative, visionary, cutting edge, progressive] | [e.g., impractical, unrealistic, full of hype words] |
| [e.g., Forward-Thinking] | [e.g., anticipatory, proactive, actively shaping the curve] | [e.g., speculative, baseless, overly futuristic] |

> **Note for AI ingestion:** The IS/NOT pattern is the most valuable part of any brand voice specification. It converts subjective tone guidance into enforceable constraints. Always prioritize capturing this data.

---

## 7. Master Style List

Editorial and copy rules that apply across all written content.

### Headlines
- Conciseness and clarity requirements
- Punctuation preferences (e.g., "&" vs "and")
- Case style (e.g., Title Case vs sentence case)
- Font/weight specification for headlines
- Kerning specification

### Punctuation
- Consistent punctuation rules
- List punctuation rules (periods at end of bullet items — yes/no)
- Hyphenation policy
- Exclamation point limits
- Oxford Comma usage (yes/no)

### Contact Information & Times
- Phone number format (e.g., hyphens, no parentheses)
- Time format (e.g., colon-separated, AM/PM with space)
- Time range notation (e.g., en-dash)
- Midnight/noon conventions
- Hour format preference (e.g., 24-hour)
- Day abbreviation policy (e.g., never abbreviate)

### Spelling Conventions
- Regional spelling preferences (e.g., gray vs grey)
- Commonly confused words to watch for

### Formatting
- Default text alignment
- Capitalization rules

---

## 8. Target Customers

Psychographic profiles of the brand's intended audience. These inform tone calibration and content strategy.

### Fields to Capture:

For each customer segment, define:

- **Segment Name** — A descriptive label (e.g., "Early Adopters & Innovators")
- **Description** — Who they are and what drives them.
- **Key Motivations** — What attracts them to brands in this category.

> **Note for AI ingestion:** Target customer profiles help calibrate language complexity, assumed knowledge, and emotional framing. An AI generating content for "privacy-conscious users" will write differently than for "gamers seeking immersive experiences."

---

# EXECUTION LAYER

---

## 9. Logo

The logo is the primary visual identifier of the brand. This section captures its components, lockups, sizing constraints, and usage rules.

### Logo Components

- **Icon** — Description of the icon/symbol element and its meaning.
- **Wordmark** — The typographic treatment of the brand name.
- **Symbolism** — The narrative behind the icon choice (if documented). This often connects back to brand values and mission.

### Logo Integrity

- The logo is a locked piece of artwork and should not be altered in any way.
- Additional treatments must be approved by the brand's media/design team.

---

## 10. Logo Lockups

Lockups define the approved arrangements of logo components.

### For Each Lockup, Capture:

- **Lockup Name** (e.g., Primary, Horizontal, Vertical)
- **Components** (e.g., Wordmark + Icon)
- **Orientation** (Horizontal / Vertical / Square)
- **Primary Use Cases** (e.g., letterheads, email signatures, social profiles)
- **Mandatory Usage Rules** (e.g., "MUST be used for first introduction of brand on all business collateral")
- **Available Color Variants** (e.g., full color, black & white, reversed)
- **Approved Background Colors** — List of specific backgrounds each variant can be placed on.

### Alternate Lockups

- **Wordmark Solo** — When and where the wordmark can be used alone, minimum sizing.
- **Icon Solo** — When and where the icon can be used alone, plus any conditions (e.g., "brand name must be visible nearby," "full lockup must appear at least once in the same content").

---

## 11. Logo Clear Space

- **Clear Space Rule** — The minimum clear space defined relative to a logo element (e.g., "twice the height of the letter N on all sides").
- **Principle** — More clear space is always better; the rule defines the minimum.

---

## 12. Logo Minimum Sizing

### For Each Lockup Format:

| Format | Print Minimum | Digital Minimum (px) |
|--------|---------------|----------------------|
| Vertical Lockup | [e.g., .75" height] | [e.g., 60×76px] |
| Horizontal Lockup | [e.g., .75" height] | [e.g., 120×38px] |
| Wordmark Solo | [e.g., .25" height] | [e.g., 96×12px] |
| Icon Solo | [e.g., .75" height] | [e.g., 33×50px] |
| Favicon | N/A | [e.g., 32×32px] |

---

## 13. Logo Usage Rules

### On the Page
- Default alignment (e.g., left aligned on primary gridline)
- First page vs subsequent page rules
- Stationery-specific layouts (reference to collateral section)

### Watermarks
- Opacity setting for watermark use (e.g., 20%)
- Which lockup to use for watermarks
- Fallback for limited space

### Social Media
- Platform-specific sizing awareness
- Approved avatar implementations (circular and square crops)
- Clear space considerations for platform cropping
- Locked avatar designs — do not alter

### App Icon
- OS-specific aspect ratio awareness
- Reference artwork for clear space and placement

---

## 14. Logo Common Errors

A comprehensive "Do Not" list. Critical for AI enforcement.

### Contrast Errors
- Do not combine dark logo with dark background
- Do not combine light logo with light background
- Do not use true black (if brand specifies a custom black)
- Maintain minimum contrast ratio (e.g., 4.5:1)
- Tool recommendation for checking contrast (e.g., contrast-ratio.com)

### Color Errors
- Do not use off-brand colors
- Do not change or adjust logo colors
- Do not use tints as primary colors (reserve for effects/secondary tones)

### Distortion Errors
- Do not squash, stretch, skew, distort, or crop the logo
- Do not add graphic elements (including drop shadows)
- Do not place on busy or distracting backgrounds

### Layout Errors
- Do not alter the layout or relationship between logo elements
- Do not reduce logo opacity (except for approved watermark use)
- Do not encroach on required clear space

> *Note: This is not a comprehensive list. These are the most common or egregious errors.*

---

## 15. Color Palette

Colors must be reproduced faithfully. Any color outside the approved palette is unauthorized.

### For Each Named Color, Capture:

| Field | Description |
|-------|-------------|
| Color Name | Internal reference name (e.g., "Brand_P1", "Brand_Gray") |
| Hex Code | Web hex value |
| Pantone | Pantone matching system code |
| RGB | Red, Green, Blue values |
| CMYK | Cyan, Magenta, Yellow, Key values |
| Role | Where this color sits in the hierarchy (primary, secondary, accent, neutral) |

### Color Hierarchy Notes
- Which colors are primary vs secondary vs accent vs neutral
- Black/White usage rules (e.g., for maximum contrast or printed materials only)
- Instructions for using brand black vs true black
- Rules about using palette colors for logos vs text vs backgrounds

### Color Usage Rules
- Brand should always be represented in approved colors only.
- No unauthorized colors or gradients.

---

## 16. Gradients

### Gradient Rules

- **Direction** — The approved angle and flow direction (e.g., -90°, lighter on top to darker on bottom).
- **Exceptions** — Any contexts where direction may differ (e.g., buttons, UI elements).
- **Resolution** — Use high enough resolution to avoid banding across mobile, print, and web.
- **Anti-Banding** — Do not use Noise/Grain to mask banding. Use higher resolution source files or regenerate in design software.

### Approved Gradient Combinations

For each approved gradient, capture:

| Gradient Name | Top Color (Light) | Bottom Color (Dark) |
|---------------|-------------------|---------------------|
| [Name/ID] | [Color Name + Hex] | [Color Name + Hex] |

### Gradient Common Errors
- Do not combine tints or lower gradient opacity
- Do not use unapproved gradients
- Do not apply treatments (vignettes, glows) to gradient edges
- Do not reverse gradient direction (unless in approved exception contexts)
- Do not use unapproved angles
- Do not use multiple colors in a single gradient (two-stop only)
- Maintain minimum contrast ratio (e.g., 4.5:1)

---

## 17. Typography

### Font Pairing

For each font in the system, capture:

| Field | Description |
|-------|-------------|
| Font Name | Full name including weight (e.g., "Archivo Extra Bold") |
| Role | Primary (headlines) / Supporting (body) / Fallback |
| Rationale | Why this font was chosen and what it communicates |
| Fallback Fonts | System defaults to use when custom fonts unavailable |

### Typography Rules
- Which font maps to which content type (headlines, body, etc.)
- When fallback fonts are acceptable
- Weight variation guidance for hierarchy of information

### Principal Typography
- Full character set sample for primary font
- Full character set sample for supporting font(s)

---

## 18. Type Scale & Weights

### Scale System

- **Base Size** — The root paragraph size (e.g., 1rem equivalent)
- **Scale Ratio** — The mathematical ratio used (e.g., 1.250 Major Third)
- **Line Height — Headlines** — (e.g., 1.3)
- **Line Height — Body/Paragraph** — (e.g., 1.6)

### Type Scale Table

| Level | Size | Font | Style | Kerning | Usage |
|-------|------|------|-------|---------|-------|
| HL (Hero/Display) | [size]px | [Font] | [e.g., All Caps] | [value] | [e.g., Single Text Elements, Section Headings] |
| H1 | [size]px | [Font] | [style] | [value] | [usage] |
| H2 | [size]px | [Font] | [style] | [value] | [usage] |
| H3 | [size]px | [Font] | [style] | [value] | [usage] |
| H4 | [size]px | [Font] | [style] | [value] | [usage] |
| H5 | [size]px | [Font] | [style] | [value] | [usage] |
| H6 | [size]px | [Font] | [style] | [value] | [usage] |
| p | [size]px (1rem) | [Font] | [style] | [value] | [usage] |
| small | [size]px | [Font] | [style] | [value] | [usage] |
| footnotes | [size]px | [Font] | [style] | [value] | [usage] |

---

## 19. Body Text Specifications

### For Each Text Type, Capture:

#### Paragraph
| Property | Value |
|----------|-------|
| Weight | [weight] |
| Size | [range]px |
| Line Height | [multiplier]x Size |
| Kerning | [value] |
| Color | [approved colors for body text] |

#### Links
| Property | Value |
|----------|-------|
| Weight | [weight] |
| Size | [range]px |
| Line Height | [multiplier]x Size |
| Color | [approved colors for links, including any tint rules] |

#### Bold Text
| Property | Value |
|----------|-------|
| Weight | [specific weight name] |

#### Block Quote
| Property | Value |
|----------|-------|
| Weight | [weight] |
| Size | [size]px |
| Line Height | [size]px |
| Margins | [values] |
| Padding | [values] |
| Border (left) | [size]px |

#### Lists
- Ordered list nesting structure
- Unordered list nesting structure
- Bullet/number style at each level

---

# FRAMEWORK NOTES

## For AI Ingestion Engineers

When encoding a brand into this framework, prioritize the following:

1. **IS/NOT Tone Constraints** — These are the single most enforceable element of any brand guide. They translate directly into system-level instructions for AI content generation.

2. **Color Hex Codes** — Always capture hex as the canonical value. RGB, CMYK, and Pantone are format-specific translations.

3. **Logo "Do Not" Lists** — These negative constraints are more valuable than positive guidance for AI enforcement. An AI can easily apply a logo; it's much harder to know what NOT to do without explicit rules.

4. **Type Scale Mathematics** — Capture the scale ratio and base size, not just the individual sizes. This allows the system to extrapolate if custom sizes are needed.

5. **Gradient Direction + Stop Colors** — Two data points per gradient (top color, bottom color) plus a global direction rule. Simple, enforceable.

6. **Tagline Immutability** — Taglines are locked copy. Flag them explicitly so AI systems never paraphrase or "improve" them.

7. **Clear Space as Relative Units** — Clear space defined relative to a logo element (not absolute pixels) scales correctly across contexts.

---

## SMART Branding Checklist

> See the **complete SMART Branding Checklist** at the end of this document, including the Extended Verification (Execution Layer) items.

---

## 20. Design Layouts

Grid systems and layout rules that govern how content is composed across different formats. These ensure visual consistency and proper content hierarchy.

### Print / Portrait (Letter)

- **Grid System** — Define the column count for portrait orientation (e.g., 8 columns).
- **Margins** — Generous margins to give adequate clear space and correct content weighting.
- **Logo Placement — First Page** — Full Primary Lockup in designated header zone.
- **Logo Placement — Subsequent Pages** — Approved alternate lockups (e.g., Icon Solo, Wordmark Solo) aligned according to page layout.
- **Content Zones** — Define which color/palette zones body text, headers, and logos should occupy. Map palette colors to specific layout regions (header zone, body zone, footer zone).

### Digital / Standard (Web & Social)

- **Minimum Resolution** — Define minimum resolution for web content (e.g., 1920×1080px / 4K+), or platform-appropriate ratios.
- **Grid System — Vertical** — Column count for vertical compositions (e.g., 8 columns).
- **Grid System — Horizontal** — Column count for horizontal compositions (e.g., 16 columns).
- **Safe Zone Rule** — Define where logos and main text must stay within the composition. Any placement outside the safe zone requires approval.

---

## 21. UI Elements

Interactive components that make up the brand's digital product experience. This section captures the design philosophy and specific rules for buttons, icons, inputs, and other interface elements.

### UI Design Philosophy

Capture the overarching approach to UI design:

- **Visual Treatment** — The dominant UI style (e.g., neumorphic, flat, glassmorphic, skeuomorphic). Describe the tactile/visual qualities (e.g., "soft glows and raised buttons give a 'touchable' feel").
- **Negative Space** — How whitespace/negative space is used within UI components to prevent overcrowding.
- **Effects Usage** — Guidelines for decorative effects (e.g., glow effects should be used "tastefully and sparingly" to direct focus).

### UI Element Rules

For each rule, capture:

- **Background Context** — How elements relate to their background (e.g., "always placed on a solid background of the same color, unless used as the main CTA in dark mode").
- **Depth / Elevation** — How the visual "depth" of a button/element is determined (e.g., by size and attention priority of the CTA).
- **Proportion** — Balance of font size to negative/border space within elements.
- **Lighting Direction** — Where the highlight/light source comes from for consistency across all elements (e.g., "highlight should come from above").
- **Internal Gradient Direction** — Whether elements use a reversed or standard gradient direction internally (e.g., "reverse gradient for insides of buttons/icons — 90° dark to light, opposite of background gradients").
- **Accessibility Stroke** — Whether a thin stroke/outline is required on UI elements for accessibility (e.g., "always use a thin brand-color stroke on UI elements to maximize accessibility for vision impaired users").

---

## 22. Graphic Elements

Supplementary visual assets derived from the brand identity that add texture, pattern, and visual interest to compositions. These weave aspects of the logo or brand motifs into a consistent visual language.

### Fields to Capture:

For each graphic element type:

- **Element Name** — Descriptive label (e.g., "Dots Pattern," "Diamond Grid," "Stroke Shapes").
- **Description** — What it looks like and how it's constructed.
- **Derivation** — How it connects to the brand identity (e.g., derived from logo geometry, color palette, brand motif).
- **Approved Usage Context** — Where it should be used (e.g., "subtly on dark backgrounds," "apparel and marketing materials").
- **Color Treatment** — How the element is colored relative to its background (e.g., "soft brand-color graphics against plain backgrounds").
- **Modification Rules** — Whether the element can be altered or requires approval for changes.

### Common Graphic Element Types

- **Pattern / Texture** — Repeating visual motifs (dots, grids, geometric shapes) used as background texture.
- **Stroke / Outline Shapes** — Basic shapes (rounded rectangles, circles, pills) used to outline neumorphic or interactive elements for accessibility.
- **Logo-Derived Pattern** — A pattern created from the logo or icon viewed from a specific angle or abstraction. Often used for apparel, physical merchandise, and large-format marketing.

---

## 23. Alternative Styling / Modes

Many brands have dual visual identities for different contexts — often a formal/corporate mode and an expressive/creative mode. This section captures how the brand adapts while maintaining cohesion.

### Fields to Capture:

For each style mode:

| Field | Description |
|-------|-------------|
| Mode Name | Descriptive label (e.g., "Corporate/Professional" or "Gamer/Expressive") |
| Visual Treatment | How the brand identity is rendered in this mode (e.g., light background vs dark background, clean vs textured) |
| Approved Contexts | Where this mode should be used (e.g., "formal contexts, standard content" vs "play-related contexts, after initial branding is established") |
| Light/Dark Mode Mapping | Whether this mode corresponds to a UI light or dark mode |
| Priority Rules | Which mode takes precedence (e.g., "corporate is default; expressive only after initial branding is established") |

### Design Principle

The brand's visual identity should balance its multiple facets. Designers should choose logo and background combinations that align with the specific context of use. While adapting to different settings, maintain a cohesive brand identity — the logo and background should complement each other, reinforcing the brand's dual nature.

---

## 24. Content & Imagery

Guidelines for the images, photographs, and visual content used to represent the brand across all media.

### Image Content Strategy

- **Purpose** — Define the role imagery plays in the brand (e.g., "create an experience in the mind of the user," "focus the message of a campaign," "strengthen Brand Recognition").
- **Color Sourcing** — All images should be sourced or color-graded to match the brand color palette as closely as possible. Define the preferred technique (e.g., 3-point color grading).
- **Approval Process** — If images outside the palette cannot be found, define the approval pathway.

### Approved Image Categories

List the specific thematic categories that brand imagery should focus on. Examples:

- Brand icon/symbol renderings
- Sacred geometry / mathematical patterns
- Soft glows and light effects in brand colors
- Brand-color dot/particle patterns
- Neumorphic / dimensional treatments

### Image Usage Rules

- **Sharpness** — All photography must be sharp unless blur serves a specific contrast purpose.
- **Screenshots** — If using app or game screenshots, all on-screen text must be readable.
- **People** — If using photographs of people, faces must be clear with no graphic elements overlaid on faces.
- **Context** — Use imagery when sharing a brand experience, whether digital or physical.

### Image Tone

- Images should convey warmth, approachability, ease of use, and technical expertise.
- Unless documenting a specific event, location, or person, imagery should be color-graded to match the brand palette.

---

## 25. Closing / Contact

The final section of a brand style guide typically reiterates the guide's purpose and provides a contact point for questions.

### Fields to Capture:

- **Guide Version / Year** — The edition or date of the style guide.
- **Contact Email** — The media/design team contact for questions about the guide.
- **Approval Authority** — Who has final say on brand decisions not explicitly covered by the guide.

---

# FRAMEWORK NOTES (continued)

## Additional AI Ingestion Priorities (from Pages 33–44)

8. **UI Element Lighting & Gradient Reversal** — UI elements often have different gradient rules than backgrounds (e.g., reversed direction inside buttons). This is a subtle but critical distinction — capture it explicitly or AI-generated UI will look wrong.

9. **Accessibility as Brand Rule** — When a brand mandates accessibility features (strokes on neumorphic elements, contrast ratios, clear faces in photography), these are not optional nice-to-haves. They should be encoded as hard constraints, same as color rules.

10. **Alternative Styling as Contextual Modes** — Brands with multiple visual modes (corporate/expressive, light/dark) need the AI to understand WHEN to use each. The trigger conditions ("formal contexts" vs "play-related contexts, only after initial branding is established") are the key data, not just the visual differences.

11. **Image Color Grading Mandate** — Many brands require all imagery to be color-graded to match the palette. This is often the most overlooked rule in AI-generated content. Capture the technique (e.g., 3-point color grading) and the target palette colors.

12. **Grid Systems as Constraints** — Column counts and safe zones aren't suggestions — they're the structural skeleton of every composition. An AI generating layouts needs these numbers.

---

## SMART Branding Checklist (Final — Complete)

Before considering a brand fully ingested, verify coverage across all five SMART dimensions:

- [ ] **Story-driven** — Is the brand narrative, origin, mission, and symbolism captured? Can an AI tell this brand's story?
- [ ] **Memorable** — Are the distinctive elements (logo, colors, taglines, personality traits) encoded in a way that produces recognizable output?
- [ ] **Agile** — Are the rules flexible enough to accommodate different contexts (print, web, social, mobile, light mode, dark mode) while maintaining consistency?
- [ ] **Responsive** — Are the sizing minimums, type scales, grid systems, and layout rules documented for responsive design across screen sizes and orientations?
- [ ] **Targeted** — Are the audience psychographics captured so content can be calibrated to the right people?

### Extended Verification (Execution Layer):

- [ ] All logo lockups documented with sizing minimums, clear space rules, and approved backgrounds
- [ ] Complete "Do Not" lists for logo, color, gradient, and imagery usage
- [ ] Full color palette with Hex, RGB, CMYK, and Pantone values
- [ ] All approved gradients with direction, stop colors, and exception rules
- [ ] Typography system with font names, weights, scale ratio, base size, and level-by-level usage mapping
- [ ] Body text specs including paragraph, link, bold, blockquote, and list formatting
- [ ] Grid systems for print (portrait) and digital (vertical/horizontal) with column counts
- [ ] UI element rules including lighting, depth, gradient reversal, and accessibility strokes
- [ ] Graphic element library with derivation, usage context, and modification rules
- [ ] Alternative styling modes with trigger conditions and priority hierarchy
- [ ] Image content categories, color grading requirements, and usage rules
- [ ] Contact/approval authority for edge cases not covered by the guide

---

> **SMART Brand Ingestion Framework — Complete**
> Version 1.0 — Derived from analysis of a full 44-page brand style guide
> Framework by Justin / Weyl.ai
