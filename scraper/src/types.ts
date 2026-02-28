/**
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *                                                       // foundry // scraper // types
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *
 * TypeScript types that mirror Foundry.Extract.Types exactly.
 * These must serialize to JSON that the Haskell FromJSON instances accept.
 *
 * CRITICAL: Field names must match Haskell record fields exactly.
 *
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 */

// ============================================================================
// Scrape Result (top-level output)
// ============================================================================

export interface ScrapeResult {
  srDomain: string;
  srURL: string;
  srStylesheets: CSSStylesheet[];
  srComputedStyles: ElementStyles[];
  srTextContent: TextContent;
  srFontData: FontData;
  srAssets: AssetData[];
  srRawHTML: string; // Base64 encoded
  /** Visual decomposition for pixel-perfect reconstruction */
  srVisualDecomposition: VisualDecomposition | null;
}

// ============================================================================
// CSS Data
// ============================================================================

export interface CSSStylesheet {
  cssSource: string;
  cssRules: CSSRule[];
}

export interface CSSRule {
  cssSelector: string;
  cssProperties: CSSProperty[];
}

export interface CSSProperty {
  cssPropName: string;
  cssPropValue: CSSValue;
}

/**
 * CSS value - tagged union matching Haskell ADT
 * Haskell uses generic JSON encoding, so we need {"tag": "...", "contents": ...}
 */
export type CSSValue =
  | { tag: "CSSColor"; contents: string }
  | { tag: "CSSLength"; contents: [number, string] }
  | { tag: "CSSFont"; contents: string }
  | { tag: "CSSKeyword"; contents: string }
  | { tag: "CSSNumber"; contents: number }
  | { tag: "CSSRaw"; contents: string };

// ============================================================================
// Computed Styles
// ============================================================================

export interface ComputedStyle {
  csColor: string | null;
  csBackgroundColor: string | null;
  csFontFamily: string | null;
  csFontSize: number | null;
  csFontWeight: number | null;
  csLineHeight: number | null;
  csMarginTop: number | null;
  csMarginRight: number | null;
  csMarginBottom: number | null;
  csMarginLeft: number | null;
  csPaddingTop: number | null;
  csPaddingRight: number | null;
  csPaddingBottom: number | null;
  csPaddingLeft: number | null;
}

export interface ElementStyles {
  esSelector: string;
  esTagName: string;
  esStyles: ComputedStyle;
}

// ============================================================================
// Text Content
// ============================================================================

export interface TextContent {
  tcTitle: string | null;
  tcHeadings: TextBlock[];
  tcParagraphs: TextBlock[];
  tcButtons: TextBlock[];
  tcNavigation: TextBlock[];
  tcFooter: TextBlock[];
}

export interface TextBlock {
  tbText: string;
  tbType: TextBlockType;
  tbSelector: string;
}

/**
 * Text block types - must match Haskell Enum exactly
 */
export type TextBlockType =
  | "TBHeading1"
  | "TBHeading2"
  | "TBHeading3"
  | "TBHeading4"
  | "TBHeading5"
  | "TBHeading6"
  | "TBParagraph"
  | "TBButton"
  | "TBLink"
  | "TBListItem"
  | "TBBlockquote";

// ============================================================================
// Font Data
// ============================================================================

export interface FontData {
  fdFaces: FontFace[];
  fdUsedFonts: Record<string, number>;
}

export interface FontFace {
  ffFamily: string;
  ffWeight: string | null;
  ffStyle: string | null;
  ffSrc: string;
}

// ============================================================================
// Asset Data
// ============================================================================

export interface AssetData {
  adURL: string;
  adType: AssetType;
  adAlt: string | null;
  adContext: string;
}

/**
 * Asset types - must match Haskell Enum exactly
 */
export type AssetType = "ATImage" | "ATSVG" | "ATFavicon" | "ATLogo" | "ATIcon";

// ============================================================================
// Visual Elements (pixel-perfect extraction)
// ============================================================================

/**
 * A visual element extracted from the DOM with exact pixel coordinates.
 * This enables pixel-perfect reconstruction of the website as pure data.
 */
export interface VisualElement {
  /** Unique identifier for this element (CSS selector path) */
  veId: string;
  /** Element tag name */
  veTagName: string;
  /** Semantic type of the element */
  veType: VisualElementType;
  /** Bounding box in viewport coordinates */
  veBounds: BoundingBox;
  /** Z-index / stacking layer */
  veZIndex: number;
  /** Is element visible? */
  veVisible: boolean;
  /** Computed visual styles */
  veStyles: VisualStyles;
  /** Text content (if any) */
  veText: string | null;
  /** Image source URL (if image element) */
  veImageSrc: string | null;
  /** Screenshot of just this element (base64 PNG) */
  veScreenshot: string | null;
  /** Parent element ID */
  veParentId: string | null;
  /** Child element IDs */
  veChildIds: string[];
}

/**
 * Types of visual elements for semantic classification
 */
export type VisualElementType =
  | "VEBackground"     // Full-page or section backgrounds
  | "VEHeader"         // Header/navigation area
  | "VENavigation"     // Navigation menus
  | "VELogo"           // Logo images
  | "VEHero"           // Hero sections
  | "VEHeading"        // Headings (h1-h6)
  | "VEParagraph"      // Paragraph text
  | "VEButton"         // Buttons and CTAs
  | "VELink"           // Links
  | "VEImage"          // Images
  | "VEIcon"           // Icons
  | "VECard"           // Card components
  | "VEForm"           // Form elements
  | "VEInput"          // Input fields
  | "VEFooter"         // Footer area
  | "VEContainer"      // Generic container
  | "VEUnknown";       // Unclassified

/**
 * Pixel-precise bounding box
 */
export interface BoundingBox {
  /** X coordinate (left edge) */
  bbX: number;
  /** Y coordinate (top edge) */
  bbY: number;
  /** Width in pixels */
  bbWidth: number;
  /** Height in pixels */
  bbHeight: number;
}

/**
 * Visual styles relevant for rendering
 */
export interface VisualStyles {
  /** Background color (computed) */
  vsBackgroundColor: string | null;
  /** Background image URL */
  vsBackgroundImage: string | null;
  /** Background gradient (if any) */
  vsBackgroundGradient: string | null;
  /** Text color */
  vsColor: string | null;
  /** Font family */
  vsFontFamily: string | null;
  /** Font size in pixels */
  vsFontSize: number | null;
  /** Font weight */
  vsFontWeight: number | null;
  /** Line height */
  vsLineHeight: number | null;
  /** Text alignment */
  vsTextAlign: string | null;
  /** Border radius (all corners) */
  vsBorderRadius: string | null;
  /** Box shadow */
  vsBoxShadow: string | null;
  /** Opacity */
  vsOpacity: number | null;
  /** Transform matrix */
  vsTransform: string | null;
}

/**
 * Complete visual decomposition of a page
 */
export interface VisualDecomposition {
  /** Viewport dimensions */
  vdViewport: { width: number; height: number };
  /** Full page dimensions (including scroll) */
  vdPageSize: { width: number; height: number };
  /** All visual elements in z-order (back to front) */
  vdElements: VisualElement[];
  /** Full page screenshot (base64 PNG) */
  vdFullScreenshot: string;
  /** Layers: elements grouped by z-index */
  vdLayers: VisualLayer[];
}

/**
 * A visual layer (elements at same z-index)
 */
export interface VisualLayer {
  vlZIndex: number;
  vlElementIds: string[];
}

// ============================================================================
// Protocol Types
// ============================================================================

export interface ScrapeRequest {
  type: "scrape";
  url: string;
  options: ScrapeOptions;
}

export interface ScrapeOptions {
  timeout: number;
  waitForJS: boolean;
  extractImages: boolean;
  extractFonts: boolean;
  maxDepth: number;
  /** Extract visual decomposition (bounding boxes, screenshots) */
  extractVisualElements: boolean;
  /** Take element-level screenshots (expensive but complete) */
  elementScreenshots: boolean;
}

export type ScrapeResponse =
  | { type: "success"; result: ScrapeResult }
  | { type: "error"; error: ScrapeError };

export interface ScrapeError {
  code: string;
  message: string;
  details?: string;
}
