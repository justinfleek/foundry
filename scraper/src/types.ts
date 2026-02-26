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
}

export type ScrapeResponse =
  | { type: "success"; result: ScrapeResult }
  | { type: "error"; error: ScrapeError };

export interface ScrapeError {
  code: string;
  message: string;
  details?: string;
}
