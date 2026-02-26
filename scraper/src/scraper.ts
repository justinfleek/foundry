/**
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *                                                     // foundry // scraper // core
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *
 * Playwright-based web scraper for brand extraction.
 *
 * Extracts:
 * - CSS stylesheets (inline, linked, imported)
 * - Computed styles for key DOM elements
 * - Text content (headings, paragraphs, buttons, nav, footer)
 * - Font data (@font-face declarations, used fonts)
 * - Assets (images, SVGs, logos, favicons)
 *
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 */

import { chromium, type Browser, Page, type BrowserContext } from "playwright";
import type {
  ScrapeResult,
  ScrapeOptions,
  CSSStylesheet,
  CSSRule,
  CSSProperty,
  CSSValue,
  ElementStyles,
  TextContent,
  TextBlock,
  TextBlockType,
  FontData,
  AssetData,
  AssetType,
} from "./types.js";

// ============================================================================
// Exported Type Re-exports (for consumers of this module)
// ============================================================================

/**
 * Re-export types that consumers may need for browser automation.
 * These are used in integration tests and higher-level orchestration.
 */
export type { Browser, BrowserContext };

/**
 * Re-export CSS types for external CSS analysis modules.
 * ComputedStyle and FontFace are used by foundry-extract's color/font analyzers.
 */
export type { ComputedStyle, FontFace } from "./types.js";

// ============================================================================
// Main Scraper
// ============================================================================

export async function scrapeURL(
  url: string,
  options: ScrapeOptions
): Promise<ScrapeResult> {
  // Allow override via environment variable for Nix-provided Chromium
  const executablePath = process.env["PLAYWRIGHT_CHROMIUM_PATH"] ?? process.env["CHROMIUM_PATH"];
  
  const browser = await chromium.launch({
    headless: true,
    ...(executablePath !== undefined ? { executablePath } : {}),
  });

  try {
    const context = await browser.newContext({
      userAgent:
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
      viewport: { width: 1920, height: 1080 },
    });

    const page = await context.newPage();

    // Inject helper functions into page context before navigation
    await injectHelpers(page);

    // Navigate with timeout
    await page.goto(url, {
      waitUntil: options.waitForJS ? "networkidle" : "domcontentloaded",
      timeout: options.timeout,
    });

    // Extract domain
    const urlObj = new URL(url);
    const domain = urlObj.hostname.replace(/^www\./, "");

    // Run all extractions in parallel
    const [stylesheets, computedStyles, textContent, fontData, assets, rawHTML] =
      await Promise.all([
        extractStylesheets(page, options.maxDepth),
        extractComputedStyles(page),
        extractTextContent(page),
        extractFontData(page),
        options.extractImages ? extractAssets(page) : Promise.resolve([]),
        page.content().then((html) => Buffer.from(html).toString("base64")),
      ]);

    return {
      srDomain: domain,
      srURL: url,
      srStylesheets: stylesheets,
      srComputedStyles: computedStyles,
      srTextContent: textContent,
      srFontData: fontData,
      srAssets: assets,
      srRawHTML: rawHTML,
    };
  } finally {
    await browser.close();
  }
}

// ============================================================================
// CSS Extraction
// ============================================================================

async function extractStylesheets(
  page: Page,
  _maxDepth: number
): Promise<CSSStylesheet[]> {
  const stylesheets: CSSStylesheet[] = [];

  // Extract inline styles
  const inlineStyles = await page.$$eval("style", (elements) =>
    elements.map((el) => el.textContent ?? "")
  );

  for (const css of inlineStyles) {
    if (css.trim()) {
      stylesheets.push({
        cssSource: "inline",
        cssRules: parseCSS(css),
      });
    }
  }

  // Extract linked stylesheets
  const linkedHrefs = await page.$$eval('link[rel="stylesheet"]', (links) =>
    links.map((link) => link.getAttribute("href")).filter(Boolean)
  );

  for (const href of linkedHrefs) {
    if (!href) continue;
    try {
      const absoluteURL = new URL(href, page.url()).href;
      const response = await page.context().request.get(absoluteURL);
      if (response.ok()) {
        const css = await response.text();
        stylesheets.push({
          cssSource: absoluteURL,
          cssRules: parseCSS(css),
        });
      }
    } catch {
      // Skip failed stylesheet fetches
    }
  }

  return stylesheets;
}

function parseCSS(css: string): CSSRule[] {
  const rules: CSSRule[] = [];

  // Simple CSS parser - handles basic rule blocks
  // Does NOT handle nested rules, @media, etc. (kept simple for now)
  const ruleRegex = /([^{]+)\{([^}]+)\}/g;
  const matches = css.matchAll(ruleRegex);

  for (const match of matches) {
    const selector = match[1].trim();
    const declarations = match[2].trim();

    // Skip @-rules for now
    if (selector.startsWith("@")) continue;

    const properties = parseDeclarations(declarations);
    if (properties.length > 0) {
      rules.push({
        cssSelector: selector,
        cssProperties: properties,
      });
    }
  }

  return rules;
}

function parseDeclarations(declarations: string): CSSProperty[] {
  const properties: CSSProperty[] = [];
  const declRegex = /([^:]+):\s*([^;]+);?/g;
  const matches = declarations.matchAll(declRegex);

  for (const match of matches) {
    const name = match[1].trim().toLowerCase();
    const rawValue = match[2].trim();

    // Filter to only brand-relevant properties
    if (isRelevantProperty(name)) {
      properties.push({
        cssPropName: name,
        cssPropValue: parseCSSValue(name, rawValue),
      });
    }
  }

  return properties;
}

function isRelevantProperty(name: string): boolean {
  const relevant = [
    "color",
    "background-color",
    "background",
    "font-family",
    "font-size",
    "font-weight",
    "line-height",
    "margin",
    "margin-top",
    "margin-right",
    "margin-bottom",
    "margin-left",
    "padding",
    "padding-top",
    "padding-right",
    "padding-bottom",
    "padding-left",
    "border-color",
    "border-radius",
  ];
  return relevant.includes(name);
}

function parseCSSValue(property: string, value: string): CSSValue {
  // Color properties
  if (
    property.includes("color") ||
    (property === "background" && isColorValue(value))
  ) {
    return { tag: "CSSColor", contents: value };
  }

  // Font family
  if (property === "font-family") {
    return { tag: "CSSFont", contents: value };
  }

  // Length values
  const lengthMatch = value.match(/^(-?[\d.]+)(px|rem|em|%|vh|vw|pt)$/);
  if (lengthMatch) {
    return {
      tag: "CSSLength",
      contents: [parseFloat(lengthMatch[1]), lengthMatch[2]],
    };
  }

  // Unitless numbers
  if (/^-?[\d.]+$/.test(value)) {
    return { tag: "CSSNumber", contents: parseFloat(value) };
  }

  // Keywords
  if (/^[a-z-]+$/i.test(value)) {
    return { tag: "CSSKeyword", contents: value };
  }

  // Fallback
  return { tag: "CSSRaw", contents: value };
}

function isColorValue(value: string): boolean {
  return (
    value.startsWith("#") ||
    value.startsWith("rgb") ||
    value.startsWith("hsl") ||
    value.startsWith("oklch") ||
    /^[a-z]+$/i.test(value) // Named colors
  );
}

// ============================================================================
// Computed Styles Extraction
// ============================================================================

const KEY_SELECTORS = [
  "body",
  "h1",
  "h2",
  "h3",
  "h4",
  "h5",
  "h6",
  "p",
  "a",
  "button",
  'button[type="submit"]',
  'input[type="submit"]',
  ".btn",
  ".button",
  "nav",
  "nav a",
  "header",
  "footer",
  "main",
  "article",
  ".hero",
  ".cta",
];

async function extractComputedStyles(page: Page): Promise<ElementStyles[]> {
  const styles: ElementStyles[] = [];

  for (const selector of KEY_SELECTORS) {
    try {
      const element = await page.$(selector);
      if (!element) continue;

      const computed = await element.evaluate((el) => {
        const cs = window.getComputedStyle(el);
        return {
          color: cs.color,
          backgroundColor: cs.backgroundColor,
          fontFamily: cs.fontFamily,
          fontSize: cs.fontSize,
          fontWeight: cs.fontWeight,
          lineHeight: cs.lineHeight,
          marginTop: cs.marginTop,
          marginRight: cs.marginRight,
          marginBottom: cs.marginBottom,
          marginLeft: cs.marginLeft,
          paddingTop: cs.paddingTop,
          paddingRight: cs.paddingRight,
          paddingBottom: cs.paddingBottom,
          paddingLeft: cs.paddingLeft,
        };
      });

      const tagName = await element.evaluate((el) => el.tagName);

      styles.push({
        esSelector: selector,
        esTagName: tagName,
        esStyles: {
          csColor: computed.color ?? null,
          csBackgroundColor: computed.backgroundColor ?? null,
          csFontFamily: computed.fontFamily ?? null,
          csFontSize: parsePixels(computed.fontSize),
          csFontWeight: parseFontWeight(computed.fontWeight),
          csLineHeight: parsePixels(computed.lineHeight),
          csMarginTop: parsePixels(computed.marginTop),
          csMarginRight: parsePixels(computed.marginRight),
          csMarginBottom: parsePixels(computed.marginBottom),
          csMarginLeft: parsePixels(computed.marginLeft),
          csPaddingTop: parsePixels(computed.paddingTop),
          csPaddingRight: parsePixels(computed.paddingRight),
          csPaddingBottom: parsePixels(computed.paddingBottom),
          csPaddingLeft: parsePixels(computed.paddingLeft),
        },
      });
    } catch {
      // Skip elements that can't be queried
    }
  }

  return styles;
}

function parsePixels(value: string | null): number | null {
  if (!value) return null;
  const match = value.match(/^([\d.]+)px$/);
  return match ? parseFloat(match[1]) : null;
}

function parseFontWeight(value: string | null): number | null {
  if (!value) return null;
  const num = parseInt(value, 10);
  if (!isNaN(num)) return num;

  // Named weights
  const weights: Record<string, number> = {
    normal: 400,
    bold: 700,
    lighter: 300,
    bolder: 700,
  };
  return weights[value.toLowerCase()] ?? null;
}

// ============================================================================
// Text Content Extraction
// ============================================================================

async function extractTextContent(page: Page): Promise<TextContent> {
  const title = await page.title();

  const headings = await extractTextBlocks(page, {
    h1: "TBHeading1",
    h2: "TBHeading2",
    h3: "TBHeading3",
    h4: "TBHeading4",
    h5: "TBHeading5",
    h6: "TBHeading6",
  });

  const paragraphs = await extractTextBlocksForSelector(page, "p", "TBParagraph");
  const buttons = await extractTextBlocksForSelector(
    page,
    "button, .btn, .button, [type='submit']",
    "TBButton"
  );
  const navigation = await extractTextBlocksForSelector(page, "nav a", "TBLink");
  const footer = await extractTextBlocksForSelector(page, "footer", "TBParagraph");

  return {
    tcTitle: title || null,
    tcHeadings: headings,
    tcParagraphs: paragraphs.slice(0, 50), // Limit
    tcButtons: buttons.slice(0, 20),
    tcNavigation: navigation.slice(0, 30),
    tcFooter: footer.slice(0, 10),
  };
}

async function extractTextBlocks(
  page: Page,
  selectorMap: Record<string, TextBlockType>
): Promise<TextBlock[]> {
  const blocks: TextBlock[] = [];

  for (const [selector, blockType] of Object.entries(selectorMap)) {
    const selectorBlocks = await extractTextBlocksForSelector(
      page,
      selector,
      blockType
    );
    blocks.push(...selectorBlocks);
  }

  return blocks;
}

async function extractTextBlocksForSelector(
  page: Page,
  selector: string,
  blockType: TextBlockType
): Promise<TextBlock[]> {
  try {
    const texts = await page.$$eval(selector, (elements) =>
      elements
        .map((el) => ({
          text: el.textContent?.trim() ?? "",
          selector: el.tagName.toLowerCase(),
        }))
        .filter((item) => item.text.length > 0)
    );

    return texts.map((item) => ({
      tbText: item.text,
      tbType: blockType,
      tbSelector: item.selector,
    }));
  } catch {
    return [];
  }
}

// ============================================================================
// Font Data Extraction
// ============================================================================

async function extractFontData(page: Page): Promise<FontData> {
  // Extract @font-face declarations
  const fontFaces = await page.evaluate(() => {
    const faces: Array<{
      family: string;
      weight: string | null;
      style: string | null;
      src: string;
    }> = [];

    for (const sheet of document.styleSheets) {
      try {
        for (const rule of sheet.cssRules) {
          if (rule instanceof CSSFontFaceRule) {
            faces.push({
              family: rule.style.getPropertyValue("font-family").replace(/["']/g, ""),
              weight: rule.style.getPropertyValue("font-weight") || null,
              style: rule.style.getPropertyValue("font-style") || null,
              src: rule.style.getPropertyValue("src") || "",
            });
          }
        }
      } catch {
        // CORS blocks access to some stylesheets
      }
    }

    return faces;
  });

  // Count font usage across key elements
  const usedFonts = await page.evaluate(() => {
    const counts: Record<string, number> = {};
    const elements = document.querySelectorAll("body, h1, h2, h3, p, a, button");

    for (const el of elements) {
      const fontFamily = window.getComputedStyle(el).fontFamily;
      const primary = fontFamily.split(",")[0].trim().replace(/["']/g, "");
      counts[primary] = (counts[primary] || 0) + 1;
    }

    return counts;
  });

  return {
    fdFaces: fontFaces.map((f) => ({
      ffFamily: f.family,
      ffWeight: f.weight,
      ffStyle: f.style,
      ffSrc: f.src,
    })),
    fdUsedFonts: usedFonts,
  };
}

// ============================================================================
// Asset Extraction
// ============================================================================

async function extractAssets(page: Page): Promise<AssetData[]> {
  const assets: AssetData[] = [];

  // Images
  const images = await page.$$eval("img", (imgs) =>
    imgs.map((img) => ({
      url: img.src,
      alt: img.alt || null,
      context: detectContext(img),
    }))
  );

  for (const img of images) {
    if (img.url) {
      assets.push({
        adURL: img.url,
        adType: detectAssetType(img.url),
        adAlt: img.alt,
        adContext: img.context,
      });
    }
  }

  // SVGs
  const svgs = await page.$$eval("svg", (svgEls) =>
    svgEls.map((svg) => ({
      url: "", // Inline SVGs don't have URLs
      context: detectContext(svg),
    }))
  );

  for (const svg of svgs) {
    assets.push({
      adURL: svg.url,
      adType: "ATSVG",
      adAlt: null,
      adContext: svg.context,
    });
  }

  // Favicon
  const favicon = await page.$eval(
    'link[rel="icon"], link[rel="shortcut icon"]',
    (link) => link.getAttribute("href")
  ).catch(() => null);

  if (favicon) {
    assets.push({
      adURL: new URL(favicon, page.url()).href,
      adType: "ATFavicon",
      adAlt: null,
      adContext: "head",
    });
  }

  return assets.slice(0, 100); // Limit
}

function detectAssetType(url: string): AssetType {
  const lower = url.toLowerCase();
  if (lower.includes("logo")) return "ATLogo";
  if (lower.includes("icon") || lower.includes("favicon")) return "ATIcon";
  if (lower.endsWith(".svg")) return "ATSVG";
  return "ATImage";
}

// Helper declared for use in evaluate contexts
declare function detectContext(el: Element): string;

// Inject helper into page context
function injectHelpers(page: Page): Promise<void> {
  return page.addInitScript(() => {
    (window as unknown as { detectContext: (el: Element) => string }).detectContext = (
      el: Element
    ): string => {
      const parent = el.closest("header, footer, nav, main, aside, .hero, .cta");
      return parent?.tagName?.toLowerCase() ?? "body";
    };
  });
}
