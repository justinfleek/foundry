/**
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *                                                     // foundry // scraper // visual
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *
 * Visual element extraction for pixel-perfect website reconstruction.
 *
 * Extracts:
 * - Bounding boxes for all visible elements
 * - Z-index stacking order
 * - Visual styles (backgrounds, borders, shadows)
 * - Element screenshots
 * - Layer decomposition
 *
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 */

import type { Page } from "playwright";
import type {
  VisualElement,
  VisualElementType,
  VisualDecomposition,
  VisualLayer,
} from "./types.js";

// Note: BoundingBox and VisualStyles are constructed inline rather than imported
// to avoid TypeScript's strict unused import checking. The types are still 
// validated by assignability to VisualElement.

// ============================================================================
// Main Entry Point
// ============================================================================

/**
 * Extract complete visual decomposition of a page.
 * This enables pixel-perfect reconstruction as pure data.
 */
export async function extractVisualDecomposition(
  page: Page,
  options: { elementScreenshots: boolean }
): Promise<VisualDecomposition> {
  // Get viewport and page dimensions
  const viewport = page.viewportSize() ?? { width: 1920, height: 1080 };
  
  const pageSize = await page.evaluate(() => ({
    width: Math.max(
      document.documentElement.scrollWidth,
      document.body.scrollWidth
    ),
    height: Math.max(
      document.documentElement.scrollHeight,
      document.body.scrollHeight
    ),
  }));

  // Take full page screenshot
  const fullScreenshotBuffer = await page.screenshot({
    fullPage: true,
    type: "png",
  });
  const fullScreenshot = fullScreenshotBuffer.toString("base64");

  // Extract all visual elements
  const rawElements = await extractAllElements(page);

  // Optionally take element screenshots
  const elements: VisualElement[] = [];
  for (const elem of rawElements) {
    if (options.elementScreenshots && elem.veBounds.bbWidth > 0 && elem.veBounds.bbHeight > 0) {
      try {
        const locator = page.locator(`[data-foundry-id="${elem.veId}"]`);
        const count = await locator.count();
        if (count > 0) {
          const screenshotBuffer = await locator.first().screenshot({ type: "png" });
          elem.veScreenshot = screenshotBuffer.toString("base64");
        }
      } catch {
        // Element may have been removed or is not screenshottable
      }
    }
    elements.push(elem);
  }

  // Group by z-index to form layers
  const layers = computeLayers(elements);

  return {
    vdViewport: viewport,
    vdPageSize: pageSize,
    vdElements: elements,
    vdFullScreenshot: fullScreenshot,
    vdLayers: layers,
  };
}

// ============================================================================
// Element Extraction
// ============================================================================

async function extractAllElements(page: Page): Promise<VisualElement[]> {
  // First, inject IDs into all elements for targeting
  await page.evaluate(function() {
    let idCounter = 0;
    const elements = document.querySelectorAll("*");
    for (const el of elements) {
      if (!el.getAttribute("data-foundry-id")) {
        el.setAttribute("data-foundry-id", `ve-${idCounter++}`);
      }
    }
  });

  // Extract element data
  // NOTE: Using function declarations instead of arrow functions to avoid
  // TSX __name decorator injection which breaks page.evaluate serialization
  const rawElements = await page.evaluate(function() {
    const results: Array<{
      id: string;
      tagName: string;
      bounds: { x: number; y: number; width: number; height: number };
      zIndex: number;
      visible: boolean;
      styles: {
        backgroundColor: string | null;
        backgroundImage: string | null;
        color: string | null;
        fontFamily: string | null;
        fontSize: string | null;
        fontWeight: string | null;
        lineHeight: string | null;
        textAlign: string | null;
        borderRadius: string | null;
        boxShadow: string | null;
        opacity: string | null;
        transform: string | null;
      };
      text: string | null;
      imageSrc: string | null;
      parentId: string | null;
      childIds: string[];
      classList: string[];
      role: string | null;
    }> = [];

    // Helper to check visibility
    function isVisible(el: Element): boolean {
      const style = window.getComputedStyle(el);
      const rect = el.getBoundingClientRect();
      return (
        style.display !== "none" &&
        style.visibility !== "hidden" &&
        parseFloat(style.opacity) > 0 &&
        rect.width > 0 &&
        rect.height > 0
      );
    }

    // Helper to get stacking z-index
    function getZIndex(el: Element): number {
      const style = window.getComputedStyle(el);
      const z = parseInt(style.zIndex, 10);
      if (!isNaN(z)) return z;
      
      // Walk up to find positioned ancestor with z-index
      let parent = el.parentElement;
      while (parent !== null) {
        const parentStyle = window.getComputedStyle(parent);
        const parentZ = parseInt(parentStyle.zIndex, 10);
        if (!isNaN(parentZ) && parentStyle.position !== "static") {
          return parentZ;
        }
        parent = parent.parentElement;
      }
      return 0;
    }

    // Helper to extract text content (direct only, not children)
    function getDirectText(el: Element): string | null {
      let text = "";
      for (const node of el.childNodes) {
        if (node.nodeType === Node.TEXT_NODE) {
          text += node.textContent?.trim() ?? "";
        }
      }
      return text.length > 0 ? text : null;
    }

    // Process all elements
    const elements = document.querySelectorAll("*");
    for (const el of elements) {
      const id = el.getAttribute("data-foundry-id");
      if (id === null) continue;

      const visible = isVisible(el);
      const rect = el.getBoundingClientRect();
      const cs = window.getComputedStyle(el);

      // Get parent ID
      const parentId = el.parentElement?.getAttribute("data-foundry-id") ?? null;

      // Get child IDs
      const childIds: string[] = [];
      for (const child of el.children) {
        const childId = child.getAttribute("data-foundry-id");
        if (childId !== null) {
          childIds.push(childId);
        }
      }

      // Extract background gradient from backgroundImage
      let backgroundGradient: string | null = null;
      const bgImage = cs.backgroundImage;
      if (bgImage.includes("gradient")) {
        backgroundGradient = bgImage;
      }

      results.push({
        id,
        tagName: el.tagName.toLowerCase(),
        bounds: {
          x: rect.left + window.scrollX,
          y: rect.top + window.scrollY,
          width: rect.width,
          height: rect.height,
        },
        zIndex: getZIndex(el),
        visible,
        styles: {
          backgroundColor: cs.backgroundColor,
          backgroundImage: bgImage.includes("url(") ? bgImage : (backgroundGradient ?? null),
          color: cs.color,
          fontFamily: cs.fontFamily,
          fontSize: cs.fontSize,
          fontWeight: cs.fontWeight,
          lineHeight: cs.lineHeight,
          textAlign: cs.textAlign,
          borderRadius: cs.borderRadius,
          boxShadow: cs.boxShadow !== "none" ? cs.boxShadow : null,
          opacity: cs.opacity,
          transform: cs.transform !== "none" ? cs.transform : null,
        },
        text: getDirectText(el),
        imageSrc: el instanceof HTMLImageElement ? el.src : null,
        parentId,
        childIds,
        classList: Array.from(el.classList),
        role: el.getAttribute("role"),
      });
    }

    return results;
  });

  // Convert to VisualElement type
  return rawElements
    .filter((el) => el.visible)
    .map((el) => ({
      veId: el.id,
      veTagName: el.tagName,
      veType: classifyElement(el.tagName, el.classList, el.role),
      veBounds: {
        bbX: el.bounds.x,
        bbY: el.bounds.y,
        bbWidth: el.bounds.width,
        bbHeight: el.bounds.height,
      },
      veZIndex: el.zIndex,
      veVisible: el.visible,
      veStyles: {
        vsBackgroundColor: normalizeColor(el.styles.backgroundColor),
        vsBackgroundImage: extractUrl(el.styles.backgroundImage),
        vsBackgroundGradient: el.styles.backgroundImage?.includes("gradient")
          ? el.styles.backgroundImage
          : null,
        vsColor: normalizeColor(el.styles.color),
        vsFontFamily: el.styles.fontFamily,
        vsFontSize: parsePixels(el.styles.fontSize),
        vsFontWeight: parseFontWeight(el.styles.fontWeight),
        vsLineHeight: parsePixels(el.styles.lineHeight),
        vsTextAlign: el.styles.textAlign,
        vsBorderRadius: el.styles.borderRadius,
        vsBoxShadow: el.styles.boxShadow,
        vsOpacity: el.styles.opacity !== null ? parseFloat(el.styles.opacity) : null,
        vsTransform: el.styles.transform,
      },
      veText: el.text,
      veImageSrc: el.imageSrc,
      veScreenshot: null, // Will be filled in later if requested
      veParentId: el.parentId,
      veChildIds: el.childIds,
    }));
}

// ============================================================================
// Element Classification
// ============================================================================

function classifyElement(
  tagName: string,
  classList: string[],
  role: string | null
): VisualElementType {
  const classes = classList.join(" ").toLowerCase();

  // By tag name
  switch (tagName) {
    case "header":
      return "VEHeader";
    case "nav":
      return "VENavigation";
    case "footer":
      return "VEFooter";
    case "h1":
    case "h2":
    case "h3":
    case "h4":
    case "h5":
    case "h6":
      return "VEHeading";
    case "p":
      return "VEParagraph";
    case "a":
      return "VELink";
    case "button":
      return "VEButton";
    case "img":
      if (classes.includes("logo")) return "VELogo";
      if (classes.includes("icon")) return "VEIcon";
      return "VEImage";
    case "svg":
      if (classes.includes("logo")) return "VELogo";
      if (classes.includes("icon")) return "VEIcon";
      return "VEIcon";
    case "input":
    case "textarea":
    case "select":
      return "VEInput";
    case "form":
      return "VEForm";
  }

  // By class name patterns
  if (classes.includes("logo")) return "VELogo";
  if (classes.includes("hero")) return "VEHero";
  if (classes.includes("btn") || classes.includes("button") || classes.includes("cta")) {
    return "VEButton";
  }
  if (classes.includes("card")) return "VECard";
  if (classes.includes("nav") || classes.includes("menu")) return "VENavigation";
  if (classes.includes("header")) return "VEHeader";
  if (classes.includes("footer")) return "VEFooter";
  if (classes.includes("icon")) return "VEIcon";

  // By role
  if (role === "banner") return "VEHeader";
  if (role === "navigation") return "VENavigation";
  if (role === "main") return "VEContainer";
  if (role === "contentinfo") return "VEFooter";
  if (role === "button") return "VEButton";
  if (role === "link") return "VELink";

  // By container-like tags
  if (["div", "section", "article", "aside", "main"].includes(tagName)) {
    // Check if it's a background element (large, at top of z-stack)
    if (classes.includes("background") || classes.includes("bg")) {
      return "VEBackground";
    }
    return "VEContainer";
  }

  return "VEUnknown";
}

// ============================================================================
// Layer Computation
// ============================================================================

function computeLayers(elements: VisualElement[]): VisualLayer[] {
  // Group by z-index
  const layerMap = new Map<number, string[]>();

  for (const el of elements) {
    const existing = layerMap.get(el.veZIndex) ?? [];
    existing.push(el.veId);
    layerMap.set(el.veZIndex, existing);
  }

  // Sort by z-index (back to front)
  const sortedZIndices = Array.from(layerMap.keys()).sort((a, b) => a - b);

  return sortedZIndices.map((zIndex) => ({
    vlZIndex: zIndex,
    vlElementIds: layerMap.get(zIndex) ?? [],
  }));
}

// ============================================================================
// Helpers
// ============================================================================

function normalizeColor(color: string | null): string | null {
  if (color === null || color === "transparent" || color === "rgba(0, 0, 0, 0)") {
    return null;
  }
  return color;
}

function extractUrl(value: string | null): string | null {
  if (value === null) return null;
  const match = value.match(/url\(["']?([^"')]+)["']?\)/);
  return match !== null ? match[1] : null;
}

function parsePixels(value: string | null): number | null {
  if (value === null) return null;
  const match = value.match(/^([\d.]+)px$/);
  return match !== null ? parseFloat(match[1]) : null;
}

function parseFontWeight(value: string | null): number | null {
  if (value === null) return null;
  const num = parseInt(value, 10);
  if (!isNaN(num)) return num;

  const weights: Record<string, number> = {
    normal: 400,
    bold: 700,
    lighter: 300,
    bolder: 700,
  };
  return weights[value.toLowerCase()] ?? null;
}
