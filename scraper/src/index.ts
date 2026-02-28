/**
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *                                                      // foundry // scraper // main
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *
 * Foundry Scraper - Playwright-based brand extraction
 *
 * Usage:
 *   # Start ZMQ server (for Haskell client)
 *   npm start
 *
 *   # Scrape a single URL (CLI mode)
 *   npm run dev -- --url https://example.com
 *
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 */

export { scrapeURL } from "./scraper.js";
export { ScraperServer } from "./server.js";
export type * from "./types.js";

import { scrapeURL } from "./scraper.js";
import { ScraperServer } from "./server.js";
import type { ScrapeOptions } from "./types.js";

// ============================================================================
// CLI
// ============================================================================

async function main(): Promise<void> {
  const args = process.argv.slice(2);

  // Parse arguments
  const urlIndex = args.indexOf("--url");
  const serverMode = args.includes("--server");

  if (serverMode || args.length === 0) {
    // Start ZMQ server
    const endpoint = process.env["SCRAPER_ENDPOINT"] ?? "tcp://127.0.0.1:5555";
    const server = new ScraperServer({ endpoint });

    // Graceful shutdown
    process.on("SIGINT", async () => {
      console.log("\nShutting down...");
      await server.stop();
      process.exit(0);
    });

    await server.start();
  } else if (urlIndex !== -1 && args[urlIndex + 1]) {
    // Single URL scrape mode
    const url = args[urlIndex + 1];
    const outputJson = args.includes("--json");

    const options: ScrapeOptions = {
      timeout: 30000,
      waitForJS: true,
      extractImages: true,
      extractFonts: true,
      maxDepth: 3,
      extractVisualElements: args.includes("--visual"),
      elementScreenshots: args.includes("--screenshots"),
    };

    console.log(`Scraping: ${url}`);
    const startTime = Date.now();

    try {
      const result = await scrapeURL(url, options);
      const elapsed = Date.now() - startTime;

      if (outputJson) {
        console.log(JSON.stringify(result, null, 2));
      } else {
        console.log(`\nScrape completed in ${elapsed}ms`);
        console.log(`Domain: ${result.srDomain}`);
        console.log(`Stylesheets: ${result.srStylesheets.length}`);
        console.log(`Computed styles: ${result.srComputedStyles.length}`);
        console.log(`Text blocks: ${countTextBlocks(result.srTextContent)}`);
        console.log(`Font faces: ${result.srFontData.fdFaces.length}`);
        console.log(`Used fonts: ${Object.keys(result.srFontData.fdUsedFonts).length}`);
        console.log(`Assets: ${result.srAssets.length}`);
      }
    } catch (err) {
      console.error("Scrape failed:", err);
      process.exit(1);
    }
  } else {
    console.log(`
Foundry Scraper - Brand extraction via Playwright

Usage:
  npm start                     Start ZMQ server
  npm run dev -- --url <URL>    Scrape single URL
  npm run dev -- --url <URL> --json   Output as JSON

Environment:
  SCRAPER_ENDPOINT     ZMQ endpoint (default: tcp://127.0.0.1:5555)
  SCRAPER_MAX_CONCURRENT   Max concurrent scrapes (default: 4)
`);
  }
}

function countTextBlocks(tc: {
  tcHeadings: unknown[];
  tcParagraphs: unknown[];
  tcButtons: unknown[];
  tcNavigation: unknown[];
  tcFooter: unknown[];
}): number {
  return (
    tc.tcHeadings.length +
    tc.tcParagraphs.length +
    tc.tcButtons.length +
    tc.tcNavigation.length +
    tc.tcFooter.length
  );
}

main().catch((err) => {
  console.error("Fatal error:", err);
  process.exit(1);
});
