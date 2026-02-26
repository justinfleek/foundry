/**
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *                                                    // foundry // scraper // server
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *
 * ZMQ ROUTER server that receives scrape requests from Haskell client.
 *
 * Protocol:
 * - Receives: [clientId, requestId, JSON(ScrapeRequest)]
 * - Sends: [clientId, requestId, JSON(ScrapeResponse)]
 *
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 */

import { Router } from "zeromq";
import { scrapeURL } from "./scraper.js";
import type {
  ScrapeRequest,
  ScrapeResponse,
  ScrapeOptions,
} from "./types.js";

// ============================================================================
// Configuration
// ============================================================================

interface ServerConfig {
  endpoint: string;
  maxConcurrent: number;
}

const DEFAULT_CONFIG: ServerConfig = {
  endpoint: "tcp://127.0.0.1:5555",
  maxConcurrent: 4,
};

// ============================================================================
// Server
// ============================================================================

export class ScraperServer {
  private socket: Router;
  private config: ServerConfig;
  private running: boolean = false;
  private activeJobs: number = 0;

  constructor(config: Partial<ServerConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
    this.socket = new Router();
  }

  async start(): Promise<void> {
    await this.socket.bind(this.config.endpoint);
    this.running = true;
    console.log(`Scraper server listening on ${this.config.endpoint}`);

    this.receiveLoop();
  }

  async stop(): Promise<void> {
    this.running = false;
    this.socket.close();
    console.log("Scraper server stopped");
  }

  private async receiveLoop(): Promise<void> {
    while (this.running) {
      try {
        const [clientId, requestId, messageBuffer] = await this.socket.receive();

        // Don't block - handle request asynchronously
        this.handleRequest(clientId, requestId, messageBuffer).catch((err) => {
          console.error("Error handling request:", err);
        });
      } catch (err) {
        if (this.running) {
          console.error("Error receiving message:", err);
        }
      }
    }
  }

  private async handleRequest(
    clientId: Buffer,
    requestId: Buffer,
    messageBuffer: Buffer
  ): Promise<void> {
    let response: ScrapeResponse;

    try {
      const message = JSON.parse(messageBuffer.toString()) as ScrapeRequest;

      if (message.type !== "scrape") {
        response = {
          type: "error",
          error: {
            code: "INVALID_TYPE",
            message: `Unknown message type: ${message.type}`,
          },
        };
      } else {
        // Wait if too many concurrent jobs
        while (this.activeJobs >= this.config.maxConcurrent) {
          await new Promise((resolve) => setTimeout(resolve, 100));
        }

        this.activeJobs++;
        try {
          const result = await scrapeURL(message.url, message.options);
          response = { type: "success", result };
        } finally {
          this.activeJobs--;
        }
      }
    } catch (err) {
      const error = err instanceof Error ? err : new Error(String(err));
      response = {
        type: "error",
        error: {
          code: "SCRAPE_ERROR",
          message: error.message,
          details: error.stack,
        },
      };
    }

    // Send response back
    try {
      await this.socket.send([clientId, requestId, JSON.stringify(response)]);
    } catch (err) {
      console.error("Error sending response:", err);
    }
  }
}

// ============================================================================
// CLI Entry Point
// ============================================================================

if (import.meta.url === `file://${process.argv[1]}`) {
  const endpoint = process.env["SCRAPER_ENDPOINT"] ?? DEFAULT_CONFIG.endpoint;
  const maxConcurrent = parseInt(
    process.env["SCRAPER_MAX_CONCURRENT"] ?? String(DEFAULT_CONFIG.maxConcurrent),
    10
  );

  const server = new ScraperServer({ endpoint, maxConcurrent });

  // Graceful shutdown
  process.on("SIGINT", async () => {
    console.log("\nShutting down...");
    await server.stop();
    process.exit(0);
  });

  process.on("SIGTERM", async () => {
    await server.stop();
    process.exit(0);
  });

  server.start().catch((err) => {
    console.error("Failed to start server:", err);
    process.exit(1);
  });
}
