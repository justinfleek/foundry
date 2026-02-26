{
  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  #                                                                // metxt // nix
  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  #
  # METXT - SMART Brand Ingestion Engine
  #
  # ARCHITECTURE:
  #   Lean4   - CIC proofs, invariants defined FIRST (Hydrogen.Schema.Brand.*)
  #   Haskell - Backend runtime, graded monads, GHC 9.12 + StrictData
  #   PureScript - Hydrogen framework frontend
  #   Buck2   - Hermetic builds via sensenet
  #   Dhall   - Typed build configuration with coeffect algebra
  #
  # DEPENDENCIES:
  #   ZeroMQ     - Agent/scraper communication (ZMTP 3.x)
  #   SearXNG    - Privacy-respecting discovery
  #   Playwright - Browser automation (sandboxed)
  #   gVisor     - Container sandboxing (runsc)
  #   Bubblewrap - Lightweight sandboxing (bwrap)
  #   DuckDB     - L2 analytical storage
  #   PostgreSQL - L3 durable storage
  #   Hedgehog   - Property-based testing
  #   QuickCheck - Property-based testing
  #
  # BUILD:
  #   nix develop         - Enter development shell
  #   buck2 build //...   - Build all targets
  #   lake build          - Build Lean4 proofs (in lean/)
  #
  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  description = "METXT - SMART Brand Ingestion Engine (Lean4/Haskell/PureScript)";

  nixConfig = {
    extra-substituters = [
      "https://cache.nixos.org"
      "https://weyl-ai.cachix.org"
    ];
    extra-trusted-public-keys = [
      "cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY="
      "weyl-ai.cachix.org-1:NWy8MiNiSLvkompKqN5+WZ8rDWiMXPrkVQO2c4FqXWQ="
    ];
  };

  inputs = {
    # ══════════════════════════════════════════════════════════════════════════════
    # CORE INFRASTRUCTURE
    # ══════════════════════════════════════════════════════════════════════════════

    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    systems.url = "github:nix-systems/default";
    flake-parts.url = "github:hercules-ci/flake-parts";

    # ══════════════════════════════════════════════════════════════════════════════
    # SENSENET - Production build system (Buck2, LLVM, Dhall, remote execution)
    # ══════════════════════════════════════════════════════════════════════════════

    sensenet = {
      url = "git+ssh://git@github.com/straylight-software/sensenet";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.nix-compile.url = "git+ssh://git@github.com/straylight-software/nix-compile";
    };

    # ══════════════════════════════════════════════════════════════════════════════
    # HYDROGEN - PureScript framework + Lean4 proofs (Brand schemas)
    # ══════════════════════════════════════════════════════════════════════════════

    hydrogen = {
      url = "github:justinfleek/hydrogen";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # ══════════════════════════════════════════════════════════════════════════════
    # PURESCRIPT OVERLAY
    # ══════════════════════════════════════════════════════════════════════════════

    purescript-overlay = {
      url = "github:thomashoneyman/purescript-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = import inputs.systems;

      # ════════════════════════════════════════════════════════════════════════════
      # IMPORTS
      # ════════════════════════════════════════════════════════════════════════════
      # NOTE: sensenet.flakeModules.default currently has a module interface
      # mismatch. Using standalone devShell until resolved.
      # TODO: Re-enable sensenet integration once module API is compatible

      imports = [ ];

      # ════════════════════════════════════════════════════════════════════════════
      # PER-SYSTEM CONFIGURATION
      # ════════════════════════════════════════════════════════════════════════════

      perSystem =
        {
          config,
          pkgs,
          system,
          ...
        }:
        let
          # ──────────────────────────────────────────────────────────────────────────
          # HASKELL TOOLCHAIN (GHC 9.12)
          # ──────────────────────────────────────────────────────────────────────────

          ghc912 = pkgs.haskell.packages.ghc912;

          haskellDevDeps = [
            ghc912.ghc
            pkgs.cabal-install
            ghc912.haskell-language-server
            ghc912.hlint
            ghc912.fourmolu
            ghc912.hedgehog
            ghc912.QuickCheck
          ];

          # Haskell library dependencies for metxt packages
          haskellLibDeps = hp: [
            hp.aeson
            hp.attoparsec
            hp.base
            hp.bytestring
            hp.containers
            hp.crypton
            hp.directory
            hp.duckdb
            hp.filepath
            hp.hashable
            hp.hedgehog
            hp.megaparsec
            hp.memory
            hp.postgresql-simple
            hp.process
            hp.scientific
            hp.stm
            hp.text
            hp.time
            hp.transformers
            hp.unordered-containers
            hp.uuid
            hp.vector
            hp.zeromq4-haskell
          ];

          # ──────────────────────────────────────────────────────────────────────────
          # PURESCRIPT TOOLCHAIN (Hydrogen framework)
          # ──────────────────────────────────────────────────────────────────────────

          psPkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [ inputs.purescript-overlay.overlays.default ];
          };

          purescriptDeps = [
            psPkgs.purs
            psPkgs.spago-unstable
            psPkgs.purs-tidy
            psPkgs.purs-backend-es
            pkgs.esbuild
            pkgs.nodejs_22
          ];

          # ──────────────────────────────────────────────────────────────────────────
          # LEAN4 TOOLCHAIN
          # ──────────────────────────────────────────────────────────────────────────

          lean4Deps = [
            pkgs.elan
          ];

          # ──────────────────────────────────────────────────────────────────────────
          # INFRASTRUCTURE DEPENDENCIES
          # ──────────────────────────────────────────────────────────────────────────

          infrastructureDeps = [
            # Message passing (ZMTP 3.x)
            pkgs.zeromq

            # Browser automation (sandboxed)
            pkgs.playwright-driver
            pkgs.chromium

            # Sandboxing
            pkgs.bubblewrap
            # pkgs.gvisor  # runsc - may need to add manually

            # Discovery
            # SearXNG runs as a service, not a package dep

            # Database
            pkgs.duckdb
            pkgs.postgresql

            # Configuration
            pkgs.dhall
            pkgs.dhall-json
            pkgs.dhall-lsp-server

            # AST manipulation
            pkgs.tree-sitter
            pkgs.ast-grep

            # Utilities
            pkgs.jq
            pkgs.yq-go
            pkgs.ripgrep
            pkgs.fd
            pkgs.git
            pkgs.pkg-config
          ];

        in
        {
          # ════════════════════════════════════════════════════════════════════════
          # DEVELOPMENT SHELLS
          # ════════════════════════════════════════════════════════════════════════
          #
          # NOTE: sensenet Buck2 project config disabled until module API resolved.
          # Build targets for future reference:
          #   //haskell/foundry-core:foundry-core
          #   //haskell/foundry-extract:foundry-extract
          #   //haskell/foundry-scraper:foundry-scraper
          #   //haskell/foundry-storage:foundry-storage
          #   //scraper:scraper
          #

          devShells.default = pkgs.mkShell {
            name = "metxt-dev";

            packages = haskellDevDeps ++ purescriptDeps ++ lean4Deps ++ infrastructureDeps ++ [ pkgs.buck2 ];

            PLAYWRIGHT_BROWSERS_PATH = "${pkgs.playwright-driver.browsers}";

            PKG_CONFIG_PATH = pkgs.lib.makeSearchPath "lib/pkgconfig" [
              pkgs.zeromq
              pkgs.postgresql
              pkgs.duckdb
            ];

            shellHook = ''
              echo ""
              echo "  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
              echo "                                                      // metxt // dev"
              echo "  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
              echo ""
              echo "  GHC:        $(ghc --version | head -1)"
              echo "  PureScript: $(purs --version)"
              echo "  Spago:      $(spago --version)"
              echo "  Lean4:      via elan (see lean-toolchain)"
              echo "  Buck2:      $(buck2 --version 2>/dev/null || echo 'available')"
              echo "  Dhall:      $(dhall version)"
              echo ""
              echo "  Commands:"
              echo "    cabal build all         - Build Haskell packages"
              echo "    spago build             - Build PureScript schemas"
              echo "    lake build              - Build Lean4 proofs (in lean/)"
              echo "    buck2 build //...       - Build all via Buck2"
              echo ""
            '';
          };

          # ════════════════════════════════════════════════════════════════════════
          # PACKAGES
          # ════════════════════════════════════════════════════════════════════════

          packages = {
            default = pkgs.hello; # Placeholder

            # Haskell packages built via Cabal/sensenet
            # metxt-core = ...
            # metxt-extract = ...
            # metxt-scraper = ...
            # metxt-storage = ...
          };
        };
    };
}
