{
  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  #                                                              // metxt // nix
  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  #
  # SMART Brand Ingestion Engine
  #
  # Stack:
  #   - Lean4 4.26+    :: CIC proofs, invariants defined FIRST
  #   - Haskell GHC 9.12 :: Backend runtime, graded monads
  #   - PureScript     :: Schema layer, Hydrogen frontend
  #   - Buck2          :: Hermetic builds via aleph
  #
  # Dependencies:
  #   - ZeroMQ         :: Agent communication
  #   - SearXNG        :: Privacy-respecting web search
  #   - Playwright     :: Browser automation, skill execution
  #   - gVisor/Bubblewrap :: Container sandboxing
  #   - Hedgehog       :: Property-based testing
  #
  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  description = "METXT - SMART Brand Ingestion Engine";

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
    # ══════════════════════════════════════════════════════════════════════════
    # Core Infrastructure
    # ══════════════════════════════════════════════════════════════════════════

    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    systems.url = "github:nix-systems/default";

    # Aleph - Straylight build system (Buck2, LLVM, NVIDIA, Haskell toolchains)
    aleph.url = "github:straylight-software/aleph";

    # ══════════════════════════════════════════════════════════════════════════
    # Language Toolchains
    # ══════════════════════════════════════════════════════════════════════════

    # PureScript overlay (provides spago-unstable, purs, etc.)
    purescript-overlay.url = "github:thomashoneyman/purescript-overlay";

    # ══════════════════════════════════════════════════════════════════════════
    # Buck2 Prelude (Straylight fork with Haskell/Lean rules)
    # ══════════════════════════════════════════════════════════════════════════

    buck2-prelude = {
      url = "github:weyl-ai/straylight-buck2-prelude";
      flake = false;
    };
  };

  outputs =
    inputs@{ flake-parts, aleph, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      # ════════════════════════════════════════════════════════════════════════
      # Imports
      # ════════════════════════════════════════════════════════════════════════

      imports = [
        aleph.modules.flake.nixpkgs
        aleph.modules.flake.formatter
        aleph.modules.flake.build
      ];

      systems = import inputs.systems;

      # ════════════════════════════════════════════════════════════════════════
      # Aleph Configuration
      # ════════════════════════════════════════════════════════════════════════

      # Allow unfree packages (NVIDIA, etc.)
      aleph.nixpkgs.allow-unfree = true;
      aleph.nixpkgs.nv.enable = true;

      # Buck2 build configuration
      aleph.build = {
        enable = true;
        generate-buckconfig-main = true;

        toolchain = {
          cxx.enable = true; # LLVM C++ (required base)
          haskell.enable = true; # GHC 9.12
          lean.enable = true; # Lean4
          rust.enable = false; # Not needed for metxt
          nv.enable = false; # No CUDA needed for brand ingestion
          python.enable = true; # For ML interop
        };
      };

      # ════════════════════════════════════════════════════════════════════════
      # Per-System Configuration
      # ════════════════════════════════════════════════════════════════════════

      perSystem =
        {
          config,
          pkgs,
          system,
          ...
        }:
        let
          # ────────────────────────────────────────────────────────────────────
          # PureScript Toolchain
          # ────────────────────────────────────────────────────────────────────

          # Apply PureScript overlay
          psPkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [ inputs.purescript-overlay.overlays.default ];
          };

          # ────────────────────────────────────────────────────────────────────
          # Haskell Toolchain (GHC 9.12)
          # ────────────────────────────────────────────────────────────────────

          # Use GHC 9.10 for stability (9.12 may have dep issues)
          hpkgs = pkgs.haskell.packages.ghc910;

          # Haskell development tools
          haskellTools = [
            pkgs.cabal-install
            hpkgs.haskell-language-server
            hpkgs.ghcid
            hpkgs.hlint
            hpkgs.ormolu
            hpkgs.fourmolu
            hpkgs.hedgehog
          ];

          # ────────────────────────────────────────────────────────────────────
          # Infrastructure Dependencies
          # ────────────────────────────────────────────────────────────────────

          infrastructureDeps = [
            # Message passing / Agent communication
            pkgs.zeromq

            # Browser automation
            pkgs.playwright-driver
            pkgs.chromium

            # Sandboxing
            pkgs.bubblewrap

            # AST manipulation / Code generation
            pkgs.tree-sitter

            # Dhall configuration
            pkgs.dhall
            pkgs.dhall-json
            pkgs.dhall-lsp-server

            # Database
            pkgs.duckdb
            pkgs.postgresql

            # Utilities
            pkgs.jq
            pkgs.yq
            pkgs.ripgrep
            pkgs.fd
          ];

          # ────────────────────────────────────────────────────────────────────
          # PureScript Dependencies
          # ────────────────────────────────────────────────────────────────────

          purescriptTools = [
            psPkgs.purs
            psPkgs.spago-unstable
            psPkgs.purs-tidy
            psPkgs.purs-backend-es
            pkgs.esbuild
            pkgs.nodejs_22
          ];

          # ────────────────────────────────────────────────────────────────────
          # Lean4 Dependencies
          # ────────────────────────────────────────────────────────────────────

          lean4Tools = [
            pkgs.elan # Lean toolchain manager (reads lean-toolchain)
          ];

        in
        {
          # ══════════════════════════════════════════════════════════════════
          # Development Shell
          # ══════════════════════════════════════════════════════════════════

          devShells.default = pkgs.mkShell {
            name = "metxt-dev";

            packages =
              purescriptTools
              ++ haskellTools
              ++ lean4Tools
              ++ infrastructureDeps
              ++ config.aleph.build.packages # Buck2 toolchain packages
              ++ [
                pkgs.buck2
                pkgs.pkg-config
                pkgs.git
              ];

            # Environment variables
            PLAYWRIGHT_BROWSERS_PATH = "${pkgs.playwright-driver.browsers}";

            # pkg-config paths for native dependencies
            PKG_CONFIG_PATH = pkgs.lib.makeSearchPath "lib/pkgconfig" [
              pkgs.zeromq
              pkgs.postgresql
              pkgs.duckdb
            ];

            shellHook = ''
              ${config.aleph.build.shellHook}

              echo ""
              echo "  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
              echo "                                                    // metxt // dev"
              echo "  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
              echo ""
              echo "  PureScript: $(purs --version)"
              echo "  Spago:      $(spago --version)"
              echo "  GHC:        $(ghc --version | head -1)"
              echo "  Lean4:      via elan (see lean-toolchain)"
              echo "  Buck2:      $(buck2 --version 2>/dev/null || echo 'available')"
              echo "  Dhall:      $(dhall version)"
              echo ""
              echo "  Commands:"
              echo "    spago build     - Build PureScript schemas"
              echo "    cabal build     - Build Haskell backend"
              echo "    lake build      - Build Lean4 proofs (in lean/)"
              echo "    buck2 build     - Build via Buck2"
              echo ""
            '';
          };

          # ══════════════════════════════════════════════════════════════════
          # Specialized Shells
          # ══════════════════════════════════════════════════════════════════

          devShells.purescript = pkgs.mkShell {
            name = "metxt-purescript";
            packages = purescriptTools ++ [ pkgs.git ];

            shellHook = ''
              echo "PureScript development shell"
              echo "  purs: $(purs --version)"
              echo "  spago: $(spago --version)"
            '';
          };

          devShells.haskell = hpkgs.shellFor {
            packages = p: [ ]; # Add Haskell packages here when created
            withHoogle = true;

            nativeBuildInputs = haskellTools ++ [
              pkgs.pkg-config
              pkgs.zeromq
            ];

            buildInputs = [
              pkgs.zeromq
              pkgs.postgresql
              pkgs.duckdb
            ];

            shellHook = ''
              echo "Haskell development shell (GHC 9.10)"
              echo "  ghc: $(ghc --version)"
            '';
          };

          devShells.lean = pkgs.mkShell {
            name = "metxt-lean";
            packages = lean4Tools ++ [ pkgs.git ];

            shellHook = ''
              echo "Lean4 development shell"
              echo "  elan: $(elan --version)"
              echo "  Run 'lake build' in lean/ directory"
            '';
          };

          # ══════════════════════════════════════════════════════════════════
          # Packages
          # ══════════════════════════════════════════════════════════════════

          packages = {
            # Default package (placeholder until we have Haskell packages)
            default = pkgs.hello;

            # TODO: Add actual metxt packages here:
            # metxt-core = ...
            # metxt-extract = ...
            # metxt-scraper = ...
          };

          # ══════════════════════════════════════════════════════════════════
          # Checks
          # ══════════════════════════════════════════════════════════════════

          checks = {
            # Verify PureScript compiles
            purescript-build =
              pkgs.runCommand "purescript-build-check"
                {
                  nativeBuildInputs = purescriptTools;
                  src = inputs.self;
                }
                ''
                  cd $src
                  # spago build would go here once packages.dhall is valid
                  echo "PureScript check placeholder"
                  touch $out
                '';
          };
        };
    };
}
