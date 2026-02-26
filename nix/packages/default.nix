# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                         // foundry // packages
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Package definitions for foundry
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{ pkgs, hpkgs }:

{
  # Haskell packages (to be implemented)
  # foundry-core = hpkgs.callCabal2nix "foundry-core" ../../haskell/foundry-core { };
  # foundry-extract = hpkgs.callCabal2nix "foundry-extract" ../../haskell/foundry-extract { };
  # foundry-scraper = hpkgs.callCabal2nix "foundry-scraper" ../../haskell/foundry-scraper { };
  # foundry-storage = hpkgs.callCabal2nix "foundry-storage" ../../haskell/foundry-storage { };

  # PureScript bundle (to be implemented)
  # foundry-ui = pkgs.runCommand "foundry-ui" { ... } ''...''
}
