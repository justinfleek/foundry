# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                           // metxt // packages
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Package definitions for metxt
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{ pkgs, hpkgs }:

{
  # Haskell packages (to be implemented)
  # metxt-core = hpkgs.callCabal2nix "metxt-core" ../../haskell/metxt-core { };
  # metxt-extract = hpkgs.callCabal2nix "metxt-extract" ../../haskell/metxt-extract { };
  # metxt-scraper = hpkgs.callCabal2nix "metxt-scraper" ../../haskell/metxt-scraper { };
  # metxt-storage = hpkgs.callCabal2nix "metxt-storage" ../../haskell/metxt-storage { };

  # PureScript bundle (to be implemented)
  # metxt-ui = pkgs.runCommand "metxt-ui" { ... } ''...''
}
