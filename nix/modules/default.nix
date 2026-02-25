# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                            // metxt // modules
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Flake modules for metxt
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{ inputs, lib, ... }:

{
  # Export modules for use by downstream flakes
  flake.modules = {
    # NixOS module for running metxt services
    nixos.metxt =
      { config, pkgs, ... }:
      {
        # SearXNG service configuration
        # services.searx = {
        #   enable = true;
        #   settings = { ... };
        # };
      };

    # Home-manager module
    home.metxt =
      { config, pkgs, ... }:
      {
        # User-level metxt configuration
      };
  };
}
