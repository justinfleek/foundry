# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                          // foundry // modules
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Flake modules for foundry
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{ inputs, lib, ... }:

{
  # Export modules for use by downstream flakes
  flake.modules = {
    # NixOS module for running foundry services
    nixos.foundry =
      { config, pkgs, ... }:
      {
        # SearXNG service configuration
        # services.searx = {
        #   enable = true;
        #   settings = { ... };
        # };
      };

    # Home-manager module
    home.foundry =
      { config, pkgs, ... }:
      {
        # User-level foundry configuration
      };
  };
}
