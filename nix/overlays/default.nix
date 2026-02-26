# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                         // foundry // overlays
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Nixpkgs overlays for foundry
#
# An overlay is a pure function from the world as it is to the world as it
# ought to be.
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{ inputs }:

{
  # Foundry-specific overlay
  foundry = final: prev: {
    # Haskell package overrides for foundry
    haskellPackages = prev.haskellPackages.override {
      overrides = hfinal: hprev: {
        # Add foundry Haskell packages here when created
        # foundry-core = hfinal.callCabal2nix "foundry-core" ../../haskell/foundry-core { };
      };
    };
  };
}
