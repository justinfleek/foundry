# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                           // metxt // overlays
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Nixpkgs overlays for metxt
#
# An overlay is a pure function from the world as it is to the world as it
# ought to be.
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{ inputs }:

{
  # Metxt-specific overlay
  metxt = final: prev: {
    # Haskell package overrides for metxt
    haskellPackages = prev.haskellPackages.override {
      overrides = hfinal: hprev: {
        # Add metxt Haskell packages here when created
        # metxt-core = hfinal.callCabal2nix "metxt-core" ../../haskell/metxt-core { };
      };
    };
  };
}
