{
  inputs = {
    opam-nix.url = "github:tweag/opam-nix";
    opam-repository.url = "github:ocaml/opam-repository";
    opam-repository.flake = false;
    opam-coq-archive.url = "github:coq/opam-coq-archive";
    opam-coq-archive.flake = false;
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.follows = "opam-nix/nixpkgs";
  };
  outputs = { self, flake-utils, opam-nix, opam-repository, opam-coq-archive, nixpkgs }@inputs:
    let package = "destination";
    in flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        on = opam-nix.lib.${system};
        inherit (opam-nix.lib.${system}) queryToScope;
        scope = on.buildOpamProject'
          {
            repos = [ "${opam-repository}" "${opam-coq-archive}/released" ];
          }
          ./.
          {
            ocaml-base-compiler = "*";
          };
        overlay = final: prev:
          {
            # Your overrides go here
          };
        scope' = scope.overrideScope' overlay;
        main = scope'.${package};
      in {
        legacyPackages = scope';

        packages.default = main;

        devShells.default = pkgs.mkShell {
          inputsFrom = [ main ];
          buildInputs = [
            #additional packages from nixpkgs
            pkgs.eprover
            pkgs.cvc5
            pkgs.vampire
          ];
        };
      });
}
