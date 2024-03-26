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
          # These are the Coq dependencies. The whole `main` stuff is
          # a little silly. It's because there's a corresponding .opam
          # file. It's a little easier this way.
          inputsFrom = [ main ];
          buildInputs = [
            # Theorem provers for CoqHammer and SMTCoq.
            pkgs.eprover
            pkgs.cvc4
            pkgs.vampire
            # dev utilities
            pkgs.entr
            # Latex stuff
            pkgs.ott
            pkgs.biber
            pkgs.haskellPackages.lhs2tex
            (pkgs.texlive.combine {
              inherit (pkgs.texlive)
                scheme-small
                cleveref
                latexmk
                biblatex biblatex-software
                stmaryrd
                unicode-math lm lm-math
                logreq xstring
                xargs todonotes
                mathpartir
                bbold
                halloweenmath
                pict2e
                # newunicodechar

                # for lhs2tex
                lazylist polytable

                # for ott
                supertabular

                # acmart and dependencies
                # acmart totpages trimspaces
                # libertine environ hyperxmp
                # ifmtarg comment ncctools
                # inconsolata newtx txfonts
                # xpatch xurl
                ;
            })

          ];
        };
      });
}
