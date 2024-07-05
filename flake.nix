{
  inputs = {
    opam-nix.url = "github:tweag/opam-nix?rev=e807e4ff89fa43233267db5fd2269c6ab7863989";
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
            pkgs.python310
            pkgs.eprover
            pkgs.cvc4
            pkgs.vampire
            (pkgs.z3-tptp.overrideAttrs (oldAttrs : {
                installPhase = ''
                  mkdir -p "$out/bin"
                  cp "z3_tptp5" "$out/bin/"
                  ln -s "z3_tptp5" "$out/bin/z3_tptp"
                '';
            }))
            # dev utilities
            pkgs.entr
            # Latex stuff
            pkgs.ott
            pkgs.biber
            pkgs.haskellPackages.lhs2tex
            (pkgs.texlive.combine {
              inherit (pkgs.texlive)
                scheme-basic
                latexmk
                acmart
                cleveref
                xargs
                todonotes

                # acmart dependencies
                amscls
                amsfonts
                amsmath
                # supplies binhex:
                kastrup
                # supplies balance:
                preprint
                booktabs
                caption
                comment
                cm-super
                cmap
                doclicense
                draftwatermark
                environ
                etoolbox
                fancyhdr
                float
                fontaxes
                geometry
                graphics
                hyperref
                hyperxmp
                iftex
                # not listed in the documentation, but needed:
                ifmtarg
                inconsolata
                libertine
                # already supplied by ncctools: manyfoot
                microtype
                mmap
                ms
                mweights
                natbib
                ncctools
                newtx
                oberdiek
                # supplies pdftex-def:
                graphics-def
                refcount
                setspace
                textcase
                totpages
                trimspaces
                upquote
                url
                xcolor
                xkeyval
                xstring

                # for lhs2tex
                lazylist polytable

                # for ott
                supertabular
                mathpartir

                # styling for the language
                stmaryrd
                bbold
                tipa
                halloweenmath pict2e

                # for erroneuous code
                ulem

                # for aligned let
                tools

                # for tikzit figures
                tikz-cd
                ;
            })
          ];
        };
      });
}
