{ sources ? import ./nix/sources.nix # See: https://github.com/nmattia/niv and https://nix.dev/tutorials/towards-reproducibility-pinning-nixpkgs.html#dependency-management-with-niv
, pkgs ? import sources.nixpkgs {}   # Use the pinned sources.
}:

pkgs.mkShell
  { buildInputs = with pkgs; [
      niv
      ott
      biber
      (texlive.combine {
        inherit (texlive)
          # basic toolbox
          scheme-small
          latexmk
          biblatex
          unicode-math
          lm
          lm-math
          preprint xcolor
          bussproofs
          supertabular
          geometry
          ulem
          mathtools
          abraces
          times
          rsfs
          enumitem
          stmaryrd
          tipa
          bbold
          # mathptmx
          # minted
          # minted fvextra catchfile xstring kvoptions fancyvrb
          # upquote float ifplatform pdftexcmds etoolbox
          # xcolor lineno framed
          ;
      })

      ];
}
