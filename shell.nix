{ sources ? import ./nix/sources.nix # See: https://github.com/nmattia/niv and https://nix.dev/tutorials/towards-reproducibility-pinning-nixpkgs.html#dependency-management-with-niv
, pkgs ? import sources.nixpkgs {}   # Use the pinned sources.
}:

pkgs.mkShell
  { buildInputs = with pkgs; [
      niv
      ott
      biber
      haskellPackages.lhs2tex
      entr
      (texlive.combine {
        inherit (texlive)
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
}
