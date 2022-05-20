let
  pkgs = (import <nixpkgs> { });
  inherit (pkgs) stdenv lib;

  coreDevel = with pkgs; [
    coreutils
    git
    gnused
  ];

  ocamlPkgs = pkgs.ocaml-ng.ocamlPackages_4_14;

  ocamlDevel = (with ocamlPkgs; [
    ocaml
    dune_3
    utop
  ]) ++ (with pkgs; [
    ocamlformat_0_20_1
  ]);

  ocamlDeps = with pkgs.ocamlPackages; [
    menhir
    ppx_expect
    ppx_inline_test
    ocaml-lsp
  ];

in pkgs.mkShell {
  buildInputs = coreDevel ++ ocamlDevel ++ ocamlDeps;
}
