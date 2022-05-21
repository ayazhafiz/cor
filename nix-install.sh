#!/bin/bash
# Eventually this should be shell.nix, but I'm having a lot of trouble getting
# opam2nix working on Darwin right now.

set -exv

exists() {
  command -v "$1" &> /dev/null
}

install() {
  nix-env -iA "$1"
}

if ! exists "ocaml"; then install "nixpkgs.ocaml-ng.ocamlPackages_4_14.ocaml"; fi
if ! exists "opam"; then
  install "nixpkgs.opam"
  opam init
fi

opam install \
  dune ocaml-lsp-server ocamlformat \
  ppx_expect ppx_inline_test \
  menhir sedlex
