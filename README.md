# cor

cor of roc

This project hosts tiny subsets of Roc as standalone languages. My goal is that
this will provide a convinient testbed for experimenting with new language and
compiler features.

## Experiments to try

- [ ] [Unspecialized lambda set variables](https://www.notion.so/rwx/Non-linear-monomorphization-0b26991a028949a285ca77a8ffcff3c5#1930c4eadf08465f9c7b96469f11f664) ([./experiments/uls](./experiments/uls))
- [ ] Only open tag unions in output positions
- [ ] Can -> x86 lowering

## Organization

`roc` contains the core of the language (haha i'm so good). What that core
consists of and doesn't consist of is enumerated below.

My goal is you can just copy `roc` into a folder under `experiments`, named
to represent your experiment, say `e1`. You'll need to update `cor` and dune's
build files to recognize `e1` and correctly implement a few functors. Afterwards,
running `cor e1 ...` will run the compiler in `e1`. Ideally you can prune
everything that's not needed for your experiment from the forked mini-compiler.

### `roc`

#### What's included

- Shapes
  - modules (no import/export mechanism, everything is globally visible)
  - let-bindings
  - closures
  - function application
  - tag application
  - records (TODO)
  - ints
- Types
  - arrows (function types)
  - lambda sets
  - tag unions
  - recursive tag unions (TODO)
  - polymorphic records (TODO)
  - aliases, opaques
  - abilities (TODO)
  - int
- Code gen
  - Monomorphization
  - Evaluation (TODO)
  - Refcounting (TODO)
  - x86 gen (TODO)
- Platform/Host
  - Nothing yet

#### What's not

A lot.

- Shapes
  - import/export
  - infix operators
  - stdlib
  - most sugar

- None of platform/host

- Types
  - Ranged numbers. These are a trick we use in Roc to constrain the types a
    number literal can be instantiated as. But it's not relevant to the core.

- No error reporting

### Installation

If you have nix, run `./nix-install.sh` to get started. It's not a nix shell
because I can't get opam2nix to work on Darwin, and so you will have a opam
installation with local state in your home directory.
Otherwise, install

- OCaml; nix is using OCaml 4.14 (`ocamlc --version`)
- dune >=3.2
- ocamlformat, ocaml-lsp, utop, other development tools you may want

Then run `dune build` and follow the hints to install needed packages from opam.

### Development

There are two options:
1. Build and install the `cor` binary to your system. This is `dune build; dune
   install`. The installation can be tested with `cor --help`. Note that on all
   changes, you will need to re-run `dune build; dune install`.
2. On changes, run `dune exec ./cor.exe -- <program arguments>` to rebuild
   and run `cor`.

The behavior of `cor` is detailed in `cor --help` (resp. `dune exec
./cor.exe -- --help`). In short:

```
dune exec ./cor.exe -- \
  [roc] +[parse|solve] -[print|elab] (input_file)?
#                                    ^^^^^^^^^^^^ if elided, reads from stdin
#                       ^^^^^^^^^^^^ emit strategy
#        ^^^^^^^^^^^^^ target compiler phase
# ^^^^^ target language

# Examples:

dune exec ./cor.exe -- roc +parse -print
\x -> x<EOF>
\x -> x
```

#### Tips

Some general tips I've found useful:

- ocaml-lsp uses Merlin, which only works with mli metadata built by the
    compiler. So for an interactive experience, run `dune build --watch` in the
    background.
