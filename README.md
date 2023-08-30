# Coda

Certified Circom circuits in Coq.

## Requirements

- [`opam`](https://opam.ocaml.org/)
- [Coq Platform 2022.04.1](https://github.com/coq/platform/releases/tag/2022.04.1).
- [`coq-rewriter`](https://github.com/mit-plv/rewriter)
  
## Setup

Install [`OPAM`](https://opam.ocaml.org/).

To setup OPAM, create this new switch and install these dependencies.
```
opam switch 4.13.1+options
opam install base core fmt ppx_deriving ocamlformat
```

To build the Coq project, it's reccomended to install [Coq Platform 2022.04.1](https://github.com/coq/platform/releases/tag/2022.04.1).

Install [coq-rewriter](https://github.com/mit-plv/rewriter).
```
git clone
git submodule update --init --recursive
make
make install
```

If you didn't install Coq-Platform, you may need to install `coqprime` via OPAM.
```
opam install coqprime
```

Generate the `Makefile.coq` for `BigInt`:
```
cd BigInt && coq_makefile -f _CoqProject *.v -o Makefile.coq
```

Build and install `fiat-crypto`:
```
make fiat-crypto
make install-fiat-crypto
```

Build `BigInt`:
```
cd BigInt && make
```

## Development tips

For auditing purposes, you can use the command 'make audit' to disable warnings.

For development, you can use the command 'make dev' to compile the library.

- Before starting working on a new source file, please add the file path to `_Coqproject`

- If you need any other file from [fiat-crypto](https://github.com/mit-plv/fiat-crypto/) that's absent in this repo:
  - remove comment lines for the desired file and its transitive dependencies in `fiat-crypto/_Coqproject`
  - rerun `make install-fiat-crypto` in project root directory

- You might need to add the installation directory to the `COQPATH` environment variable.

## Coda DSL

See `DSL.md`