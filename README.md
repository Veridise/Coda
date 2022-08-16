# circom-coq

Formally verified circom circuits with machine-checked proofs, in Coq.

## Requirements
- [`opam`](https://opam.ocaml.org/)
- [Coq Platform 2022.04.1](https://github.com/coq/platform/releases/tag/2022.04.1).
- [`coq-rewriter`](https://github.com/mit-plv/rewriter)
  
## How to set up for development

```bash
make install-fiat-crypto
make
```

- Before starting working on a new source file, please add the file path to `_Coqproject`

- If you need any other file from [fiat-crypto](https://github.com/mit-plv/fiat-crypto/) that's absent in this repo:
  - remove comment lines for the desired file and its transitive dependencies in `fiat-crypto/_Coqproject`
  - rerun `make install-fiat-crypto` in project root directory

- You might need to add the installation directory to the `COQPATH` environment variable.