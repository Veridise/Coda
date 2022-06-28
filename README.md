# circom-coq

## Requirements
- opam
- Coq v8.15.0
- [coq-bignums](https://github.com/coq-community/bignums) (no need to install if you have Coq Platform)
- [coq-rewriter](https://github.com/mit-plv/rewriter)
  
## How to set up for development
```bash
git submodule update --init --recursive
make install-coqprime
make install-fiat-crypto
make
```

- To add a new source file:
  - add the file name to `_Coqproject`
  - run `coq_makefile -f _CoqProject  -o Makefile.coq`

- If you need any file from [fiat-crypto](https://github.com/mit-plv/fiat-crypto/):
  - remove comments for the desired file and its transitive dependencies in `fiat-crypto/_Coqproject`
  - `coq_makefile -f _CoqProject -o Makefile` in `fiat-crypto`
  - rerun `make install-fiat-crypto` in project root directory

- You might need to add the installation directory to the `COQPATH` environment variable.

- To set up Coq environment:
  ```bash
  opam update
  opam pin add coq 8.15.0
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam install coq-bignums
  opam install coq-rewriter
  ```