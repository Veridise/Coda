all:
	dune fmt
	dune build

test-codegen:
	dune exec ./test/test_codegen.exe

Makefile:
	@echo make $@

%:	force
	dune $@

.PHONY: all force
