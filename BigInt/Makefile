FIAT_CRYPTO_FOLDER := fiat-crypto
COQPRIME_FOLDER := coqprime

%: Makefile.coq

.PHONY: fiat-crypto coqprime

fiat-crypto:
	$(MAKE) --no-print-directory -C $(FIAT_CRYPTO_FOLDER)

install-fiat-crypto: fiat-crypto
	$(MAKE) --no-print-directory -C $(FIAT_CRYPTO_FOLDER) install

coqprime:
	$(MAKE) --no-print-directory -C $(COQPRIME_FOLDER)

install-coqprime: coqprime
	$(MAKE) --no-print-directory -C $(COQPRIME_FOLDER) install

coqmake:
	coq_makefile -f _CoqProject -o Makefile.coq

dev: coqmake
	cat src/.ConfigDev > src/Config.v
	$(MAKE) --no-print-directory

audit: coqmake
	cat src/.ConfigAudit > src/Config.v
	$(MAKE) --no-print-directory

-include Makefile.coq