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

dev:
	cat src/ConfigDev.v > src/Config.v
	$(MAKE) --no-print-directory

audit:
	cat src/ConfigAudit.v > src/Config.v
	$(MAKE) --no-print-directory

-include Makefile.coq