.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
