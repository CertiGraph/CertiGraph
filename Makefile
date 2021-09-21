.PHONY: all coq

all: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f *Makefile.coq*
	rm -f `find ./ -name ".*.aux"`
	rm -f `find ./ -name "*.glob"`
	rm -f `find ./ -name "*.vo"`
