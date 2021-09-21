.PHONY: all coq

all: coq


COMPCERT_DIR=""
VST_DIR=""
-include CONFIGURE

define _COQ_PROJECT_HEADER
-Q CertiGraph CertiGraph
-Q ext/coq_ext CertiGraph.lib
-Q ext/msl_ext CertiGraph.msl_ext
-Q ext/floyd_ext CertiGraph.floyd_ext
-Q ext/veric_ext CertiGraph.veric_ext
endef
export _COQ_PROJECT_HEADER

_CoqProject:
	@echo "$$_COQ_PROJECT_HEADER" > $@
	@[ -z $(VST_DIR) ] || echo "-Q $(VST_DIR) VST" >> $@
	@[ -z $(COMPCERT_DIR) ] || echo "-Q $(COMPCERT_DIR) compcert" >> $@
	@find ./ext -name "*.v" >> $@
	@find ./CertiGraph -name "*.v" >> $@

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f *Makefile.coq* _CoqProject
	rm -f `find ./ -name ".*.aux"`
	rm -f `find ./ -name "*.glob"`
	rm -f `find ./ -name "*.vo"`
