.PHONY: all install clean

all: lib-and-examples

install: lib
	$(MAKE) -f Makefile.lib install

clean:: Makefile.lib Makefile.lib-and-examples
	$(MAKE) -f Makefile.lib clean
	$(MAKE) -f Makefile.lib-and-examples clean
	rm -f *Makefile.lib* _CoqProject.lib
	rm -f *Makefile.lib-and-examples* _CoqProject
	rm -f `find ./ -name ".*.aux"`
	rm -f `find ./ -name "*.glob"`
	rm -f `find ./ -name "*.vo"`



#
# Configurable parameters
#
# These can be set at the command line:
# `make VAR_1=VALUE_1 ... VAR_N=VALUE_N target`
# They can also be specified in the `CONFIGURE` file
#

COQC=coqc

J=1
BITSIZE=64

COQLIB=$(shell $(COQC) -where | tr -d '\r' | tr '\\' '/')
ifeq ($(BITSIZE),64)
	COMPCERT_DIR=$(COQLIB)/user-contrib/compcert
	VST_DIR=$(COQLIB)/user-contrib/VST
else ifeq ($(BITSIZE),32)
	COMPCERT_DIR=$(COQLIB)/../coq-variant/compcert32/compcert
	VST_DIR=$(COQLIB)/../coq-variant/VST32/VST
endif

-include CONFIGURE



#
# Project modules
#

define _COQ_PROJECT_HEADER
-Q CertiGraph           CertiGraph
-Q ext/coq_ext          CertiGraph.lib
-Q ext/msl_ext          CertiGraph.msl_ext
-Q ext/floyd_ext        CertiGraph.floyd_ext
-Q ext/veric_ext        CertiGraph.veric_ext
endef
export _COQ_PROJECT_HEADER

define _COQ_PROJECT_HEADER_EXAMPLES
-Q examples/append      CertiGraph.append
-Q examples/binheap     CertiGraph.binheap
-Q examples/CertiGC     CertiGraph.CertiGC
-Q examples/copy        CertiGraph.copy
-Q examples/dijkstra    CertiGraph.dijkstra
-Q examples/dispose     CertiGraph.dispose
-Q examples/kruskal     CertiGraph.kruskal
-Q examples/mark        CertiGraph.mark
-Q examples/prim        CertiGraph.prim
-Q examples/priq        CertiGraph.priq
-Q examples/summatrix   CertiGraph.summatrix
-Q examples/unionfind   CertiGraph.unionfind
endef
export _COQ_PROJECT_HEADER_EXAMPLES



#
# CertiGraph
#

.PHONY: lib
lib: Makefile.lib
	$(MAKE) -f Makefile.lib -j$(J)

Makefile.lib: Makefile _CoqProject.lib
	coq_makefile -f _CoqProject.lib -o Makefile.lib

_CoqProject.lib:
	@echo "$$_COQ_PROJECT_HEADER" > $@
	@[ -z $(VST_DIR) ] || echo "-Q $(VST_DIR) VST" >> $@
	@[ -z $(COMPCERT_DIR) ] || echo "-Q $(COMPCERT_DIR) compcert" >> $@
	@echo "" >> $@
	@find ./ext -name "*.v" >> $@
	@find ./CertiGraph -name "*.v" >> $@



#
# Everything
#

.PHONY: lib-and-examples
lib-and-examples: Makefile.lib-and-examples
	$(MAKE) -f Makefile.lib-and-examples -j$(J)

Makefile.lib-and-examples: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.lib-and-examples

_CoqProject: _CoqProject.lib examples-certigc-stage
	@cat _CoqProject.lib > $@
	@echo "" >> $@
	@echo "$$_COQ_PROJECT_HEADER_EXAMPLES" >> $@
	@echo "" >> $@
	@find ./examples -name "*.v" >> $@

.PHONY: examples-certigc-stage
examples-certigc-stage: examples/CertiGC/gc32.v examples/CertiGC/gc64.v
ifeq (,$(wildcard examples/CertiGC/gc.v))
ifeq ($(BITSIZE),64)
	cp examples/CertiGC/gc64.v examples/CertiGC/gc.v
else
	cp examples/CertiGC/gc32.v examples/CertiGC/gc.v
endif
endif
