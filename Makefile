.PHONY: all lib examples

all: lib examples

J=1
BITSIZE=32

COMPCERT_DIR=""
VST_DIR=""
-include CONFIGURE

clean:: Makefile.lib Makefile.examples
	$(MAKE) -f Makefile.lib clean
	$(MAKE) -f Makefile.examples clean
	rm -f *Makefile.lib* _CoqProject
	rm -f *Makefile.examples* _CoqProject.examples
	rm -f `find ./ -name ".*.aux"`
	rm -f `find ./ -name "*.glob"`
	rm -f `find ./ -name "*.vo"`


#
# CertiGraph
#

lib: Makefile.lib
	$(MAKE) -f Makefile.lib -j$(J)

Makefile.lib: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.lib

_CoqProject:
	@echo "$$_COQ_PROJECT_HEADER" > $@
	@[ -z $(VST_DIR) ] || echo "-Q $(VST_DIR) VST" >> $@
	@[ -z $(COMPCERT_DIR) ] || echo "-Q $(COMPCERT_DIR) compcert" >> $@
	@echo "" >> $@
	@find ./ext -name "*.v" >> $@
	@find ./CertiGraph -name "*.v" >> $@

define _COQ_PROJECT_HEADER
-Q CertiGraph           CertiGraph
-Q ext/coq_ext          CertiGraph.lib
-Q ext/msl_ext          CertiGraph.msl_ext
-Q ext/floyd_ext        CertiGraph.floyd_ext
-Q ext/veric_ext        CertiGraph.veric_ext
endef
export _COQ_PROJECT_HEADER



#
# Examples
#

examples: Makefile.examples
	$(MAKE) -f Makefile.examples -j$(J)

Makefile.examples: Makefile _CoqProject.examples
	coq_makefile -f _CoqProject.examples -o Makefile.examples

_CoqProject.examples: examples-certigc-stage
	@echo "$$_COQ_PROJECT_HEADER" > $@
	@[ -z $(VST_DIR) ] || echo "-Q $(VST_DIR) VST" >> $@
	@[ -z $(COMPCERT_DIR) ] || echo "-Q $(COMPCERT_DIR) compcert" >> $@
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
