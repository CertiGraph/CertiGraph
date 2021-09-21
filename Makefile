.PHONY: all coq

all: coq

J=1
COMPCERT_DIR=""
VST_DIR=""
-include CONFIGURE

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

_CoqProject:
	@echo "$$_COQ_PROJECT_HEADER" > $@
	@[ -z $(VST_DIR) ] || echo "-Q $(VST_DIR) VST" >> $@
	@[ -z $(COMPCERT_DIR) ] || echo "-Q $(COMPCERT_DIR) compcert" >> $@
	@echo "" >> $@
	@find ./ext -name "*.v" >> $@
	@find ./CertiGraph -name "*.v" >> $@
	@echo "" >> $@
	@[ -z $(BUILD_CERTIGRAPH_EXAMPLES) ] || echo "$$_COQ_PROJECT_HEADER_EXAMPLES" >> $@
	@[ -z $(BUILD_CERTIGRAPH_EXAMPLES) ] || find ./examples -name "*.v" >> $@

coq: Makefile.coq
	$(MAKE) -f Makefile.coq -j$(J)

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f *Makefile.coq* _CoqProject
	rm -f `find ./ -name ".*.aux"`
	rm -f `find ./ -name "*.glob"`
	rm -f `find ./ -name "*.vo"`
