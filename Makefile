# How to use this Makefile
# 1. If you have VST (and CompCert) installed in a Coq Platform install,
#   just "make" should work to build the CertiGraph tool.
# 2. The "-j" option should work for all variations described here
# 3. If you want to build all the application demos, "make all"
# 4. If you want to use a 32-bit VST/CompCert, BITSIZE=32
#   (either in the CONFIGURE file or as a command-line option to "make")
# 5. If you want a 64-bit VST/CompCert, BITSIZE=64 is default
# 6. By default, this Makefile will not run "clightgen" to convert
#    .c files to .v files; the clightgenned .v files are already
#    present, named */*64.v and */*32.v.
#    "make clightgen" will run clightgen locally on all application demos
#    (define CLIGHTGEN variable if your clightgen is not in the default place)
# 7. To install the pre-clightgenned files in */*64.v, "make clightgen64"
#    (define CLIGHTGEN64 if your clightgen is not in the default place)
# 8. To install the pre-clightgenned files in */*32.v, "make clightgen32"
#    (define CLIGHTGEN32 if your clightgen is not in the default place)

-include CONFIGURE

default: certigraph

CURRENT_DIR = "./"
COQC ?= $(COQBIN)coqc -w -overriding-logical-loadpath
COQDEP ?= $(COQBIN)coqdep
COQLIB ?= $(shell $(COQC) -where | tr -d '\r' | tr '\\' '/')

BITSIZE ?= 64
FLOCQ ?=

ifeq ($(BITSIZE),64)
	COQLIBINSTALL ?= $(COQLIB)/user-contrib
	COMPCERT_DIR ?= $(COQLIB)/user-contrib/compcert
	VST_DIR ?= $(COQLIB)/user-contrib/VST
	CLIGHTGEN ?= $(COQLIB)/../../bin/clightgen
	CLIGHTGEN64 ?= $(CLIGHTGEN)
	CLIGHTGEN32 ?= $(COQLIB)/../../variants/compcert32/bin/clightgen
#	TARGET_ARCH ?= x86_64-linux
else ifeq ($(BITSIZE),32)
	COQLIBINSTALL ?= $(COQLIB)/../coq-variant/CertiGraph32
	COMPCERT_DIR ?= $(COQLIB)/../coq-variant/compcert32/compcert
	VST_DIR ?= $(COQLIB)/../coq-variant/VST32/VST
	CLIGHTGEN ?= $(COQLIB)/../../variants/compcert32/bin/clightgen
	CLIGHTGEN32 ?= $(CLIGHTGEN)
	CLIGHTGEN64 ?= $(COQLIB)/../../bin/clightgen
#	TARGET_ARCH ?= x86_32-linux
endif


INSTALLDIR ?= $(COQLIBINSTALL)/CertiGraph

ifdef COMPCERT_DIR
INCLUDE_COMPCERT = -Q $(COMPCERT_DIR) compcert $(FLOCQ)
endif

ifdef VST_DIR
INCLUDE_VST = -Q $(VST_DIR) VST
endif

DIRS = lib msl_ext msl_application graph heap_model_direct
INCLUDE_CERTIGRAPH = $(foreach d, $(DIRS), -Q $(d) CertiGraph.$(d)) -Q "." CertiGraph
NORMAL_FLAG = $(INCLUDE_CERTIGRAPH) $(INCLUDE_VST) $(INCLUDE_COMPCERT)
CLIGHT_FLAG = $(INCLUDE_COMPCERT) $(INCLUDE_CERTIGRAPH)

LIB_FILES = \
  Coqlib.v Equivalence_ext.v List_Func_ext.v Ensembles_ext.v List_ext.v \
  EnumEnsembles.v Relation_ext.v relation_list.v EquivDec_ext.v Morphisms_ext.v \
  find_lemmas.v

MSL_EXT_FILES = \
  log_normalize.v iter_sepcon.v ramification_lemmas.v abs_addr.v seplog.v \
  # ramify_tactics.v msl_ext.v sepalg.v overlapping.v precise.v alg_seplog.v \
  # overlapping_direct.v precise_direct.v alg_seplog_direct.v

MSL_APPLICATION_FILES = \
  Graph.v Graph_Mark.v GraphBin.v GraphBin_Mark.v DagBin_Mark.v Graph_Copy.v \
  GraphBin_Copy.v GList.v GList_UnionFind.v ArrayGraph.v UnionFindGraph.v

VERIC_EXT_FILES = \
  res_predicates.v seplog.v SeparationLogic.v

FLOYD_EXT_FILES = closed_lemmas.v share.v
  # MapstoSL.v DataatSL.v semax_ram_lemmas.v semax_ram_tac.v exists_trick.v closed_lemmas.v ramification.v share.v

# HEAP_MODEL_DIRECT_FILES = \
#   SeparationAlgebra.v mapsto.v SeparationLogic.v

GRAPH_FILES = \
  graph_model.v path_lemmas.v graph_gen.v graph_relation.v reachable_computable.v \
  find_not_in.v reachable_ind.v subgraph2.v spanning_tree.v dag.v marked_graph.v \
  weak_mark_lemmas.v dual_graph.v graph_morphism.v local_graph_copy.v tree_model.v \
  list_model.v BinGraph.v MathGraph.v FiniteGraph.v GraphAsList.v LstGraph.v UnionFind.v \
  graph_isomorphism.v undirected_graph.v undirected_uf_lemmas.v \
  MathAdjMatGraph.v SpaceAdjMatGraph1.v SpaceAdjMatGraph2.v SpaceAdjMatGraph3.v \
  path_cost.v \
  MathUAdjMatGraph.v SpaceUAdjMatGraph1.v SpaceUAdjMatGraph2.v SpaceUAdjMatGraph3.v \
  MathEdgeLabelGraph.v SpaceEdgeLabelGraph.v
  # 1 = noncontiguous
  # 2 = contiguous 1-d
  # 3 = contiguous 2-d

DATA_STRUCTURE_FILES = \
  spatial_graph_unaligned_bin_VST.v spatial_graph_dispose_bin.v

BINARY_HEAP_FILES = \
  binary_heap_model.v binary_heap_Zmodel.v \
  binary_heap_malloc_spec.v \
  env_binary_heap.v verif_binary_heap.v \
  env_binary_heap_pro.v spec_binary_heap_pro.v verif_binary_heap_pro.v

MARK_FILES = \
  env_mark_bin.v spatial_graph_bin_mark.v verif_mark_bin.v verif_mark_bin_dag.v

SUMMATRIX_FILES = verif_summatrix.v

COPY_FILES = \
  env_copy_bin.v spatial_graph_bin_copy.v verif_copy_bin.v

DISPOSE_FILES = \
  env_dispose_bin.v verif_dispose_bin.v

UNION_FIND_FILES = \
  env_unionfind.v env_unionfind_iter.v env_unionfind_arr.v uf_arr_specs.v \
  spatial_graph_uf_iter.v spatial_graph_glist.v spatial_array_graph.v \
  verif_unionfind.v verif_unionfind_slim.v verif_unionfind_rank.v \
  verif_unionfind_iter.v verif_unionfind_iter_rank.v verif_unionfind_arr.v

HIP_FILES = \
  hip_graphmark.v hip_graphmark_proofs.v spanningtree.v

# Using "clightgen -DCOMPCERT -normalize -isystem . gc.c" to generate gc.v

CERTIGC_FILES = \
  data_at_test.v spatial_gcgraph.v verif_conversion.v verif_Is_from.v \
  gc_spec.v verif_create_space.v verif_create_heap.v verif_make_tinfo.v env_graph_gc.v verif_Is_block.v verif_garbage_collect.v verif_resume.v \
  GCGraph.v verif_forward.v verif_do_scan.v verif_forward_roots.v \
  forward_lemmas.v verif_forward1.v verif_forward2.v \
  verif_do_generation.v gc_correct.v \
  refine_bug.v

KRUSKAL_FILES = \
  WeightedEdgeListGraph.v env_kruskal_edgelist.v spatial_wedgearray_graph.v kruskal_specs.v \
  verif_sort.v verif_kruskal_edgelist.v

#kruskal_edgelist_sort.v env_kruskal_edgelist_sort.v spatial_wedgearray_graph_sort.v kruskal_specs_sort.v \


PRIM_FILES = \
  prim_env.v prim_constants.v \
  prim_spec1.v verif_prim1.v \
  prim_spec2.v verif_prim2.v \
  prim_spec3.v verif_prim3.v \
  noroot_prim_spec.v verif_noroot_prim.v

DIJKSTRA_FILES = \
  dijkstra_spec1.v verif_dijkstra1.v \
  dijkstra_spec2.v verif_dijkstra2.v \
  dijkstra_spec3.v verif_dijkstra3.v \
  MathDijkGraph.v dijkstra_env.v dijkstra_constants.v \
  dijkstra_math_proof.v dijkstra_spec_pure.v
  # 1 = noncontiguous
  # 2 = contiguous 1-d
  # 3 = contiguous 2-d

PRIQ_FILES = \
  priq_arr_specs.v is_empty_lemmas.v verif_priq_arr.v

APPEND_FILES = \
  list_dt.v verif_append.v

CLIGHT_FILES = \
  CertiGC/gc.v summatrix/summatrix.v kruskal/kruskal_edgelist.v unionfind/unionfind.v \
  unionfind/unionfind_iter.v unionfind/unionfind_arr.v append/append.v mark/mark_bin.v \
  binheap/binary_heap_pro.v binheap/binary_heap.v prim/noroot_prim.v prim/prim1.v \
  prim/prim2.v prim/prim3.v priq/priq_arr.v dispose/dispose_bin.v copy/copy_bin.v \
  dijkstra/dijkstra1.v dijkstra/dijkstra2.v dijkstra/dijkstra3.v

C_FILES = $(CLIGHT_FILES:%.v=%.c)

CG_CORE_FILES = \
  $(MSL_EXT_FILES:%.v=msl_ext/%.v) \
  $(MSL_APPLICATION_FILES:%.v=msl_application/%.v) \
  $(FLOYD_EXT_FILES:%.v=floyd_ext/%.v) \
  $(DATA_STRUCTURE_FILES:%.v=data_structure/%.v) \
  $(GRAPH_FILES:%.v=graph/%.v) \
  $(LIB_FILES:%.v=lib/%.v) \

APPLICATIONS_FILES = \
  $(BINARY_HEAP_FILES:%.v=binheap/%.v) \
  $(SAMPLE_EDGE_WEIGHT_FILES:%.v=sample_edge_weight/%.v) \
  $(KRUSKAL_FILES:%.v=kruskal/%.v) \
  $(DIJKSTRA_FILES:%.v=dijkstra/%.v) \
  $(PRIQ_FILES:%.v=priq/%.v) \
  $(APPEND_FILES:%.v=append/%.v) \
  $(PRIM_FILES:%.v=prim/%.v) \
  $(UNION_FIND_FILES:%.v=unionfind/%.v) \
  $(COPY_FILES:%.v=copy/%.v) \
  $(MARK_FILES:%.v=mark/%.v) \
  $(DISPOSE_FILES:%.v=dispose/%.v) \
  $(SUMMATRIX_FILES:%.v=summatrix/%.v)

NORMAL_FILES = $(CG_CORE_FILES) \
  $(CERTIGC_FILES:%.v=CertiGC/%.v) \
  $(APPLICATIONS_FILES)

certigraph: $(CG_CORE_FILES:%.v=%.vo)

all: certigraph certigc applications

certigc: $(CERTIGC_FILES:%.v=CertiGC/%.vo)

applications: $(APPLICATIONS_FILES:%.v=%.vo)


$(NORMAL_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)/$*.v

$(CLIGHT_FILES): %.v: %$(BITSIZE).v
	@echo CP $< $@
	@cp $< $(CURRENT_DIR)/$@

$(CLIGHT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(CLIGHT_FLAG) $(CURRENT_DIR)/$*.v

all: \
  $(NORMAL_FILES:%.v=%.vo) \
  $(CLIGHT_FILES:%.v=%.vo)

# A minimal list of files that need to built within VST for our build to work.
# Please add to this as needed.
VST_CRITICAL_FILES = \
  concurrency/conclib.v floyd/proofauto.v floyd/library.v floyd/reassoc_seq.v compcert/cfrontend/ClightBigstep.v msl/msl_direct.v msl/alg_seplog_direct.v


clightgen:
	cp CertiGC/'GC Source'/{config.h,gc.h,mem.h,values.h,gc.c} CertiGC
	$(CLIGHTGEN) -DCOMPCERT -normalize -isystem . $(C_FILES)

clightgen64:
	cp CertiGC/'GC Source'/{config.h,gc.h,mem.h,values.h,gc.c} CertiGC
	$(CLIGHTGEN64) -DCOMPCERT -normalize -isystem . $(C_FILES)
	$(foreach x,$(C_FILES:%.c=%), mv $(x).v $(x)64.v; )

clightgen32:
	cp CertiGC/'GC Source'/{config.h,gc.h,mem.h,values.h,gc.c} CertiGC
	$(CLIGHTGEN32) -DCOMPCERT -normalize -isystem . $(C_FILES)
	$(foreach x,$(C_FILES:%.c=%), mv $(x).v $(x)32.v; )


.PHONY: vstandme7
vstandme7:
	cd $(VST_DIR) && make $(VST_CRITICAL_FILES:%.v=%.vo) -j7 && cd - && make -j7

.PHONY: vstandme3
vstandme3:
	cd $(VST_DIR) && make $(VST_CRITICAL_FILES:%.v=%.vo) -j3 && cd - && make -j3

.PHONY: cav
cav:
	make binheap/verif_binary_heap.vo binheap/verif_binary_heap_pro.vo \
	prim/verif_prim1.vo prim/verif_prim2.vo prim/verif_prim3.vo prim/verif_noroot_prim.vo \
	dijkstra/verif_dijkstra1.vo dijkstra/verif_dijkstra2.vo dijkstra/verif_dijkstra3.vo \
	kruskal/verif_sort.v kruskal/verif_kruskal_edgelist.vo -kj7


.PHONY: depend
.depend depend: $(CLIGHT_FILES)
	@echo 'coqdep ... >.depend'
	@$(COQDEP) $(NORMAL_FLAG) $(NORMAL_FILES) > .depend
	@$(COQDEP) $(CLIGHT_FLAG) $(CLIGHT_FILES) >> .depend

.PHONY: clean
clean:
	@rm -f */*.vo */*.glob */.*.aux $(CLIGHT_FILES) .depend

.PHONY: coqide
coqide:
	echo >coqide "exec coqide $(NORMAL_FLAG)" $$\*
	chmod +x coqide

INSTALL_SOURCES = $(NORMAL_FILES) $(CLIGHT_FILES)
INSTALL_COMPILED = $(INSTALL_SOURCES:%.v=%.vo)

.PHONY: install
install:
	install -d "$(INSTALLDIR)"
	for d in $(sort $(dir $(INSTALL_SOURCES) $(INSTALL_COMPILED))); do install -d "$(INSTALLDIR)/$$d"; done
	for f in $(INSTALL_SOURCES) $(INSTALL_COMPILED); do install -m 0644 $$f "$(INSTALLDIR)/$$(dirname $$f)"; done

.DEFAULT_GOAL := all

-include .depend
