COMPCERT_DIR = "../CompCert"
VST_DIR = "../VST"
CURRENT_DIR = "./"
-include CONFIGURE

COQC=$(COQBIN)coqc -w -overriding-logical-loadpath
COQDEP=$(COQBIN)coqdep

DIRS = lib msl_ext msl_application graph heap_model_direct
INCLUDE_COMPCERT = -Q $(COMPCERT_DIR) compcert
INCLUDE_VST = -Q $(VST_DIR) VST
INCLUDE_CERTIGRAPH = $(foreach d, $(DIRS), -Q $(d) CertiGraph.$(d)) -Q "." CertiGraph
NORMAL_FLAG = $(INCLUDE_CERTIGRAPH) $(INCLUDE_VST) $(INCLUDE_COMPCERT)
CLIGHT_FLAG = $(INCLUDE_COMPCERT) $(INCLUDE_CERTIGRAPH)

LIB_FILES = \
  Coqlib.v Equivalence_ext.v List_Func_ext.v Ensembles_ext.v List_ext.v \
  EnumEnsembles.v Relation_ext.v relation_list.v EquivDec_ext.v Morphisms_ext.v \
  find_lemmas.v 

MSL_EXT_FILES = \
  log_normalize.v iter_sepcon.v ramification_lemmas.v abs_addr.v seplog.v \
  ramify_tactics.v msl_ext.v sepalg.v overlapping.v precise.v alg_seplog.v \
  overlapping_direct.v precise_direct.v alg_seplog_direct.v

MSL_APPLICATION_FILES = \
  Graph.v Graph_Mark.v GraphBi.v GraphBi_Mark.v DagBi_Mark.v Graph_Copy.v \
  GraphBi_Copy.v GList.v GList_UnionFind.v ArrayGraph.v UnionFindGraph.v

VERIC_EXT_FILES = \
  res_predicates.v seplog.v SeparationLogic.v

FLOYD_EXT_FILES = closed_lemmas.v share.v
  # MapstoSL.v DataatSL.v semax_ram_lemmas.v semax_ram_tac.v exists_trick.v closed_lemmas.v ramification.v share.v

HEAP_MODEL_DIRECT_FILES = \
  SeparationAlgebra.v mapsto.v SeparationLogic.v

GRAPH_FILES = \
  graph_model.v path_lemmas.v graph_gen.v graph_relation.v reachable_computable.v \
  find_not_in.v reachable_ind.v subgraph2.v spanning_tree.v dag.v marked_graph.v \
  weak_mark_lemmas.v dual_graph.v graph_morphism.v local_graph_copy.v tree_model.v \
  list_model.v BiGraph.v MathGraph.v FiniteGraph.v GraphAsList.v LstGraph.v UnionFind.v \
  graph_isomorphism.v undirected_graph.v undirected_uf_lemmas.v \
  MathAdjMatGraph.v SpaceAdjMatGraph1.v SpaceAdjMatGraph2.v SpaceAdjMatGraph3.v \
  path_cost.v \
  MathUAdjMatGraph.v SpaceUAdjMatGraph1.v SpaceUAdjMatGraph2.v SpaceUAdjMatGraph3.v \
  MathEdgeLabelGraph.v SpaceEdgeLabelGraph.v
  # 1 = noncontiguous
  # 2 = contiguous 1-d
  # 3 = contiguous 2-d

DATA_STRUCTURE_FILES = \
  spatial_graph_unaligned_bi_VST.v spatial_graph_dispose_bi.v

BINARY_HEAP_FILES = \
  binary_heap_model.v binary_heap_Zmodel.v \
  binary_heap_malloc_spec.v \
  binary_heap.v env_binary_heap.v verif_binary_heap.v \
  binary_heap_pro.v env_binary_heap_pro.v spec_binary_heap_pro.v verif_binary_heap_pro.v

MARK_FILES = \
  env_mark_bi.v spatial_graph_bi_mark.v verif_mark_bi.v verif_mark_bi_dag.v 

SUMMATRIX_FILES = \
  verif_summatrix.v 

COPY_FILES = \
  env_copy_bi.v spatial_graph_bi_copy.v verif_copy_bi.v  

DISPOSE_FILES = \
  env_dispose_bi.v verif_dispose_bi.v

UNION_FIND_FILES = \
  unionfind.v env_unionfind.v \
  unionfind_iter.v env_unionfind_iter.v \
  unionfind_arr.v env_unionfind_arr.v uf_arr_specs.v \
  spatial_graph_uf_iter.v spatial_graph_glist.v spatial_array_graph.v \
  verif_unionfind.v verif_unionfind_slim.v verif_unionfind_rank.v \
  verif_unionfind_iter.v verif_unionfind_iter_rank.v verif_unionfind_arr.v

HIP_FILES = \
  hip_graphmark.v hip_graphmark_proofs.v spanningtree.v

# Using "clightgen -DCOMPCERT -normalize -isystem . gc.c" to generate gc.v

CERTIGC_FILES = \
  gc.v data_at_test.v spatial_gcgraph.v verif_conversion.v verif_Is_from.v \
  gc_spec.v verif_create_space.v verif_create_heap.v verif_make_tinfo.v env_graph_gc.v verif_Is_block.v verif_garbage_collect.v verif_resume.v \
  GCGraph.v verif_forward.v verif_do_scan.v verif_forward_roots.v verif_do_generation.v gc_correct.v

KRUSKAL_FILES = \
  WeightedEdgeListGraph.v \
  kruskal_edgelist.v env_kruskal_edgelist.v spatial_wedgearray_graph.v kruskal_specs.v \
  verif_sort.v verif_kruskal_edgelist.v

#kruskal_edgelist_sort.v env_kruskal_edgelist_sort.v spatial_wedgearray_graph_sort.v kruskal_specs_sort.v \


PRIM_FILES = \
  prim_env.v prim_constants.v \
  prim1.v prim_spec1.v verif_prim1.v \
  prim2.v prim_spec2.v verif_prim2.v \
  prim3.v prim_spec3.v verif_prim3.v \
  noroot_prim.v noroot_prim_spec.v verif_noroot_prim.v 

DIJKSTRA_FILES = \
  dijkstra1.v dijkstra_spec1.v verif_dijkstra1.v \
  dijkstra2.v dijkstra_spec2.v verif_dijkstra2.v \
  dijkstra3.v dijkstra_spec3.v verif_dijkstra3.v \
  MathDijkGraph.v dijkstra_env.v dijkstra_constants.v \
  dijkstra_math_proof.v dijkstra_spec_pure.v 
  # 1 = noncontiguous
  # 2 = contiguous 1-d
  # 3 = contiguous 2-d

PRIQ_FILES = \
  priq_arr.v priq_arr_specs.v is_empty_lemmas.v verif_priq_arr.v 

APPEND_FILES = \
  append.v list_dt.v verif_append.v 

CLIGHT_FILES = mark/mark_bi.v dispose/dispose_bi.v copy/copy_bi.v summatrix/summatrix.v

C_FILES = $(CLIGHT_FILES:%.v=%.c)

NORMAL_FILES = \
  $(MSL_EXT_FILES:%.v=msl_ext/%.v) \
  $(MSL_APPLICATION_FILES:%.v=msl_application/%.v) \
  $(FLOYD_EXT_FILES:%.v=floyd_ext/%.v) \
  $(DATA_STRUCTURE_FILES:%.v=data_structure/%.v) \
  $(BINARY_HEAP_FILES:%.v=binheap/%.v) \
  $(SAMPLE_EDGE_WEIGHT_FILES:%.v=sample_edge_weight/%.v) \
  $(GRAPH_FILES:%.v=graph/%.v) \
  $(LIB_FILES:%.v=lib/%.v) \
  $(HEAP_MODEL_DIRECT_FILES:%.v=heap_model_direct/%.v) \
  $(CERTIGC_FILES:%.v=CertiGC/%.v) \
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


$(NORMAL_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)/$*.v

$(CLIGHT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(CLIGHT_FLAG) $(CURRENT_DIR)/$*.v

all: \
  $(NORMAL_FILES:%.v=%.vo) \
  $(CLIGHT_FILES:%.v=%.vo)

# A minimal list of files that need to built within VST for our build to work.
# Please add to this as needed.
VST_CRITICAL_FILES = \
  floyd/proofauto.v floyd/reassoc_seq.v compcert/cfrontend/ClightBigstep.v msl/msl_direct.v msl/alg_seplog_direct.v

# clightgen:
#	../CompCert/clightgen -DCOMPCERT -normalize -isystem . priq/priq_arr.c prim/prim1.c prim/prim2.c prim/prim3.c prim/noroot_prim3.c dijkstra/dijkstra1.c dijkstra/dijkstra2.c dijkstra/dijkstra3.c
#	../CompCert/clightgen -DCOMPCERT -normalize -isystem . unionfind/unionfind_arr.c kruskal/kruskal_edgelist.c 

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

.depend depend:
	@echo 'coqdep ... >.depend'
	@$(COQDEP) $(NORMAL_FLAG) $(NORMAL_FILES) > .depend
	@$(COQDEP) $(CLIGHT_FLAG) $(CLIGHT_FILES) >> .depend

clean:
	@rm */*.vo */*.glob */.*.aux .depend

.DEFAULT_GOAL := all

include .depend 
