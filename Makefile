COMPCERT_DIR = "../CompCert"
VST_DIR = "../VST"
-include CONFIGURE

COQC = coqc
COQDEP=coqdep -slash

DIRS = msl_ext graph heap_model_direct
INCLUDE_COMPCERT = -R $(COMPCERT_DIR) -as compcert
INCLUDE_VST = -R $(VST_DIR) -as VST
INCLUDE_RAMIFYCOQ = $(foreach d, $(DIRS), -R $(d) -as RamifyCoq.$(d)) -R "." -as RamifyCoq
COQFLAG = $(INCLUDE_RAMIFYCOQ) $(INCLUDE_VST) $(INCLUDE_COMPCERT)

MSL_EXT_FILES = \
  abs_addr.v seplog.v log_normalize.v ramify_tactics.v msl_ext.v overlapping.v alg_seplog.v overlapping_direct.v precise.v iter_sepcon.v sepalg.v

HEAP_MODEL_DIRECT_FILES = \
  SeparationAlgebra.v mapsto.v

GRAPH_FILES = \
  graph.v graph_reachable.v 

C_FILES = mark.c

C_LIGHT_FILES = mark.v

heap_model_direct/%.vo: heap_model_direct/%.v
	@echo COQC heap_model_direct/$*.v
	@$(COQC) $(COQFLAG) heap_model_direct/$*.v
msl_ext/%.vo: msl_ext/%.v
	@echo COQC msl_ext/$*.v
	@$(COQC) $(COQFLAG) msl_ext/$*.v
graph/%.vo: graph/%.v
	@echo COQC graph/$*.v
	@$(COQC) $(COQFLAG) graph/$*.v
Coqlib.vo: Coqlib.v
	@echo COQC Coqlib.v
	@$(COQC) -R "." -as RamifyCoq Coqlib.v

all: Coqlib.vo $(MSL_EXT_FILES:%.v=msl_ext/%.vo) $(GRAPH_FILES:%.v=graph/%.vo) $(HEAP_MODEL_DIRECT_FILES:%.v=heap_model_direct/%.vo)

depend:
	@$(COQDEP) $(COQFLAG) Coqlib.v $(MSL_EXT_FILES:%.v=msl_ext/%.v) $(GRAPH_FILES:%.v=graph/%.v) $(HEAP_MODEL_DIRECT_FILES:%.v=heap_model_direct/%.v) > .depend
	@$(COQDEP) $(INCLUDE_COMPCERT) $(C_LIGHT_FILES:%.v=sample_mark/%.v) >> .depend

clean:
	@rm *.vo */*.vo *.glob */*.glob

.DEFAULT_GOAL := all

include .depend
