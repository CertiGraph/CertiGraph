COMPCERT_DIR = "../CompCert"
VST_DIR = "../VST"
-include CONFIGURE

COQC = coqc
COQDEP=coqdep -slash

DIRS = msl_ext graph heap_model_direct
INCLUDE_COMPCERT = -R $(COMPCERT_DIR) -as compcert
INCLUDE_VST = -R $(VST_DIR) -as VST
INCLUDE_RAMIFYCOQ = $(foreach d, $(DIRS), -R $(d) -as RamifyCoq.$(d)) -R "." -as RamifyCoq
COQ_BASED_FLAG = $(INCLUDE_RAMIFYCOQ)
CLIGHT_FLAG = $(INCLUDE_COMPCERT) $(INCLUDE_RAMIFYCOQ)
VST_BASED_FLAG = $(INCLUDE_COMPCERT) $(INCLUDE_VST) $(INCLUDE_RAMIFYCOQ)

MSL_EXT_FILES = \
  abs_addr.v seplog.v log_normalize.v ramify_tactics.v msl_ext.v iter_sepcon.v \
  sepalg.v \
  overlapping.v precise.v alg_seplog.v \
  overlapping_direct.v precise_direct.v alg_seplog_direct.v

VERIC_EXT_FILES = SeparationLogic.v

HEAP_MODEL_DIRECT_FILES = \
  SeparationAlgebra.v mapsto.v SeparationLogic.v

GRAPH_FILES = \
  graph.v graph_reachable.v 

COQ_BASED_FILES = \
  Coqlib.v \
  $(GRAPH_FILES:%.v=graph/%.v)

CLIGHT_FILES = sample_mark/mark.v

C_FILES = $(CLIGHT_FILES:%.v=%.c)

VST_BASED_FILES = \
  $(MSL_EXT_FILES:%.v=msl_ext/%.v) \
  $(VERIC_EXT_FILES:%.v=veric_ext/%.v) \
  $(HEAP_MODEL_DIRECT_FILES:%.v=heap_model_direct/%.v)

$(COQ_BASED_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_BASED_FLAG) $*.v

$(CLIGHT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(CLIGHT_FLAG) $*.v

$(VST_BASED_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(VST_BASED_FLAG) $*.v

all: \
  $(COQ_BASED_FILES:%.v=%.vo) \
  $(CLIGHT_FILES:%.v=%.vo) \
  $(VST_BASED_FILES:%.v=%.vo)

depend:
	@$(COQDEP) $(COQ_BASED_FLAG) $(COQ_BASED_FILES) > .depend
	@$(COQDEP) $(CLIGHT_FLAG) $(CLIGHT_FILES) >> .depend
	@$(COQDEP) $(VST_BASED_FLAG) $(VST_BASED_FILES) >> .depend

clean:
	@rm *.vo */*.vo *.glob */*.glob

.DEFAULT_GOAL := all

include .depend
