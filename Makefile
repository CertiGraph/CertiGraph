COMPCERT_DIR = "../CompCert"
VST_DIR = "../VST"
-include CONFIGURE

COQC = coqc
COQDEP=coqdep -slash

DIRS = msl_ext
INCLUDE_COMPCERT = -R $(COMPCERT_DIR) -as compcert
INCLUDE_VST = -R $(VST_DIR) -as VST
INCLUDE_RAMIFYCOQ = $(foreach d, $(DIRS), -R $(d) -as RamifyCoq.$(d)) -R "." -as RamifyCoq
COQFLAG = $(INCLUDE_RAMIFYCOQ) $(INCLUDE_VST) $(INCLUDE_COMPCERT)

msl_ext/%.vo: msl_ext/%.v
	@echo COQC msl_ext/$*.v
	@$(COQC) $(COQFLAG) msl_ext/$*.v
graph/%.vo: graph/%.v
	@echo COQC graph/$*.v
	@$(COQC) $(COQFLAG) graph/$*.v
Coqlib.vo: Coqlib.v
	@echo COQC Coqlib.v
	@$(COQC) -R "." -as RamifyCoq Coqlib.v

all: Coqlib.vo msl_ext/abs_addr.vo msl_ext/seplog.vo msl_ext/log_normalize.vo msl_ext/ramify_tactics.vo msl_ext/msl_ext.vo msl_ext/overlapping.vo msl_ext/alg_seplog.vo graph/graph.vo graph/graph_reachable.vo msl_ext/heap_model_direct.vo msl_ext/mapsto_direct.vo msl_ext/overlapping_direct.vo msl_ext/precise.vo msl_ext/iter_sepcon.vo

depend:	
	@$(COQDEP) $(COQFLAG) Coqlib.v */*.v > .depend

clean:
	@rm *.vo */*.vo *.glob */*.glob

.DEFAULT_GOAL := all

include .depend
