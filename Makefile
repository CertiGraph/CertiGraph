COMPCERT_DIR = "../CompCert"
VST_DIR = "../VST"
-include CONFIGURE

COQC = coqc
DIRS = msl_ext
INCLUDE_COMPCERT = -R $(COMPCERT_DIR) -as compcert
INCLUDE_VST = -R $(VST_DIR) -as VST
INCLUDE_RAMIFYCOQ = $(foreach d, $(DIRS), -R $(d) -as RamifyCoq.$(d)) -R "." -as RamifyCoq

msl_ext/%.vo: msl_ext/%.v
	@echo COQC msl_ext/$*.v
	@$(COQC) $(INCLUDE_RAMIFYCOQ) $(INCLUDE_VST) $(INCLUDE_COMPCERT) msl_ext/$*.v
Coqlib.vo: Coqlib.v
	@echo COQC Coqlib.v
	@$(COQC) -R "." -as RamifyCoq Coqlib.v

all: Coqlib.vo msl_ext/seplog.vo msl_ext/log_normalize.vo msl_ext/ramify_tactics.vo msl_ext/msl_ext.vo
