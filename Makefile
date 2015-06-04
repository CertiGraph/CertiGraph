COQC = coqc
DIRS = msl_ext
COMPCERT_DIR = "/Users/Qinxiang/Documents/vst-latest/CompCert"
VST_DIR = "/Users/Qinxiang/Documents/vst-latest/VST"
INCLUDE_COMPCERT = -R $(COMPCERT_DIR) -as compcert
INCLUDE_VST = -R $(VST_DIR) -as VST
INCLUDE_RAMIFYCOQ = $(foreach d, $(DIRS), -R $(d) -as RamifyCoq.$(d))

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(INCLUDE_RAMIFYCOQ) $(INCLUDE_VST) $(INCLUDE_COMPCERT) $*.v

all: msl_ext/seplog.vo
