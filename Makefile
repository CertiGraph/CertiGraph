# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
KNOWNFILES   := Makefile _CoqProject

$(KNOWNFILES): ;

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
ifneq (clean,$(MAKECMDGOALS))
	$(MAKE) -f CoqMakefile generated_files
endif
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
