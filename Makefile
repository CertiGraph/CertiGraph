# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject
GENERATED_VFILES := CertiGC/gc_stack.v summatrix/summatrix.v \
	kruskal/kruskal_edgelist.v unionfind/unionfind.v \
	unionfind/unionfind_iter.v unionfind/unionfind_arr.v append/append.v \
	mark/mark_bin.v binheap/binary_heap_pro.v binheap/binary_heap.v \
	prim/noroot_prim.v prim/prim1.v prim/prim2.v prim/prim3.v \
	priq/priq_arr.v dispose/dispose_bin.v copy/copy_bin.v \
	dijkstra/dijkstra1.v dijkstra/dijkstra2.v dijkstra/dijkstra3.v

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
ifneq (clean,$(MAKECMDGOALS))
	$(MAKE) -f CoqMakefile generated_files
	$(MAKE) postprocess-generated-files
endif
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

postprocess-generated-files:
	@for f in $(GENERATED_VFILES); do \
		if [ -f "$$f" ]; then \
			perl -pi -e 's/^From Coq Require /From Stdlib Require /' "$$f"; \
		fi; \
	done

.PHONY: postprocess-generated-files

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
