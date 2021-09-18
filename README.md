# SETTING UP YOUR ENVIRONMENT

1. Download and Unpack
	1. Clone VST
	1. Clone CertiGraph
	1. Things will be a tiny bit easier if these are in sibling directories named VST and CertiGraph. This is not critical, and the only edits will come in step 3.1.

1. Build VST
In VST/
	1. `make clean`
	1. `make -jn`, where `n` is the number of cores you want to dedicate

1. Build CertiGraph
In CertiGraph/
	1. We supply a file `CONFIGURE` in your CertiGraph folder with these two lines in it:
	> COMPCERT_DIR=../VST/compcert
	> VST_DIR=../VST 
	Where we assume that CertiGraph/ and VST/ are sibling directories with those names. If this is not the case, change these as needed to reflect the actual path to VST.
	1. `make clean`
	1. `make -jn`, where `n` is the number of cores you want to dedicate

1. Developing Inside CertiGraph (requires that you have clightgen)
	1. Write your `newfile.c` inside CertiGraph.
	1. `{path_to_clightgen}/clightgen -DCOMPCERT -normalize -isystem . newfile.c`
	1. Open CertiGraph/Makefile and add `newfile.v` to the list of sources
	1. In CertiGraph/, `make depend` (this is for every time you edit the makefile)
	1. In CertiGraph/, `make path_to_newfile/newfile.vo` (note the .vo)
	1. Create the file `verif_newfile.v`. Now something like `Require Import CertiGraph.path.to.newfile.` will go through inside `verif_newfile.v`.