Compilation Instructions
========================

Copy minexample.v into VST/progs

Then, while in VST/progs, run coqc to create a .vo file:
coqc -Q ../../CompCert compcert -Q . VST.progs minexample.v

If you are using the compcert internal to VST, the following will likely work:
coqc -Q ../compcert compcert -Q . VST.progs minexample.v

Please note that I created this minimal example using the extermal CompCert.

Then you can open up my verif_minexample.v file.
