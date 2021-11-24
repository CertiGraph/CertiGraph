# Certigraph demo

This directory provides a brief introduction to the use of CertiGraph,
illustrating its most basic features.  You can just read [treeread.c](treeread.c)
and [Verif_treeread.v](Verif_treeread.v), or you can build the demo
and step through [Verif_treeread.v](Verif_treeread.v) interactively.

To build the demo, first adjust the [_CoqProject](_CoqProject) to give the
correct path to the CertiGraph library.  No adjustment at all will be needed
if you have simply checked out the CertiGraph repo and already have done a `make`
in the parent directory.  Then do `make` in this subdirectory.
