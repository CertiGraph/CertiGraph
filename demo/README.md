# Certigraph demo

This directory provides a brief introduction to the use of CertiGraph,
illustrating its most basic features.  You can just read [treeread.c](treeread.c)
and [verif_treeread.v](verif_treeread.v), or you can build the demo
and step through [verif_treeread.v](verif_treeread.v) interactively.

To build the demo, first adjust the [_CoqProject](_CoqProject) to give the
correct path to the CertiGraph library.  No adjustment at all will be needed
if you have simply checked out the CertiGraph repo and already have done a `make`
in the parent directory.  Then do `make` in this subdirectory.

The demo is in these parts:

1. treeread.c, verif_treeread.v
 - 1.0 Traversing a tree in separation logic
 - 1.1 Traversing a tree-in-graph using magic wand
 - 1.2 Traversing a tree-in-graph using CertiGraph

2. mark_bi.c, verif_mark_bi.v
 - Depth-first search of a graph, using CertiGraph
