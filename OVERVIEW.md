# CertiGraph overview

Separation-logic tools for manipulating pointer data structures make
it easy to represent trees, lists, and other structures without sharing,
using the *separating conjunction* `*` operator.  But *graphs*, where
there is shared structure (multiple pointers to a node), are not so
simple to describe in separation logic.  **CertiGraph** is a library
written in Coq, usable in Separation Hoare Logics such as
Verifiable C (the program logic of the Verified Software Toolchain, VST).
CertiGraph is modularly structured so that it could be applied
to other separation logics embedded in Coq, but currently there is
only a VST binding.

The paper, 
[Certifying Graph-Manipulating C Programs via Localizations within Data Structures](https://dl.acm.org/doi/pdf/10.1145/3360597),
gives a detailed explanation of CertiGraph's rational and design, with
several examples of its application to verifying C programs.

The [demo](demo) subdirectory of this repository gives a tutorial
introduction to the use of CertiGraph.

The basic idea is this.  In ordinary separation logic, we describe a
tree-node as,
```
tree(p) =
   Exists left, Exists right, p |-> (left,right) * tree(left) * tree(right)
```
where the separating conjunction `*` ensures that the left and right subtrees
are disjoint.  But when representing a DAG or a cyclic graph, the left and
right will point to overlapping structures, so we can't just write `*`.

The solution is to describe an abstract graph structure--think of it as
a collection of nodes, each with an address and a contents.  Then we
can describe structural properties of this graph as a pure proposition,
using ordinary conjunction instead of separating conjunction.  Finally,
we can use separation logic to say
that the entire graph is represented as pointers in memory,
using an iterated separating conjunction of all the individual nodes.

Once that's done, we want a library to manipulate the abstract structures,
manipulate the representation relations, and provide operators for focusing
on individual nodes so that the program can traverse the graph.  That's
what CertiGraph provides.
