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

The paper
"[Certifying Graph-Manipulating C Programs via Localizations within Data Structures](https://dl.acm.org/doi/pdf/10.1145/3360597)"
gives a detailed explanation of CertiGraph's rationale and design, with
several examples of its application to verifying C programs.  Then, 
"[Functional Correctness of C Implementations of Dijkstra's, Kruskal's, and Prim's Algorithms](https://doi.org/10.1007/978-3-030-81688-9_37)" describes features of CertiGraph for edge labels, spatial representations for edge-labeled graphs, and undirected graphs.


The [demo](demo) subdirectory of this repository gives a tutorial
introduction to the use of CertiGraph.

## Representing and traversing graphs in Separation Logic
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

## Functional models of graphs

Choose whatever type you like for Vertex and for Edge (as long as they have decidable equality functions).
Then you can make a graph, of type `PreGraph`, in which you say: which vertices are valid, which edges are valid,
(i.e., which subset of the values of type Vertex and Edge are actually in your graph), 
and how to extract the source and destination vertices out of an edge.
```
Record PreGraph (Vertex Edge : Type)
                (EV : EquivDec.EqDec Vertex eq) (EE : EquivDec.EqDec Edge eq)
  : Type := Build_PreGraph
  { vvalid : Ensembles.Ensemble Vertex;
    evalid : Ensembles.Ensemble Edge;
    src : Edge -> Vertex;
    dst : Edge -> Vertex }
```
Then, a `LabeledGraph` is a record containing a PreGraph with additional functions to extract 
the vertex-label from a vertex, the edge-label from an edge, and the graph-label from a graph.

CertiGraph provides operators operators lemmas for traversing and modifying graphs.  With these you can prove the correctness of functional models of graph algorithms, such as shortest-path, union-find, garbage collection, and so on.  

CertiGraph also provides operators and lemmas for representing labeled graphs in the memory of an imperative program:  adjacency matrices (in several flavors), adjacency lists, and so on.  With those you can prove that your C program correctly implements  the functional model.
