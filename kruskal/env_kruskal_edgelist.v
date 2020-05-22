Require Import VST.floyd.proofauto.
Require Import Coq.ZArith.ZArith.
Require Import RamifyCoq.floyd_ext.closed_lemmas.
Require Export RamifyCoq.kruskal.kruskal_edgelist.

Local Open Scope Z.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.

Definition MAX_EDGES:= 8.
Definition t_struct_edge := Tstruct _edge noattr.
Definition t_wedgearray_graph := Tstruct _graph noattr.