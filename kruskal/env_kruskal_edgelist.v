Require Export VST.floyd.proofauto.
Require Export Coq.ZArith.ZArith.
Require Export RamifyCoq.floyd_ext.closed_lemmas.
Require Export RamifyCoq.kruskal.kruskal_edgelist.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Global Existing Instance CompSpecs.

Local Open Scope Z.

Definition SIZE:= 8.
Definition t_struct_edge := Tstruct _edge noattr.
Definition t_wedgearray_graph := Tstruct _graph noattr.