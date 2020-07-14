Require Export VST.floyd.proofauto.
Require Export RamifyCoq.floyd_ext.closed_lemmas.
Require Export RamifyCoq.dijkstra.dijkstra.

(* grabbed from verif and put here *)
Require Export VST.msl.iter_sepcon.
Require Export RamifyCoq.lib.List_ext.
Require Export RamifyCoq.graph.graph_model.
Require Export RamifyCoq.graph.path_lemmas.
Require Export RamifyCoq.floyd_ext.share.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Global Existing Instance CompSpecs.
  
Definition vertex_type := tint.
