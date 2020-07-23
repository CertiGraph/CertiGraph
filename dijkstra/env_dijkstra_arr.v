Require Export VST.floyd.proofauto.
Require Export CertiGraph.floyd_ext.closed_lemmas.
Require Export CertiGraph.dijkstra.dijkstra.

(* grabbed from verif and put here *)
Require Export VST.msl.iter_sepcon.
Require Export CertiGraph.lib.List_ext.
Require Export CertiGraph.graph.graph_model.
Require Export CertiGraph.graph.path_lemmas.
Require Export CertiGraph.graph.AdjMatGraph.
Require Export CertiGraph.floyd_ext.share.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Global Existing Instance CompSpecs.
  
Definition vertex_type := tint.
