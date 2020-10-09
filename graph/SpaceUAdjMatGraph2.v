Require Import VST.floyd.proofauto.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.MathUAdjMatGraph.
Require Export CertiGraph.graph.SpaceAdjMatGraph2.
Require Import CertiGraph.lib.List_ext.

Local Open Scope logic.

Section Spatial_UAdjMat_Model_2.
  (* Model 2 is for a stack-allocated graph,
     where the graph is declared on the stack
     as a single-dimension array of size "size^2". 
     Access to graph[u][v] is via graph[size*u + v].
   *)

Context {size : Z}.
Context {inf : Z}.
  
Definition graph_to_symm_mat g :=
  @graph_to_mat size g eformat.

Lemma graph_to_mat_eq:
  forall (g: AdjMatLG) i j, 0 <= i < size -> 0 <= j < size ->
    (Znth i (Znth j (graph_to_symm_mat g))) = elabel g (eformat (i,j)).
Proof.
  intros.
  symmetry. rewrite eformat_symm.
  apply elabel_Znth_graph_to_mat; lia.
Qed.

Lemma graph_to_mat_symmetric:
  forall (g: AdjMatLG) i j,
    0 <= i < size -> 0 <= j < size ->
    (Znth i (Znth j (graph_to_symm_mat g))) =
    (Znth j (Znth i (graph_to_symm_mat g))).
Proof.
  intros. repeat rewrite graph_to_mat_eq; trivial.
  f_equal. apply eformat_symm.
Qed.

Lemma graph_to_mat_inf:
  forall (g: @AdjMatGG size inf) u v,
    0 <= u < v ->
    v < size ->
    ~ evalid g (u,v) ->
    Znth v (Znth u (graph_to_symm_mat g)) =
    inf.
Proof.
  intros. unfold graph_to_symm_mat.
  rewrite <- elabel_Znth_graph_to_mat; try lia.
  rewrite eformat1.
  apply (MathAdjMatGraph.invalid_edge_weight); auto.
  simpl; lia.
Qed.

End Spatial_UAdjMat_Model_2.
