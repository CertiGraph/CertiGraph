Require Import VST.floyd.proofauto.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.undirected_graph.
Require Export CertiGraph.graph.SpaceAdjMatGraph3.
Require Import CertiGraph.prim.MatrixUGraph.
Require Import CertiGraph.priq.priq_arr_utils.
Require Import CertiGraph.lib.List_ext.

Local Open Scope logic.

Definition graph_to_symm_mat g :=
  @graph_to_mat SIZE g eformat.

Lemma graph_to_mat_eq:
  forall (g: AdjMatLG) i j, 0 <= i < SIZE -> 0 <= j < SIZE ->
    (Znth i (Znth j (graph_to_symm_mat g))) = elabel g (eformat (i,j)).
Proof.
  intros.
  symmetry. rewrite eformat_symm.
  apply elabel_Znth_graph_to_mat; lia.
Qed.

Lemma graph_to_mat_symmetric:
  forall (g: AdjMatLG) i j,
    0 <= i < SIZE -> 0 <= j < SIZE ->
    (Znth i (Znth j (graph_to_symm_mat g))) =
    (Znth j (Znth i (graph_to_symm_mat g))).
Proof.
  intros. repeat rewrite graph_to_mat_eq; trivial.
  f_equal. apply eformat_symm.
Qed.

Lemma graph_to_mat_inf:
  forall (g: @AdjMatGG SIZE inf) u v,
    0 <= u < v ->
    v < SIZE ->
    ~ evalid g (u,v) ->
    Znth v (Znth u (graph_to_symm_mat g)) =
    priq_arr_utils.inf.
Proof.
  intros. unfold graph_to_symm_mat.
  rewrite <- elabel_Znth_graph_to_mat; try lia.
  rewrite eformat1.
  apply (MathAdjMatGraph.invalid_edge_weight); auto.
  simpl; lia.
Qed.
 
Lemma edgeless_vert_rep:
  forall v,
    0 <= v < SIZE ->
    (@vert_to_list SIZE edgeless_graph' eformat v) =
    list_repeat (Z.to_nat SIZE) inf.
Proof.
  intros. simpl. auto.
  (*should try to find a better scalable way*)
Qed.

Lemma edgeless_to_symm_mat:
  graph_to_symm_mat edgeless_graph' =
  list_repeat (Z.to_nat SIZE) (list_repeat (Z.to_nat SIZE) inf).
Proof.
  simpl. repeat rewrite edgeless_vert_rep; simpl. auto.
Qed.
