Require Import VST.floyd.proofauto.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.undirected_graph.
Require Export CertiGraph.graph.SpaceAdjMatGraph3.
Require Export CertiGraph.graph.MathAdjMatGraph.
Require Import CertiGraph.graph.eformat_lemmas.
Require Import CertiGraph.priq.priq_arr_utils.
(* 
Anshuman, Oct 1:
I want to stop using priq/priq_arr_utils.
Whatever you're using from in there is pure, 
and not related to PQ.

That stuff should be lifted into its own file, 
and PQ and this file should both just call that file.    

After that is done, most of this file can be lifted
up to graph/
*)
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


(* 
Anshuman, Oct 1:
I know the import needs to go up. Just showing that
only after this point do we need to get specific to 
MatrixUGraph. The above can be lifted.
*)
Require Import CertiGraph.prim.MatrixUGraph.

Definition edgeless_graph' := @edgeless_graph inf SIZE inf_rep SIZE_rep'.
Definition adde := @MatrixUGraph_adde inf SIZE.
Definition eremove := @MatrixUGraph_eremove inf SIZE.


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
