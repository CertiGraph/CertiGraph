Require Import VST.floyd.proofauto.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.undirected_graph.
Require Export CertiGraph.graph.SpaceAdjMatGraph3.
Require Import CertiGraph.prim.MatrixUGraph.
Require Import CertiGraph.priq.priq_arr_utils.
Require Import CertiGraph.lib.List_ext.

Local Open Scope logic.

Definition vert_rep_symm (g : G) (v : V): list Z :=
  (@vert_to_list SIZE g eformat v).

(* from Graph to list (list Z) *)
Definition graph_to_symm_mat (g : G) : list (list Z) :=
  (@graph_to_mat SIZE g eformat).

Lemma graph_to_mat_eq:
  forall (g: G) i j, 0 <= i < SIZE -> 0 <= j < SIZE ->
    (Znth i (Znth j (graph_to_symm_mat g))) = elabel g (eformat (i,j)).
Proof.
  intros.
  symmetry. rewrite eformat_symm.
  apply elabel_Znth_graph_to_mat; lia.
Qed.

Lemma graph_to_mat_symmetric:
  forall (g: G) i j, 0 <= i < SIZE -> 0 <= j < SIZE ->
    (Znth i (Znth j (graph_to_symm_mat g))) = (Znth j (Znth i (graph_to_symm_mat g))).
Proof.
  intros. repeat rewrite graph_to_mat_eq; trivial.
  f_equal. apply eformat_symm.
Qed.

Lemma graph_to_mat_inf:
  forall (g: G) u v, 0 <= u < v -> v < SIZE -> ~ evalid g (u,v) -> Znth v (Znth u (graph_to_symm_mat g)) = priq_arr_utils.inf.
Proof.
unfold graph_to_symm_mat, graph_to_mat, vert_to_list; intros.
repeat rewrite Znth_map. repeat rewrite nat_inc_list_i.
rewrite eformat1. apply invalid_edge_weight; auto. simpl; lia.
all: try (rewrite Z2Nat.id; lia).
all: try (rewrite nat_inc_list_Zlength, Z2Nat.id; lia).
rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; lia.
Qed.

Lemma edgeless_vert_rep:
forall v, 0<=v<SIZE -> vert_rep_symm edgeless_graph' v = list_repeat (Z.to_nat SIZE) inf.
Proof.
unfold vert_rep_symm; intros.
simpl. auto. (*should try to find a better scalable way*)
Qed.

Lemma edgeless_to_symm_mat:
graph_to_symm_mat edgeless_graph' = list_repeat (Z.to_nat SIZE) (list_repeat (Z.to_nat SIZE) inf).
Proof.
unfold graph_to_symm_mat.
simpl. repeat rewrite edgeless_vert_rep; simpl. auto.
all: unfold SIZE; lia.
Qed.

Definition undirected_matrix {cs: compspecs} sh g_contents gaddr : mpred :=
  (@SpaceAdjMatGraph' SIZE (cs: compspecs) sh eformat g_contents gaddr). 

(*isolate the "ith row"*)
Lemma graph_unfold: forall {cs: compspecs} sh contents ptr i,
    Zlength contents = SIZE ->
    0 <= i < (Zlength contents) ->
    undirected_matrix sh contents ptr =
    iter_sepcon.iter_sepcon (@list_rep SIZE cs sh ptr contents) (*<---before*)
            (sublist 0 i (nat_inc_list (Z.to_nat (Zlength contents)))) *
    (@list_rep SIZE cs sh ptr contents i * (*ith array*)
           iter_sepcon.iter_sepcon (@list_rep SIZE cs sh ptr contents) (*after*)
             (sublist (i + 1) (Zlength contents) (nat_inc_list (Z.to_nat (Zlength contents))))).
Proof.
  intros.
  unfold undirected_matrix.
  rewrite (SpaceAdjMatGraph_unfold' _ _ _ _ [] i); try lia.
  rewrite H. reflexivity.
Qed.
