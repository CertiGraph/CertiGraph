Require Import VST.floyd.proofauto.
Require Import CertiGraph.graph.graph_model.
Require Export CertiGraph.graph.SpaceAdjMatGraph3.
Require Import CertiGraph.prim.MatrixUGraph3.
Require Import CertiGraph.prim.prim_constants.

(* 
Anshuman, Oct 2:
priq/priq_arr_utils comes from MatrixUGraph via Import-Export.

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

Definition G := @MatrixUGraph inf size.
Definition edgeless_graph' := @edgeless_graph inf size inf_rep size_rep'.
Definition adde := @MatrixUGraph_adde inf size.
Definition eremove := @MatrixUGraph_eremove inf size.

Lemma edgeless_vert_rep:
  forall v,
    0 <= v < size ->
    (@vert_to_list size edgeless_graph' eformat v) =
    list_repeat (Z.to_nat size) inf.
Proof.
  intros. simpl. auto.
  (*should try to find a better scalable way*)
Qed.

Lemma edgeless_to_symm_mat:
  graph_to_symm_mat edgeless_graph' =
  list_repeat (Z.to_nat size) (list_repeat (Z.to_nat size) inf).
Proof.
  simpl. repeat rewrite edgeless_vert_rep; simpl. auto.
Qed.

Lemma eformat_evalid_vvalid:
forall (g: G) u v, evalid g (eformat (u,v)) -> vvalid g u /\ vvalid g v.
Proof.
intros. apply evalid_strong_evalid in H.
destruct (Z.lt_trichotomy u v).
rewrite eformat1 in H. destruct H.
rewrite src_fst, dst_snd in H1; auto. simpl; lia.
destruct H0.
subst u. rewrite eformat1 in H. destruct H.
rewrite src_fst, dst_snd in H0; auto. simpl; lia.
rewrite eformat2 in H. simpl in H; destruct H.
rewrite src_fst, dst_snd in H1; auto. simpl in H1.
split; apply H1. simpl; lia.
Qed.

Lemma eformat_adj': forall (g: G) u v, evalid g (eformat (u,v)) -> adj_edge g (eformat (u,v)) u v.
Proof.
intros. split. apply evalid_strong_evalid; auto.
destruct (Z.le_ge_cases u v).
rewrite eformat1 in *. left. rewrite src_fst, dst_snd; auto. auto. auto.
rewrite eformat2 in *. right. rewrite src_fst, dst_snd; auto. auto. auto.
Qed.

Lemma eformat_adj: forall (g: G) u v, adjacent g u v <-> evalid g (eformat (u,v)).
Proof.
intros. split. intros.
+
destruct H. destruct H. destruct H.
destruct H0; destruct H0. assert (x = (u,v)). {
  rewrite src_fst in H0.
  rewrite dst_snd in H2. rewrite <- H0, <- H2. destruct x; simpl; auto.
} subst x.
rewrite eformat1; auto. simpl.
rewrite <- H0. rewrite <- H2 at 2. apply undirected_edge_rep; auto.
assert (x = (v,u)). {
  rewrite src_fst in H0; rewrite dst_snd in H2.
  rewrite <- H0, <- H2. destruct x; simpl; auto.
} subst x.
rewrite eformat2. simpl. auto. simpl. rewrite <- H0. rewrite <- H2 at 2.
apply undirected_edge_rep; auto.
+intros. destruct (Z.lt_trichotomy u v).
rewrite eformat1 in H. 2: simpl; lia.
assert (evalid g (u,v)). auto.
exists (u,v). split. apply evalid_strong_evalid; auto. left.
rewrite src_fst, dst_snd; auto.
(*equal, repeat*)
destruct H0. rewrite eformat1 in H. 2: simpl; lia.
assert (evalid g (u,v)). auto.
exists (u,v). split. apply evalid_strong_evalid; auto. left.
rewrite src_fst, dst_snd; auto.
rewrite eformat2 in H. 2: simpl; lia. simpl in H.
assert (evalid g (v,u)). auto.
exists (v,u). split. apply evalid_strong_evalid; auto.
rewrite src_fst, dst_snd; auto.
Qed.

Corollary eformat_adj_elabel: forall (g: G) u v, adjacent g u v <-> elabel g (eformat (u,v)) < inf.
Proof.
intros. rewrite eformat_adj. apply evalid_inf_iff.
Qed.
