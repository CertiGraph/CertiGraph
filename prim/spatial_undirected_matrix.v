Require Import VST.floyd.proofauto.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.undirected_graph.
Require Export CertiGraph.graph.SpaceAdjMatGraph3.
Require Import CertiGraph.prim.MatrixUGraph.
Require Import CertiGraph.priq.priq_arr_utils.
Require Import CertiGraph.lib.List_ext.

Local Open Scope logic.

Definition G := @MatrixUGraph inf SIZE.
Definition edgeless_graph' := @edgeless_graph inf SIZE inf_rep SIZE_rep'.
Definition adde := @MatrixUGraph_adde inf SIZE.
Definition eremove := @MatrixUGraph_eremove inf SIZE.

Definition eformat (e: E) := if fst e <=? snd e then e else (snd e, fst e).

Lemma eformat1: forall (e: E), fst e <= snd e -> eformat e = e.
Proof. unfold eformat; intros. rewrite Zle_is_le_bool in H; rewrite H. auto. Qed.

Lemma eformat2': forall (e: E), snd e < fst e -> eformat e = (snd e, fst e).
Proof. unfold eformat; intros. rewrite <- Z.leb_gt in H; rewrite H. auto. Qed.

Lemma eformat2: forall (e: E), snd e <= fst e -> eformat e = (snd e, fst e).
Proof.
intros. apply Z.le_lteq in H. destruct H. rewrite eformat2'; auto. rewrite eformat1, H. rewrite <- H at 2. destruct e; auto. lia.
Qed.

Lemma eformat_eq:
  forall u v a b, eformat (u,v) = eformat (a,b) -> ((u=a /\ v=b) \/ (u=b /\ v=a)).
Proof.
intros. destruct (Z.le_ge_cases u v); destruct (Z.le_ge_cases a b).
rewrite eformat1, eformat1 in H. apply pair_equal_spec in H. left; auto. simpl; auto. simpl; auto. simpl; auto.
rewrite eformat1, eformat2 in H. simpl in H. apply pair_equal_spec in H. right; auto. simpl; auto. simpl; auto.
rewrite eformat2, eformat1 in H. simpl in H. apply pair_equal_spec in H. right; split; apply H. simpl; auto. simpl; auto.
rewrite eformat2, eformat2 in H. simpl in H. apply pair_equal_spec in H. left; split; apply H. simpl; auto. simpl; auto.
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

Lemma eformat_symm:
forall u v, eformat (u,v) = eformat (v,u).
Proof.
intros. destruct (Z.lt_trichotomy u v).
rewrite eformat1. rewrite eformat2. simpl; auto. simpl; lia. simpl; lia.
destruct H.
rewrite eformat1. rewrite eformat2. simpl; auto. simpl; lia. simpl; lia.
rewrite eformat2'. rewrite eformat1. simpl; auto. simpl; lia. simpl; lia.
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

(*When these are unfolded in the goal and I destruct evalid_dec, I can get the hypothesis but the if... doesn't simplify

Definition elabel_inf (g: MatrixUGraph) (e: E) := if evalid_dec g e then elabel g e else inf.

Definition elabel_inf_symm (g: MatrixUGraph) (e: E) :=
  if evalid_dec g (eformat e) then elabel g (eformat e) else inf.
*)


(************* Spatial Rep **********)

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
