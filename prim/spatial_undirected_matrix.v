Require Import VST.veric.SeparationLogic. (*hm interesting, they have a separate sublist definition*)
Require Import VST.floyd.proofauto.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.FiniteGraph.
Require Import CertiGraph.graph.undirected_graph.
Require Import CertiGraph.graph.MathAdjMatGraph.
Require Import CertiGraph.graph.SpaceAdjMatGraph_noncont.
Require Import CertiGraph.prim.MatrixUGraph.
Require Import CertiGraph.priq.priq_arr_utils.
Require Import CertiGraph.lib.List_ext.

Local Open Scope logic.

Definition G := @MatrixUGraph priq_arr_utils.inf priq_arr_utils.SIZE.
Definition edgeless_graph' := @edgeless_graph priq_arr_utils.inf priq_arr_utils.SIZE inf_rep SIZE_rep.
Definition adde := @MatrixUGraph_adde priq_arr_utils.inf priq_arr_utils.SIZE.
Definition eremove := @MatrixUGraph_eremove priq_arr_utils.inf priq_arr_utils.SIZE.

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
rewrite (@src_fst _ _ _ (sound_MatrixUGraph g)), (@dst_snd _ _ _ (sound_MatrixUGraph g)) in H1; auto. simpl; lia.
destruct H0.
subst u. rewrite eformat1 in H. destruct H.
rewrite (@src_fst _ _ _ (sound_MatrixUGraph g)), (@dst_snd _ _ _ (sound_MatrixUGraph g)) in H0; auto. simpl; lia.
rewrite eformat2 in H. simpl in H; destruct H.
rewrite (@src_fst _ _ _ (sound_MatrixUGraph g)), (@dst_snd _ _ _ (sound_MatrixUGraph g)) in H1; auto. simpl in H1.
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
rewrite eformat1 in *. left. rewrite (@src_fst _ _ _ (sound_MatrixUGraph _)); auto.
rewrite (@dst_snd _ _ _ (sound_MatrixUGraph _)); auto. simpl; auto. simpl; auto.
rewrite eformat2 in *. right. rewrite (@src_fst _ _ _ (sound_MatrixUGraph _)); auto.
rewrite (@dst_snd _ _ _ (sound_MatrixUGraph _)); auto. simpl; auto. simpl; auto.
Qed.

Lemma eformat_adj: forall (g: G) u v, adjacent g u v <-> evalid g (eformat (u,v)).
Proof.
intros. split. intros.
+
destruct H. destruct H. destruct H.
destruct H0; destruct H0. assert (x = (u,v)). {
  rewrite (@src_fst _ _ _ (sound_MatrixUGraph g) x H) in H0.
  rewrite (@dst_snd _ _ _ (sound_MatrixUGraph g) x H) in H2. rewrite <- H0, <- H2. destruct x; simpl; auto.
} subst x.
rewrite eformat1; auto. simpl.
rewrite <- H0. rewrite <- H2 at 2. apply (@undirected_edge_rep _ _ _ (sound_MatrixUGraph g)). auto.
assert (x = (v,u)). {
  rewrite (@src_fst _ _ _ (sound_MatrixUGraph g) x H) in H0.
  rewrite (@dst_snd _ _ _ (sound_MatrixUGraph g) x H) in H2. rewrite <- H0, <- H2. destruct x; simpl; auto.
} subst x.
rewrite eformat2. simpl. auto. simpl. rewrite <- H0. rewrite <- H2 at 2.
apply (@undirected_edge_rep _ _ _ (sound_MatrixUGraph g)). auto.
+intros. destruct (Z.lt_trichotomy u v).
rewrite eformat1 in H. 2: simpl; lia.
assert (evalid g (u,v)). auto.
exists (u,v). split. apply evalid_strong_evalid; auto. left.
rewrite (@src_fst _ _ _ (sound_MatrixUGraph g)); auto.
rewrite (@dst_snd _ _ _ (sound_MatrixUGraph g)); auto.
(*equal, repeat*)
destruct H0. rewrite eformat1 in H. 2: simpl; lia.
assert (evalid g (u,v)). auto.
exists (u,v). split. apply evalid_strong_evalid; auto. left.
rewrite (@src_fst _ _ _ (sound_MatrixUGraph g)); auto.
rewrite (@dst_snd _ _ _ (sound_MatrixUGraph g)); auto.
rewrite eformat2 in H. 2: simpl; lia. simpl in H.
assert (evalid g (v,u)). auto.
exists (v,u). split. apply evalid_strong_evalid; auto.
rewrite (@src_fst _ _ _ (sound_MatrixUGraph g)); auto.
rewrite (@dst_snd _ _ _ (sound_MatrixUGraph g)); auto.
Qed.

Corollary eformat_adj_elabel: forall (g: G) u v, adjacent g u v <-> elabel g (eformat (u,v)) < inf.
Proof.
intros. pose proof (@edge_weight_not_inf _ _ _ (sound_MatrixUGraph g)).
rewrite eformat_adj. apply evalid_inf_iff.
Qed.

(*When these are unfolded in the goal and I destruct evalid_dec, I can get the hypothesis but the if... doesn't simplify

Definition elabel_inf (g: MatrixUGraph) (e: E) := if evalid_dec g e then elabel g e else inf.

Definition elabel_inf_symm (g: MatrixUGraph) (e: E) :=
  if evalid_dec g (eformat e) then elabel g (eformat e) else inf.
*)

(* Use vert_to_list, 
   graph_to_mat, 
   elabel_Znth_graph_to_mat. 
   In each, there is a 
   special field "f" for your "eformat" to go
 *)
Definition vert_rep_symm (g : G) (v : V): list Z :=
  map (elabel g) (map (fun x => eformat (v,x)) (nat_inc_list (Z.to_nat SIZE))).

(* from Graph to list (list Z) *)
Definition graph_to_symm_mat (g : G) : list (list Z) :=
  map (vert_rep_symm g) (nat_inc_list (Z.to_nat SIZE)).

Lemma graph_to_mat_eq:
  forall (g: G) i j, 0 <= i < SIZE -> 0 <= j < SIZE ->
    (Znth i (Znth j (graph_to_symm_mat g))) = elabel g (eformat (i,j)).
Proof.
intros. unfold graph_to_symm_mat, vert_rep_symm. rewrite Znth_map. rewrite Znth_map. rewrite Znth_map.
rewrite nat_inc_list_i. rewrite nat_inc_list_i. rewrite eformat_symm; auto.
lia. lia. rewrite nat_inc_list_Zlength; lia. rewrite Zlength_map.
all: rewrite nat_inc_list_Zlength; lia.
Qed.

Lemma graph_to_mat_symmetric:
  forall (g: G) i j, 0 <= i < SIZE -> 0 <= j < SIZE ->
    (Znth i (Znth j (graph_to_symm_mat g))) = (Znth j (Znth i (graph_to_symm_mat g))).
Proof.
unfold graph_to_symm_mat, vert_rep_symm; intros.
repeat rewrite Znth_map. repeat rewrite nat_inc_list_i by lia.
rewrite eformat_symm. auto.
all: try (rewrite nat_inc_list_Zlength, Z2Nat.id; lia).
all: rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; lia.
Qed.

Lemma graph_to_mat_inf:
  forall (g: G) u v, 0 <= u < v -> v < SIZE -> ~ evalid g (u,v) -> Znth v (Znth u (graph_to_symm_mat g)) = priq_arr_utils.inf.
Proof.
unfold graph_to_symm_mat, vert_rep_symm; intros.
repeat rewrite Znth_map. repeat rewrite nat_inc_list_i.
rewrite eformat1. apply (@invalid_edge_weight priq_arr_utils.inf priq_arr_utils.SIZE g (sound_MatrixUGraph g)); auto. simpl; lia.
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

(*************C related**********)

Definition list_address {cs: compspecs} a index size : val :=
  offset_val (index * sizeof (tarray tint size)) a.

Definition list_rep {cs: compspecs} sh size l contents_mat index :=
  let mylist := (Znth index contents_mat) in
  data_at sh (tarray tint size) (map (fun x => Vint (Int.repr x)) mylist) (list_address l index size).

Definition undirected_matrix {cs: compspecs} sh matrix_contents gaddr : mpred :=
  iter_sepcon.iter_sepcon (list_rep sh SIZE gaddr matrix_contents)
                          (nat_inc_list (Z.to_nat (Zlength matrix_contents))).

(*isolate the "ith row"*)
Lemma graph_unfold: forall {cs: compspecs} sh contents ptr i,
    0 <= i < (Zlength contents) ->
    undirected_matrix sh contents ptr =
    iter_sepcon.iter_sepcon (list_rep sh SIZE ptr contents) (*<---before*)
            (sublist 0 i (nat_inc_list (Z.to_nat (Zlength contents)))) *
    (list_rep sh SIZE ptr contents i * (*ith array*)
           iter_sepcon.iter_sepcon (list_rep sh SIZE ptr contents) (*after*)
             (sublist (i + 1) (Zlength contents) (nat_inc_list (Z.to_nat (Zlength contents))))).
Proof.
  intros. unfold undirected_matrix.
  replace (nat_inc_list (Z.to_nat (Zlength contents))) with
      (sublist 0 (Zlength contents) (nat_inc_list (Z.to_nat (Zlength contents)))) at 1.
  2: { rewrite sublist_same; trivial.
       rewrite nat_inc_list_Zlength, Z2Nat_id', Z.max_r; trivial.
       apply Zlength_nonneg.
  }
  rewrite (sublist_split 0 i (Zlength contents)),
  (sublist_split i (i+1) (Zlength contents)), (sublist_one i); try lia.
  2, 3, 4: rewrite nat_inc_list_Zlength; rewrite Z2Nat.id; lia.
  rewrite nat_inc_list_i.
  2: rewrite Z2Nat_id', Z.max_r; trivial; apply Zlength_nonneg. 
  repeat rewrite iter_sepcon.iter_sepcon_app.
  simpl. rewrite sepcon_emp. reflexivity.
Qed.
