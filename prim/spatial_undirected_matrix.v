Require Import VST.veric.SeparationLogic. (*hm interesting, they have a separate sublist definition*)
Require Import VST.floyd.proofauto.
Require Import CertiGraph.floyd_ext.share.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.FiniteGraph.
Require Import CertiGraph.graph.undirected_graph.
Require Import CertiGraph.graph.AdjMatGraph.
Require Import CertiGraph.prim.MatrixUGraph.
Require Import CertiGraph.prim.prim.
Require Import CertiGraph.lib.List_ext.

Local Open Scope logic.

Definition vertex_type := tint.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.

Definition SIZE := 8.

Lemma SIZE_rep: 0 <= SIZE < Int.max_signed.
Proof. unfold SIZE. set (i:=Int.max_signed); compute in i; subst i. lia. Qed.

Definition inf := Int.max_signed - Int.max_signed / SIZE.

Lemma inf_rep: 0 <= inf < Int.max_signed.
Proof. unfold inf. set (i:=Int.max_signed); compute in i; subst i. unfold SIZE.
set (j:=2147483647 / 8); compute in j; subst j. lia. Qed.

Definition G := @MatrixUGraph inf SIZE.
Definition edgeless_graph' := @edgeless_graph inf SIZE inf_rep SIZE_rep.

Definition eformat (e: E) := if fst e <=? snd e then e else (snd e, fst e).

Lemma eformat1: forall (e: E), fst e <= snd e -> eformat e = e.
Proof. unfold eformat; intros. rewrite Zle_is_le_bool in H; rewrite H. auto. Qed.

Lemma eformat2': forall (e: E), snd e < fst e -> eformat e = (snd e, fst e).
Proof. unfold eformat; intros. rewrite <- Z.leb_gt in H; rewrite H. auto. Qed.

Lemma eformat2: forall (e: E), snd e <= fst e -> eformat e = (snd e, fst e).
Proof.
intros. apply Z.le_lteq in H. destruct H. rewrite eformat2'; auto. rewrite eformat1, H. rewrite <- H at 2. destruct e; auto. lia.
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

Lemma eformat_adj: forall (g: G) u v, adjacent g u v <-> elabel g (eformat (u,v)) <> inf.
Proof.
intros. pose proof (@edge_weight_not_inf _ _ _ (sound_MatrixUGraph g)).
split; intros.
+
destruct H0. destruct H0. destruct H0.
destruct H1; destruct H1. assert (x = (u,v)). {
  rewrite (@src_fst _ _ _ (sound_MatrixUGraph g) x H0) in H1.
  rewrite (@dst_snd _ _ _ (sound_MatrixUGraph g) x H0) in H3. rewrite <- H1, <- H3. destruct x; simpl; auto.
} subst x.
rewrite eformat1. apply H; auto. simpl; auto.
rewrite <- H1. rewrite <- H3 at 2. apply (@undirected_edge_rep _ _ _ (sound_MatrixUGraph g)). auto.
assert (x = (v,u)). {
  rewrite (@src_fst _ _ _ (sound_MatrixUGraph g) x H0) in H1.
  rewrite (@dst_snd _ _ _ (sound_MatrixUGraph g) x H0) in H3. rewrite <- H1, <- H3. destruct x; simpl; auto.
} subst x.
rewrite eformat2. simpl. apply H; auto. simpl. rewrite <- H1. rewrite <- H3 at 2.
apply (@undirected_edge_rep _ _ _ (sound_MatrixUGraph g)). auto.
+
destruct (Z.lt_trichotomy u v).
rewrite eformat1 in H0. 2: simpl; lia.
assert (evalid g (u,v)). apply evalid_inf_iff; auto.
exists (u,v). split. apply evalid_strong_evalid; auto. left.
rewrite (@src_fst _ _ _ (sound_MatrixUGraph g)); auto.
rewrite (@dst_snd _ _ _ (sound_MatrixUGraph g)); auto.
(*equal, repeat*)
destruct H1. rewrite eformat1 in H0. 2: simpl; lia.
assert (evalid g (u,v)). apply evalid_inf_iff; auto.
exists (u,v). split. apply evalid_strong_evalid; auto. left.
rewrite (@src_fst _ _ _ (sound_MatrixUGraph g)); auto.
rewrite (@dst_snd _ _ _ (sound_MatrixUGraph g)); auto.
rewrite eformat2 in H0. 2: simpl; lia. simpl in H0.
assert (evalid g (v,u)). apply evalid_inf_iff; auto.
exists (v,u). split. apply evalid_strong_evalid; auto.
rewrite (@src_fst _ _ _ (sound_MatrixUGraph g)); auto.
rewrite (@dst_snd _ _ _ (sound_MatrixUGraph g)); auto.
Qed.

(*When these are unfolded in the goal and I destruct evalid_dec, I can get the hypothesis but the if... doesn't simplify

Definition elabel_inf (g: MatrixUGraph) (e: E) := if evalid_dec g e then elabel g e else inf.

Definition elabel_inf_symm (g: MatrixUGraph) (e: E) :=
  if evalid_dec g (eformat e) then elabel g (eformat e) else inf.
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
  forall (g: G) u v, 0 <= u < v -> v < SIZE -> ~ evalid g (u,v) -> Znth v (Znth u (graph_to_symm_mat g)) = inf.
Proof.
unfold graph_to_symm_mat, vert_rep_symm; intros.
repeat rewrite Znth_map. repeat rewrite nat_inc_list_i.
rewrite eformat1. apply (@invalid_edge_weight inf SIZE g (sound_MatrixUGraph g)); auto. simpl; lia.
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

Definition list_address a index size : val :=
  offset_val (index * sizeof (tarray tint size)) a.

Definition list_rep sh size l contents_mat index :=
  let mylist := (Znth index contents_mat) in
  data_at sh (tarray tint size) (map (fun x => Vint (Int.repr x)) mylist) (list_address l index size).

Definition undirected_matrix sh matrix_contents gaddr : mpred :=
  iter_sepcon.iter_sepcon (list_rep sh SIZE gaddr matrix_contents)
                          (nat_inc_list (Z.to_nat (Zlength matrix_contents))).

(*isolate the "ith row"*)
Lemma graph_unfold: forall sh contents ptr i,
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
