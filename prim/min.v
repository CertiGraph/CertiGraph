(*this copy is to target the minimality proof directly*)

Require Import VST.floyd.proofauto.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.floyd_ext.share.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_relation.
Require Import CertiGraph.graph.FiniteGraph.
Require Import CertiGraph.graph.undirected_graph.
Require Import CertiGraph.graph.AdjMatGraph.
Require Import CertiGraph.prim.MatrixUGraph.
Require Import CertiGraph.priq.priq_arr_specs.
Require Import CertiGraph.priq.priq_arr_utils.
Require Import CertiGraph.prim.prim.
Require Import CertiGraph.prim.spatial_undirected_matrix.
Require Import CertiGraph.prim.specs_prim.

Local Open Scope Z.

Lemma adjacent_dec:
forall (g: G) u v, adjacent g u v \/ ~ adjacent g u v.
Proof.
intros. tauto.
Qed.

(*ideally generalise in_dec to any decidable function, and don't need NoDup*)
Lemma filter_list_Permutation:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l1 l2: list A),
  NoDup l2 ->
  Permutation
    ((filter (fun x => in_dec EA x l1) l2) ++ (filter (fun x => negb (in_dec EA x l1)) l2))
    l2.
Proof.
intros. apply NoDup_Permutation.
apply NoDup_app_inv. apply NoDup_filter. auto. apply NoDup_filter. auto.
intros. rewrite filter_In in H0. rewrite filter_In. destruct H0.
unfold not; intros. destruct H2. destruct (in_dec EA x l1).
inversion H3. inversion H1. auto.
intros; split; intros.
apply in_app_or in H0; destruct H0; rewrite filter_In in H0; destruct H0; auto.
apply in_or_app. repeat rewrite filter_In.
destruct (in_dec EA x l1). left; split; auto. right; split; auto.
Qed.

Lemma fold_left_Zadd_diff_accum:
forall (l: list Z) (x y: Z), x <= y -> fold_left Z.add l x <= fold_left Z.add l y.
Proof.
induction l; intros. simpl; auto.
apply IHl. lia.
Qed.

Lemma fold_left_Zadd_comp:
forall (l1 l2: list Z), Zlength l1 = Zlength l2 -> (forall i, 0<=i<Zlength l1 -> Znth i l1 <= Znth i l2)
  -> (forall s, fold_left Z.add l1 s <= fold_left Z.add l2 s).
Proof.
induction l1; intros.
rewrite Zlength_nil in H. symmetry in H. apply Zlength_nil_inv in H. subst l2. lia.
destruct l2. rewrite Zlength_cons in H. rewrite Zlength_nil in H. pose proof (Zlength_nonneg l1). lia.
simpl. assert (a <= z). replace a with (Znth 0 (a::l1)). replace z with (Znth 0 (z::l2)).
apply H0. split. lia. rewrite Zlength_cons. pose proof (Zlength_nonneg l1). lia.
auto. auto.
apply (Z.le_trans _ (fold_left Z.add l1 (s + z)) _).
apply fold_left_Zadd_diff_accum. lia.
apply IHl1. do 2 rewrite Zlength_cons in H. lia.
intros. replace (Znth i l1) with (Znth (i+1) (a::l1)).
 replace (Znth i l2) with (Znth (i+1) (z::l2)). apply H0. rewrite Zlength_cons. lia.
all: rewrite (Znth_pos_cons (i+1)) by lia; rewrite Z.add_simpl_r; auto.
Qed.

(*todo: get a version of this that only cares about validty of p's vertices instead of VList g ...
and any decidable function instead of l1 l2*)
Lemma path_partition_checkpoint:
forall (g: G) {fg: FiniteGraph g} (l1 l2: list V) p a b, Permutation (l1++l2) (VList g) ->
  In a l1 -> In b l2 -> connected_by_path g p a b ->
  exists v1 v2, In v1 p /\ In v2 p /\
    In v1 l1 /\ In v2 l2 /\ adjacent g v1 v2.
Proof.
  induction p; intros. destruct H2. destruct H3. inversion H3.
  destruct p. destruct H2. destruct H3. inversion H3; inversion H4; subst a. subst a0.
  assert (~ In b l2).
  apply (NoDup_app_not_in V l1). apply (Permutation_NoDup (l:=VList g)).
  apply Permutation_sym; auto. apply NoDup_VList. auto. contradiction.
  destruct H2. destruct H3. destruct H2. inversion H3. subst a0.
  assert (In v (l1 ++ l2)). apply (Permutation_in (l:=VList g)). apply Permutation_sym; auto.
  rewrite VList_vvalid. apply adjacent_requires_vvalid in H2; apply H2.
  apply in_app_or in H6; destruct H6.
  assert (exists v1 v2 : V, In v1 (v :: p) /\ In v2 (v :: p) /\
    In v1 l1 /\ In v2 l2 /\ adjacent g v1 v2). apply (IHp v b); auto.
  split. auto. split. simpl; auto. rewrite last_error_cons in H4. auto.
    unfold not; intros. assert (In v (v::p)). left; auto. rewrite H7 in H8. contradiction.
  destruct H7 as [v1 [v2 [? [? [? [? ?]]]]]]. exists v1; exists v2. split. right; auto. split. right; auto.
  split3; auto.
  exists a; exists v. split3. left; auto. right; left; auto. split3; auto.
Qed.

Corollary path_partition_checkpoint2:
forall (g: G) {fg: FiniteGraph g} (l: list V) p a b, In a l -> ~ In b l ->
  connected_by_path g p a b ->
  exists v1 v2, In v1 p /\ In v2 p /\
    In v1 l /\ ~ In v2 l /\ adjacent g v1 v2.
Proof.
intros.
apply (path_partition_checkpoint g
  (filter (fun x => (in_dec V_EqDec x l)) (VList g))
  (filter (fun x => negb (in_dec V_EqDec x l)) (VList g))
) in H1.
2: { apply filter_list_Permutation. apply NoDup_VList. }
2: { rewrite filter_In. split. rewrite VList_vvalid. apply connected_by_path_vvalid in H1; apply H1.
      destruct (in_dec V_EqDec a l). auto. contradiction. }
2: { rewrite filter_In. split. rewrite VList_vvalid. apply connected_by_path_vvalid in H1; apply H1.
      destruct (In_dec V_EqDec b l). contradiction. auto. }
destruct H1 as [v1 [v2 [? [? [? [? ?]]]]]].
exists v1; exists v2. split. auto. split. auto.
split. rewrite filter_In in H3. destruct H3. destruct (in_dec V_EqDec v1 l). auto. inversion H6.
split. rewrite filter_In in H4. destruct H4. destruct (in_dec V_EqDec v2 l). inversion H6. auto.
auto.
Qed.

Lemma list_eq_Znth:
  forall {A:Type} {d: Inhabitant A} (l l': list A), Zlength l = Zlength l' ->
    (forall i, 0 <= i < Zlength l -> Znth i l = Znth i l') ->
    l = l'.
Proof.
induction l; intros. symmetry; apply Zlength_nil_inv. rewrite Zlength_nil in H; auto.
destruct l'. rewrite Zlength_cons, Zlength_nil in H.
pose proof (Zlength_nonneg (A:=A) l).
assert (Zlength l < Z.succ (Zlength l)) by lia. lia.
replace a with (Znth 0 (a::l)). 2: rewrite Znth_0_cons; auto.
replace a0 with (Znth 0 (a0::l)). 2: rewrite Znth_0_cons; auto.
rewrite (H0 0). 2: rewrite Zlength_cons; pose proof (Zlength_nonneg (A:=A) l); lia.
rewrite (IHl l'); auto.
apply Z.succ_inj. do 2 rewrite Zlength_cons in H. auto.
intros. replace (Znth i l) with (Znth (i+1) (a::l)).
replace (Znth i l') with (Znth (i+1) (a0::l')). apply H0. rewrite Zlength_cons. lia.
replace (Znth i l') with (Znth (i+1 - 1) l'). apply Znth_pos_cons. lia. rewrite Z.add_simpl_r; auto.
replace (Znth i l) with (Znth (i+1 - 1) l). apply Znth_pos_cons. lia. rewrite Z.add_simpl_r; auto.
Qed.

Lemma Zlt_Zmin:
forall x y, x < y -> Z.min x y = x.
Proof. intros. rewrite Zmin_spec. destruct (zlt x y); lia. Qed.

Lemma find_app_In1:
forall l1 l2 v ans, In v l1 -> find (l1++l2) v ans = find l1 v ans.
Proof.
induction l1; intros. contradiction.
destruct (Z.eq_dec v a). subst a.
simpl. unfold initial_world.EqDec_Z, zeq.
destruct (Z.eq_dec v v). auto. contradiction.
destruct H. symmetry in H; contradiction.
simpl. destruct (initial_world.EqDec_Z a v). symmetry in e; contradiction.
rewrite IHl1; auto.
Qed.

Lemma find_accum_add1:
forall l v ans1 ans2, find l v (ans1+ans2) = ans1 + find l v ans2.
Proof.
induction l; intros.
simpl. auto.
simpl. destruct (initial_world.EqDec_Z a v). auto.
replace (1+(ans1+ans2)) with (ans1 + (1+ans2)) by lia. apply IHl.
Qed.

Lemma find_app_notIn1:
forall l1 l2 v ans, ~ In v l1 -> find (l1++l2) v ans = Zlength l1 + find l2 v ans.
Proof.
induction l1; intros. rewrite app_nil_l, Zlength_nil. lia.
assert (~ In v l1). unfold not; intros; apply H. right; auto.
simpl. destruct (initial_world.EqDec_Z a v). subst a. exfalso. apply H. left; auto.
rewrite Zlength_cons. rewrite IHl1; auto.
rewrite <- Z.add_1_r, <- Z.add_assoc. rewrite find_accum_add1. auto.
Qed.

Corollary find_notIn:
forall l v ans, ~ In v l -> find l v ans = Zlength l + ans.
Proof.
intros. replace l with (l++[]). rewrite find_app_notIn1. simpl.
rewrite app_nil_r; auto.
auto. apply app_nil_r.
Qed.

Corollary find_notIn_0:
forall l v, ~ In v l -> find l v 0 = Zlength l.
Proof. intros. rewrite find_notIn by auto. rewrite Z.add_0_r; auto. Qed.

Lemma find_In_ubound:
forall l v ans, In v l -> find l v ans < Zlength l + ans.
Proof.
induction l; intros. contradiction.
rewrite Zlength_cons.
simpl. destruct (initial_world.EqDec_Z a v).
pose proof (Zlength_nonneg l); lia.
rewrite Z.add_succ_l. rewrite find_accum_add1, Z.add_1_l.
assert (find l v ans < Zlength l + ans). apply IHl. destruct H. contradiction. auto.
lia.
Qed.

Lemma find_ubound:
forall l v ans, find l v ans <= Zlength l + ans.
Proof.
induction l; intros. rewrite Zlength_nil; simpl; lia.
rewrite Zlength_cons.
simpl. destruct (initial_world.EqDec_Z a v).
pose proof (Zlength_nonneg l); lia.
rewrite Z.add_succ_l. rewrite find_accum_add1, Z.add_1_l.
specialize IHl with v ans.
lia.
Qed.

Lemma find_cons:
forall l v ans, find (v::l) v ans = ans.
Proof.
intros. simpl. destruct (initial_world.EqDec_Z v v). auto. contradiction.
Qed.

Lemma find_lbound:
forall l v ans, ans <= find l v ans.
Proof.
induction l; intros. simpl. lia.
simpl. destruct (initial_world.EqDec_Z a v). lia.
rewrite find_accum_add1. specialize IHl with v ans; lia.
Qed.

Lemma sublist_of_nil:
forall {A:Type} lo hi, sublist lo hi (nil (A:=A)) = nil.
Proof.
intros. unfold sublist. rewrite firstn_nil. rewrite skipn_nil. auto.
Qed.

Lemma sublist_overshoot:
forall {A:Type} (l: list A) lo hi, Zlength l <= lo -> sublist lo hi l = [].
Proof.
intros. unfold sublist.
rewrite skipn_short; auto.
rewrite <- ZtoNat_Zlength.
rewrite Zlength_firstn.
destruct (Z.lt_trichotomy 0 hi). rewrite Z.max_r by lia.
destruct (Z.lt_trichotomy hi (Zlength l)). rewrite Z.min_l. lia. lia. destruct H1. 
subst hi. rewrite Z.min_id. lia. rewrite Z.min_r by lia. lia.
destruct H0. subst hi. rewrite Z.max_id. rewrite Z.min_l. lia. pose proof (Zlength_nonneg l); lia.
rewrite Z.max_l by lia. rewrite Z.min_l. lia. pose proof (Zlength_nonneg l); lia.
Qed.

Lemma sublist_same_overshoot:
forall {A:Type} (l: list A) hi, Zlength l <= hi -> sublist 0 hi l = l.
Proof.
intros. unfold sublist. rewrite skipn_0. rewrite firstn_same. auto.
rewrite <- ZtoNat_Zlength. lia.
Qed.

Lemma find_sublist_NoDup_notIn:
forall l a, NoDup l -> ~ In a (sublist 0 (find l a 0) l).
Proof.
induction l; unfold not; intros.
rewrite sublist_nil in H0. auto.
simpl in H0. destruct (initial_world.EqDec_Z a a0).
rewrite sublist_nil in H0. contradiction.
rewrite (sublist_split 0 1) in H0. 2: lia. 2: {
  split. apply find_lbound. rewrite Zlength_cons, <- Z.add_1_r. apply find_ubound. }
apply in_app_or in H0. destruct H0. rewrite sublist_one, Znth_0_cons in H0.
destruct H0; contradiction. lia. rewrite Zlength_cons, <- Z.add_1_l. pose proof (Zlength_nonneg l). lia. lia.
rewrite sublist_1_cons in H0. replace (find l a0 1) with (find l a0 (1+0)) in H0.
2: rewrite Z.add_0_r; auto. rewrite find_accum_add1 in H0.
replace (1 + find l a0 0 - 1) with (find l a0 0) in H0 by lia.
apply (IHl a0). apply NoDup_cons_1 in H; auto. auto.
Qed.

Lemma sublist_cons:
forall {A:Type} (l: list A) lo hi a, 0 <= lo < hi -> hi < Zlength l -> (*<-very strict conditions, but too tired to prove general version*)
  sublist (lo+1) (hi+1) (a::l) = sublist lo hi l.
Proof.
intros. unfold sublist; simpl.
Search firstn cons.
repeat rewrite Z.add_1_r, Z2Nat.inj_succ by lia.
rewrite firstn_cons. rewrite skipn_cons. auto.
Qed.

Lemma Znth_In_sublist:
forall {A:Type} {d: Inhabitant A} (l: list A) lo i hi, 0 <= lo < hi -> hi < Zlength l -> lo <= i < hi -> In (Znth i l) (sublist lo hi l).
Proof.
induction l; intros.
rewrite Zlength_nil in H0; lia.
assert (0 <= lo) by lia. apply (Z.le_lteq 0 lo) in H2. destruct H2.
rewrite Znth_pos_cons by lia. replace lo with ((lo-1)+1) by lia. replace hi with ((hi-1)+1) by lia.
rewrite Zlength_cons in H0. rewrite sublist_cons by lia. apply IHl; lia.
subst lo. assert (0 <= i) by lia. apply Z.le_lteq in H2. destruct H2.
rewrite Znth_pos_cons by lia. rewrite (sublist_split 0 (0+1)) by lia. apply in_or_app; right.
replace hi with ((hi-1)+1) by lia. rewrite Zlength_cons in H0. rewrite sublist_cons by lia.
apply IHl; lia.
subst i. rewrite (sublist_split 0 1), sublist_one by lia. apply in_or_app. left; left; auto.
Qed.

(********INF/SIZE CONVENIENCE LEMMAS************)

Lemma inf_equiv':
(Int.sub (Int.repr 2147483647) (Int.divs (Int.repr 2147483647) (Int.repr 8))) = (Int.repr inf).
Proof. compute. trivial. Qed.

Lemma inf_repable:
repable_signed inf.
Proof.
unfold repable_signed, inf, SIZE.
set (j:=Int.min_signed); compute in j; subst j.
set (j:=Int.max_signed); compute in j; subst j.
set (j:=2147483647 / 8); compute in j; subst j.
lia.
Qed.

Lemma inf_priq:
inf = priq_arr_utils.inf.
Proof.
compute; trivial.
Qed.

Lemma inf_literal:
inf = 1879048192.
Proof.
compute; trivial.
Qed.

Lemma SIZE_priq:
SIZE = priq_arr_utils.SIZE.
Proof.
compute; trivial.
Qed.



(***********************VERIFICATION***********************)
(*
Lemma prim_induct:
forall lmst lsame (g mst t': G) {fg: FiniteGraph mst} {ft: FiniteGraph t'} popped_vertices parents,
  labeled_spanning_uforest mst g -> labeled_spanning_uforest t' g ->
  Permutation (EList mst) (map (fun v : Z => eformat (v, Znth v parents)) (filter (fun v : Z => Znth v parents <? SIZE) popped_vertices)) ->
  Permutation (lmst++lsame) (map (fun v : Z => eformat (v, Znth v parents)) (filter (fun v : Z => Znth v parents <? SIZE) popped_vertices)) ->
  (forall v : Z, 0 <= v < SIZE -> 0 <= Znth v parents < SIZE ->
     evalid g (eformat (v, Znth v parents)) /\
     (exists i : Z,
        0 <= i < Zlength popped_vertices /\ Znth i popped_vertices = Znth v parents)) ->
  (forall v u1 u2 : V, In v popped_vertices -> 0 <= Znth v parents < SIZE -> vvalid g u2 ->
     In u1 (sublist 0 (find popped_vertices v 0) popped_vertices) ->
     ~ In u2 (sublist 0 (find popped_vertices v 0) popped_vertices) ->
     elabel g (eformat (v, Znth v parents)) <= elabel g (eformat (u1, u2))) ->
  (exists lt : list E, Permutation (lt ++ lsame) (EList t') /\ Zlength lt = Zlength lmst /\
    (forall i : Z, 0 <= i < Zlength lmst -> elabel mst (Znth i lmst) <= elabel t' (Znth i lt))).
*)



Lemma body_prim: semax_body Vprog Gprog f_prim prim_spec.
Proof.
start_function. rename H into Hprecon_1.
pose proof inf_repable as inf_repable.
assert (size_repable: repable_signed SIZE). unfold repable_signed. unfold SIZE.
set (i:=Int.min_signed); compute in i; subst i.
set (i:=Int.max_signed); compute in i; subst i. lia.
(*replace all data_at_ with data_at Vundef*)
repeat rewrite data_at__tarray.
set (k:=default_val tint); compute in k; subst k.
forward_call (Tsh, v_key, (list_repeat (Z.to_nat 8) Vundef), inf).
forward_call (Tsh, v_parent, (list_repeat (Z.to_nat 8) Vundef), SIZE).
forward_call (Tsh, v_out, (list_repeat (Z.to_nat 8) Vundef), 0).
assert (Hrbound: 0 <= r < SIZE). apply vert_bound in Hprecon_1; auto.
forward.
assert (Hstarting_keys: forall i, 0 <= i < SIZE -> is_int I32 Signed (Znth i (upd_Znth r (list_repeat (Z.to_nat SIZE) (Vint (Int.repr inf))) (Vint (Int.repr 0))))). {
  intros. unfold is_int. destruct (Z.eq_dec i r).
  +subst i. rewrite upd_Znth_same. auto. rewrite Zlength_list_repeat; lia.
  +rewrite Znth_upd_Znth_diff; auto. rewrite Znth_list_repeat_inrange by lia. auto.
}
replace (upd_Znth r (list_repeat (Z.to_nat SIZE) (Vint (Int.repr inf))) (Vint (Int.repr 0))) with
  (map (fun x => Vint (Int.repr x)) (upd_Znth r (list_repeat (Z.to_nat SIZE) inf) 0)) in *.
2: rewrite (upd_Znth_map (fun x => Vint (Int.repr x)) r (list_repeat (Z.to_nat SIZE) inf)); auto.
set (starting_keys:=map (fun x => Vint (Int.repr x)) (upd_Znth r (list_repeat (Z.to_nat SIZE) inf) 0)) in *.
assert (HZlength_starting_keys: Zlength starting_keys = SIZE). {
  unfold starting_keys. rewrite Zlength_map. rewrite Zlength_upd_Znth. rewrite Zlength_list_repeat; lia.
}
assert (H_SIZE_pos: 0 <= SIZE < Int.max_signed). unfold SIZE. unfold SIZE; set (j:=Int.max_signed); compute in j; lia.
(*push all vertices into priq*)
forward_for_simple_bound SIZE
  (EX i : Z,
    PROP ()
    LOCAL (
      lvar _pq (tarray tint 8) v_pq; lvar _out (tarray tint 8) v_out;
      lvar _parent (tarray tint 8) v_parent; lvar _key (tarray tint 8) v_key;
      temp _graph (pointer_val_val gptr); temp _r (Vint (Int.repr r));
      temp _msf (pointer_val_val mstptr)
    )
    SEP (
      data_at Tsh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr 0))) v_out;
      data_at Tsh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr SIZE))) v_parent;
      data_at Tsh (tarray tint SIZE) starting_keys v_key;
      data_at Tsh (tarray tint 8) (sublist 0 i starting_keys ++ sublist i SIZE (list_repeat (Z.to_nat 8) Vundef)) v_pq;
      undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr);
      undirected_matrix sh (graph_to_symm_mat edgeless_graph') (pointer_val_val mstptr))
  )%assert.
entailer!. (*precon taken care of*)
(*loop*)
forward.
assert (Znth i starting_keys = Vint (Int.repr (Znth i (upd_Znth r (list_repeat (Z.to_nat SIZE) inf) 0)))). {
  unfold starting_keys. rewrite Znth_map; auto.
  rewrite Zlength_upd_Znth. rewrite Zlength_list_repeat; lia.
}
forward_call (v_pq, i, Znth i (upd_Znth r (list_repeat (Z.to_nat SIZE) inf) 0), sublist 0 i starting_keys ++ sublist i SIZE (list_repeat (Z.to_nat 8) Vundef)).
split. rewrite <- SIZE_priq; auto. unfold weight_inrange_priq.
destruct (Z.eq_dec i r). subst i. rewrite upd_Znth_same. split. pose proof Int.min_signed_neg; lia.
rewrite <- inf_priq, inf_literal; lia. rewrite Zlength_list_repeat; lia.
rewrite upd_Znth_diff, Znth_list_repeat_inrange. rewrite <- inf_priq. pose proof inf_repable. unfold repable_signed in H1. lia.
lia. rewrite Zlength_list_repeat; lia. rewrite Zlength_list_repeat; lia. auto.
entailer!. unfold priq_arr_utils.SIZE.
rewrite upd_Znth_app2. rewrite Zlength_sublist, Z.sub_0_r, Z.sub_diag; try lia.
rewrite (sublist_split i (i+1) SIZE). rewrite (sublist_one i (i+1)). rewrite upd_Znth_app1.
rewrite upd_Znth0. rewrite app_assoc.
rewrite (sublist_split 0 i (i+1)). rewrite (sublist_one i (i+1)). rewrite <- H0. entailer!.
all: try lia.
rewrite Zlength_cons, Zlength_nil; lia.
rewrite Zlength_list_repeat. unfold SIZE in H; lia. lia.
unfold SIZE in *; rewrite Zlength_list_repeat; lia.
rewrite Zlength_sublist. rewrite Zlength_sublist. lia. lia. rewrite Zlength_list_repeat; unfold SIZE; lia. lia. lia.
rewrite sublist_nil, app_nil_r, sublist_same; try lia.
(*one last thing for convenience*)
rewrite <- (map_list_repeat (fun x => Vint (Int.repr x))).
rewrite <- (map_list_repeat (fun x => Vint (Int.repr x))).
pose proof (@fin inf SIZE g (sound_MatrixUGraph g)) as fg.
(*whew! all setup done!*)
(*now for the pq loop*)
forward_loop (
  EX mst':G,
  EX fmst': FiniteGraph mst',
  EX parents: list V,
  EX keys: list DE, (*can give a concrete definition in SEP, but it leads to shenanigans during entailer*)
  EX pq_state: list V, (*can give a concrete definition in SEP, but it leads to shenanigans during entailer*)
  EX popped_vertices: list V,
  EX unpopped_vertices: list V,
    PROP (
      (*graph stuff*)
      is_partial_lgraph mst' g;
      uforest' mst';
      (*about the lists*)
      Permutation (popped_vertices++unpopped_vertices) (VList g);
      forall v, 0 <= v < SIZE -> 0 <= Znth v parents <= SIZE;
      forall v, 0 <= v < SIZE -> Znth v keys = if V_EqDec v r then 0 else elabel g (eformat (v, Znth v parents));
      forall v, 0 <= v < SIZE -> Znth v pq_state = if in_dec V_EqDec v popped_vertices then Z.add inf 1 else Znth v keys;
      forall v, 0 <= v < SIZE -> 0 <= Znth v parents < SIZE ->
          (evalid g (eformat (v, Znth v parents)) /\ (*together you form a valid edge in g*)
          (exists i, 0<=i<Zlength popped_vertices /\ Znth i popped_vertices = Znth v parents /\ i < find popped_vertices v 0) /\ (*your parent has been popped, only time parents is updated, and you weren't in it when it was*)
          (forall u, In u (sublist 0 (find popped_vertices v 0) popped_vertices) -> elabel g (eformat (v, Znth v parents)) <= elabel g (eformat (u,v))) (*your current parent is the lowest among the popped, until you're popped too*) (*<-used for proving weight invar below*)
          );
      forall v, 0 <= v < SIZE -> Znth v parents = SIZE -> forall u, In u (sublist 0 (find popped_vertices v 0) popped_vertices) -> ~adjacent g u v;
      (*mst specific*)
      Permutation (EList mst') (map (fun v => eformat (v, Znth v parents)) (filter (fun v => Znth v parents <? SIZE) popped_vertices));
      forall u v, In u popped_vertices -> In v popped_vertices -> (connected g u v <-> connected mst' u v);
      (*the following two are yuck...*)
      popped_vertices = nil -> r = find pq_state (fold_right Z.min (hd 0 pq_state) pq_state) 0;
      popped_vertices <> nil -> hd_error popped_vertices = Some r;
      (*misc*)
      forall u v, In u unpopped_vertices -> ~ adjacent mst' u v;
      (*weight*)
      (* at the point of being popped, you had the lowest weight of all potential branches *)
      forall v u1 u2, In v popped_vertices -> 0 <= Znth v parents < SIZE ->
        vvalid g u2 ->
        In u1 (sublist 0 (find popped_vertices v 0) popped_vertices) ->
        ~ In u2 (sublist 0 (find popped_vertices v 0) popped_vertices) ->
        elabel g (eformat (v, Znth v parents)) <= elabel g (eformat (u1,u2))
    )
    LOCAL (
      lvar _pq (tarray tint 8) v_pq; lvar _out (tarray tint 8) v_out;
      lvar _parent (tarray tint 8) v_parent; lvar _key (tarray tint 8) v_key;
      temp _graph (pointer_val_val gptr); temp _r (Vint (Int.repr r));
      temp _msf (pointer_val_val mstptr)
    )
    SEP (
      data_at Tsh (tarray tint SIZE) (map (fun x => if in_dec V_EqDec x popped_vertices
        then (Vint (Int.repr 1)) else (Vint (Int.repr 0))) (nat_inc_list (Z.to_nat SIZE))) v_out;
      data_at Tsh (tarray tint SIZE) (map (fun x => Vint (Int.repr x)) parents) v_parent;
      data_at Tsh (tarray tint SIZE) (map (fun x => Vint (Int.repr x)) keys) v_key;
      data_at Tsh (tarray tint SIZE) (map (fun x => Vint (Int.repr x))
        pq_state) v_pq;
      undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr);
      undirected_matrix sh (graph_to_symm_mat edgeless_graph') (pointer_val_val mstptr)
    )
  )
break: (
  EX mst:G,
  EX fmst: FiniteGraph mst,
  EX popped_vertices: list V,
  EX parents: list V,
  EX keys: list DE,
    PROP (
      is_partial_lgraph mst g;
      uforest' mst;
      Permutation popped_vertices (VList mst);
      forall v, 0 <= v < SIZE -> 0 <= Znth v parents < SIZE ->
          (evalid g (eformat (v, Znth v parents)) /\ (*together you form a valid edge in g*)
          (exists i, 0<=i<Zlength popped_vertices /\ Znth i popped_vertices = Znth v parents
            /\ i < find popped_vertices v 0) /\ (*your parent has been popped, only time parents is updated, and you weren't in it when it was*)
          (forall u, In u (sublist 0 (find popped_vertices v 0) popped_vertices) -> elabel g (eformat (v, Znth v parents)) <= elabel g (eformat (u,v))) (*your current parent is the lowest among the popped, until you're popped too*) (*<-used for proving weight invar below*)
          );
      forall v, 0 <= v < SIZE -> Znth v parents = SIZE -> forall u, In u (sublist 0 (find popped_vertices v 0) popped_vertices) -> ~adjacent g u v;
      (*something about weight*)
      Permutation (EList mst) (map (fun v => eformat (v, Znth v parents)) (filter (fun v => Znth v parents <? SIZE) popped_vertices));
      spanning mst g;
      hd_error popped_vertices = Some r; (*<-idk if necessary, just putting it in in case*)
      (*weight*)
      forall v u1 u2, In v popped_vertices -> 0 <= Znth v parents < SIZE ->
        vvalid g u2 ->
        In u1 (sublist 0 (find popped_vertices v 0) popped_vertices) ->
        ~ In u2 (sublist 0 (find popped_vertices v 0) popped_vertices) ->
        elabel g (eformat (v, Znth v parents)) <= elabel g (eformat (u1,u2));
      forall v, 0 <= v < SIZE -> 0 <= Znth v parents <= SIZE
    )
    LOCAL (
      lvar _pq (tarray tint 8) v_pq; lvar _out (tarray tint 8) v_out;
      lvar _parent (tarray tint 8) v_parent; lvar _key (tarray tint 8) v_key;
      temp _graph (pointer_val_val gptr); temp _r (Vint (Int.repr r));
      temp _msf (pointer_val_val mstptr)
    )
    SEP (
      data_at Tsh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr 1))) v_out;
      data_at Tsh (tarray tint SIZE) (map (fun x => Vint (Int.repr x)) parents) v_parent;
      data_at Tsh (tarray tint SIZE) (map (fun x => Vint (Int.repr x)) keys) v_key;
      data_at Tsh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr (inf+1)))) v_pq;
      undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr);
      undirected_matrix sh (graph_to_symm_mat edgeless_graph') (pointer_val_val mstptr)
    )
  )
%assert.
(****PRECON****) {
  admit.
}
(****MAIN LOOP****) {
admit.
}
(*POST-LOOP*) {
clear Hstarting_keys HZlength_starting_keys starting_keys.
Intros mst fmst popped_vertices parents keys.
rename H into Hinv_1; rename H0 into Hinv_2;
rename H1 into Hinv_3; rename H2 into Hinv_4;
rename H3 into Hinv_5; rename H4 into Hinv_6;
rename H5 into Hinv_7; rename H6 into Hinv_8;
rename H7 into Hinv_9; rename H8 into Hinv_10.
(*Do the minimum proof here*)
assert (Hmst_spanning: labeled_spanning_uforest mst g). {
  split. split. apply Hinv_1. split. apply Hinv_2. apply Hinv_7.
  split. unfold preserve_vlabel; intros. destruct vlabel. destruct vlabel. auto.
  unfold preserve_elabel; intros. apply Hinv_1. auto.
}
assert (minimum_spanning_forest mst g). {
split. auto.
(*minimality proof*)
set (mst_list:=(map (fun v : Z => eformat (v, Znth v parents))
              (filter (fun v : Z => Znth v parents <? SIZE) popped_vertices))).
assert (HNoDup_mst_list: NoDup mst_list). {
  apply (Permutation_NoDup (l:=EList mst)). unfold mst_list; apply Hinv_6. apply NoDup_EList.
}
assert (prim_induct: forall lmst lsame (t: G) {ft: FiniteGraph t},
  labeled_spanning_uforest t g ->
  lmst = filter (fun e => negb (in_dec E_EqDec e (EList t))) mst_list ->
  lsame = filter (fun e => in_dec E_EqDec e (EList t)) mst_list ->
  (exists lt, Permutation (lt ++ lsame) (EList t) /\ Zlength lt = Zlength lmst /\
  forall i, 0 <= i < Zlength lmst -> elabel g (Znth i lmst) <= elabel g (Znth i lt))). {
induction lmst; intros.
++ (*nil case*)
exists nil. split3.
2: auto. 2: { intros. rewrite Zlength_nil in H2. lia. }
rewrite app_nil_l. rewrite H1. apply NoDup_Permutation.
apply NoDup_filter. auto. apply NoDup_EList.
intros. set (tlist:=EList t); fold tlist. fold tlist in H0; fold tlist in H1.
rewrite filter_In; split; intros.
destruct H2. destruct (in_dec E_EqDec x tlist). auto. simpl in H3; inversion H3.
split. 2: destruct (in_dec E_EqDec x tlist); auto.
assert (Permutation (lsame++[]) (EList mst)). { rewrite H0; rewrite H1.
  apply (Permutation_trans (l':=mst_list)). 2: apply Permutation_sym; unfold mst_list; auto.
  apply filter_list_Permutation. auto.
} rewrite app_nil_r in H3.
(*Copy past from kruskal:
u is connected to v in all graphs. So if u-v is not in lsame, exists another path in mst
Then, exists a list of edges l, fits_upath mst l p.
All of l's edges must belong in EList mst => mst_list => lsame.
Thus, incl l t. Which means connected_by_path t p u v.
But (u,v) is an alternative path in t. contra*)
destruct x as [u v].
unfold tlist in H2. rewrite EList_evalid in H2.
assert (connected_by_path t [u;v] u v). {
  unfold connected_by_path; simpl. split3; try auto. split.
  apply evalid_adjacent; auto. apply evalid_vvalid in H2; apply H2.
}
assert (connected mst u v). apply Hmst_spanning. apply H. exists [u;v]. auto.
destruct H5 as [p ?]. assert (exists l, fits_upath mst l p).
apply connected_exists_list_edges in H5. auto. destruct H6 as [l ?].
assert (fits_upath t l p). { apply (fits_upath_transfer' p l mst t).
  intros. do 2 rewrite vert_bound. split; lia.
  intros. apply (fits_upath_evalid mst p l) in H7; auto. rewrite <- EList_evalid in H7.
  apply (Permutation_in (l':=lsame)) in H7. rewrite H1, filter_In in H7.
  destruct H7. destruct (in_dec E_EqDec e tlist). unfold tlist in i.
  rewrite <- EList_evalid. apply i. inversion H8.
  apply Permutation_sym; apply H3.
  intros. rewrite (@src_fst _ _ _ (sound_MatrixUGraph mst)); auto.
  rewrite (@src_fst _ _ _ (sound_MatrixUGraph t)); auto.
  intros. rewrite (@dst_snd _ _ _ (sound_MatrixUGraph mst)); auto.
  rewrite (@dst_snd _ _ _ (sound_MatrixUGraph t)); auto. auto.
}
assert (incl l mst_list). unfold incl; intros. apply (Permutation_in (l:=EList mst)).
unfold mst_list; auto. rewrite EList_evalid. apply (fits_upath_evalid mst p l); auto.
apply H8. apply (forest_edge' p l t). apply H.
apply evalid_strong_evalid; auto.
apply connected_exists_list_edges'. intros. apply (valid_upath_vvalid mst) in H9.
rewrite vert_bound in H9; rewrite vert_bound; lia. apply H5.
exists l; auto.
rewrite (@src_fst _ _ _ (sound_MatrixUGraph t)) by auto. simpl; apply H5.
rewrite (@dst_snd _ _ _ (sound_MatrixUGraph t)) by auto. simpl; apply H5.
auto.
++ (************inductive step************)
(*we find a matching edge b in t for a, then show that elabel mst a <= elabel t b*)
set (tlist:=EList t).
assert (In a mst_list /\ ~ In a (EList t)). {
  assert(In a (a::lmst)). left; auto. rewrite H0, filter_In in H2. destruct H2.
  split. apply H2. fold tlist; fold tlist in H3; destruct (in_dec E_EqDec a tlist).
  inversion H3. auto.
} destruct H2.
assert (evalid mst a). rewrite <- EList_evalid. apply (Permutation_in (l:=mst_list)).
apply Permutation_sym; unfold mst_list. apply Hinv_6. auto.
assert (exists v i, a = eformat (v, Znth v parents) /\ evalid g (eformat (v, Znth v parents)) /\
            0 <= i < Zlength popped_vertices /\
            Znth i popped_vertices = Znth v parents /\ i < find popped_vertices v 0). {
  unfold mst_list in H2. apply list_in_map_inv in H2. destruct H2 as [v [? ?]].
  rewrite filter_In in H5. destruct H5. rewrite Z.ltb_lt in H6.
  assert (0 <= v < SIZE). rewrite <- (vert_bound mst), <- VList_vvalid; apply (Permutation_in (l:=popped_vertices)).
  apply Hinv_3. auto.
  assert (evalid g (eformat (v, Znth v parents)) /\
         (exists i : Z,
            0 <= i < Zlength popped_vertices /\
            Znth i popped_vertices = Znth v parents /\ i < find popped_vertices v 0) /\
         (forall u : V,
          In u (sublist 0 (find popped_vertices v 0) popped_vertices) ->
          elabel g (eformat (v, Znth v parents)) <= elabel g (eformat (u, v)))).
  apply (Hinv_4 v). auto. split. apply Hinv_10; auto. auto.
  destruct H8 as [? [? ?]]. clear H10. destruct H9 as [i [? [? ?]]].
  exists v. exists i. split. auto. split3; auto. }
destruct H5 as [v [i [? [? [? [? ?]]]]]].
assert (0 <= v < SIZE /\ 0 <= Znth v parents < SIZE). repeat rewrite <- (vert_bound g). apply eformat_evalid_vvalid in H6. apply H6.
destruct H10.
assert (connected t (Znth v parents) v). {
  apply H. apply Hmst_spanning. exists [Znth v parents; v]. unfold connected_by_path; simpl.
  split; auto. split. rewrite eformat_adj. rewrite eformat_symm. rewrite H5 in H4; auto.
  rewrite vert_bound; auto.
}
destruct H12 as [p ?].
(*use the simple one for good measure*)
apply connected_by_upath_exists_simple_upath in H12. clear p. destruct H12 as [p [? ?]].
(*then, since a is not evalid in t, there must exist l, fits_upath t l p and ~ In a l*)
assert (exists l, fits_upath t l p). apply connected_exists_list_edges in H12; auto.
destruct H14 as [l ?].
assert (~ In a l). unfold not; intros. apply (fits_upath_evalid t p l a) in H15; auto. rewrite EList_evalid in H3; auto.
(*get the new form of path_partition out and use it to find an edge in l such that
one vertex is in popped, one isn't
NOTE: My invariant declares ~ In v (sublist 0 i popped_vertices) instead of (i+1).
For simplicity, show it holds for (i+1) too here, to not further complicate the invariant*)
set (partition:=sublist 0 (find popped_vertices v 0) popped_vertices).
assert (~ In v partition). unfold partition. apply find_sublist_NoDup_notIn.
  apply (Permutation_NoDup (l:=VList mst)). apply Permutation_sym; apply Hinv_3. apply NoDup_VList.
assert (In (Znth v parents) partition). rewrite <- H8. unfold partition.
  pose proof (find_lbound popped_vertices v 0). apply Z.le_lteq in H17. destruct H17.
  apply Znth_In_sublist. lia. rewrite <- (Z.add_0_r (Zlength popped_vertices)).
  apply (find_In_ubound).
  apply (Permutation_in (l:=VList mst)). apply Permutation_sym; apply Hinv_3.
  rewrite VList_vvalid, vert_bound; lia. lia. lia.
assert (exists v1 v2 : V, In v1 p /\ In v2 p /\ In v1 partition /\ ~ In v2 partition /\ adjacent t v1 v2).
apply (path_partition_checkpoint2 t partition) in H12; auto.
destruct H18 as [v1 [v2 [? [? [? [? ?]]]]]]. rewrite eformat_adj in H22. set (b:=(eformat (v1,v2))).
assert (v1 <> v2). unfold not; intros; subst v2; contradiction.
assert (In b l). apply (bridge_must_be_crossed t b v1 v2 p l); auto.
  apply forest_adj_bridge. apply H. apply eformat_adj'; auto.
(*now assert elabel b < elabel a*)
assert (evalid t b). apply (fits_upath_evalid t p l); auto.
assert (elabel g a <= elabel g b). {
  unfold b. rewrite H5. apply Hinv_9; auto.
  apply (Permutation_in (l:=VList mst)). apply Permutation_sym. apply Hinv_3. rewrite VList_vvalid, vert_bound; auto.
  apply eformat_evalid_vvalid in H22. rewrite vert_bound; repeat rewrite vert_bound in H22. apply H22. }
(*to handle spanning, we split l into l1++b++l2, p into p1++p2, and replace b with a*)
(*set (swap:=adde(eremove...)). Use*).

}
intros.
pose proof (@fin _ _ _ (@sound_MatrixUGraph inf SIZE t')) as ft'.
set (tlist := EList t'). (*slowdown if you directly use Elist t'*)
set (lmst := filter (fun e => negb (in_dec E_EqDec e tlist)) mst_list).
set (lsame := filter (fun e => in_dec E_EqDec e tlist) mst_list).
assert (incl lsame mst_list). { unfold lsame. apply filter_incl. }
assert (incl lsame tlist). { unfold lsame, incl. intros.
  rewrite filter_In in H1. destruct H1. destruct (in_dec E_EqDec a tlist). auto.
  simpl in H2. inversion H2.
}
assert (incl lmst mst_list). { unfold lmst. apply filter_incl. }
assert (forall a, In a lmst -> ~ In a tlist). {

  unfold lmst; intros. rewrite filter_In in H3. destruct H3.
  destruct (in_dec E_EqDec a tlist). simpl in H4. inversion H4. auto.
}
assert (NoDup lmst). { apply NoDup_filter. auto. }
assert (NoDup lsame). { apply NoDup_filter. auto. }
assert (forall x : E, In x lmst -> ~ In x lsame). {
  unfold not; intros. apply H1 in H8. apply H3 in H7. contradiction.
}
assert (Permutation (lmst++lsame) mst_list). {
  apply NoDup_Permutation. apply NoDup_app_inv; auto. auto.
  unfold lmst; unfold lsame; intros. split; intros.
  apply in_app_or in H8. destruct H8; rewrite filter_In in H8; apply H8.
  apply in_or_app. do 2 rewrite filter_In. destruct (in_dec E_EqDec x tlist).
  right; split; auto.
  left; split; auto.
}
assert (exists lt, Permutation (lt ++ lsame) tlist /\ Zlength lt = Zlength lmst /\
  forall i, 0 <= i < Zlength lmst -> elabel mst (Znth i lmst) <= elabel t' (Znth i lt)). {
(*
  lmst should be sorted based on popped_vertices
  then we induct on lmst: (to get an lt where elabel g (Znth i lmst) <= elabel g (Znth i lt))
    nil case something something
    induct case: a::l => a is the earliest edge that was added,
      so map (fun u => (u, Znth u parents)) (sublist 0 (find popped_vertices a) popped_vertices) is in t'
      this means
  do the same as kruskal: (sum (lsame++lmst) <= sum (ldiff))
*)

  admit.
}
destruct H9 as [lt [? [? ?]]].
rewrite (sum_LE_equiv t' (lt++lsame)). 2: {
  apply Permutation_sym. unfold tlist in H9.
  (*apply H9.*) apply (Permutation_trans H9). apply NoDup_Permutation.
  apply NoDup_EList. apply NoDup_EList. intros; do 2 rewrite EList_evalid; split; auto.
}
rewrite (sum_LE_equiv mst (lmst++lsame)). 2: {
  apply Permutation_sym. apply (Permutation_trans (l':=mst_list)); auto.
  unfold mst_list. (*apply Hinv_6.*) apply Permutation_sym in Hinv_6.
  apply (Permutation_trans Hinv_6). apply NoDup_Permutation.
  apply NoDup_EList. apply NoDup_EList. intros; do 2 rewrite EList_evalid; split; auto.
}
do 2 rewrite map_app. do 2 rewrite fold_left_app.
replace (map (elabel mst) lsame) with (map (elabel g) lsame).
replace (map (elabel t') lsame) with (map (elabel g) lsame).
apply fold_left_Zadd_diff_accum.
apply fold_left_Zadd_comp. do 2 rewrite Zlength_map. auto.
rewrite Zlength_map. intros.
rewrite Znth_map by lia. rewrite Znth_map by lia. apply H11. auto.
apply map_ext_in; intros. symmetry; apply H.
rewrite <- EList_evalid. apply (Permutation_in (l:=lt++lsame)). unfold tlist in H9. apply H9.
apply in_or_app; right; auto.
apply map_ext_in; intros. symmetry; apply Hinv_1.
rewrite <- EList_evalid. apply (Permutation_in (l:=lmst++lsame)).
apply (Permutation_trans (l':=mst_list)). auto. apply Permutation_sym; unfold mst_list; apply Hinv_6.
apply in_or_app; right; auto.
}
(*Should we bother with filling a matrix for it? The original Prim doesn't bother
  Well I guess we need to return the graph somehow, as parents is a local array so we need to pass it out
*)
(*
forward_for_simple_bound SIZE (
  EX i : Z,
  EX t : G,
  EX ft: FiniteGraph t,
  PROP (is_partial_lgraph t mst';
        forall j, 0 <= j < i -> In 
       )
  LOCAL (
    lvar _pq (tarray tint 8) v_pq; lvar _out (tarray tint 8) v_out;
    lvar _parent (tarray tint 8) v_parent; lvar _key (tarray tint 8) v_key;
    temp _graph (pointer_val_val gptr); temp _r (Vint (Int.repr r));
    temp _msf (pointer_val_val mstptr)
  )
  SEP (
    data_at Tsh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr 1))) v_out;
    data_at Tsh (tarray tint SIZE) (map (fun x : Z => Vint (Int.repr x)) parents) v_parent;
    data_at Tsh (tarray tint SIZE) (map (fun x : Z => Vint (Int.repr x)) keys) v_key;
    data_at Tsh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr (inf + 1)))) v_pq;
    undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr);
    undirected_matrix sh (graph_to_symm_mat t) (pointer_val_val mstptr)
  )
)%assert.
*)
admit.
}
Abort.