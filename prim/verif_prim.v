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

Lemma find_app_le:
forall l1 l2 v ans, find l1 v ans <= find (l1++l2) v ans.
Proof.
induction l1; intros.
rewrite app_nil_l. simpl. apply find_lbound.
simpl. destruct (initial_world.EqDec_Z a v). lia.
do 2 rewrite find_accum_add1. specialize IHl1 with l2 v ans. lia.
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

(**Initialisation functions**)

Lemma body_initialise_list: semax_body Vprog Gprog f_initialise_list initialise_list_spec.
Proof.
start_function.
forward_for_simple_bound SIZE
    (EX i : Z,
     PROP ()
     LOCAL (temp _list arr; temp _a (Vint (Int.repr a)))
     SEP (
      data_at sh (tarray tint SIZE) (list_repeat (Z.to_nat i) (Vint (Int.repr a))++(sublist i SIZE old_list)) arr
    ))%assert.
unfold SIZE; set (j:=Int.max_signed); compute in j; lia.
entailer!. rewrite app_nil_l. rewrite sublist_same by lia. entailer!.
(*loop*)
forward. entailer!.
rewrite (sublist_split i (i+1)) by lia.
replace (sublist i (i+1) old_list) with [Znth i old_list]. simpl.
rewrite upd_Znth_char.
rewrite <- list_repeat_app' by lia.
rewrite <- app_assoc. simpl. auto.
apply Zlength_list_repeat; lia.
symmetry; apply sublist_one; lia.
(*postcon*)
entailer!. rewrite sublist_nil. rewrite app_nil_r. entailer!.
Qed.

Lemma body_initialise_matrix: semax_body Vprog Gprog f_initialise_matrix initialise_matrix_spec.
Proof.
start_function.
assert (HZlength_nat_inc_list: SIZE = Zlength (nat_inc_list (Datatypes.length old_contents))).
rewrite nat_inc_list_Zlength. rewrite <- Zlength_correct. lia.
forward_for_simple_bound SIZE
    (EX i : Z,
     PROP ()
     LOCAL (temp _graph arr; temp _a (Vint (Int.repr a)))
     SEP (
      iter_sepcon.iter_sepcon (fun i => data_at sh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr a))) (list_address arr i SIZE))
        (sublist 0 i (nat_inc_list (Z.to_nat (Zlength old_contents))));
      iter_sepcon.iter_sepcon (list_rep sh SIZE arr old_contents)
        (sublist i SIZE (nat_inc_list (Z.to_nat (Zlength old_contents))))
    ))%assert.
unfold SIZE; set (j:=Int.max_signed); compute in j; lia.
rewrite (graph_unfold _ _ _ 0). rewrite H. entailer!.
replace (list_rep sh SIZE arr old_contents 0) with (iter_sepcon.iter_sepcon (list_rep sh SIZE arr old_contents) [0]).
2: { simpl. rewrite sepcon_emp. auto. }
rewrite <- iter_sepcon.iter_sepcon_app.
(*ok this is not good, make a generic scalable lemma*) simpl. entailer!.
rewrite H; unfold SIZE; lia.
(*inner loop*)
replace (sublist i SIZE (nat_inc_list (Z.to_nat (Zlength old_contents))))
  with ([i]++sublist (i+1) SIZE (nat_inc_list (Z.to_nat (Zlength old_contents)))).
2: { rewrite (sublist_split i (i+1)). rewrite (sublist_one i). rewrite nat_inc_list_i; auto.
rewrite Z2Nat.id; lia. lia. rewrite nat_inc_list_Zlength, Z2Nat.id; lia. lia. lia. rewrite nat_inc_list_Zlength, Z2Nat.id; lia. }
rewrite iter_sepcon.iter_sepcon_app. Intros.
forward_for_simple_bound SIZE
    (EX j : Z,
     PROP ()
     LOCAL (temp _i (Vint (Int.repr i)); temp _graph arr; temp _a (Vint (Int.repr a)))
     SEP (
      iter_sepcon.iter_sepcon (fun i => data_at sh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr a))) (list_address arr i SIZE))
        (sublist 0 i (nat_inc_list (Z.to_nat (Zlength old_contents))));
      data_at sh (tarray tint SIZE) (list_repeat (Z.to_nat j) (Vint (Int.repr a))++sublist j SIZE (map (fun x => Vint (Int.repr x)) (Znth i old_contents))) (list_address arr i SIZE);
      iter_sepcon.iter_sepcon (list_rep sh SIZE arr old_contents)
        (sublist (i+1) SIZE (nat_inc_list (Z.to_nat (Zlength old_contents))))
    ))%assert.
unfold SIZE; set (j:=Int.max_signed); compute in j; lia.
entailer!. simpl. rewrite sepcon_emp. unfold list_rep. rewrite sublist_same. entailer!.
auto. rewrite Zlength_map. symmetry; apply H0. apply Znth_In; lia.
(*inner loop body*)
rename i0 into j. unfold list_address.
assert (Zlength (map (fun x => Vint (Int.repr x)) (Znth i old_contents)) = SIZE).
rewrite Zlength_map. apply H0. apply Znth_In; lia.
assert_PROP (field_compatible (tarray tint SIZE) [ArraySubsc j] (offset_val (i * sizeof (tarray tint SIZE)) arr)). entailer!.
assert_PROP(force_val (sem_add_ptr_int tint Signed (force_val (sem_add_ptr_int (tarray tint SIZE) Signed arr (Vint (Int.repr i))))
 (Vint (Int.repr j))) = (field_address (tarray tint SIZE) [ArraySubsc j] (offset_val (i * sizeof (tarray tint SIZE)) arr))). {
  entailer!. symmetry; rewrite field_address_offset. simpl. unfold offset_val.
  destruct arr; simpl; auto.
  rewrite Ptrofs.add_assoc. rewrite (Ptrofs.add_signed (Ptrofs.repr (i*32))).
  rewrite Ptrofs.signed_repr. rewrite Ptrofs.signed_repr. rewrite Z.add_0_l. rewrite Z.mul_comm. auto.
  all: set (k:=Ptrofs.min_signed); compute in k; subst k; set (k:=Ptrofs.max_signed); compute in k; subst k.
  rewrite Z.add_0_l. unfold SIZE in H3. lia. unfold SIZE in H2; lia. auto.
}
(*g[i][j] = a*)
forward.
unfold list_address.
replace (upd_Znth j (list_repeat (Z.to_nat j) (Vint (Int.repr a)) ++ sublist j SIZE (map (fun x => Vint (Int.repr x)) (Znth i old_contents))) (Vint (Int.repr a)))
with (list_repeat (Z.to_nat (j + 1)) (Vint (Int.repr a)) ++ sublist (j + 1) SIZE (map (fun x => Vint (Int.repr x)) (Znth i old_contents))).
entailer!.
rewrite <- list_repeat_app' by lia. rewrite <- app_assoc. rewrite upd_Znth_app2.
rewrite Zlength_list_repeat by lia. rewrite Z.sub_diag by lia.
rewrite (sublist_split j (j+1)) by lia. rewrite (sublist_one j (j+1)) by lia. simpl. rewrite upd_Znth0 by lia. auto.
rewrite Zlength_list_repeat by lia. rewrite Zlength_sublist; lia.
(*inner loop postcon*)
entailer!.
rewrite (sublist_split 0 i (i+1)) by lia. rewrite (sublist_one i (i+1)) by lia. rewrite nat_inc_list_i.
rewrite iter_sepcon.iter_sepcon_app. rewrite sublist_nil. rewrite app_nil_r. entailer!. simpl. rewrite sepcon_emp; auto.
rewrite <- Zlength_correct. lia.
(*postcon*)
entailer!. rewrite (graph_unfold _ _ _ 0). repeat rewrite sublist_nil. repeat rewrite iter_sepcon.iter_sepcon_nil.
rewrite sepcon_emp. rewrite sepcon_comm. rewrite sepcon_emp.
rewrite Z.add_0_l. rewrite (sublist_split 0 1 (SIZE)). rewrite sublist_one. rewrite nat_inc_list_i.
rewrite iter_sepcon.iter_sepcon_app. rewrite Zlength_list_repeat. replace (Datatypes.length old_contents) with (Z.to_nat SIZE).
rewrite <- (map_list_repeat (fun x => Vint (Int.repr x))).
unfold list_rep. rewrite Znth_list_repeat_inrange.
(*we can just simpl; entailer! here, but that relies on our SIZE being fixed at a small number, so providing the scalable proof*)
rewrite (iter_sepcon.iter_sepcon_func_strong _ (fun index : Z =>
       data_at sh (tarray tint SIZE)
         (map (fun x : Z => Vint (Int.repr x)) (Znth index (list_repeat (Z.to_nat SIZE) (list_repeat (Z.to_nat SIZE) a))))
         (list_address arr index SIZE)) (fun i : Z =>
   data_at sh (tarray tint SIZE) (map (fun x : Z => Vint (Int.repr x)) (list_repeat (Z.to_nat SIZE) a))
     (list_address arr i SIZE))). entailer!. simpl; entailer.
intros. replace (Znth x (list_repeat (Z.to_nat SIZE) (list_repeat (Z.to_nat SIZE) a))) with
(list_repeat (Z.to_nat SIZE) a); auto.
symmetry; apply Znth_list_repeat_inrange. apply sublist_In, nat_inc_list_in_iff in H2.
rewrite Z2Nat.id in H2; auto. unfold SIZE; lia.
(*remaining lias*)
unfold SIZE; lia. rewrite <- ZtoNat_Zlength. rewrite H; auto. unfold SIZE; lia. rewrite <- Zlength_correct, H; unfold SIZE; lia.
lia. rewrite <- HZlength_nat_inc_list; unfold SIZE; lia. lia. lia.
rewrite <- HZlength_nat_inc_list; unfold SIZE; lia. rewrite Zlength_list_repeat; unfold SIZE; lia.
Qed.

(******************PRIM'S***************)

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
          (exists i, 0<=i<Zlength popped_vertices /\ Znth i popped_vertices = Znth v parents /\
            i < find popped_vertices v 0) /\ (*your parent has been popped, only time parents is updated, and you weren't in it when it was*)
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
  Exists edgeless_graph'.
  Exists (@fin _ _ _ (sound_MatrixUGraph edgeless_graph')).
  Exists (list_repeat (Z.to_nat SIZE) SIZE).
  Exists (upd_Znth r (list_repeat (Z.to_nat SIZE) inf) 0).
  Exists (upd_Znth r (list_repeat (Z.to_nat SIZE) inf) 0).
  Exists (nil (A:=V)).
  Exists (VList g). rewrite app_nil_l.
  entailer!.
  split3. 3: split3. 5: split3. 7: split.
  +apply edgeless_partial_lgraph.
  +apply uforest'_edgeless_graph.
  +intros. rewrite Znth_list_repeat_inrange; lia.
  +intros. destruct (V_EqDec v r).
  hnf in e; subst v. rewrite upd_Znth_same. auto. rewrite Zlength_list_repeat; lia.
  unfold RelationClasses.complement, Equivalence.equiv in c. rewrite upd_Znth_diff.
  repeat rewrite Znth_list_repeat_inrange by lia. rewrite (@invalid_edge_weight _ _ _ (sound_MatrixUGraph g)); auto.
  unfold not; intros. rewrite <- eformat_adj in H11. apply adjacent_requires_vvalid in H11. destruct H11.
  rewrite vert_bound in H12. lia.
  rewrite Zlength_list_repeat; lia. rewrite Zlength_list_repeat; lia. auto.
  +intros. rewrite Znth_list_repeat_inrange in H11; lia.
  +(*because I've trouble using edgeless_graph_EList*) apply NoDup_Permutation. apply NoDup_EList. apply NoDup_nil.
  intros. rewrite EList_evalid. split; intros. pose proof (@edgeless_graph_evalid inf SIZE inf_rep SIZE_rep x); contradiction. contradiction.
  +intros. replace SIZE with priq_arr_utils.SIZE. rewrite find_src. auto. unfold priq_arr_utils.SIZE; auto. unfold priq_arr_utils.SIZE, SIZE; split.
  +unfold not; intros. destruct H11. destruct H11. destruct H11. pose proof (@edgeless_graph_evalid inf SIZE inf_rep SIZE_rep x); contradiction.
}
(****MAIN LOOP****) {
  clear Hstarting_keys HZlength_starting_keys starting_keys.
  Intros mst' fmst' parents keys pq_state popped_vertices unpopped_vertices.
  (*do a mass renaming for convenience*)
  rename H into Hinv_1; rename H0 into Hinv_2;
  rename H1 into Hinv_3; rename H2 into Hinv_4;
  rename H3 into Hinv_5; rename H4 into Hinv_6;
  rename H5 into Hinv_7; rename H6 into Hinv_8;
  rename H7 into Hinv_9; rename H8 into Hinv_10;
  rename H9 into Hinv_11; rename H10 into Hinv_12;
  rename H11 into Hinv_13; rename H12 into Hinv_14.
  assert_PROP (Zlength (map (fun x : Z => Vint (Int.repr x)) parents) = SIZE /\
              Zlength (map (fun x : Z => Vint (Int.repr x)) keys) = SIZE /\
              Zlength (map (fun x : Z => Vint (Int.repr x)) pq_state) = SIZE
  ). entailer!.
  repeat rewrite Zlength_map in H. destruct H as [HZlength_parents [HZlength_keys HZlength_pq_state]].
  assert (Hpopped_or_unpopped: forall v, vvalid g v -> In v popped_vertices \/ In v unpopped_vertices). {
    intros. apply in_app_or. apply (Permutation_in (l:=VList g)). apply Permutation_sym; auto. apply VList_vvalid; auto.
  }
  (*^^significant lag from the three entailers above*)
  assert (Hpopped_vvalid: forall v, In v popped_vertices -> vvalid g v). {
    intros. rewrite <- VList_vvalid. apply (Permutation_in (l:=popped_vertices++unpopped_vertices)).
    apply Hinv_3. apply in_or_app; left; auto.
  }
  assert (Hunpopped_vvalid: forall v, In v unpopped_vertices -> vvalid g v). {
    intros. rewrite <- VList_vvalid. apply (Permutation_in (l:=popped_vertices++unpopped_vertices)).
    apply Hinv_3. apply in_or_app; right; auto.
  }
  assert (priq_arr_utils.inrange_priq pq_state). {
    unfold priq_arr_utils.inrange_priq. rewrite Forall_forall. intros x Hx. rewrite <- inf_priq.
    rewrite In_Znth_iff in Hx. destruct Hx as [i [? ?]]. rewrite HZlength_pq_state in H. subst x.
    rewrite Hinv_6. 2: lia. destruct (in_dec V_EqDec i popped_vertices).
    pose proof inf_repable; unfold repable_signed in H0; lia.
    rewrite Hinv_5. 2: lia. destruct (V_EqDec i r). auto.
    split. apply weight_representable. apply (Z.le_trans _ inf). apply weight_inf_bound. lia.
  }
  replace (data_at Tsh (tarray tint SIZE) (map (fun x : Z => Vint (Int.repr x)) pq_state) v_pq)
    with (data_at Tsh (tarray tint priq_arr_utils.SIZE) (map Vint (map Int.repr pq_state)) v_pq).
  2: { unfold priq_arr_utils.SIZE, SIZE. rewrite list_map_compose. auto. }
  forward_call (v_pq, pq_state).
  forward_if.
  (*PROCEED WITH LOOP*) {
  assert (priq_arr_utils.isEmpty pq_state = Vzero). {
    destruct (priq_arr_utils.isEmptyTwoCases pq_state);
    rewrite H1 in H0; simpl in H0; now inversion H0.
  }
  forward_call (v_pq, pq_state). Intros u. rename H2 into Hu.
  (* u is the minimally chosen item from the
     "seen but not popped" category of vertices *)
  assert (0 <= u < SIZE). {
    rewrite Hu. rewrite <- HZlength_pq_state. apply find_range.
    apply min_in_list. apply incl_refl. destruct pq_state.
    rewrite Zlength_nil in HZlength_pq_state. lia.
    simpl. left; trivial.
  }
  assert (Hu_not_popped: ~ In u popped_vertices). { unfold not; intros.
    assert (Znth u pq_state < priq_arr_utils.inf + 1). apply (find_min_lt_inf u pq_state Hu H1).
    rewrite HZlength_pq_state; lia. rewrite <- inf_priq, Hinv_6 in H4 by lia.
    destruct (in_dec V_EqDec u popped_vertices). lia. contradiction.
  }
  assert (Hu_unpopped: In u unpopped_vertices). { destruct (Hpopped_or_unpopped u).
    rewrite (@vert_representable _ _ _ (sound_MatrixUGraph g)). auto. contradiction. auto.
  }
  forward.
  replace (upd_Znth u (map (fun x : V =>
    if in_dec V_EqDec x popped_vertices then Vint (Int.repr 1) else Vint (Int.repr 0))
    (nat_inc_list (Z.to_nat SIZE))) (Vint (Int.repr 1))) with (map (fun x : V =>
    if in_dec V_EqDec x (popped_vertices+::u) then Vint (Int.repr 1) else Vint (Int.repr 0))
    (nat_inc_list (Z.to_nat 8))).
  2: { unfold SIZE.
    apply list_eq_Znth. rewrite Zlength_upd_Znth. do 2 rewrite Zlength_map. auto.
    intros. rewrite Zlength_map in H3. rewrite nat_inc_list_Zlength in H3.
    destruct (Z.eq_dec i u). subst i.
    +rewrite upd_Znth_same. rewrite Znth_map.
    rewrite nat_inc_list_i. assert (In u (popped_vertices+::u)). apply in_or_app. right; simpl; auto.
    destruct (in_dec V_EqDec u (popped_vertices+::u)). auto. contradiction.
    lia. rewrite nat_inc_list_Zlength; lia.
    rewrite Zlength_map, nat_inc_list_Zlength; lia.
    +rewrite upd_Znth_diff. rewrite Znth_map. rewrite Znth_map. rewrite nat_inc_list_i.
    destruct (in_dec V_EqDec i (popped_vertices+::u));
    destruct (in_dec V_EqDec i popped_vertices). auto.
    apply in_app_or in i0; destruct i0. contradiction. destruct H4. symmetry in H4; contradiction. contradiction.
    assert (In i (popped_vertices+::u)). apply in_or_app. left; auto. contradiction.
    auto. auto. rewrite nat_inc_list_Zlength; auto. rewrite nat_inc_list_Zlength; auto.
    rewrite Zlength_map, nat_inc_list_Zlength; auto.
    rewrite Zlength_map, nat_inc_list_Zlength; auto.
    auto.
  }
  rewrite upd_Znth_map. rewrite upd_Znth_map. rewrite list_map_compose. (*pq state*)
  replace (Znth 0 pq_state) with (hd 0 pq_state). rewrite <- Hu. 2: { destruct pq_state. rewrite Zlength_nil in HZlength_pq_state; lia. simpl. rewrite Znth_0_cons. auto. }
  assert (Hur: popped_vertices = nil -> u = r). {
    intros. rewrite Hu. symmetry; apply Hinv_11. auto.
  }
  assert (Hu_min: forall v, 0 <= v < SIZE -> Znth u pq_state <= Znth v pq_state). {
    intros. rewrite Hu. rewrite Znth_find.
    apply fold_min. apply Znth_In. lia.
    apply fold_min_in_list. lia.
  }
  clear Hu. set (upd_pq_state:=upd_Znth u pq_state (priq_arr_utils.inf + 1)).
  (*for loop to update un-popped vertices' min weight.
  The result is every vertex who's NOT in popped_vertices and connected, as their weight maintained or lowered*)
  forward_for_simple_bound SIZE (
    EX i: Z,
    EX parents': list Z,
    EX keys': list Z,
    EX pq_state': list Z,
      PROP (
        (*if you were already popped (out=1) or not adjacent, nothing happens*)
        forall v, 0<=v<i -> (~adjacent g u v \/ In v (popped_vertices+::u)) -> (
          Znth v parents' = Znth v parents /\
          Znth v keys' = Znth v keys /\
          Znth v pq_state' = Znth v upd_pq_state);
        (*if you are still in pq and adjacent, you are updated*)
        forall v, 0<=v<i -> adjacent g u v -> ~ In v (popped_vertices+::u) -> (
          Znth v parents' = (if Z.ltb (elabel g (eformat (u,v))) (Znth v upd_pq_state) then u else Znth v parents) /\
          Znth v keys' = Z.min (elabel g (eformat (u,v))) (Znth v upd_pq_state) /\
          Znth v pq_state' = Z.min (elabel g (eformat (u,v))) (Znth v upd_pq_state));
        (*no change for those that haven't been checked*)
        forall v, i<=v<SIZE -> (
          Znth v parents' = Znth v parents /\
          Znth v keys' = Znth v keys /\
          Znth v pq_state' = Znth v upd_pq_state
        );
        forall v, 0 <= v < SIZE -> Int.min_signed <= Znth v keys' <= inf
        (*for convenience, unpopped and not u -> Znth v keys = Znth v pq_state'?*)
      )
      LOCAL (
        temp _u (Vint (Int.repr u)); temp _t'1 (isEmpty pq_state); lvar _pq (tarray tint 8) v_pq; lvar _out (tarray tint 8) v_out;
        lvar _parent (tarray tint 8) v_parent; lvar _key (tarray tint 8) v_key; temp _graph (pointer_val_val gptr);
        temp _r (Vint (Int.repr r)); temp _msf (pointer_val_val mstptr)
      )
      SEP (data_at Tsh (tarray tint SIZE) (map (fun x => Vint (Int.repr x)) pq_state') v_pq;
     data_at Tsh (tarray tint 8)
       (map
          (fun x : V =>
           if in_dec V_EqDec x (popped_vertices+::u) then Vint (Int.repr 1) else Vint (Int.repr 0))
          (nat_inc_list (Z.to_nat 8))) v_out;
     data_at Tsh (tarray tint 8) (map (fun x : Z => Vint (Int.repr x)) parents') v_parent;
     data_at Tsh (tarray tint 8) (map (fun x : Z => Vint (Int.repr x)) keys') v_key;
     undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr);
     undirected_matrix sh (graph_to_symm_mat edgeless_graph') (pointer_val_val mstptr)
      )
    )
  %assert.
  (*precon*) {
  Exists parents. Exists keys. Exists upd_pq_state. entailer!.
  intros. rewrite Hinv_5 by lia. destruct (V_EqDec v r). auto. split.
  apply weight_representable. apply weight_inf_bound.
  }
  (*loop*)
  assert (is_int I32 Signed (if in_dec V_EqDec (Znth i (nat_inc_list (Z.to_nat 8))) (popped_vertices+::u)
    then Vint (Int.repr 1) else Vint (Int.repr 0))). {
    unfold is_int. rewrite nat_inc_list_i. 2: rewrite Z2Nat.id; unfold SIZE in H3; lia.
    destruct (in_dec V_EqDec i (popped_vertices+::u)); auto.
  } forward.
  rename H5 into Hinv2_1; rename H6 into Hinv2_2;
  rename H7 into Hinv2_3; rename H8 into Hinv2_4.
  assert_PROP (Zlength (map (fun x : Z => Vint (Int.repr x)) parents') = SIZE). entailer!. rewrite Zlength_map in H5. rename H5 into HZlength_parents'.
  assert_PROP (Zlength (map (fun x : Z => Vint (Int.repr x)) keys') = SIZE). entailer!. rewrite Zlength_map in H5. rename H5 into HZlength_keys'.
  assert_PROP (Zlength (map (fun x : Z => Vint (Int.repr x)) pq_state') = SIZE). entailer!. rewrite Zlength_map in H5. rename H5 into HZlength_pq_state'.

  rewrite nat_inc_list_i. 2: rewrite Z2Nat.id; unfold SIZE in H3; lia.
  set (out_i:=if in_dec V_EqDec i (popped_vertices+::u)
               then Vint (Int.repr 1)
               else Vint (Int.repr 0)). fold out_i.
  forward_if.
  (**In queue**)
  +assert (~ In i (popped_vertices+::u)). {
    destruct (in_dec V_EqDec i (popped_vertices +:: u)). simpl in H5. inversion H5. auto.
  }
  rewrite (graph_unfold _ _ _ u). unfold list_rep.
  2: { unfold graph_to_symm_mat. rewrite Zlength_map, nat_inc_list_Zlength. rewrite Z2Nat.id. lia. unfold SIZE; lia. }
  assert_PROP (field_compatible (tarray tint SIZE) [ArraySubsc i] (offset_val (u * sizeof (tarray tint SIZE)) (pointer_val_val gptr))). entailer!.
  assert_PROP(force_val (sem_add_ptr_int tint Signed (force_val (sem_add_ptr_int (tarray tint SIZE) Signed (pointer_val_val gptr) (Vint (Int.repr u))))
   (Vint (Int.repr i))) = (field_address (tarray tint SIZE) [ArraySubsc i] (offset_val (u * sizeof (tarray tint SIZE)) (pointer_val_val gptr)))). {
    entailer!. symmetry; rewrite field_address_offset. simpl. unfold offset_val.
    destruct gptr; simpl; auto.
    rewrite Ptrofs.add_assoc. rewrite (Ptrofs.add_signed (Ptrofs.repr (u*32))).
    rewrite Ptrofs.signed_repr. rewrite Ptrofs.signed_repr. rewrite Z.add_0_l. rewrite Z.mul_comm. auto.
    all: set (k:=Ptrofs.min_signed); compute in k; subst k; set (k:=Ptrofs.max_signed); compute in k; subst k.
    rewrite Z.add_0_l. unfold SIZE in H3; lia. unfold SIZE in H2; lia. auto.
  } Intros.
  assert (Zlength (Znth u (graph_to_symm_mat g)) = SIZE). {
    unfold graph_to_symm_mat. unfold vert_rep_symm. rewrite Znth_map.
    rewrite Zlength_map. rewrite Zlength_map. rewrite nat_inc_list_Zlength, Z2Nat.id; auto.
    unfold SIZE; lia. rewrite nat_inc_list_Zlength, Z2Nat.id. lia. lia.
  }
  forward. forward.
  forward_if.
    -(*g[u][i] < ...*)
    (*implies adjacency*)
    rewrite graph_to_mat_eq in H10; try lia. rewrite eformat_symm in H10.
    rewrite Int.signed_repr in H10. rewrite Int.signed_repr in H10.
    2: { assert (Int.min_signed <= Znth i keys' <= inf). apply Hinv2_4; lia.
      set (k:=Int.max_signed); compute in k; subst k. rewrite inf_literal in H11; lia. }
    2: { apply weight_representable. }
    assert (Hadj_ui: adjacent g u i). {
      rewrite eformat_adj_elabel.
      assert (Znth i keys' <= inf). apply Hinv2_4. lia.
      (*can't lia here for some reason*) apply (Z.lt_le_trans _ (Znth i keys')); auto.
    }
    forward. forward. forward. forward. entailer!.
    rewrite upd_Znth_same. simpl. auto. rewrite Zlength_map. rewrite HZlength_keys'. auto.
    rewrite upd_Znth_same. 2: { simpl. auto. rewrite Zlength_map. rewrite HZlength_keys'. auto. }
    forward_call (v_pq, i, Znth i (Znth u (graph_to_symm_mat g)), pq_state').
    replace (map (fun x : Z => Vint (Int.repr x)) pq_state') with (map Vint (map Int.repr pq_state')).
    entailer!. rewrite list_map_compose. auto.
    split. unfold priq_arr_utils.SIZE. unfold SIZE in H3; lia.
    unfold weight_inrange_priq. rewrite <- inf_priq. rewrite graph_to_mat_eq. split.
    apply weight_representable. rewrite eformat_adj_elabel, eformat_symm in Hadj_ui. lia. lia. lia.
    Exists (upd_Znth i parents' u).
    Exists (upd_Znth i keys' (Znth i (Znth u (graph_to_symm_mat g)))).
    Exists (upd_Znth i pq_state' (Znth i (Znth u (graph_to_symm_mat g)))).
    rewrite (graph_unfold _ (graph_to_symm_mat g) _ u). unfold list_rep.
    rewrite list_map_compose. repeat rewrite (upd_Znth_map (fun x => Vint (Int.repr x))). unfold SIZE.
    entailer!.
    { clear H0 H5 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28.
      clear Pv_pq HPv_pq Pv_pq0 Pv_out HPv_out Pv_out0 Pv_parent HPv_parent Pv_parent0 Pv_key HPv_key Pv_key0.
    split3. 3: split.
    *intros. destruct (Z.lt_trichotomy v i). repeat rewrite upd_Znth_diff; try lia. apply Hinv2_1. lia. apply H5.
    destruct H13. subst v. destruct H5; contradiction. lia.
    *intros. destruct (Z.lt_trichotomy v i).
      (*v<i*) repeat rewrite upd_Znth_diff; try lia. apply Hinv2_2. lia. auto. auto.
      destruct H14.
      (*v=i*) subst v. repeat rewrite upd_Znth_same; try lia.
      (*i not in popped, so must be in unpopped, which means upd_pq_state = pq_state = keys*)
      assert (Znth i upd_pq_state = Znth i keys').
        unfold upd_pq_state. rewrite upd_Znth_diff. 2: replace (Zlength pq_state) with SIZE; lia. 2: replace (Zlength pq_state) with SIZE; lia.
        replace (Znth i keys') with (Znth i keys). rewrite Hinv_6.
        destruct (in_dec V_EqDec i popped_vertices). exfalso; apply H13. apply in_or_app; left; auto. auto. lia.
        symmetry. apply Hinv2_3. lia. unfold not; intros. apply H13. apply in_or_app; right; subst i; left; auto.
      rewrite H14. split3.
      rewrite <- graph_to_mat_eq; try lia. destruct (Znth u (Znth i (graph_to_symm_mat g)) <? Znth i keys') eqn:bool.
      auto. rewrite graph_to_mat_eq in bool; try lia. rewrite Z.ltb_nlt in bool. contradiction.
      rewrite graph_to_mat_eq; try lia. rewrite eformat_symm. rewrite Zlt_Zmin; auto.
      rewrite graph_to_mat_eq; try lia. rewrite eformat_symm. rewrite Zlt_Zmin; auto.
      (*v>i*) lia.
    *intros. repeat rewrite upd_Znth_diff; try lia. apply Hinv2_3. unfold SIZE; lia.
      rewrite HZlength_pq_state'. unfold SIZE; lia.
      rewrite HZlength_keys'. unfold SIZE; lia.
      rewrite HZlength_parents'. unfold SIZE; lia.
    *intros. destruct (Z.eq_dec v i). subst i. rewrite upd_Znth_same. rewrite graph_to_mat_eq.
      split. apply (weight_representable g (eformat (v,u))). apply weight_inf_bound. lia. lia. rewrite HZlength_keys'; lia.
      rewrite upd_Znth_diff. apply Hinv2_4. unfold SIZE; auto. rewrite HZlength_keys'; unfold SIZE; lia.
      rewrite HZlength_keys'; lia. auto.
    }
    entailer!.
    unfold graph_to_symm_mat. rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; lia.
    -forward. (*nothing changed*)
    Exists parents'. Exists keys'. Exists pq_state'.
    rewrite (graph_unfold _ (graph_to_symm_mat g) _ u). unfold list_rep.
    2: unfold graph_to_symm_mat; rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; lia.
    entailer!.
    clear H0 H5 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28.
    clear Pv_pq HPv_pq Pv_pq0 Pv_out HPv_out Pv_out0 Pv_parent HPv_parent Pv_parent0 Pv_key HPv_key Pv_key0.
    split3.
    *intros. destruct (Z.lt_trichotomy v i). apply Hinv2_1; auto. lia. destruct H13. subst v. apply Hinv2_3. lia. lia.
    *intros. destruct (Z.lt_trichotomy v i).
    (*v < i*) apply Hinv2_2. lia. auto. auto.
    destruct H14.
    (*v = i*) subst v. rewrite <- graph_to_mat_eq; try lia.
    assert (Znth i upd_pq_state = Znth i keys'). {
      unfold upd_pq_state. rewrite upd_Znth_diff. 2: replace (Zlength pq_state) with SIZE; lia.  2: replace (Zlength pq_state) with SIZE; lia.
      replace (Znth i keys') with (Znth i keys). rewrite Hinv_6.
      destruct (in_dec V_EqDec i popped_vertices). exfalso. apply H13. apply in_or_app; left; auto.
      auto. lia. symmetry. apply Hinv2_3. lia. unfold not; intros. apply H13. apply in_or_app; right; subst i; left; auto.
    } rewrite H14. rewrite graph_to_mat_symmetric; try lia.
    rewrite !Int.signed_repr in H10. split3.
    destruct (Znth i (Znth u (graph_to_symm_mat g)) <? Znth i keys') eqn:bool.
    rewrite Z.ltb_lt in bool. lia.
    apply Hinv2_3. lia.
    rewrite Z.min_r; lia.
    replace (Znth i pq_state') with (Znth i upd_pq_state). rewrite H14. rewrite Z.min_r; lia. symmetry; apply Hinv2_3; lia.
    assert (Int.min_signed <= Znth i keys' <= inf). apply Hinv2_4. lia. pose proof (inf_repable); unfold repable_signed in H16; lia.
    rewrite graph_to_mat_eq; try lia. apply weight_representable.
    (*v > i*) lia.
    *intros. apply Hinv2_3. lia.
  +(*nothing changed because out of pq*)
  assert (In i (popped_vertices+::u)). {
    unfold typed_false in H5. destruct (V_EqDec u i); simpl in H5. unfold Equivalence.equiv in e; subst i. apply in_or_app; right; left; auto.
    destruct (in_dec V_EqDec i (popped_vertices+::u)); simpl in H5. auto. inversion H5.
  }
  forward. (*again nothing changed*)
  Exists parents'. Exists keys'. Exists pq_state'.
  rewrite (graph_unfold _ (graph_to_symm_mat g) _ u). unfold list_rep.
  2: unfold graph_to_symm_mat; rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; lia.
  entailer!.
  clear H0 H5 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24.
  clear Pv_pq HPv_pq Pv_pq0 Pv_out HPv_out Pv_out0 Pv_parent HPv_parent Pv_parent0 Pv_key HPv_key Pv_key0.
  split3.
  *intros. destruct (Z.lt_trichotomy v i). apply Hinv2_1; auto. lia. destruct H13. subst v. apply Hinv2_3. lia. lia.
  *intros. destruct (Z.lt_trichotomy v i).
  (*v < i*) apply Hinv2_2. lia. auto. auto. destruct H14.
  subst v. contradiction. (*i is popped*)
  lia.
  *intros. apply Hinv2_3. lia.
  +(*inner loop done, postcon leading to next outer loop iter*)
  Intros parents' keys' pq_state'.
  assert (Htmp: Znth u parents' = Znth u parents /\ Znth u keys' = Znth u keys /\ Znth u pq_state' = Znth u upd_pq_state). {
    apply H3. lia. right; apply in_or_app; right; left; auto.
  } destruct Htmp as [Hu_parents [Hu_keys Hu_pq_state]].
  (*need to split into two cases: if Znth u keys = inf, then it's a "starter" and so the same mst. Else, it's adde(eformat (u, Znth u keys))*)
  clear H5. rename H3 into Hinv2_1; rename H4 into Hinv2_2; rename H6 into Hinv2_3.
  assert (0 <= Znth u parents). { apply Hinv_4. auto. }
  assert (Znth u parents <= SIZE). { apply Hinv_4. auto. }
  (*****We do as many props as we can here, especially the non-mst ones*****)
  assert (Hperm_g: Permutation (popped_vertices +:: u ++ remove V_EqDec u unpopped_vertices) (VList g)). {
    assert (NoDup unpopped_vertices). apply (NoDup_app_r V popped_vertices). apply (Permutation_NoDup (l:=VList g)). apply Permutation_sym; auto.
    apply NoDup_VList.
    rewrite <- app_assoc. simpl. apply (Permutation_trans (l':=popped_vertices++unpopped_vertices)).
    apply Permutation_app_head. apply NoDup_Permutation. apply NoDup_cons. apply remove_In.
    apply nodup_remove_nodup. auto. auto. intros; split; intros.
    destruct H6. subst x. auto. rewrite remove_In_iff in H6. apply H6.
    destruct (V_EqDec x u). unfold Equivalence.equiv in e. subst x. left; auto.
    unfold RelationClasses.complement, Equivalence.equiv in c. right. rewrite remove_In_iff. split; auto.
    auto.
  }
  assert (Hparents_bound: forall v : Z, 0 <= v < SIZE -> 0 <= Znth v parents' <= SIZE). {
    intros. destruct (adjacent_dec g u v). destruct (in_dec Z.eq_dec v (popped_vertices +::u)).
    replace (Znth v parents') with (Znth v parents). 2: symmetry; apply Hinv2_1; auto. apply Hinv_4; auto.
    replace (Znth v parents') with (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents).
    2: symmetry; apply (Hinv2_2 v); auto. rewrite <- graph_to_mat_eq; auto.
    destruct (Znth u (Znth v (graph_to_symm_mat g)) <? Znth v upd_pq_state) eqn:bool. lia. apply Hinv_4; auto.
    replace (Znth v parents') with (Znth v parents). 2: symmetry; apply Hinv2_1; auto. apply Hinv_4; auto.
  }
  assert (Hkeys': forall v : Z, 0 <= v < SIZE -> Znth v keys' = (if V_EqDec v r then 0 else elabel g (eformat (v, Znth v parents')))). {
    intros. destruct (adjacent_dec g u v). destruct (in_dec Z.eq_dec v (popped_vertices +::u)).
    ****
    replace (Znth v keys') with (Znth v keys). 2: symmetry; apply Hinv2_1; auto. rewrite Hinv_5.
    replace (Znth v parents') with (Znth v parents). 2: symmetry; apply Hinv2_1; auto. auto. auto.
    ****
    replace (Znth v keys') with (Z.min (elabel g (eformat (u, v))) (Znth v upd_pq_state)). 2: symmetry; apply Hinv2_2; auto.
    replace (Znth v parents') with (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents). 2: symmetry; apply Hinv2_2; auto.
    destruct (V_EqDec v r). hnf in e.
    (*v=r*) subst v. destruct popped_vertices. exfalso. apply n. apply in_or_app; right; left. apply Hur; auto.
    assert (hd_error (v :: popped_vertices) = Some r). apply Hinv_12. unfold not; intros. inversion H7. inversion H7. subst v.
    exfalso. apply n. apply in_or_app; left; left; auto.
    (*v <> r*)
    rewrite <- graph_to_mat_eq by lia. destruct (Znth u (Znth v (graph_to_symm_mat g)) <? Znth v upd_pq_state) eqn:bool.
    rewrite graph_to_mat_eq by lia. rewrite graph_to_mat_eq in bool by lia. rewrite Z.ltb_lt in bool. rewrite Zlt_Zmin by auto. rewrite eformat_symm; auto.
    rewrite graph_to_mat_eq by lia. rewrite graph_to_mat_eq in bool by lia. rewrite Z.ltb_ge in bool. rewrite Z.min_r by auto.
    unfold upd_pq_state. destruct (Z.eq_dec v u). subst v. exfalso; apply n. apply in_or_app; right; left; auto.
    rewrite upd_Znth_diff. rewrite Hinv_6 by lia. destruct (in_dec V_EqDec v popped_vertices). exfalso; apply n. apply in_or_app; left; auto.
    rewrite Hinv_5 by lia. destruct (V_EqDec v r). contradiction. auto.
    replace (Zlength pq_state) with SIZE by lia. lia.
    replace (Zlength pq_state) with SIZE by lia. lia. auto.
    ****
    replace (Znth v keys') with (Znth v keys). 2: symmetry; apply Hinv2_1; auto. rewrite Hinv_5.
    replace (Znth v parents') with (Znth v parents). 2: symmetry; apply Hinv2_1; auto. auto. auto.
  }
  assert (Hpq_state': forall v : Z, 0 <= v < SIZE -> Znth v pq_state' = (if in_dec V_EqDec v (popped_vertices +:: u) then inf + 1 else Znth v keys')). {
    intros. destruct (in_dec V_EqDec v (popped_vertices +:: u)).
    replace (Znth v pq_state') with (Znth v upd_pq_state). 2: symmetry; apply Hinv2_1; auto. unfold upd_pq_state.
    apply in_app_or in i; destruct i.
    rewrite upd_Znth_diff. rewrite Hinv_6 by lia. destruct (in_dec V_EqDec v popped_vertices). auto. contradiction.
    replace (Zlength pq_state) with SIZE; lia. replace (Zlength pq_state) with SIZE; lia.
    unfold not; intros; subst v. contradiction.
    destruct H6. subst v. rewrite upd_Znth_same. rewrite inf_priq. auto. replace (Zlength pq_state) with SIZE; lia.
    contradiction.
    destruct (adjacent_dec g u v).
    (*second case*)
    replace (Znth v pq_state') with (Z.min (elabel g (eformat (u, v))) (Znth v upd_pq_state)). 2: symmetry; apply Hinv2_2; auto.
    replace (Znth v keys') with (Z.min (elabel g (eformat (u, v))) (Znth v upd_pq_state)). 2: symmetry; apply Hinv2_2; auto.
    auto.
    (*third case*)
    replace (Znth v pq_state') with (Znth v upd_pq_state). 2: symmetry; apply Hinv2_1; auto. unfold upd_pq_state.
    rewrite upd_Znth_diff. rewrite Hinv_6 by lia. destruct (in_dec V_EqDec v popped_vertices).
    exfalso; apply n. apply in_or_app; left; auto.
    symmetry; apply Hinv2_1; auto. unfold upd_pq_state.
    replace (Zlength pq_state) with SIZE; lia. replace (Zlength pq_state) with SIZE; lia.
    unfold not; intros. subst v. apply n. apply in_or_app; right; left; auto.
  }
  assert (Hpopped_nil: popped_vertices +:: u = [] -> r = find pq_state' (fold_right Z.min (hd 0 pq_state') pq_state') 0). {
    intros. assert (In u (popped_vertices+::u)). apply in_or_app; right; left; auto.
    rewrite H5 in H6. contradiction.
  }
  assert (Hpopped_unnil: popped_vertices +:: u <> [] -> hd_error (popped_vertices +:: u) = Some r). {
    intros. destruct popped_vertices. rewrite Hur; auto.
    apply hd_error_app. rewrite Hinv_12; auto. unfold not; intros. inversion H6.
  }
  assert (Hheavy: forall v : Z, 0 <= v < SIZE -> 0 <= Znth v parents' < SIZE ->
    evalid g (eformat (v, Znth v parents')) /\
    (exists i : Z, 0 <= i < Zlength (popped_vertices +:: u) /\
      Znth i (popped_vertices +:: u) = Znth v parents' /\
      i < find (popped_vertices+::u) v 0)
    /\ (forall u0 : V,
     In u0 (sublist 0 (find (popped_vertices +:: u) v 0) (popped_vertices +:: u)) ->
     elabel g (eformat (v, Znth v parents')) <= elabel g (eformat (u0, v)))). {
    intros. (*the main issue is u and unpopped; popped_vertices is an application of Hinv2_1 and Hinv_7*)
    destruct (in_dec V_EqDec v (popped_vertices+::u)).
    (*v in popped_vertices+::u*)
    replace (Znth v parents') with (Znth v parents). 2: symmetry; apply Hinv2_1; auto.
    replace (Znth v parents') with (Znth v parents) in H6. 2: symmetry; apply Hinv2_1; auto.
    destruct (Hinv_7 v H5 H6). destruct H8 as [[j [? ?]] ?].
    split. auto. split. exists j. split.
    rewrite Zlength_app. rewrite Zlength_cons, Zlength_nil. lia.
    split. rewrite app_Znth1 by lia. apply H9.
    destruct H9. apply (Z.lt_le_trans _ (find popped_vertices v 0)). auto. apply find_app_le.
    intros.
    apply H10. rewrite sublist_app1 in H11. auto.
    2: { split. lia. apply (find_range_gen (popped_vertices+::u) v 0). auto. lia. }
    2: { assert (0 <= find (popped_vertices +:: u) v 0 < Zlength (popped_vertices +:: u)).
        apply (find_range (popped_vertices+::u) v). auto. rewrite Zlength_app, Zlength_cons, Zlength_nil in H12. lia. }
    destruct (V_EqDec v u).
    (*subcase v = u*) hnf in e. subst v.
    replace (find (popped_vertices +:: u) u 0) with (Zlength popped_vertices) in H11.
    replace (find popped_vertices u 0) with (Zlength popped_vertices). auto.
    rewrite find_notIn_0; auto.
    rewrite find_app_notIn1. rewrite find_cons. rewrite Z.add_0_r. auto. auto.
    (*subcase v <> u*) unfold RelationClasses.complement, Equivalence.equiv in c.
    assert (In v popped_vertices). apply in_app_or in i; destruct i. auto. destruct H12. symmetry in H12; contradiction. contradiction.
    replace (find (popped_vertices +:: u) v 0) with (find popped_vertices v 0) in H11. auto.
    symmetry; apply find_app_In1. auto.
    (*****NOT IN POPPED_VERTICES+::U*****)
    assert (In v (remove V_EqDec u unpopped_vertices)). destruct (Hpopped_or_unpopped v). rewrite vert_bound; auto.
    exfalso; apply n; apply in_or_app; left; auto. rewrite remove_In_iff. split. auto. unfold not; intros.
    subst v. apply n; apply in_or_app; right; left; auto.
    destruct (adjacent_dec g u v).
    (*adjacent*)
    replace (Znth v parents') with (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents).
    2: symmetry; apply Hinv2_2; auto.
    replace (Znth v parents') with (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents) in H6.
    2: symmetry; apply Hinv2_2; auto.
    rewrite <- (graph_to_mat_eq g u v) in * by lia.
    destruct (Znth u (Znth v (graph_to_symm_mat g)) <? Znth v upd_pq_state) eqn: bool.
    (*smaller, updated: u is the new parent*)
      rewrite Z.ltb_lt in bool. split. rewrite eformat_symm. apply eformat_adj. auto.
      split. exists (Zlength popped_vertices). split. rewrite Zlength_app, Zlength_cons, Zlength_nil.
      split. apply Zlength_nonneg. lia. rewrite Znth_app2 by lia. rewrite Z.sub_diag, Znth_0_cons.
      split. auto. rewrite find_notIn by auto. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      intros.
      assert (v <> u). unfold not; intros. subst v. apply n. apply in_or_app; right; left; auto.
      rewrite sublist_same in H9. 2: auto. 2: { rewrite find_notIn, Z.add_0_r. auto. auto. }
      apply in_app_or in H9; destruct H9.
      rewrite eformat_symm, <- graph_to_mat_eq by lia.
      unfold upd_pq_state in bool.
      rewrite upd_Znth_diff in bool. 2: replace (Zlength pq_state) with SIZE; lia.
      2: replace (Zlength pq_state) with SIZE; lia. 2: auto.
      rewrite Hinv_6 in bool. 2: lia. destruct (in_dec V_EqDec v popped_vertices).
      exfalso. apply n. apply in_or_app; left; auto.
      rewrite Hinv_5 in bool by lia. destruct (V_EqDec v r). hnf in e; subst v.
      destruct popped_vertices. exfalso; apply H10; symmetry; apply Hur. auto.
      assert (hd_error (v :: popped_vertices) = Some r). apply Hinv_12. unfold not; intros; inversion H11.
      inversion H11. subst v. exfalso; apply n. apply in_or_app; left; left; auto.
      (*now check whether Znth v parents is SIZE or lower.
        If < SIZE, use Hinv_7 to show that eformat(u0,v) must be bigger than parents.
        If SIZE, use Hinv_8 to derive that eformat(u0,v) is invalid.
        *)
      assert (Htmp: Znth v parents <= SIZE). apply Hinv_4. lia. apply Z.le_lteq in Htmp; destruct Htmp.
      assert (elabel g (eformat (v, Znth v parents)) <= elabel g (eformat (u0, v))). { apply (Hinv_7 v). lia.
        split. apply Hinv_4. lia. lia. rewrite find_notIn, Z.add_0_r, sublist_same. auto. auto. auto.
        unfold not; intros; apply n; apply in_or_app; left; auto.
      }
      apply (Z.le_trans _ (elabel g (eformat (v, Znth v parents)))). lia. lia.
      (*Znth v parents = SIZE. So elabel = inf, meaning it should not be connected to u0 by Hinv_8*)
      assert (~ evalid g (eformat (u0, v))). {
        unfold not; intros. rewrite <- eformat_adj in H12.
        assert (~ adjacent g u0 v). apply Hinv_8. lia. lia.
        rewrite find_notIn, Z.add_0_r by auto. rewrite sublist_same by auto. auto.
        contradiction.
      }
      apply (@invalid_edge_weight _ _ _ (sound_MatrixUGraph g)) in H12. rewrite H12.
      rewrite graph_to_mat_eq by lia. apply (weight_inf_bound).
      (*u0 = u.*)
      destruct H9. 2: contradiction. subst u0.
      rewrite eformat_symm. apply Z.eq_le_incl. reflexivity.
    (*case not smaller, so parent remains the same. Use Hinv_7*)
    assert (Htmp: 0 <= Znth v parents < SIZE). apply H6.
    apply Hinv_7 in Htmp. 2: lia. destruct Htmp. destruct H10 as [[j [? ?]] ?].
    split. auto. split. exists j. split. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    split. rewrite Znth_app1 by lia. apply H11.
    destruct H11. apply (Z.lt_le_trans _ (find popped_vertices v 0)). auto. apply find_app_le.
    intros. rewrite find_notIn in H13 by auto. rewrite sublist_same in H13. 2: auto. 2: rewrite Z.add_0_r; auto.
    apply in_app_or in H13. destruct H13. apply H12. rewrite find_notIn. rewrite Z.add_0_r, sublist_same by auto.
    auto. unfold not; intros; apply n. apply in_or_app; left; auto.
    destruct H13. 2: contradiction. subst u0.
    (*use bool*)
    unfold upd_pq_state in bool. rewrite Z.ltb_ge in bool.
    destruct (V_EqDec u v).
      (*v=u.*)
      hnf in e; subst v. rewrite upd_Znth_same, <- inf_priq in bool.
      2: replace (Zlength pq_state) with SIZE; lia.
      pose proof (weight_inf_bound g (eformat (u, u))). rewrite <- graph_to_mat_eq in H13 by lia.
      lia.
      (*v<>u*)
      unfold RelationClasses.complement, Equivalence.equiv in c. rewrite upd_Znth_diff in bool.
      2: replace (Zlength pq_state) with SIZE; lia. 2: replace (Zlength pq_state) with SIZE; lia.
      2: auto.
      rewrite Hinv_6 in bool by lia. destruct (in_dec V_EqDec v popped_vertices). exfalso; apply n; apply in_or_app; left; auto.
      rewrite Hinv_5 in bool by lia. destruct (V_EqDec v r).
      (*v=r*)hnf in e; subst v. (*hm...*)
      exfalso; apply n. apply hd_error_In. apply Hpopped_unnil. unfold not; intros.
      assert (In u (popped_vertices+::u)). apply in_or_app; right; left; auto. rewrite H13 in H14; contradiction.
      (*v<>r*)
      rewrite graph_to_mat_eq in bool by lia. apply bool.
    (*finally, non adjacent*)
    replace (Znth v parents') with (Znth v parents). 2: symmetry; apply Hinv2_1; auto.
    replace (Znth v parents') with (Znth v parents) in H6. 2: symmetry; apply Hinv2_1; auto.
    destruct (Hinv_7 v H5 H6). destruct H10 as [[j [? ?]] ?].
    split. auto. split. exists j. split.
    rewrite Zlength_app. rewrite Zlength_cons, Zlength_nil. lia.
    split. rewrite app_Znth1 by lia. apply H11.
    destruct H11. apply (Z.lt_le_trans _ (find popped_vertices v 0)). auto. apply find_app_le.
    intros. rewrite find_notIn in H13 by auto. rewrite Z.add_0_r, sublist_same in H13 by auto.
    apply in_app_or in H13. destruct H13. apply H12.
    rewrite find_notIn. rewrite Z.add_0_r, sublist_same by auto.
    auto. unfold not; intros; apply n. apply in_or_app; left; auto.
    destruct H13. 2: contradiction. subst u0.
    (*but elabel g (eformat (u,v)) = inf because it's invalid*)
    assert (~ evalid g (eformat (u,v))). unfold not; intros; apply H8. rewrite eformat_adj; auto.
    apply (@invalid_edge_weight _ _ _ (sound_MatrixUGraph g)) in H13.
    (*replace (elabel g (eformat (u,v))) with inf.*) (*here we go again...*)
    repeat rewrite <- graph_to_mat_eq by lia. replace (Znth u (Znth v (graph_to_symm_mat g))) with inf.
    rewrite graph_to_mat_eq by lia. apply weight_inf_bound.
    rewrite <- graph_to_mat_eq in H13 by lia. lia.
  }
  assert (Hheavy2: forall v : Z, 0 <= v < SIZE -> Znth v parents' = SIZE ->
    forall u0 : V, In u0 (sublist 0 (find (popped_vertices +:: u) v 0) (popped_vertices +:: u)) ->
    ~ adjacent g u0 v). {
    intros. destruct (in_dec V_EqDec v (popped_vertices+::u)).
    apply in_app_or in i; destruct i.
    rewrite find_app_In1 in H7 by auto. rewrite sublist_app1 in H7.
    2: pose proof (find_lbound popped_vertices v 0); lia.
    2: { rewrite find_ubound, Z.add_0_r. apply Z.le_refl. }
    apply Hinv_8. lia. 2: auto.
    replace (Znth v parents) with (Znth v parents'). auto. apply Hinv2_1. lia.
    right; apply in_or_app; left; auto.
    (*v=u, pretty much same deal*)
    destruct H8. 2: contradiction. subst v. rewrite find_app_notIn1, find_cons, Z.add_0_r in H7 by auto.
    rewrite sublist_app1 in H7. 2: { pose proof (Zlength_nonneg popped_vertices). split. lia. auto. }
    2: apply Z.le_refl.
    (*rewrite sublist_same in H7 by auto.*)
    apply Hinv_8. lia. replace (Znth u parents) with (Znth u parents'); auto.
    rewrite find_notIn_0; auto.
    (*v unpopped, means u0 in popped or u0=u. Former: Hinv_8. Latter:?*)
    rewrite find_notIn, Z.add_0_r, sublist_same in H7 by auto.
    apply in_app_or in H7; destruct H7.
    destruct (adjacent_dec g u v).
    replace (Znth v parents') with (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents) in H6.
    2: { symmetry; apply Hinv2_2; auto. }
    rewrite <- graph_to_mat_eq in H6 by lia. destruct (Znth u (Znth v (graph_to_symm_mat g)) <? Znth v upd_pq_state).
    assert (vvalid g u). apply adjacent_requires_vvalid in H8. apply H8. rewrite vert_bound in H9. lia.
    apply Hinv_8. lia. lia. rewrite find_notIn_0, sublist_same; auto.
    unfold not; intros; apply n; apply in_or_app; left; auto.
    (*not adjacent: rewrite parents' into parents*)
    replace (Znth v parents') with (Znth v parents) in H6. 2: { symmetry; apply Hinv2_1. lia. auto. }
    apply Hinv_8. lia. lia. rewrite find_notIn_0, sublist_same; auto.
    unfold not; intros; apply n; apply in_or_app; left; auto.
    (*u0=u*)
    destruct H7. 2: contradiction. subst u0.
    destruct (adjacent_dec g u v). 2: auto.
    replace (Znth v parents') with (if elabel g (eformat (u, v)) <? Znth v upd_pq_state then u else Znth v parents) in H6.
    2: { symmetry; apply Hinv2_2; auto. }
    rewrite <- graph_to_mat_eq in H6 by lia. destruct (Znth u (Znth v (graph_to_symm_mat g)) <? Znth v upd_pq_state) eqn:bool.
    assert (vvalid g u). apply adjacent_requires_vvalid in H7. apply H7. rewrite vert_bound in H8. lia.
    rewrite eformat_adj, evalid_inf_iff, <- graph_to_mat_eq in H7 by lia.
    rewrite Z.ltb_ge in bool. unfold upd_pq_state in bool.
    rewrite upd_Znth_diff in bool. rewrite Hinv_6 in bool by lia.
    destruct (in_dec V_EqDec v popped_vertices). exfalso; apply n; apply in_or_app; left; auto.
    rewrite Hinv_5 in bool by lia. destruct (V_EqDec v r).
    hnf in e; subst v. exfalso; apply n. apply hd_error_In. apply Hpopped_unnil.
    unfold not; intros. assert (In u (popped_vertices+::u)). apply in_or_app; right; left; auto.
    rewrite H8 in H9; contradiction.
    rewrite (@invalid_edge_weight _ _ _ (sound_MatrixUGraph g)) in bool. lia.
    unfold not; intros. apply eformat_evalid_vvalid in H8. destruct H8. rewrite H6 in H9. rewrite vert_bound in H9. lia.
    replace (Zlength pq_state) with SIZE; lia.
    replace (Zlength pq_state) with SIZE; lia.
    unfold not; intros; subst v. apply n; apply in_or_app; right; left; auto.
  }
  assert (Hweight: forall v u1 u2 : V,
          In v (popped_vertices +:: u) ->
          0 <= Znth v parents' < SIZE ->
          vvalid g u2 ->
          In u1 (sublist 0 (find (popped_vertices +:: u) v 0) (popped_vertices +:: u)) ->
          ~ In u2 (sublist 0 (find (popped_vertices +:: u) v 0) (popped_vertices +:: u)) ->
          elabel g (eformat (v, Znth v parents')) <= elabel g (eformat (u1, u2))
  ). { intros.
    assert (0 <= v < SIZE). {
      apply in_app_or in H5. destruct H5. rewrite <- (vert_bound g). apply Hpopped_vvalid. auto.
      destruct H5. 2: contradiction. subst u; auto. }
    replace (Znth v parents') with (Znth v parents) in *. 2: { symmetry; apply (Hinv2_1 v); auto. }
    apply in_app_or in H5. destruct H5.
    (*case was already in popped vertices*)
    rewrite find_app_In1 in H8, H9 by auto. rewrite sublist_app1 in H8, H9.
      2: pose proof (find_lbound popped_vertices v 0); lia.
      2: { pose proof (find_ubound popped_vertices v 0). rewrite Z.add_0_r in H11. auto. }
      2: pose proof (find_lbound popped_vertices v 0); lia.
      2: { pose proof (find_ubound popped_vertices v 0). rewrite Z.add_0_r in H11. auto. }
    apply Hinv_14; auto.
    (*case v = u*)
    destruct H5. 2: contradiction. subst v.
    assert ((sublist 0 (find (popped_vertices +:: u) u 0) (popped_vertices +:: u)) =
      (popped_vertices)).
    { rewrite find_app_notIn1, find_cons, Z.add_0_r by auto.
         rewrite sublist_app1, sublist_same. auto. auto. auto.
          pose proof (Zlength_nonneg popped_vertices). split. lia. auto.
          apply Z.le_refl.
    } rewrite H5 in H9, H8.
    (*make use of Hu_min
      case u2 = u: then apply Hheavy, done (guess it wasn't useless after all)
      case u2 <> u: then by Hu_min, Znth u pq_state <= Znth u2 pq_state
        u2 is unpopped, so by Hinv_6, Znth u2 pq_state = Znth v keys
        u2 can't be r, so by Hinv_5, Znth v keys = elabel g (eformat (u2, Znth u2 parents))
        ===> Znth u pq_state <= elabel g (eformat (u2, Znth u2 parents))
        using Hheavy again? and Z.le_trans, Znth u pq_state <= elabel g (eformat (u1, u2))
        subcase u = r a.k.a. popped_vertices = []: then contradiction on u1 being in empty
        Then Znth u pq_state = Znth v keys = elabel g (eformat (u,Znth u parents)). Apply
    *)
    destruct (V_EqDec u2 u). hnf in e. subst u2.
    assert ((forall u0 : V,
          In u0 (sublist 0 (find (popped_vertices +:: u) u 0) (popped_vertices +:: u)) ->
          elabel g (eformat (u, Znth u parents')) <= elabel g (eformat (u0, u)))).
    apply Hheavy; lia. rewrite Hu_parents in H11. apply H11. rewrite H5. auto.
    rewrite vert_bound in H7. assert (vvalid g u1). apply Hpopped_vvalid; auto. rewrite vert_bound in H11.
    assert (0 <= Znth u2 parents <= SIZE). apply Hinv_4; lia. destruct H12.
    apply Z.le_lteq in H13. destruct H13.
    2: { assert (~ adjacent g u1 u2). apply Hinv_8. lia. lia.
          rewrite find_notIn, Z.add_0_r, sublist_same by auto. auto.
        rewrite eformat_adj in H14. apply (@invalid_edge_weight _ _ _ (sound_MatrixUGraph g)) in H14.
        rewrite H14. apply weight_inf_bound. }
    (*u2 <> u*) unfold RelationClasses.complement, Equivalence.equiv in c.
    assert (Znth u pq_state <= Znth u2 pq_state). apply Hu_min; lia.
    rewrite (Hinv_6 u2) in H14 by lia. destruct (in_dec V_EqDec u2 popped_vertices). contradiction.
    clear n. rewrite Hinv_5 in H14. destruct (V_EqDec u2 r).
    hnf in e. subst u2. destruct popped_vertices. contradiction. exfalso; apply H9.
    apply hd_error_In. apply Hinv_12. unfold not; intros. assert (In v (v::popped_vertices)) by (left; auto).
    rewrite H15 in H16; contradiction.
    unfold RelationClasses.complement, Equivalence.equiv in c0.
    assert (elabel g (eformat (u2, Znth u2 parents)) <= elabel g (eformat (u1,u2))).
      apply Hinv_7. lia. lia. rewrite find_notIn, Z.add_0_r, sublist_same by auto. auto. 2: auto.
    apply (Z.le_trans _ (elabel g (eformat (u2, Znth u2 parents)))). 2: auto.
    apply (Z.le_trans _ (Znth u pq_state)). 2: auto.
    clear H14 H15.
    rewrite Hinv_6 by lia. destruct (in_dec V_EqDec u popped_vertices). contradiction.
    rewrite Hinv_5 by lia. destruct (V_EqDec u r).
    hnf in e; subst u. destruct popped_vertices. contradiction. exfalso; apply n.
    apply hd_error_In. apply Hinv_12. unfold not; intros. assert (In v (v::popped_vertices)). left; auto.
    rewrite H14 in H15; contradiction.
    apply Z.le_refl.
  }
  (*now split into cases*)
  apply Z.le_lteq in H4. destruct H4.
  ++ (*adde case*)
  assert (vvalid mst' u). apply vert_bound. lia.
  assert (vvalid mst' (Znth u parents)). apply vert_bound. lia.
  assert (evalid g (eformat (u,(Znth u parents)))). apply Hinv_7; lia.
  assert (Hfst: vvalid mst' (fst (eformat (u,(Znth u parents))))). {
    destruct (Z.le_ge_cases u (Znth u parents)). rewrite eformat1; simpl; auto.
    rewrite eformat2; simpl; auto.
  }
  assert (Hsnd: vvalid mst' (snd (eformat (u,(Znth u parents))))). {
    destruct (Z.le_ge_cases u (Znth u parents)). rewrite eformat1; simpl; auto.
    rewrite eformat2; simpl; auto.
  }
  assert (Hfst_le_snd: (fst (eformat (u,Znth u parents))) <= (snd (eformat (u,Znth u parents)))). {
    destruct (Z.le_ge_cases u (Znth u parents)). rewrite eformat1; simpl; auto.
    rewrite eformat2; simpl; auto.
  }
  assert (Int.min_signed <= elabel g (eformat (u,(Znth u parents))) < inf). {
    split. apply weight_representable. apply evalid_inf_iff; auto.
  }
  assert (Hu_evalid: ~ evalid mst' (eformat (u,(Znth u parents)))). {
    unfold not; intros. apply (Hinv_13 u (Znth u parents)).
    auto. rewrite eformat_adj. auto.
  }
  assert (Huparents_popped: In (Znth u parents) popped_vertices). {
    assert (exists i : Z,
            0 <= i < Zlength (popped_vertices) /\
            Znth i (popped_vertices) = Znth u parents /\ i < find popped_vertices u 0
            ). apply Hinv_7; lia.
    destruct H9 as [i [? [? ?]]]. rewrite <- H10. apply Znth_In. lia.
  }
  assert (Huparents_unpopped: ~ In (Znth u parents) unpopped_vertices). {
    apply (NoDup_app_not_in V popped_vertices). apply (Permutation_NoDup (l:=VList g)).
    apply Permutation_sym; apply Hinv_3. apply NoDup_VList. auto.
  }
  set (adde_u:=adde mst' (fst (eformat (u,Znth u parents))) (snd (eformat (u,Znth u parents))) Hfst Hsnd Hfst_le_snd (elabel g (eformat (u,(Znth u parents)))) H8).
  Exists (adde_u).
  Exists (@fin _ _ _ (sound_MatrixUGraph adde_u)).
  Exists parents' keys' pq_state' (popped_vertices+::u) (remove V_EqDec u unpopped_vertices).
  entailer!.
  clear H9 H10 H11 H12 H14 H15 H16 H17 H19 H20 H22 Pv_pq HPv_pq Pv_pq0 Pv_out HPv_out Pv_out0 Pv_parent HPv_parent Pv_parent0 Pv_key HPv_key Pv_key0.
  rewrite Zlength_map in H13, H18, H21.
  rename H13 into HZlength_pq_state'.
  rename H18 into HZlength_parents'.
  rename H21 into HZlength_keys'.
  (*assert ((fst (eformat (u, Znth u parents)), snd (eformat (u, Znth u parents))) = eformat (u,Znth u parents)). {
    destruct (eformat (u,Znth u parents)); simpl; auto.
  }*)
  assert (Hu_new: evalid adde_u (eformat (u, Znth u parents))). {
    unfold adde_u, adde. rewrite <- eformat_eq. apply adde_evalid_new. }
  assert (Hsrc: src adde_u (eformat (u, Znth u parents)) = fst (eformat (u, Znth u parents))). {
    apply (@src_fst _ _ adde_u (sound_MatrixUGraph _)). apply Hu_new.
  }
  assert (Hdst: dst adde_u (eformat (u, Znth u parents)) = snd (eformat (u, Znth u parents))). {
    apply (@dst_snd _ _ adde_u (sound_MatrixUGraph _)). apply Hu_new.
  }
  assert (Hpartial: is_partial_lgraph adde_u g). {
    apply adde_partial_lgraph. auto. rewrite eformat_eq; auto. rewrite eformat_eq; auto. }
  split3. 3: split3.
  **auto.
  **apply add_edge_uforest'; auto.
    unfold not; intros. destruct (Z.le_ge_cases u (Znth u parents)).
      ****
      rewrite eformat1 in *; try (simpl; lia).
      destruct H9 as [p [? [? ?]]]. destruct p. inversion H11.
      destruct p. inversion H11; inversion H12. subst v.
      rewrite H15 in Hu_unpopped; contradiction.
      destruct H9. inversion H11. subst v.
      apply (Hinv_13 u v0). auto. apply H9.
      ****
      rewrite eformat2 in *; try (simpl; lia).
      simpl in H9. apply connected_symm in H9.
      destruct H9 as [p [? [? ?]]]. destruct p. inversion H11.
      destruct p. inversion H11; inversion H12. subst v.
      rewrite H15 in Hu_unpopped; contradiction.
      destruct H9. inversion H11. subst v.
      apply (Hinv_13 u v0). auto. apply H9.
  **(*permutation of EList*)
  apply (Permutation_trans (l':=(eformat (u,Znth u parents))::(EList mst'))).
  apply Permutation_sym.
  { apply NoDup_Permutation. apply NoDup_cons. rewrite EList_evalid; auto. apply NoDup_EList. apply NoDup_EList.
    intros; split; intros. rewrite EList_evalid. simpl. unfold graph_gen.addValidFunc. destruct H9.
    rewrite eformat_eq. right; symmetry; auto. left; rewrite EList_evalid in H9; auto.
    rewrite EList_evalid in H9; simpl in H9. unfold graph_gen.addValidFunc in H9; destruct H9.
    right; rewrite EList_evalid; auto. left; symmetry; auto. rewrite eformat_eq in H9; auto.
  }
  apply (Permutation_trans (l':=(eformat (u, Znth u parents)) :: (map (fun v : Z => eformat (v, Znth v parents))
     (filter (fun v : Z => Znth v parents <? SIZE) (popped_vertices))))).
  { apply Permutation_cons. auto. apply Hinv_9. }
  apply (Permutation_trans (l':=(map (fun v : Z => eformat (v, Znth v parents))
     (filter (fun v : Z => Znth v parents <? SIZE) (popped_vertices)))+::(eformat (u, Znth u parents)))).
  { apply Permutation_cons_append. }
  replace (map (fun v : Z => eformat (v, Znth v parents))
     (filter (fun v : Z => Znth v parents <? SIZE) popped_vertices) +:: 
   (eformat (u, Znth u parents))) with (map (fun v : Z => eformat (v, Znth v parents'))
     (filter (fun v : Z => Znth v parents' <? SIZE) (popped_vertices +:: u))). apply Permutation_refl.
  replace [eformat (u,Znth u parents)] with (map (fun v : Z => eformat (v, Znth v parents)) [u]). 2: { simpl; auto. }
  rewrite <- list_append_map.
  replace (filter (fun v : Z => Znth v parents' <? SIZE) (popped_vertices +:: u)) with (filter (fun v : Z => Znth v parents <? SIZE) (popped_vertices +:: u)).
  2: {
    apply filter_ext_in. intros. replace (Znth a parents) with (Znth a parents'). auto.
    apply Hinv2_1. 2: right; auto. apply in_app_or in H9; destruct H9.
    rewrite <- (vert_bound g). apply Hpopped_vvalid; auto.
    destruct H9. 2: contradiction. subst a; lia.
  }
  replace (filter (fun v : Z => Znth v parents <? SIZE) popped_vertices +:: u) with (filter (fun v : Z => Znth v parents <? SIZE) (popped_vertices +:: u)).
  2: { rewrite filter_app. simpl. destruct (Znth u parents <? SIZE) eqn: bool. auto.
    rewrite Z.ltb_ge in bool; lia. }
  apply map_ext_in; intros. rewrite filter_In in H9. destruct H9.
  replace (Znth a parents) with (Znth a parents'). auto.
  apply Hinv2_1.
  rewrite <- (vert_bound g). apply in_app_or in H9. destruct H9.
  apply Hpopped_vvalid; auto.
  destruct H9. 2: contradiction. subst a. apply Hunpopped_vvalid; auto.
  right; auto.
  **intros. apply in_app_or in H9; apply in_app_or in H10. destruct H9; destruct H10.
    ****(*both in popped vertices, reuse invariant*)
        split; intros.
        apply Hinv_10 in H11; auto. apply add_edge_connected; auto.
        rewrite eformat_eq; auto.
        apply (is_partial_lgraph_connected adde_u); auto.
    ****(*v=u*) destruct H10. 2: contradiction. subst v.
        split; intros.
        (*g -> adde*)
        (* u0 is popped, so is Znth u parents, thus use invariant on them by adding eformat (u, Znth u parents) to the path
            Then add it again to go back to u*)
        apply (connected_trans adde_u u0 (Znth u parents) u).
        apply adde_connected. rewrite <- Hinv_10; auto. apply (connected_trans g u0 u).
        auto. apply adjacent_connected. rewrite eformat_adj. apply H7.
        apply connected_symm. apply adjacent_connected. rewrite eformat_adj. auto.
        (*adde -> g*)
        apply (is_partial_lgraph_connected adde_u); auto.
    ****(*u0=u, repeat of above*) destruct H9. 2: contradiction. subst u0. rename H10 into H9.
        split; intros.
        apply (connected_trans adde_u u (Znth u parents) v).
        apply adjacent_connected. rewrite eformat_adj. auto.
        apply adde_connected. rewrite <- Hinv_10; auto.
        apply (connected_trans g (Znth u parents) u).
        apply adjacent_connected. rewrite eformat_adj, eformat_symm. apply H7. auto.
        apply (is_partial_lgraph_connected adde_u); auto.
    ****destruct H9. 2: contradiction. destruct H10. 2: contradiction. subst u0. subst v.
        split; intros; apply connected_refl; rewrite vert_bound; lia.
  **intros. rewrite remove_In_iff in H9; destruct H9.
    assert (~ adjacent mst' u0 v). apply Hinv_13. auto.
    unfold not; intros. destruct H12 as [e ?]. destruct (E_EqDec (eformat (u,Znth u parents)) e).
    hnf in e0. subst e.
    destruct H12. rewrite Hsrc, Hdst in H13.
    destruct (Z.le_ge_cases u (Znth u parents)).
      rewrite eformat1 in H13 by (simpl; lia). simpl in H13.
      destruct H13; destruct H13. symmetry in H13; contradiction.
      subst u0. contradiction.
      rewrite eformat2 in H13 by (simpl; lia). simpl in H13.
      destruct H13; destruct H13. subst u0; contradiction.
      symmetry in H15; contradiction.
    unfold RelationClasses.complement, Equivalence.equiv in c. apply H11.
    exists e. apply adde_adj_edge_rev in H12; auto.
    rewrite eformat_eq. auto.
  ++ (*Znth u keys = inf. Implies u has no other vertices from the mst that can connect to it. Thus, no change to graph*)
  Exists mst' fmst' parents' keys' pq_state' (popped_vertices+::u) (remove V_EqDec u unpopped_vertices).
  entailer!.
  clear H6 H7 H8 H10 H11 H12 H13 H15 H16 H18 Pv_pq HPv_pq Pv_pq0 Pv_out HPv_out Pv_out0 Pv_parent HPv_parent Pv_parent0 Pv_key HPv_key Pv_key0.
  rewrite Zlength_map in H9. rename H9 into HZlength_pq_state'.
  rewrite Zlength_map in H14. rename H14 into HZlength_parents'.
  rewrite Zlength_map in H17. rename H17 into HZlength_keys'.
  split3.
  **(*permutation of EList mst*)
    replace (filter (fun v : Z => Znth v parents' <? SIZE) (popped_vertices +:: u)) with
      (filter (fun v : Z => Znth v parents' <? SIZE) (popped_vertices)).
    2: { rewrite filter_app. simpl. destruct (Znth u parents' <? SIZE) eqn: bool.
    rewrite Z.ltb_lt in bool; lia.
    rewrite app_nil_r; auto. }
    replace (filter (fun v : Z => Znth v parents' <? SIZE) popped_vertices) with
      (filter (fun v : Z => Znth v parents <? SIZE) popped_vertices).
    2: { apply filter_ext_in. intros.
      replace (Znth a parents) with (Znth a parents'). auto.
      apply Hinv2_1. rewrite <- (vert_bound g). apply Hpopped_vvalid; auto.
      right; apply in_or_app; left; auto. }
    replace (map (fun v : Z => eformat (v, Znth v parents'))
     (filter (fun v : Z => Znth v parents <? SIZE) popped_vertices)) with
      (map (fun v : Z => eformat (v, Znth v parents))
     (filter (fun v : Z => Znth v parents <? SIZE) popped_vertices)). apply Hinv_9.
    apply map_ext_in. intros. rewrite filter_In in H6. destruct H6.
      replace (Znth a parents) with (Znth a parents'). auto.
      apply Hinv2_1. rewrite <- (vert_bound g). apply Hpopped_vvalid; auto.
      right; apply in_or_app; left; auto.
  **intros. apply in_app_or in H6; apply in_app_or in H7.
    destruct H6; destruct H7.
    ****(*both in popped_vertices*)apply Hinv_10; auto.
    ****(*v=u*) destruct H7. 2: contradiction. subst v.
      (*hm in this case, because Znth u parents = inf, NOTHING in popped_vertices should be connected in g or mst?*)
      split; intros.
      (*get a contradiction about ~connected g u0 u:
        thoughts: destruct p:=the path to u0 u.
        assert exists a v1 v2, both in p /\ In v1 popped /\ In v2 unpopped /\ adj g v1 v2
      *)
      destruct H7 as [p ?].
      apply (path_partition_checkpoint g popped_vertices unpopped_vertices p u0 u) in H7; auto.
      destruct H7 as [v1 [v2 [? [? [? [? ?]]]]]].
      (*
        Znth v2 pq_state = keys, because it is unpopped
        Znth v2 keys >= Znth u keys = inf, because u is popped first
        Then Znth v2 parents =SIZE using Hinv_7 and stuff
        but that violates Hinv_8
      *)
      assert (0 <= v2 < SIZE). rewrite <- (vert_bound g); apply Hunpopped_vvalid; auto.
      assert (Hv2_notin: ~ In v2 popped_vertices). {
      apply (NoDup_app_not_in V unpopped_vertices). apply (Permutation_NoDup (l:=popped_vertices++unpopped_vertices)).
      apply Permutation_app_comm. apply (Permutation_NoDup (l:=VList g)). apply Permutation_sym; apply Hinv_3.
      apply NoDup_VList. auto.
      }
      assert (Znth v2 parents = SIZE). {
        assert (0<=Znth v2 parents <= SIZE). apply Hinv_4; auto.
        destruct H13. apply Z.le_lteq in H14. destruct H14. 2: auto. exfalso.
        assert (Znth v2 pq_state = Znth v2 keys). rewrite Hinv_6 by lia.
          destruct (in_dec V_EqDec v2 popped_vertices). contradiction. auto.
        assert (Znth u pq_state = Znth u keys). rewrite Hinv_6 by lia.
          destruct (in_dec V_EqDec u popped_vertices). contradiction. auto.
        assert (Znth u keys <= Znth v2 keys). rewrite <- H15, <- H16. apply Hu_min; lia.
        assert (Znth v2 keys < inf). rewrite Hinv_5 by lia. destruct (V_EqDec v2 r). rewrite inf_literal; lia.
          apply (@edge_weight_not_inf _ _ _ (sound_MatrixUGraph g)). apply Hinv_7; lia.
        (*now so Znth u keys = inf*)
        destruct popped_vertices. contradiction.
        (*case u=r, then Znth v2 pq_state = Znth v2 keys should be = inf, lia. Easiest way to solve this is to hack Hinv_11*)
        (*edit: ok that was unnecessary, lots of things to kill off u=r*)
        (*case u<>r, then Znth u keys = elabel g (eformat (u, Znth u parents)), but Znth u parents = inf, so Znth u keys = inf. Then inf < inf*)
        assert( Znth u keys = elabel g (eformat (u,Znth u parents))). rewrite Hinv_5 by lia.
        destruct (V_EqDec u r). hnf in e.
          assert (In r (v::popped_vertices)). apply hd_error_In. apply Hinv_12.
          unfold not; intros. assert (In v (v::popped_vertices)). left; auto.
          rewrite H19 in H20; contradiction. subst u. contradiction.
          auto.
        rewrite H19 in H17. rewrite (@invalid_edge_weight _ _ _ (sound_MatrixUGraph g)) in H17. lia.
        unfold not; intros. rewrite H4 in H20. apply eformat_evalid_vvalid in H20. destruct H20.
        rewrite vert_bound in H21; lia.
      }
      exfalso. apply (Hinv_8 v2 H12 H13 v1).
      rewrite find_notIn, Z.add_0_r, sublist_same. auto. auto. auto.
      auto. auto.
      (*mst' -> g*) apply connected_symm in H7. destruct H7 as [p [? [? ?]]]. destruct p. inversion H8.
      inversion H8. destruct p. inversion H9. subst v. subst u0. apply connected_refl. rewrite vert_bound; lia.
      subst v. destruct H7. exfalso. apply (Hinv_13 u v0); auto.
    ****(*u0=u, which is repeat of above*) destruct H6. 2: contradiction. subst u0. rename H7 into H6.
      split; intros.
      (*g -> mst'*)
      apply connected_symm in H7. destruct H7 as [p ?].
      apply (path_partition_checkpoint g popped_vertices unpopped_vertices p v u) in H7; auto.
      destruct H7 as [v1 [v2 [? [? [? [? ?]]]]]].
(*
        Znth v2 pq_state = keys, because it is unpopped
        Znth v2 keys >= Znth u keys = inf, because u is popped first
        Then Znth v2 parents =SIZE using Hinv_7 and stuff
        but that violates Hinv_8
      *)
      assert (0 <= v2 < SIZE). rewrite <- (vert_bound g); apply Hunpopped_vvalid; auto.
      assert (Hv2_notin: ~ In v2 popped_vertices). {
      apply (NoDup_app_not_in V unpopped_vertices). apply (Permutation_NoDup (l:=popped_vertices++unpopped_vertices)).
      apply Permutation_app_comm. apply (Permutation_NoDup (l:=VList g)). apply Permutation_sym; apply Hinv_3.
      apply NoDup_VList. auto.
      }
      assert (Znth v2 parents = SIZE). {
        assert (0<=Znth v2 parents <= SIZE). apply Hinv_4; auto.
        destruct H13. apply Z.le_lteq in H14. destruct H14. 2: auto. exfalso.
        assert (Znth v2 pq_state = Znth v2 keys). rewrite Hinv_6 by lia.
          destruct (in_dec V_EqDec v2 popped_vertices). contradiction. auto.
        assert (Znth u pq_state = Znth u keys). rewrite Hinv_6 by lia.
          destruct (in_dec V_EqDec u popped_vertices). contradiction. auto.
        assert (Znth u keys <= Znth v2 keys). rewrite <- H15, <- H16. apply Hu_min; lia.
        assert (Znth v2 keys < inf). rewrite Hinv_5 by lia. destruct (V_EqDec v2 r). rewrite inf_literal; lia.
          apply (@edge_weight_not_inf _ _ _ (sound_MatrixUGraph g)). apply Hinv_7; lia.
        (*now so Znth u keys = inf*)
        destruct popped_vertices. contradiction.
        (*case u=r, then Znth v2 pq_state = Znth v2 keys should be = inf, lia. Easiest way to solve this is to hack Hinv_11*)
        (*edit: ok that was unnecessary, lots of things to kill off u=r*)
        (*case u<>r, then Znth u keys = elabel g (eformat (u, Znth u parents)), but Znth u parents = inf, so Znth u keys = inf. Then inf < inf*)
        assert( Znth u keys = elabel g (eformat (u,Znth u parents))). rewrite Hinv_5 by lia.
        destruct (V_EqDec u r). hnf in e.
          assert (In r (v0::popped_vertices)). apply hd_error_In. apply Hinv_12.
          unfold not; intros. assert (In v0 (v0::popped_vertices)). left; auto.
          rewrite H19 in H20; contradiction. subst u. contradiction.
          auto.
        rewrite H19 in H17. rewrite (@invalid_edge_weight _ _ _ (sound_MatrixUGraph g)) in H17. lia.
        unfold not; intros. rewrite H4 in H20. apply eformat_evalid_vvalid in H20. destruct H20.
        rewrite vert_bound in H21; lia.
      }
      exfalso. apply (Hinv_8 v2 H12 H13 v1).
      rewrite find_notIn, Z.add_0_r, sublist_same. auto. auto. auto.
      auto. auto.
      (*mst' -> g*) destruct H7 as [p [? [? ?]]]. destruct p. inversion H8.
      inversion H8. destruct p. inversion H9. subst v0. subst v. apply connected_refl. rewrite vert_bound; lia.
      subst v0. destruct H7. exfalso. apply (Hinv_13 u v1); auto.
    ****(*both=u*)destruct H6. 2: contradiction. destruct H7. 2: contradiction. subst u0; subst v.
    split; intros; apply connected_refl; rewrite vert_bound; lia.
    **intros. apply Hinv_13. rewrite remove_In_iff in H6; apply H6.
  }
  { (*break*) forward. (*no more vertices in queue*)
    assert (Hempty: priq_arr_utils.isEmpty pq_state = Vone). {
      destruct (priq_arr_utils.isEmptyTwoCases pq_state);
      rewrite H1 in H0; simpl in H0; now inversion H0.
    } clear H0.
    pose proof (priq_arr_utils.isEmptyMeansInf pq_state Hempty). clear Hempty. rewrite Forall_forall in H0.
    assert (Permutation popped_vertices (VList mst')). { apply NoDup_Permutation.
      apply Permutation_sym, Permutation_NoDup, NoDup_app_l in Hinv_3. auto. apply NoDup_VList.
      apply NoDup_VList. intros; split; intros.
      apply VList_vvalid. rewrite vert_bound. rewrite <- (vert_bound g). apply Hpopped_vvalid; auto.
      rewrite VList_vvalid, vert_bound, <- (vert_bound g), vert_bound in H1.
      assert (Znth x pq_state = (if in_dec V_EqDec x popped_vertices then inf + 1 else Znth x keys)). apply Hinv_6; auto.
      destruct (in_dec V_EqDec x popped_vertices). auto. exfalso. rewrite Hinv_5 in H2.
      assert (Znth x pq_state > priq_arr_utils.inf). apply H0. apply Znth_In. rewrite HZlength_pq_state. auto. 2: auto.
      rewrite <- inf_priq in H3.
      destruct (V_EqDec x r). rewrite inf_literal in H3; lia.
      rewrite H2 in H3. pose proof (weight_inf_bound g (eformat (x, Znth x parents))).
      (*how now brown cow, I can't lia*)
      apply Zgt_not_le in H3. contradiction.
    }
    Exists mst'. Exists fmst'. Exists popped_vertices. Exists parents. Exists keys.
    (*SEP matters*)
    replace (map Vint (map Int.repr pq_state)) with (list_repeat (Z.to_nat SIZE) (Vint (Int.repr (inf + 1)))). 2: {
      apply list_eq_Znth. do 2 rewrite Zlength_map. rewrite Zlength_list_repeat; lia.
      intros. rewrite Zlength_list_repeat in H2 by lia.
      rewrite Znth_list_repeat_inrange by lia. rewrite Znth_map. 2: rewrite Zlength_map; lia.
      rewrite Znth_map by lia. rewrite Hinv_6 by lia.
      destruct (in_dec V_EqDec i popped_vertices). auto.
      exfalso; apply n. apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto.
      rewrite VList_vvalid, vert_bound; auto.
    }
    replace (map (fun x : V =>
      if in_dec V_EqDec x popped_vertices then Vint (Int.repr 1) else Vint (Int.repr 0))
     (nat_inc_list (Z.to_nat SIZE))) with (list_repeat (Z.to_nat SIZE) (Vint (Int.repr 1))). 2: {
      apply list_eq_Znth. rewrite Zlength_map, Zlength_list_repeat, nat_inc_list_Zlength, Z2Nat.id by lia; auto.
      intros. rewrite Zlength_list_repeat in H2 by lia. rewrite Znth_list_repeat_inrange by lia.
      rewrite Znth_map. 2: rewrite nat_inc_list_Zlength, Z2Nat.id; lia.
      rewrite nat_inc_list_i. 2: rewrite Z2Nat.id; lia.
      destruct (in_dec V_EqDec i popped_vertices). auto.
      exfalso; apply n. apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto.
      rewrite VList_vvalid, vert_bound; auto.
    }
    entailer!.
    clear H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 Pv_pq HPv_pq Pv_pq0 Pv_out HPv_out Pv_out0 Pv_parent HPv_parent Pv_parent0 Pv_key HPv_key Pv_key0.
    split.
    ++unfold spanning; intros.
      split; intros. assert (vvalid g u /\ vvalid g v). apply connected_vvalid; auto. destruct H4.
      rewrite vert_bound, <- (vert_bound mst'), <- VList_vvalid in H4, H5.
      apply Hinv_10; auto.
      apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto. apply H4.
      apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto. apply H5.
      assert (vvalid mst' u /\ vvalid mst' v). apply connected_vvalid; auto. destruct H4.
      rewrite <- VList_vvalid in H4, H5.
      apply Hinv_10; auto.
      apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto. apply H4.
      apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto. apply H5.
    ++destruct popped_vertices. assert (vvalid mst' 0). rewrite vert_bound; lia.
      rewrite <- VList_vvalid in H3. apply (Permutation_in (l':=[])) in H3. contradiction.
      apply Permutation_sym; apply H1.
      apply Hinv_12. unfold not; intros. assert (In v (v::popped_vertices)) by (left; auto).
      rewrite H3 in H4; contradiction.
  }
}
(*POST-LOOP*) {
clear Hstarting_keys HZlength_starting_keys starting_keys.
Intros mst fmst popped_vertices parents keys.
rename H into Hinv_1; rename H0 into Hinv_2;
rename H1 into Hinv_3; rename H2 into Hinv_4;
rename H3 into Hinv_5; rename H4 into Hinv_6;
rename H5 into Hinv_7; rename H6 into Hinv_8;
rename H7 into Hinv_9.
(*Do the minimum proof here*)
assert (minimum_spanning_forest mst g). {
split. split. split. apply Hinv_1. split. apply Hinv_2. apply Hinv_7.
split. unfold preserve_vlabel; intros. destruct vlabel. destruct vlabel. auto.
unfold preserve_elabel; intros. apply Hinv_1. auto.
(*minimality proof*)
intros.
pose proof (@fin _ _ _ (@sound_MatrixUGraph inf SIZE t')) as ft'.
set (mst_list:=(map (fun v : Z => eformat (v, Znth v parents))
              (filter (fun v : Z => Znth v parents <? SIZE) popped_vertices))).
set (lsame := filter (fun e => in_dec E_EqDec e (EList t')) mst_list).
assert (incl lsame mst_list). { unfold lsame. apply filter_incl. }
assert (incl lsame (EList t')). { unfold lsame, incl. intros.
  rewrite filter_In in H1. destruct H1. Search in_dec true.
}

set (lmst := ).
(*
with this, lmst should be sorted based on popped_vertices
then we induct on lmst: (to get an lt where elabel g (Znth i lmst) <= elabel g (Znth i lt))
  nil case something something
  induct case: a::l => a is the earliest edge that was added,
    so map (fun u => (u, Znth u parents)) (sublist 0 (find popped_vertices a) popped_vertices) is in t'
    this means
do the same as kruskal: (sum (lsame++lmst) <= sum (ldiff))
*)
admit.
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