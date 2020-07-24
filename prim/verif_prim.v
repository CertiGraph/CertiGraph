Require Import VST.floyd.proofauto.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.FiniteGraph.
Require Import RamifyCoq.graph.undirected_graph.
Require Import RamifyCoq.graph.AdjMatGraph.
Require Import RamifyCoq.prim.MatrixUGraph.
Require Import RamifyCoq.prim.prim.
Require Import RamifyCoq.prim.spatial_undirected_matrix.
Require Import RamifyCoq.prim.specs_prim.

Local Open Scope Z.

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

Lemma body_prim: semax_body Vprog Gprog f_prim prim_spec.
Proof.
start_function.
pose proof inf_repable as inf_repable.
(*replace all data_at_ with data_at Vundef*)
repeat rewrite data_at__tarray.
set (k:=default_val tint); compute in k; subst k.
forward_call (Tsh, v_key, (list_repeat (Z.to_nat 8) Vundef), inf).
forward_call (Tsh, v_parent, (list_repeat (Z.to_nat 8) Vundef), inf).
forward_call (Tsh, v_out, (list_repeat (Z.to_nat 8) Vundef), 0).
assert (Hrbound: 0 <= r < SIZE). apply (@vert_representable inf SIZE g (sound_MatrixUGraph g)) in H0; auto.
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
      data_at Tsh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr inf))) v_parent;
      data_at Tsh (tarray tint SIZE) starting_keys v_key;
      data_at Tsh (tarray tint 8) (sublist 0 i starting_keys ++ sublist i SIZE (list_repeat (Z.to_nat 8) Vundef)) v_pq;
      undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr);
      undirected_matrix sh (graph_to_symm_mat (@edgeless_graph inf SIZE SIZE_rep)) (pointer_val_val mstptr))
  )%assert.
entailer!. (*precon taken care of*)
(*loop*)
forward.
assert (Znth i starting_keys = Vint (Int.repr (Znth i (upd_Znth r (list_repeat (Z.to_nat SIZE) inf) 0)))). {
  unfold starting_keys. rewrite Znth_map; auto.
  rewrite Zlength_upd_Znth. rewrite Zlength_list_repeat; lia.
}
forward_call (v_pq, i, Znth i (upd_Znth r (list_repeat (Z.to_nat SIZE) inf) 0), sublist 0 i starting_keys ++ sublist i SIZE (list_repeat (Z.to_nat 8) Vundef)).
entailer!. unfold priq_arr_utils.SIZE.
rewrite upd_Znth_app2. rewrite Zlength_sublist, Z.sub_0_r, Z.sub_diag; try lia.
rewrite (sublist_split i (i+1) SIZE). rewrite (sublist_one i (i+1)). rewrite upd_Znth_app1.
rewrite upd_Znth0. rewrite app_assoc.
rewrite (sublist_split 0 i (i+1)). rewrite (sublist_one i (i+1)). rewrite <- H2. entailer!.
all: try lia.
rewrite Zlength_cons, Zlength_nil; lia.
rewrite Zlength_list_repeat. unfold SIZE in H1; lia. lia.
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
  EX parents: list V,
  EX keys: list DE,
  EX pq_state: list Z,
  EX popped_vertices: list V,
    PROP (
      (*graph stuff*)
      is_partial_lgraph mst' g;
      forall v, vvalid g v <-> vvalid mst' v;
      uforest' mst';
      (*about the lists*)
      forall v, In v popped_vertices -> vvalid g v;
      forall u v, In u popped_vertices -> In v popped_vertices -> connected mst' u v;
      Zlength keys = SIZE;
      forall v, 0 <= v < SIZE -> 0 <= Znth v keys <= inf;
      Zlength pq_state = SIZE;
      forall v, 0 <= v < SIZE -> ~ In v popped_vertices -> Znth v pq_state = Znth v keys;
      forall v, In v popped_vertices -> Znth v pq_state = Z.add inf 1
      (*something about weight of edges already added to mst*)
      (*something about when an edge is added, one of its vertices is in the old list, one isn't*)
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
      data_at Tsh (tarray tint SIZE) (map (fun x => Vint (Int.repr x)) pq_state) v_pq;
      undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr);
      undirected_matrix sh (graph_to_symm_mat mst') (pointer_val_val mstptr)
    )
  )
break: (
  EX mst:G,
  EX parents: list V,
  EX keys: list DE,
    PROP (
      is_partial_graph mst g;
      forall v, vvalid g v <-> vvalid mst v;
      uforest' mst;
      forall u v, connected mst u v
      (*something about weight*)
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
      undirected_matrix sh (graph_to_symm_mat mst) (pointer_val_val mstptr)
    )
  )
%assert.
(*PRECON*) {
Exists (@edgeless_graph inf SIZE SIZE_rep).
Exists (list_repeat (Z.to_nat SIZE) inf).
Exists (upd_Znth r (list_repeat (Z.to_nat SIZE) inf) 0).
Exists (upd_Znth r (list_repeat (Z.to_nat SIZE) inf) 0).
Exists (sublist 0 0 (VList g)). (*<--rubbish, is nil*) rewrite sublist_nil.
entailer!.
split3. 3: split3. 5: split.
+split. split. intros. rewrite (@vert_representable _ _ _ (sound_MatrixUGraph _)) in H12.
rewrite (@vert_representable _ _ _ (sound_MatrixUGraph _)). auto.
split3; intros; pose proof (@edgeless_graph_evalid inf SIZE SIZE_rep e); contradiction.
split. unfold preserve_vlabel; intros. simpl. destruct (vlabel g v). auto.
unfold preserve_elabel; intros. pose proof (@edgeless_graph_evalid inf SIZE SIZE_rep e); contradiction.
+intros. rewrite (@vert_representable _ _ g (sound_MatrixUGraph _)).
rewrite (@vert_representable _ _ _ (sound_MatrixUGraph _)). lia.
+apply uforest'_edgeless_graph.
+rewrite Zlength_upd_Znth, Zlength_list_repeat; lia.
+intros. destruct (Z.eq_dec v r). subst v. rewrite upd_Znth_same.
set (k:=inf); compute in k; lia. rewrite Zlength_list_repeat; lia.
rewrite upd_Znth_diff. rewrite Znth_list_repeat_inrange.
set (k:=inf); compute in k; lia. lia.
rewrite Zlength_list_repeat; lia.
rewrite Zlength_list_repeat; lia. auto.
+rewrite Zlength_upd_Znth, Zlength_list_repeat; lia.
(*other PROPs*)

}
(*MAIN LOOP*) {
clear Hstarting_keys HZlength_starting_keys starting_keys.
Intros mst' parents keys pq_state popped_vertices.
assert (priq_arr_utils.inrange_priq pq_state). {
  unfold priq_arr_utils.inrange_priq. rewrite Forall_forall. intros x Hx.
  rewrite In_Znth_iff in Hx. destruct Hx as [i [? ?]]. rewrite H8 in H11.
  destruct (in_dec V_EqDec i popped_vertices).
  rewrite H10 in H12; auto. subst x. rewrite <- inf_priq. set (j:=inf); compute in j; subst j; lia.
  rewrite H9 in H12; auto. subst x. assert (0 <= Znth i keys <= inf). apply H7; auto. rewrite <- inf_priq. lia.
}
forward_call (v_pq, pq_state).
unfold priq_arr_utils.SIZE, SIZE. rewrite list_map_compose. entailer!.
forward_if.
(*PROCEED WITH LOOP*) {
assert (priq_arr_utils.isEmpty pq_state = Vzero). {
  destruct (priq_arr_utils.isEmptyTwoCases pq_state);
  rewrite H13 in H12; simpl in H12; now inversion H12.
}
forward_call (v_pq, pq_state). Intros u.
(* u is the minimally chosen item from the
   "seen but not popped" category of vertices *)
assert (vvalid g u). {
  admit.
}
forward. rewrite (@vert_representable _ _ _ (sound_MatrixUGraph g)) in H9. entailer!.
(*for loop to update un-popped vertices' min weight*)
}
(*BREAK CONDITION*) {
}
admit.
}
(*POST-LOOP*) {
Intros mst parents keys.
(*Do the minimum proof here*)
(*Should we bother with filling a matrix for it? The original Prim doesn't bother
Well I guess we need to return the graph somehow, as parents is a local array so we need to pass it out
*)
admit.
}
Abort.
