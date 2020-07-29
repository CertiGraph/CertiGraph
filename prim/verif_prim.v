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
start_function. rename H1 into Hnonneg.
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
  EX fmst': FiniteGraph mst',
  EX parents: list V,
  EX keys: list DE,
  EX pq_state: list Z,
  EX popped_vertices: list V,
  EX unpopped_vertices: list V,
    PROP (
      (*graph stuff*)
      is_partial_lgraph mst' g;
      forall v, vvalid g v <-> vvalid mst' v;
      uforest' mst';
      (*about the lists*)
      Permutation (popped_vertices++unpopped_vertices) (VList g);
      forall u v, In u popped_vertices -> In v popped_vertices -> connected mst' u v;
      (*if a vertex has been popped, then its "parent" a.k.a. edge has been decided*)
      forall v, In v popped_vertices -> (exists i, v = Znth i popped_vertices /\
        (exists u, In u (sublist 0 i popped_vertices) /\ evalid mst' (eformat (u,v)) /\
        Znth v parents = u  /\ Znth v keys = elabel mst' (eformat (u,v))));
      forall v, 0 <= v < SIZE -> 0 <= Znth v keys <= inf;
      forall v, In v unpopped_vertices -> Znth v pq_state = Znth v keys; (*<--describing pq_state instead of forming a function, because it seems hard to prove list eq...*)
      forall v, In v popped_vertices -> Znth v pq_state = Z.add inf 1;
      Zlength parents = SIZE;
      Zlength keys = SIZE;
      Zlength pq_state = SIZE
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
  EX fmst: FiniteGraph mst,
  EX popped_vertices: list V,
  EX parents: list V,
  EX keys: list DE,
    PROP (
      is_partial_lgraph mst g;
      forall v, vvalid g v <-> vvalid mst v;
      uforest' mst;
      connected_graph mst;
      Permutation popped_vertices (VList mst);
      forall v, In v popped_vertices -> (exists i, v = Znth i popped_vertices /\
        (exists u, In u (sublist 0 i popped_vertices) /\ evalid mst (eformat (u,v)) /\
        Znth v parents = u  /\
        Znth v keys = elabel mst (eformat (u,v))))
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
Exists edgeless_graph'.
Exists (@fin _ _ _ (sound_MatrixUGraph edgeless_graph')).
Exists (list_repeat (Z.to_nat SIZE) inf).
Exists (upd_Znth r (list_repeat (Z.to_nat SIZE) inf) 0).
Exists (upd_Znth r (list_repeat (Z.to_nat SIZE) inf) 0).
Exists (sublist 0 0 (VList g)). (*<--rubbish, is nil*) rewrite sublist_nil.
Exists (VList g).
entailer!.
split3. 3: split3. 5: split.
+split. split. intros. rewrite (@vert_representable _ _ _ (sound_MatrixUGraph _)) in H12.
rewrite (@vert_representable _ _ _ (sound_MatrixUGraph _)). auto.
split3; intros; pose proof (@edgeless_graph_evalid inf SIZE inf_rep SIZE_rep e); contradiction.
split. unfold preserve_vlabel; intros. simpl. destruct (vlabel g v). auto.
unfold preserve_elabel; intros. pose proof (@edgeless_graph_evalid inf SIZE inf_rep SIZE_rep e); contradiction.
+intros. rewrite (@vert_representable _ _ g (sound_MatrixUGraph _)).
rewrite (@vert_representable _ _ _ (sound_MatrixUGraph _)). lia.
+unfold edgeless_graph'. apply uforest'_edgeless_graph.
+intros. destruct (Z.eq_dec v r). subst v. rewrite upd_Znth_same.
set (k:=inf); compute in k; lia. rewrite Zlength_list_repeat; lia.
rewrite upd_Znth_diff. rewrite Znth_list_repeat_inrange.
set (k:=inf); compute in k; lia. lia.
rewrite Zlength_list_repeat; lia.
rewrite Zlength_list_repeat; lia. auto.
+rewrite Zlength_upd_Znth, Zlength_list_repeat; lia.
+rewrite Zlength_upd_Znth, Zlength_list_repeat; lia.
(*other PROPs*)
}
(*MAIN LOOP*) {
  clear Hstarting_keys HZlength_starting_keys starting_keys.
  Intros mst' fmst' parents keys pq_state popped_vertices unpopped_vertices.
  (*do a mass renaming for convenience*)
  rename H1 into Hinv_1; rename H2 into Hinv_2;
  rename H3 into Hinv_3; rename H4 into Hinv_4;
  rename H5 into Hinv_5; rename H6 into Hinv_6;
  rename H7 into Hinv_7; rename H8 into Hinv_8;
  rename H9 into Hinv_9; rename H10 into Hinv_10;
  rename H11 into Hinv_11; rename H12 into Hinv_12.
  assert (Hpopped_or_unpopped: forall v, vvalid g v -> In v popped_vertices \/ In v unpopped_vertices). {
    intros. apply in_app_or. apply (Permutation_in (l:=VList g)). apply Permutation_sym; auto. apply VList_vvalid; auto.
  }
  assert (priq_arr_utils.inrange_priq pq_state). {
    unfold priq_arr_utils.inrange_priq. rewrite Forall_forall. intros x Hx.
    rewrite In_Znth_iff in Hx. destruct Hx as [i [? ?]]. rewrite <- inf_priq.
    destruct (Hpopped_or_unpopped i).
    rewrite (@vert_representable _ _ _ (sound_MatrixUGraph g)); rewrite <- Hinv_12; lia.
    rewrite Hinv_9 in H2; auto. subst x. set (j:=inf); compute in j; subst j; lia.
    rewrite Hinv_8 in H2; auto. subst x. assert (0 <= Znth i keys <= inf). apply Hinv_7; lia. lia.
  }
  forward_call (v_pq, pq_state).
  unfold priq_arr_utils.SIZE, SIZE. rewrite list_map_compose. entailer!.
  forward_if.
  (*PROCEED WITH LOOP*) {
  assert (priq_arr_utils.isEmpty pq_state = Vzero). {
    destruct (priq_arr_utils.isEmptyTwoCases pq_state);
    rewrite H3 in H2; simpl in H2; now inversion H2.
  }
  forward_call (v_pq, pq_state). Intros u. rename H4 into Hu.
  (* u is the minimally chosen item from the
     "seen but not popped" category of vertices *)
  assert (0 <= u < SIZE). {
    rewrite Hu. rewrite <- Hinv_12.
    apply find_range.
    apply min_in_list. apply incl_refl.
    destruct pq_state. rewrite Zlength_nil in Hinv_12.
    inversion Hinv_12. simpl. left; trivial.
  }
  assert (Hu_unpopped: ~ In u popped_vertices). { unfold not; intros.
    apply Hinv_9 in H5. assert (Znth u pq_state < priq_arr_utils.inf + 1). apply (find_min_lt_inf u pq_state Hu H3).
    rewrite Hinv_12; lia. rewrite <- inf_priq in H6. lia.
  }
  forward.
  replace (upd_Znth u (map (fun x : V =>
    if in_dec V_EqDec x popped_vertices then Vint (Int.repr 1) else Vint (Int.repr 0))
    (nat_inc_list (Z.to_nat 8))) (Vint (Int.repr 1))) with (map (fun x : V =>
    if in_dec V_EqDec x (u::popped_vertices) then Vint (Int.repr 1) else Vint (Int.repr 0))
    (nat_inc_list (Z.to_nat 8))).
  2: {
    apply list_eq_Znth. rewrite Zlength_upd_Znth. do 2 rewrite Zlength_map. auto.
    intros. rewrite Zlength_map in H5. rewrite nat_inc_list_Zlength in H5.
    destruct (Z.eq_dec i u). subst i.
    +rewrite upd_Znth_same. rewrite Znth_map.
    rewrite nat_inc_list_i. assert (In u (u::popped_vertices)). left; auto.
    destruct (in_dec V_EqDec u (u :: popped_vertices)). auto. contradiction.
    lia. rewrite nat_inc_list_Zlength; lia.
    rewrite Zlength_map, nat_inc_list_Zlength; lia.
    +rewrite upd_Znth_diff. rewrite Znth_map. rewrite Znth_map. rewrite nat_inc_list_i.
    destruct (in_dec V_EqDec i (u :: popped_vertices));
    destruct (in_dec V_EqDec i popped_vertices). auto. destruct i0; [symmetry in H6; contradiction | contradiction].
    assert (In i (u:: popped_vertices)). right; auto. contradiction.
    auto. auto. rewrite nat_inc_list_Zlength; auto. rewrite nat_inc_list_Zlength; auto.
    rewrite Zlength_map, nat_inc_list_Zlength; auto.
    rewrite Zlength_map, nat_inc_list_Zlength; auto.
    auto.
  }
  rewrite upd_Znth_map. rewrite upd_Znth_map. rewrite list_map_compose. (*pq state*)
  replace (Znth 0 pq_state) with (hd 0 pq_state). rewrite <- Hu. 2: { destruct pq_state. rewrite Zlength_nil in Hinv_12; lia. simpl. rewrite Znth_0_cons. auto. }
  clear Hu. set (pq_state'':=upd_Znth u pq_state (priq_arr_utils.inf + 1)).
  (*for loop to update un-popped vertices' min weight.
  The result is every vertex who's NOT in popped_vertices and connected, as their weight maintained or lowered*)
  forward_for_simple_bound SIZE (
    EX i: Z,
    EX parents': list Z,
    EX keys': list Z,
    EX pq_state': list Z,
      PROP (
        forall v, 0<=v<i -> (~adjacent g u v \/ In v (u::popped_vertices)) -> (
          Znth v parents' = Znth v parents /\
          Znth v keys' = Znth v keys /\
          Znth v pq_state' = Znth v pq_state'');
        forall v, 0<=v<i -> adjacent g u v -> ~ In v (u::popped_vertices) -> (
          Znth v parents' = (if Z.ltb (elabel g (eformat (u,v))) (Znth v pq_state'') then u else Znth v parents) /\
          Znth v keys' = Z.min (elabel g (eformat (u,v))) (Znth v pq_state'') /\
          Znth v pq_state' = Z.min (elabel g (eformat (u,v))) (Znth v pq_state''));
        forall v, i<=v<SIZE -> (
          Znth v parents' = Znth v parents /\
          Znth v keys' = Znth v keys /\
          Znth v pq_state' = Znth v pq_state''
        ); (*no change otherwise*)
        forall v, 0 <= v < SIZE -> 0 <= Znth v keys' <= inf;
        Zlength parents' = SIZE;
        Zlength keys' = SIZE;
        Zlength pq_state' = SIZE
        (*stuff about the keys and parents?*)
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
           if in_dec V_EqDec x (u :: popped_vertices) then Vint (Int.repr 1) else Vint (Int.repr 0))
          (nat_inc_list (Z.to_nat 8))) v_out;
     data_at Tsh (tarray tint 8) (map (fun x : Z => Vint (Int.repr x)) parents') v_parent;
     data_at Tsh (tarray tint 8) (map (fun x : Z => Vint (Int.repr x)) keys') v_key;
     undirected_matrix sh (graph_to_symm_mat g) (pointer_val_val gptr);
     undirected_matrix sh (graph_to_symm_mat mst') (pointer_val_val mstptr)
      )
    )
  %assert.
  (*precon*) {
  Exists parents. Exists keys. Exists pq_state''. entailer!.
    unfold pq_state''; rewrite Zlength_upd_Znth. auto.
  }
  (*loop*)
  assert (is_int I32 Signed (if in_dec V_EqDec (Znth i (nat_inc_list (Z.to_nat 8))) (u :: popped_vertices)
    then Vint (Int.repr 1) else Vint (Int.repr 0))). {
    unfold is_int. rewrite nat_inc_list_i. 2: rewrite Z2Nat.id; unfold SIZE in H5; lia.
    destruct (in_dec V_EqDec i (u :: popped_vertices)); auto.
  } forward.
  rename H7 into Hinv2_1; rename H8 into Hinv2_2;
  rename H9 into Hinv2_3; rename H10 into Hinv2_4;
  rename H11 into Hinv2_5; rename H12 into Hinv2_6;
  rename H13 into Hinv2_7.
  rewrite nat_inc_list_i. 2: rewrite Z2Nat.id; unfold SIZE in H5; lia.
  set (out_i:=if in_dec V_EqDec i (u :: popped_vertices)
               then Vint (Int.repr 1)
               else Vint (Int.repr 0)). fold out_i.
  forward_if.
  (**In queue**)
  +assert (~ In i (u::popped_vertices)). { unfold not; intros. destruct H8. subst i.
    unfold typed_true in H7. destruct (V_EqDec u u). simpl in H7. inversion H7.
    destruct (in_dec V_EqDec u popped_vertices). contradiction. unfold RelationClasses.complement, Equivalence.equiv in c; contradiction.
    destruct (V_EqDec u i). unfold Equivalence.equiv in e; subst i. contradiction.
    destruct (in_dec V_EqDec i popped_vertices). simpl in H7. inversion H7. contradiction.
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
    rewrite Z.add_0_l. unfold SIZE in H5; lia. unfold SIZE in H4; lia. auto.
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
    assert (Hadj_ui: adjacent g u i). {
      rewrite eformat_adj.
      rewrite graph_to_mat_eq in H12. 2: lia. 2: lia. rewrite eformat_symm in H12.
      rewrite Int.signed_repr in H12. rewrite Int.signed_repr in H12.
      unfold not; intros. assert (Znth i keys' <= inf). apply Hinv2_4. lia.
      rewrite <- H13 in H14. apply Zlt_not_le in H12. contradiction.
      assert (0 <= Znth i keys' <= inf). apply Hinv2_4; lia.
      set (k:=Int.min_signed); compute in k; subst k.
      set (k:=Int.max_signed); compute in k; subst k. rewrite inf_literal in H13; lia.
      apply weight_representable.
    }
    forward. forward. forward. forward. entailer!.
    rewrite upd_Znth_same. simpl. auto. rewrite Zlength_map. rewrite Hinv2_6. auto.
    rewrite upd_Znth_same. 2: { simpl. auto. rewrite Zlength_map. rewrite Hinv2_6. auto. }
    forward_call (v_pq, i, Znth i (Znth u (graph_to_symm_mat g)), pq_state').
    replace (map (fun x : Z => Vint (Int.repr x)) pq_state') with (map Vint (map Int.repr pq_state')).
    entailer!. rewrite list_map_compose. auto.
    Exists (upd_Znth i parents' u).
    Exists (upd_Znth i keys' (Znth i (Znth u (graph_to_symm_mat g)))).
    Exists (upd_Znth i pq_state' (Znth i (Znth u (graph_to_symm_mat g)))).
    rewrite (graph_unfold _ (graph_to_symm_mat g) _ u). unfold list_rep.
    rewrite list_map_compose. repeat rewrite (upd_Znth_map (fun x => Vint (Int.repr x))). unfold SIZE.
    entailer!.
    { split3. 3: split3. 5: split3. all: clear H2 H7.
    *intros. destruct (Z.lt_trichotomy v i). repeat rewrite upd_Znth_diff; try lia. apply Hinv2_1. lia. apply H7.
    destruct H31. subst v. destruct H7. contradiction. contradiction. lia.
    *admit.
    *intros. repeat rewrite upd_Znth_diff; try lia. apply Hinv2_3. unfold SIZE; lia.
      rewrite Hinv2_7. unfold SIZE; lia.
      rewrite Hinv2_6. unfold SIZE; lia.
      rewrite Hinv2_5. unfold SIZE; lia.
    *intros. destruct (Z.eq_dec v i). subst i. rewrite upd_Znth_same.
      apply Hnonneg. rewrite Hinv2_6. unfold SIZE; auto. rewrite upd_Znth_diff.
      apply Hinv2_4. unfold SIZE; auto. rewrite Hinv2_6; unfold SIZE; lia.
      rewrite Hinv2_6; lia. auto.
    *rewrite Zlength_upd_Znth. fold SIZE; apply Hinv2_5.
    *rewrite Zlength_upd_Znth. fold SIZE; apply Hinv2_6.
    *rewrite Zlength_upd_Znth. fold SIZE; apply Hinv2_7.
    }
    entailer!.
    unfold graph_to_symm_mat. rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; lia.
    -forward. (*nothing changed*)
    Exists parents'. Exists keys'. Exists pq_state'.
    rewrite (graph_unfold _ (graph_to_symm_mat g) _ u). unfold list_rep.
    2: unfold graph_to_symm_mat; rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; lia.
    entailer!.
    split3.
    *intros. destruct (Z.lt_trichotomy v i). apply Hinv2_1; auto. lia. destruct H33. subst v. apply Hinv2_3. lia. lia.
    *admit.
    *intros. apply Hinv2_3. lia.
  +(*nothing changed because out of pq*)
  assert (In i (u::popped_vertices)). {
    unfold typed_false in H7. destruct (V_EqDec u i); simpl in H7. unfold Equivalence.equiv in e; subst i. left; auto.
    destruct (in_dec V_EqDec i popped_vertices); simpl in H7. right; auto.
    inversion H7.
  }
  forward.
  Exists parents'. Exists keys'. Exists pq_state'. (*hm, it's the same as above...*)
  rewrite (graph_unfold _ (graph_to_symm_mat g) _ u). unfold list_rep.
  2: unfold graph_to_symm_mat; rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; lia.
  entailer!.
  split3.
  *intros. destruct (Z.lt_trichotomy v i). apply Hinv2_1; auto. lia. destruct H29. subst v. apply Hinv2_3. lia. lia.
  *admit.
  *intros. apply Hinv2_3. lia.
  +(*inner loop done, postcon leading to next outer loop iter*)
  Intros parents' keys' pq_state'.
  (*need to split into two cases: if Znth u keys = inf, then it's the same mst. Else, it's adde(eformat (u, Znth u keys))*)
  (*destruct (Z.le_lteq (Znth u keys) inf).*)
  admit.
  }
  { (*break*) forward. (*no more vertices in queue*)
    assert (Permutation popped_vertices (VList g)). admit.
    Exists mst'. Exists fmst'. Exists popped_vertices. Exists parents. Exists keys. entailer!.
    split. auto.
    admit.
  }
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
 e