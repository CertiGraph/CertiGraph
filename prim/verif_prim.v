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

Lemma SIZE_priq:
SIZE = priq_arr_utils.SIZE.
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
start_function. rename H into Hprecon_1.
pose proof inf_repable as inf_repable.
(*replace all data_at_ with data_at Vundef*)
repeat rewrite data_at__tarray.
set (k:=default_val tint); compute in k; subst k.
forward_call (Tsh, v_key, (list_repeat (Z.to_nat 8) Vundef), inf).
forward_call (Tsh, v_parent, (list_repeat (Z.to_nat 8) Vundef), inf).
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
      (*if a vertex has been popped, then its "parent" a.k.a. edge has been decided*)
      forall v, In v popped_vertices -> (exists i, v = Znth i popped_vertices /\
        (exists u, In u (sublist 0 i popped_vertices) /\ evalid mst' (eformat (u,v)) /\
        Znth v parents = u  /\ Znth v keys = elabel mst' (eformat (u,v)))); (*missing: the edge is the lowest of all vertices that came before it*)
      forall v, 0 <= v < SIZE -> Int.min_signed <= Znth v keys <= inf;
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
+split. split. intros. rewrite (@vert_representable _ _ _ (sound_MatrixUGraph _)) in H10.
rewrite (@vert_representable _ _ _ (sound_MatrixUGraph _)). auto.
split3; intros; pose proof (@edgeless_graph_evalid inf SIZE inf_rep SIZE_rep e); contradiction.
split. unfold preserve_vlabel; intros. simpl. destruct (vlabel g v). auto.
unfold preserve_elabel; intros. pose proof (@edgeless_graph_evalid inf SIZE inf_rep SIZE_rep e); contradiction.
+intros. rewrite (@vert_representable _ _ g (sound_MatrixUGraph _)).
rewrite (@vert_representable _ _ _ (sound_MatrixUGraph _)). lia.
+unfold edgeless_graph'. apply uforest'_edgeless_graph.
+intros. destruct (Z.eq_dec v r). subst v. rewrite upd_Znth_same.
split. pose proof Int.min_signed_neg; lia. rewrite inf_literal; lia.
rewrite Zlength_list_repeat; lia.
rewrite upd_Znth_diff. rewrite Znth_list_repeat_inrange.
pose proof inf_repable; unfold repable_signed in H11; lia. lia.
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
  rename H into Hinv_1; rename H0 into Hinv_2;
  rename H1 into Hinv_3; rename H2 into Hinv_4;
  rename H3 into Hinv_5; rename H4 into Hinv_6;
  rename H5 into Hinv_7; rename H6 into Hinv_8;
  rename H7 into Hinv_9; rename H8 into Hinv_10;
  rename H9 into Hinv_11.
  assert (Hpopped_or_unpopped: forall v, vvalid g v -> In v popped_vertices \/ In v unpopped_vertices). {
    intros. apply in_app_or. apply (Permutation_in (l:=VList g)). apply Permutation_sym; auto. apply VList_vvalid; auto.
  }
  assert (priq_arr_utils.inrange_priq pq_state). {
    unfold priq_arr_utils.inrange_priq. rewrite Forall_forall. intros x Hx.
    rewrite In_Znth_iff in Hx. destruct Hx as [i [? ?]]. rewrite <- inf_priq.
    destruct (Hpopped_or_unpopped i).
    rewrite (@vert_representable _ _ _ (sound_MatrixUGraph g)); rewrite <- Hinv_11; lia.
    rewrite Hinv_8 in H0; auto. subst x. pose proof inf_repable; unfold repable_signed in H0; lia.
    rewrite Hinv_7 in H0; auto. subst x. assert (Int.min_signed <= Znth i keys <= inf). apply Hinv_6; lia. lia.
  }
  forward_call (v_pq, pq_state).
  unfold priq_arr_utils.SIZE, SIZE. rewrite list_map_compose. entailer!.
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
    rewrite Hu. rewrite <- Hinv_11.
    apply find_range.
    apply min_in_list. apply incl_refl.
    destruct pq_state. rewrite Zlength_nil in Hinv_11.
    inversion Hinv_11. simpl. left; trivial.
  }
  assert (Hu_not_popped: ~ In u popped_vertices). { unfold not; intros.
    apply Hinv_8 in H3. assert (Znth u pq_state < priq_arr_utils.inf + 1). apply (find_min_lt_inf u pq_state Hu H1).
    rewrite Hinv_11; lia. rewrite <- inf_priq in H4. lia.
  }
  assert (Hu_unpopped: In u unpopped_vertices). { destruct (Hpopped_or_unpopped u).
    rewrite (@vert_representable _ _ _ (sound_MatrixUGraph g)). auto. contradiction. auto.
  }
  forward.
  replace (upd_Znth u (map (fun x : V =>
    if in_dec V_EqDec x popped_vertices then Vint (Int.repr 1) else Vint (Int.repr 0))
    (nat_inc_list (Z.to_nat 8))) (Vint (Int.repr 1))) with (map (fun x : V =>
    if in_dec V_EqDec x (u::popped_vertices) then Vint (Int.repr 1) else Vint (Int.repr 0))
    (nat_inc_list (Z.to_nat 8))).
  2: {
    apply list_eq_Znth. rewrite Zlength_upd_Znth. do 2 rewrite Zlength_map. auto.
    intros. rewrite Zlength_map in H3. rewrite nat_inc_list_Zlength in H3.
    destruct (Z.eq_dec i u). subst i.
    +rewrite upd_Znth_same. rewrite Znth_map.
    rewrite nat_inc_list_i. assert (In u (u::popped_vertices)). left; auto.
    destruct (in_dec V_EqDec u (u :: popped_vertices)). auto. contradiction.
    lia. rewrite nat_inc_list_Zlength; lia.
    rewrite Zlength_map, nat_inc_list_Zlength; lia.
    +rewrite upd_Znth_diff. rewrite Znth_map. rewrite Znth_map. rewrite nat_inc_list_i.
    destruct (in_dec V_EqDec i (u :: popped_vertices));
    destruct (in_dec V_EqDec i popped_vertices). auto. destruct i0; [symmetry in H4; contradiction | contradiction].
    assert (In i (u:: popped_vertices)). right; auto. contradiction.
    auto. auto. rewrite nat_inc_list_Zlength; auto. rewrite nat_inc_list_Zlength; auto.
    rewrite Zlength_map, nat_inc_list_Zlength; auto.
    rewrite Zlength_map, nat_inc_list_Zlength; auto.
    auto.
  }
  rewrite upd_Znth_map. rewrite upd_Znth_map. rewrite list_map_compose. (*pq state*)
  replace (Znth 0 pq_state) with (hd 0 pq_state). rewrite <- Hu. 2: { destruct pq_state. rewrite Zlength_nil in Hinv_11; lia. simpl. rewrite Znth_0_cons. auto. }
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
        forall v, 0 <= v < SIZE -> Int.min_signed <= Znth v keys' <= inf;
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
    unfold is_int. rewrite nat_inc_list_i. 2: rewrite Z2Nat.id; unfold SIZE in H3; lia.
    destruct (in_dec V_EqDec i (u :: popped_vertices)); auto.
  } forward.
  rename H5 into Hinv2_1; rename H6 into Hinv2_2;
  rename H7 into Hinv2_3; rename H8 into Hinv2_4;
  rename H9 into Hinv2_5; rename H10 into Hinv2_6;
  rename H11 into Hinv2_7.
  rewrite nat_inc_list_i. 2: rewrite Z2Nat.id; unfold SIZE in H3; lia.
  set (out_i:=if in_dec V_EqDec i (u :: popped_vertices)
               then Vint (Int.repr 1)
               else Vint (Int.repr 0)). fold out_i.
  forward_if.
  (**In queue**)
  +assert (~ In i (u::popped_vertices)). { unfold not; intros. destruct H6. subst i.
    unfold typed_true in H5. destruct (V_EqDec u u). simpl in H5. inversion H5.
    destruct (in_dec V_EqDec u popped_vertices). contradiction. unfold RelationClasses.complement, Equivalence.equiv in c; contradiction.
    destruct (V_EqDec u i). unfold Equivalence.equiv in e; subst i. contradiction.
    destruct (in_dec V_EqDec i popped_vertices). simpl in H5. inversion H5. contradiction.
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
    assert (Hadj_ui: adjacent g u i). {
      rewrite eformat_adj.
      rewrite graph_to_mat_eq in H10. 2: lia. 2: lia. rewrite eformat_symm in H10.
      rewrite Int.signed_repr in H10. rewrite Int.signed_repr in H10.
      unfold not; intros. assert (Znth i keys' <= inf). apply Hinv2_4. lia.
      apply (Z.lt_le_trans _ (Znth i keys')); auto.
      assert (Int.min_signed <= Znth i keys' <= inf). apply Hinv2_4; lia.
      set (k:=Int.max_signed); compute in k; subst k. rewrite inf_literal in H11; lia.
      apply weight_representable.
    }
    forward. forward. forward. forward. entailer!.
    rewrite upd_Znth_same. simpl. auto. rewrite Zlength_map. rewrite Hinv2_6. auto.
    rewrite upd_Znth_same. 2: { simpl. auto. rewrite Zlength_map. rewrite Hinv2_6. auto. }
    forward_call (v_pq, i, Znth i (Znth u (graph_to_symm_mat g)), pq_state').
    replace (map (fun x : Z => Vint (Int.repr x)) pq_state') with (map Vint (map Int.repr pq_state')).
    entailer!. rewrite list_map_compose. auto.
    split. unfold priq_arr_utils.SIZE. unfold SIZE in H3; lia.
    unfold weight_inrange_priq. rewrite <- inf_priq. rewrite graph_to_mat_eq. split.
    apply weight_representable. rewrite eformat_adj, eformat_symm in Hadj_ui. lia. lia. lia.
    Exists (upd_Znth i parents' u).
    Exists (upd_Znth i keys' (Znth i (Znth u (graph_to_symm_mat g)))).
    Exists (upd_Znth i pq_state' (Znth i (Znth u (graph_to_symm_mat g)))).
    rewrite (graph_unfold _ (graph_to_symm_mat g) _ u). unfold list_rep.
    rewrite list_map_compose. repeat rewrite (upd_Znth_map (fun x => Vint (Int.repr x))). unfold SIZE.
    entailer!.
    { clear H0 H5. split3. 3: split3. 5: split3.
    *intros. destruct (Z.lt_trichotomy v i). repeat rewrite upd_Znth_diff; try lia. apply Hinv2_1. lia. apply H5.
    destruct H29. subst v. destruct H5; contradiction. lia.
    *admit.
    *intros. repeat rewrite upd_Znth_diff; try lia. apply Hinv2_3. unfold SIZE; lia.
      rewrite Hinv2_7. unfold SIZE; lia.
      rewrite Hinv2_6. unfold SIZE; lia.
      rewrite Hinv2_5. unfold SIZE; lia.
    *intros. destruct (Z.eq_dec v i). subst i. rewrite upd_Znth_same. rewrite graph_to_mat_eq.
      split. apply (weight_representable g (eformat (v,u))). apply weight_inf_bound. lia. lia. rewrite Hinv2_6; lia.
      rewrite upd_Znth_diff. apply Hinv2_4. unfold SIZE; auto. rewrite Hinv2_6; unfold SIZE; lia.
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
    *intros. destruct (Z.lt_trichotomy v i). apply Hinv2_1; auto. lia. destruct H31. subst v. apply Hinv2_3. lia. lia.
    *admit.
    *intros. apply Hinv2_3. lia.
  +(*nothing changed because out of pq*)
  assert (In i (u::popped_vertices)). {
    unfold typed_false in H5. destruct (V_EqDec u i); simpl in H5. unfold Equivalence.equiv in e; subst i. left; auto.
    destruct (in_dec V_EqDec i popped_vertices); simpl in H5. right; auto.
    inversion H5.
  }
  forward.
  Exists parents'. Exists keys'. Exists pq_state'. (*hm, it's the same as above...*)
  rewrite (graph_unfold _ (graph_to_symm_mat g) _ u). unfold list_rep.
  2: unfold graph_to_symm_mat; rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; lia.
  entailer!.
  split3.
  *intros. destruct (Z.lt_trichotomy v i). apply Hinv2_1; auto. lia. destruct H27. subst v. apply Hinv2_3. lia. lia.
  *admit.
  *intros. apply Hinv2_3. lia.
  +(*inner loop done, postcon leading to next outer loop iter*)
  Intros parents' keys' pq_state'.
  (*need to split into two cases: if Znth u keys = inf, then it's the same mst. Else, it's adde(eformat (u, Znth u keys))*)
  assert (Znth u keys <= inf). apply Hinv_6. lia.
  apply (Z.le_lteq (Znth u keys) inf) in H10. destruct H10.
  ++
  admit.
  ++ (*Znth u keys = inf. Implies u has no other vertices from the mst that can connect to it. Thus, no change to graph*)
  Exists mst' fmst' parents' keys' pq_state' (u::popped_vertices) (remove V_EqDec u unpopped_vertices). entailer!.
  split3. 3: split.
  *apply NoDup_Permutation. apply NoDup_app_inv. apply NoDup_cons. auto. apply (NoDup_app_l _ _ unpopped_vertices).
  apply (Permutation_NoDup (l:=VList g)). apply Permutation_sym; auto. apply NoDup_VList.
  apply nodup_remove_nodup. apply (NoDup_app_r _ popped_vertices). apply (Permutation_NoDup (l:=VList g)). apply Permutation_sym; auto. apply NoDup_VList.
  intros. destruct H25. subst x. apply remove_In. unfold not; intros. rewrite remove_In_iff in H26. destruct H26.
  assert (~ In x unpopped_vertices). apply (NoDup_app_not_in V popped_vertices). apply (Permutation_NoDup (l:=VList g)). apply Permutation_sym; auto. apply NoDup_VList.
  auto. contradiction. apply NoDup_VList.
  intros; split; intros. apply (Permutation_in (l:=popped_vertices++unpopped_vertices)). auto. apply in_or_app.
  apply in_app_or in H25. destruct H25. destruct H25.
  subst x. right; auto. left; auto. right. apply remove_In_iff in H25. apply H25.
  apply (Permutation_in (l':=popped_vertices++unpopped_vertices)) in H25. 2: apply Permutation_sym; auto.
  apply in_or_app. apply in_app_or in H25; destruct H25.
  left; right; auto. destruct (V_EqDec u x). unfold Equivalence.equiv in e. subst x. left; left; auto.
  unfold RelationClasses.complement, Equivalence.equiv in c. right. apply remove_In_iff. split; auto.
  *admit.
  *intros. rewrite remove_In_iff in H25. destruct H25.
    (*destruct into cases whether v was adjacent to u. Good to get an adjacent_dec out*)




  all:admit.
  }
  { (*break*) forward. (*no more vertices in queue*)
    assert (Hempty: priq_arr_utils.isEmpty pq_state = Vone). {
      destruct (priq_arr_utils.isEmptyTwoCases pq_state);
      rewrite H1 in H0; simpl in H0; now inversion H0.
    } clear H0.
    pose proof (priq_arr_utils.isEmptyMeansInf pq_state Hempty). clear Hempty. rewrite Forall_forall in H0.
    assert (Permutation popped_vertices (VList mst')). { apply NoDup_Permutation.
      apply Permutation_sym, Permutation_NoDup, NoDup_app_l in Hinv_4. auto. apply NoDup_VList.
      apply NoDup_VList. intros; split; intros.
      apply VList_vvalid. apply Hinv_2. rewrite <- VList_vvalid.
      apply (Permutation_in (l:=popped_vertices++unpopped_vertices)). apply Hinv_4. apply in_or_app. left; auto.
      rewrite VList_vvalid, <- Hinv_2 in H1. destruct (Hpopped_or_unpopped x H1). auto.
      assert (Znth x pq_state <= inf). apply Hinv_7 in H2. rewrite H2; apply Hinv_6. rewrite vert_bound in H1; auto.
      assert (Znth x pq_state > inf). rewrite inf_priq. apply H0. apply Znth_In. rewrite Hinv_11. rewrite vert_bound in H1; auto.
      lia.
    }
    Exists mst'. Exists fmst'. Exists popped_vertices. Exists parents. Exists keys. entailer!.
    replace (map Vint (map Int.repr pq_state)) with (list_repeat (Z.to_nat SIZE) (Vint (Int.repr (inf + 1)))).
    replace (map (fun x : V => if in_dec V_EqDec x popped_vertices then Vint (Int.repr 1) else Vint (Int.repr 0)) (nat_inc_list (Z.to_nat 8)))
      with (list_repeat (Z.to_nat SIZE) (Vint (Int.repr 1))). entailer!.
    apply list_eq_Znth. rewrite Zlength_list_repeat. rewrite Zlength_map, nat_inc_list_Zlength. unfold SIZE; lia. lia.
    intros. rewrite Zlength_list_repeat in H16. rewrite Znth_list_repeat_inrange. rewrite Znth_map.
    rewrite nat_inc_list_i. assert (In i popped_vertices). apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto.
      apply VList_vvalid. rewrite <- Hinv_2. rewrite (@vert_representable _ _ _ (sound_MatrixUGraph g)); auto.
    destruct (in_dec V_EqDec i popped_vertices). auto. contradiction.
    unfold SIZE in H16; lia. rewrite nat_inc_list_Zlength; unfold SIZE in H16; lia. lia. lia.
    apply list_eq_Znth. rewrite Zlength_list_repeat. rewrite Zlength_map; rewrite Zlength_map. symmetry; apply Hinv_11. lia.
    intros. rewrite Zlength_list_repeat in H16. rewrite Znth_list_repeat_inrange. rewrite Znth_map. rewrite Znth_map.
    rewrite Hinv_8. auto.
    apply (Permutation_in (l:=VList mst')). apply Permutation_sym; auto.
    apply VList_vvalid. rewrite <- Hinv_2. rewrite (@vert_representable _ _ _ (sound_MatrixUGraph g)); auto.
    rewrite Hinv_11; auto. rewrite Zlength_map, Hinv_11; auto. auto. lia.
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