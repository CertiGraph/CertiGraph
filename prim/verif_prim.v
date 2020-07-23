Require Import VST.floyd.proofauto.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.floyd_ext.share.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.undirected_graph.
Require Import CertiGraph.graph.AdjMatGraph.
Require Import CertiGraph.prim.MatrixUGraph.
Require Import CertiGraph.prim.prim.
Require Import CertiGraph.prim.spatial_undirected_matrix.
Require Import CertiGraph.prim.specs_prim.

Lemma inf_equiv':
(Int.sub (Int.repr 2147483647) (Int.divs (Int.repr 2147483647) (Int.repr 8))) = (Int.repr inf).
Proof.
unfold inf. unfold SIZE.
assert (Int.max_signed = 2147483647). set (j:=Int.max_signed); compute in j; lia. rewrite H.
assert (Int.min_signed <= 2147483647 <= Int.max_signed). rewrite H. set (j:=Int.min_signed); compute in j; lia.
assert (Int.min_signed <= 8 <= Int.max_signed). rewrite H. set (j:=Int.min_signed); compute in j; lia.
rewrite Int.sub_signed. rewrite !Int.signed_repr by lia.
unfold Int.divs. rewrite Zquot.Zquot_Zdiv_pos.
rewrite !Int.signed_repr. auto.
auto. auto.
rewrite !Int.signed_repr. rewrite H. set (j:=Int.min_signed); compute in j; subst j.
set (j:=2147483647 / 8); compute in j; subst j. lia.
auto. auto.
rewrite !Int.signed_repr; lia.
rewrite !Int.signed_repr; lia.
Qed.

Lemma body_init_list: semax_body Vprog Gprog f_initialise_list init_list_spec.
Proof.
Fail start_function.
Abort.
(*
forward_for_simple_bound SIZE
    (EX i : Z,
     PROP ()
     LOCAL (temp _list (pointer_val_val arr))
     SEP (
      data_at sh (tarray tint SIZE) (list_repeat (Z.to_nat i) (Vint (Int.repr inf))++(sublist i SIZE old_list)) (pointer_val_val arr)
    ))%assert.
unfold SIZE; set (j:=Int.max_signed); compute in j; lia.
entailer!. rewrite app_nil_l. rewrite sublist_same by lia. auto.
(*loop*)
forward. entailer!.
rewrite inf_equiv'.
rewrite (sublist_split i (i+1)) by lia.
replace (sublist i (i+1) old_list) with [Znth i old_list]. simpl.
rewrite upd_Znth_char.
rewrite <- list_repeat_app' by lia.
rewrite <- app_assoc. simpl. auto.
apply Zlength_list_repeat; lia.
symmetry; apply sublist_one; lia.
(*postcon*)
entailer!. rewrite sublist_nil. rewrite app_nil_r. auto.
Qed.

Lemma body_init_matrix: semax_body Vprog Gprog f_initialise_matrix init_matrix_spec.
Proof.
start_function.
assert (HZlength_nat_inc_list: SIZE = Zlength (nat_inc_list (Datatypes.length old_contents))).
rewrite nat_inc_list_Zlength. rewrite <- Zlength_correct. lia.
forward_for_simple_bound SIZE
    (EX i : Z,
     PROP ()
     LOCAL (temp _graph (pointer_val_val arr))
     SEP (
      iter_sepcon.iter_sepcon (fun i => data_at sh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr inf))) (list_address (pointer_val_val arr) i SIZE))
        (sublist 0 i (nat_inc_list (Z.to_nat (Zlength old_contents))));
      iter_sepcon.iter_sepcon (list_rep sh SIZE (pointer_val_val arr) old_contents)
        (sublist i SIZE (nat_inc_list (Z.to_nat (Zlength old_contents))))
    ))%assert.
unfold SIZE; set (j:=Int.max_signed); compute in j; lia.
rewrite (graph_unfold _ _ _ 0). rewrite H. entailer!.
replace (list_rep sh SIZE (pointer_val_val arr) old_contents 0) with (iter_sepcon.iter_sepcon (list_rep sh SIZE (pointer_val_val arr) old_contents) [0]).
2: { simpl. rewrite sepcon_emp. auto. }
rewrite <- iter_sepcon.iter_sepcon_app. simpl. auto.
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
     LOCAL (temp _i (Vint (Int.repr i)); temp _graph (pointer_val_val arr))
     SEP (
      iter_sepcon.iter_sepcon (fun i => data_at sh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr inf))) (list_address (pointer_val_val arr) i SIZE))
        (sublist 0 i (nat_inc_list (Z.to_nat (Zlength old_contents))));
      data_at sh (tarray tint SIZE) (list_repeat (Z.to_nat j) (Vint (Int.repr inf))++sublist j SIZE (map (fun x => Vint (Int.repr x)) (Znth i old_contents))) (list_address (pointer_val_val arr) i SIZE);
      iter_sepcon.iter_sepcon (list_rep sh SIZE (pointer_val_val arr) old_contents)
        (sublist (i+1) SIZE (nat_inc_list (Z.to_nat (Zlength old_contents))))
    ))%assert.
unfold SIZE; set (j:=Int.max_signed); compute in j; lia.
entailer!. simpl. rewrite sepcon_emp. unfold list_rep. rewrite sublist_same; auto.
rewrite Zlength_map. symmetry; apply H0. apply Znth_In; lia.
(*inner loop body*)
rename i0 into j. unfold list_address.
assert (Zlength (map (fun x => Vint (Int.repr x)) (Znth i old_contents)) = SIZE).
rewrite Zlength_map. apply H0. apply Znth_In; lia.
assert_PROP (field_compatible (tarray tint SIZE) [ArraySubsc j] (offset_val (i * sizeof (tarray tint SIZE)) (pointer_val_val arr))). entailer!.
assert_PROP(force_val (sem_add_ptr_int tint Signed (force_val (sem_add_ptr_int (tarray tint SIZE) Signed (pointer_val_val arr) (Vint (Int.repr i))))
 (Vint (Int.repr j))) = (field_address (tarray tint SIZE) [ArraySubsc j] (offset_val (i * sizeof (tarray tint SIZE)) (pointer_val_val arr)))). {
entailer!. symmetry; rewrite field_address_offset. simpl. unfold offset_val.
destruct arr; simpl. 2: auto.
rewrite Ptrofs.add_assoc. rewrite (Ptrofs.add_signed (Ptrofs.repr (i*32))).
rewrite Ptrofs.signed_repr. rewrite Ptrofs.signed_repr. rewrite Z.add_0_l. rewrite Z.mul_comm. auto.
all: set (k:=Ptrofs.min_signed); compute in k; subst k; set (k:=Ptrofs.max_signed); compute in k; subst k.
rewrite Z.add_0_l. unfold SIZE in H2. lia. unfold SIZE in H1; lia. auto.
}
(*g[i][j] = inf*)
forward.
rewrite inf_equiv'. unfold list_address.
replace (upd_Znth j (list_repeat (Z.to_nat j) (Vint (Int.repr inf)) ++ sublist j SIZE (map (fun x => Vint (Int.repr x)) (Znth i old_contents))) (Vint (Int.repr inf)))
with (list_repeat (Z.to_nat (j + 1)) (Vint (Int.repr inf)) ++ sublist (j + 1) SIZE (map (fun x => Vint (Int.repr x)) (Znth i old_contents))).
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
         (map (fun x : Z => Vint (Int.repr x)) (Znth index (list_repeat (Z.to_nat SIZE) (list_repeat (Z.to_nat SIZE) inf))))
         (list_address (pointer_val_val arr) index SIZE)) (fun i : Z =>
   data_at sh (tarray tint SIZE) (map (fun x : Z => Vint (Int.repr x)) (list_repeat (Z.to_nat SIZE) inf))
     (list_address (pointer_val_val arr) i SIZE))). entailer!. simpl; entailer.
intros. replace (Znth x (list_repeat (Z.to_nat SIZE) (list_repeat (Z.to_nat SIZE) inf))) with
(list_repeat (Z.to_nat SIZE) inf); auto.
symmetry; apply Znth_list_repeat_inrange. apply sublist_In, nat_inc_list_in_iff in H2.
rewrite Z2Nat.id in H2; auto. unfold SIZE; lia.
(*remaining lias*)
unfold SIZE; lia. rewrite <- ZtoNat_Zlength. rewrite H; auto. unfold SIZE; lia. rewrite <- Zlength_correct, H; unfold SIZE; lia.
lia. rewrite <- HZlength_nat_inc_list; unfold SIZE; lia. lia. lia.
rewrite <- HZlength_nat_inc_list; unfold SIZE; lia. rewrite Zlength_list_repeat; unfold SIZE; lia.
Qed.
*)

Lemma body_prim: semax_body Vprog Gprog f_prim prim_spec.
Proof.
start_function.
(*replace all data_at_ with data_at Vundef*)
rewrite data_at__tarray.
assert_PROP (isptr v_key). entailer!. destruct v_key; try contradiction. rename b into bkey; rename i into ikey.
replace (Vptr bkey ikey) with (pointer_val_val (ValidPointer bkey ikey)) by (simpl; auto). set (vkey:=ValidPointer bkey ikey) in *.
set (k:=default_val tint); compute in k; subst k.

Fail forward_call (Tsh, (ValidPointer bkey ikey), (list_repeat (Z.to_nat 8) Vundef)).
Abort.
