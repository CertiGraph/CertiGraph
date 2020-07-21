Require Import VST.floyd.proofauto.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.undirected_graph.
Require Import RamifyCoq.prim.MatrixUGraph.
Require Import RamifyCoq.prim.prim.
Require Import RamifyCoq.prim.spatial_undirected_matrix.
Require Import RamifyCoq.prim.specs_prim.

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
start_function.
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
      list_rep sh SIZE (pointer_val_val arr) old_contents i;
      iter_sepcon.iter_sepcon (list_rep sh SIZE (pointer_val_val arr) old_contents)
        (sublist (i+1) SIZE (nat_inc_list (Z.to_nat (Zlength old_contents))))
    ))%assert.
unfold SIZE; set (j:=Int.max_signed); compute in j; lia.
rewrite (graph_unfold _ _ _ 0). entailer!. rewrite H. entailer!. rewrite H; unfold SIZE; lia.
(*outer loop*)
forward_for_simple_bound SIZE
    (EX j : Z,
     PROP ()
     LOCAL (temp _i (Vint (Int.repr i)); temp _graph (pointer_val_val arr))
     SEP (
      iter_sepcon.iter_sepcon (fun i => data_at sh (tarray tint SIZE) (list_repeat (Z.to_nat SIZE) (Vint (Int.repr inf))) (list_address (pointer_val_val arr) i SIZE))
        (sublist 0 i (nat_inc_list (Z.to_nat (Zlength old_contents))));
      data_at sh (tarray tint SIZE) (list_repeat (Z.to_nat j) (Vint (Int.repr inf))++sublist j SIZE (map Vint (map Int.repr (Znth i old_contents)))) (list_address (pointer_val_val arr) i SIZE);
      iter_sepcon.iter_sepcon (list_rep sh SIZE (pointer_val_val arr) old_contents)
        (sublist (i+1) SIZE (nat_inc_list (Z.to_nat (Zlength old_contents))))
    ))%assert.
unfold SIZE; set (j:=Int.max_signed); compute in j; lia.
entailer!. unfold list_rep. rewrite list_repeat_0. rewrite app_nil_l. rewrite sublist_same. auto. auto.
rewrite Zlength_map. rewrite Zlength_map. symmetry; apply H0. apply Znth_In; lia.
(*inner loop body*)
rename i0 into j. unfold list_address.

(****I can't forward from here and am not sure what I should be aiming for. Below are just rough attempts. ******)

(*forward.*)

(*split the ith list to isolate?*)
rewrite (split2_data_at_Tarray_app j SIZE sh tint
  (list_repeat (Z.to_nat j) (Vint (Int.repr inf)))
  (sublist j SIZE (map Vint (map Int.repr (Znth i old_contents))))
). 2: { rewrite Zlength_list_repeat'. rewrite Z2Nat.id; lia. }
2: { rewrite Zlength_sublist; try lia. rewrite Zlength_map. rewrite Zlength_map. rewrite H0. lia. apply Znth_In; lia. }
Intros.
rewrite field_address0_offset. 2: admit.

(*Search ArraySubsc offset_val.
replace (field_address0 (tarray tint SIZE) [ArraySubsc j] (offset_val (i * sizeof (tarray tint SIZE)) (pointer_val_val arr))) with
(offset_val *)
assert_PROP(force_val (sem_add_ptr_int tint Signed (force_val (sem_add_ptr_int (tarray tint 8) Signed (pointer_val_val arr) (Vint (Int.repr i))))
 (Vint (Int.repr j))) = field_address (tarray tint SIZE) [ArraySubsc j] (offset_val (i * sizeof (tarray tint SIZE)) (pointer_val_val arr))). {
entailer!. symmetry; rewrite field_address_offset. simpl. unfold offset_val.
destruct arr; simpl. 2: auto.
rewrite Ptrofs.add_assoc. rewrite (Ptrofs.add_signed (Ptrofs.repr (i*32))).
rewrite Ptrofs.signed_repr. rewrite Ptrofs.signed_repr. rewrite Z.add_0_l. rewrite Z.mul_comm. auto.
admit. admit.
(*apply isptr_field_address_lemma.*) admit.
}
Fail forward.

(*postcon*)
Admitted.
