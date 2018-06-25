Require Import RamifyCoq.CertiGC.gc_spec.

Lemma root_valid_int_or_ptr: forall g (roots: roots_t) root,
    In root roots ->
    Forall (graph_has_v g) (filter_sum_right roots) ->
    graph_rep g |-- !! (valid_int_or_ptr (root2val g root)).
Proof.
  intros. destruct root as [[? | ?] | ?].
  - simpl root2val. unfold odd_Z2val. replace (2 * z + 1) with (z + z + 1) by omega.
    apply prop_right, valid_int_or_ptr_ii1.
  - destruct g0. simpl. inv_int i. rewrite ptrofs_add_repr.
    replace (ofs + ofs) with (2 * ofs)%Z by omega. apply prop_right.
    rewrite Ptrofs.unsigned_repr_eq, Zodd_mod, <- Zmod_div_mod; try rep_omega.
    + rewrite Z.mul_comm, Z_mod_mult. unfold Zeq_bool. reflexivity.
    + exists (Z.div Ptrofs.modulus 2). reflexivity.
  - rewrite Forall_forall in H0. rewrite (filter_sum_right_In_iff v roots) in H.
    apply H0 in H. simpl. apply graph_rep_valid_int_or_ptr. assumption.
Qed.

Lemma body_forward: semax_body Vprog Gprog f_forward forward_spec.
Proof.
  start_function.
  unfold forward_p_address. destruct forward_p.
  - unfold thread_info_rep. Intros. hnf in H0. destruct H as [? [? [? ?]]]. hnf in H3.
    assert (Zlength roots = Zlength (live_roots_indices f_info)). {
      rewrite <- (Zlength_map _ _ (flip Znth (ti_args t_info))), <- H3, Zlength_map.
      reflexivity.
    } rewrite H6 in H0.
    pose proof (in_map (flip Znth (ti_args t_info))
                       (live_roots_indices f_info) _ (Znth_In _ _ H0)).
    unfold flip in H7 at 1. rewrite <- H3 in H7. apply list_in_map_inv in H7.
    destruct H7 as [root [? ?]]. unfold Inhabitant_val in H7.
    assert (is_pointer_or_integer (root2val g root)). {
      destruct root as [[? | ?] | ?]; simpl; auto.
      - destruct g0. simpl. exact I.
      - destruct H4. unfold vertex_address. rewrite Forall_forall in H9.
        rewrite (filter_sum_right_In_iff v roots) in H8. apply H9 in H8.
        destruct H8. apply graph_has_gen_start_isptr in H8.
        remember (gen_start g (vgeneration v)) as vv. destruct vv; try contradiction.
        simpl. exact I.
    } forward. 1: apply prop_right, (fi_index_range f_info), Znth_In; assumption.
    1: entailer!; rewrite H7; assumption. rewrite H7.
    destruct H4. sep_apply (root_valid_int_or_ptr g roots root H8 H10). Intros.
    forward_call (root2val g root).
Abort.
