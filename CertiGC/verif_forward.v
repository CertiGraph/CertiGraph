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
    } pose proof (Znth_map _ (root2val g) _ H0). rewrite H6 in H0.
    rewrite H3, Znth_map in H7 by assumption. unfold flip in H7.
    remember (Znth z roots) as root. rewrite <- H6 in H0. pose proof (Znth_In _ _ H0).
    rewrite <- Heqroot in H8. rewrite H6 in H0. unfold Inhabitant_val in H7.
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
    forward_call (root2val g root). destruct root as [[? | ?] | ?]; simpl root2val.
    + unfold odd_Z2val. forward_if True.
      1: exfalso; apply H12'. reflexivity. 1: forward; entailer!.
      forward. Exists g t_info roots. entailer!.
      * unfold roots_compatible. intuition. rewrite <- Heqroot. simpl. constructor.
      * unfold thread_info_rep. entailer!.
    + unfold GC_Pointer2val. destruct g0. forward_if True.
      2: exfalso; apply Int.one_not_zero in H12; assumption.
      * forward_call (Vptr b (Ptrofs.add i i)).
        gather_SEP 0 6 3. rewrite <- sepcon_assoc.
        remember (graph_rep g * heap_rest_rep (ti_heap t_info) * outlier_rep outlier)
          as P. remember (nth_gen g from).(generation_sh) as fsh.
        remember (gen_start g from) as fp.
        remember (WORD_SIZE * gen_size t_info from)%Z as fn.
        assert (P |-- (weak_derives P (memory_block fsh fn fp * TT) && emp) * P). {
          subst. cancel. apply andp_right. 2: cancel.
          assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
          apply derives_weak.
          sep_apply (graph_and_heap_rest_memory_block _ _ _ H1 H). cancel.
        } replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
            (entailer; assumption). clear H13. Intros. simpl root2val in *.
        assert (P |-- (weak_derives P (valid_pointer (Vptr b (Ptrofs.add i i)) * TT) &&
                                    emp) * P). {
          subst. cancel. apply andp_right. 2: cancel.
          assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
          apply derives_weak. admit.
        } replace_SEP
          1 ((weak_derives P (valid_pointer (Vptr b (Ptrofs.add i i)) * TT) &&
                           emp) * P) by (entailer; assumption).
        admit.
      * forward. Exists g t_info roots. entailer!.
        -- unfold roots_compatible. intuition. rewrite <- Heqroot. simpl. constructor.
        -- unfold thread_info_rep. entailer!.
    +
Abort.
