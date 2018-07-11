Require Import RamifyCoq.CertiGC.gc_spec.

Lemma root_valid_int_or_ptr: forall g (roots: roots_t) root outlier,
    In root roots ->
    roots_compatible g outlier roots ->
    graph_rep g * outlier_rep outlier |-- !! (valid_int_or_ptr (root2val g root)).
Proof.
  intros. destruct H0. destruct root as [[? | ?] | ?].
  - simpl root2val. unfold odd_Z2val. replace (2 * z + 1) with (z + z + 1) by omega.
    apply prop_right, valid_int_or_ptr_ii1.
  - sep_apply (outlier_rep_single_rep _ _ _ H H0).
    sep_apply (single_outlier_rep_valid_int_or_ptr g0). entailer!.
  - rewrite Forall_forall in H1. rewrite (filter_sum_right_In_iff v roots) in H.
    apply H1 in H. simpl. sep_apply (graph_rep_valid_int_or_ptr _ _ H). entailer!.
Qed.

Lemma weak_derives_strong: forall (P Q: mpred),
    P |-- Q -> P |-- (weak_derives P Q && emp) * P.
Proof.
  intros. cancel. apply andp_right. 2: cancel.
  assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
  apply derives_weak. assumption.
Qed.

Lemma body_forward: semax_body Vprog Gprog f_forward forward_spec.
Proof.
  start_function.
  rename H3 into HC. unfold forward_p_address. destruct forward_p.
  - unfold thread_info_rep. Intros. hnf in H0. destruct H as [? [? [? ?]]]. hnf in H3.
    assert (Zlength roots = Zlength (live_roots_indices f_info)). {
      rewrite <- (Zlength_map _ _ (flip Znth (ti_args t_info))), <- H3, Zlength_map.
      reflexivity. }
    pose proof (Znth_map _ (root2val g) _ H0). rewrite H6 in H0.
    rewrite H3, Znth_map in H7 by assumption. unfold flip in H7.
    remember (Znth z roots) as root. rewrite <- H6 in H0. pose proof (Znth_In _ _ H0).
    rewrite <- Heqroot in H8. rewrite H6 in H0. unfold Inhabitant_val in H7.
    assert (forall v, In (inr v) roots -> isptr (vertex_address g v)). {
      intros. destruct H4. unfold vertex_address. rewrite Forall_forall in H10.
      rewrite (filter_sum_right_In_iff v roots) in H9. apply H10 in H9. destruct H9.
      apply graph_has_gen_start_isptr in H9.
      remember (gen_start g (vgeneration v)) as vv. destruct vv; try contradiction.
      simpl. exact I. }
    assert (is_pointer_or_integer (root2val g root)). {
      destruct root as [[? | ?] | ?]; simpl; auto.
      - destruct g0. simpl. exact I.
      - specialize (H9 _ H8). apply isptr_is_pointer_or_integer. assumption. }
    assert (HB: 0 <= Znth z (live_roots_indices f_info) < 1024) by
        (apply (fi_index_range f_info), Znth_In; assumption).
    forward; rewrite H7. 1: entailer!.
    assert_PROP (valid_int_or_ptr (root2val g root)). {
      gather_SEP 3 2. sep_apply (root_valid_int_or_ptr _ _ _ _ H8 H4). entailer!. }
    forward_call (root2val g root).
    remember (graph_rep g * heap_rest_rep (ti_heap t_info) * outlier_rep outlier)
      as P. pose proof (graph_and_heap_rest_data_at_ _ _ _ H1 H).
    unfold generation_data_at_ in H12. remember (gen_start g from) as fp.
    remember (nth_sh g from) as fsh. remember (gen_size t_info from) as gn.
    remember (WORD_SIZE * gn)%Z as fn.
    assert (P |-- (weak_derives P (memory_block fsh fn fp * TT) && emp) * P). {
      apply weak_derives_strong. subst. sep_apply H12.
      rewrite data_at__memory_block.
      rewrite sizeof_tarray_int_or_ptr; [Intros; cancel | unfold gen_size].
      destruct (total_space_tight_range (nth_space t_info from)). assumption. }
    destruct root as [[? | ?] | ?]; simpl root2val.
    + unfold odd_Z2val. apply semax_if_seq. forward_if.
      1: exfalso; apply H14'; reflexivity.
      forward. Exists g t_info roots. rewrite <- Heqroot. entailer!.
      * simpl. constructor.
      * unfold thread_info_rep. entailer!.
    + unfold GC_Pointer2val. destruct g0. apply semax_if_seq. forward_if.
      2: exfalso; apply Int.one_not_zero in H14; assumption.
      forward_call (Vptr b i). gather_SEP 3 6 2. rewrite <- sepcon_assoc.
      rewrite <- HeqP. destruct H4.
      replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
          (entailer; assumption). clear H13. Intros. simpl root2val in *.
      assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
        subst. cancel. apply andp_right. 2: cancel.
        assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
        apply derives_weak.
        sep_apply (outlier_rep_valid_pointer roots outlier (GCPtr b i) H8 H4).
        simpl GC_Pointer2val. cancel. }
      replace_SEP 1 ((weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P) by
          (entailer; assumption). Intros. clear H13.
      forward_call (fsh, fp, fn, (Vptr b i), P). Intros v. destruct v.
      * rewrite HeqP. Intros. gather_SEP 0 1. sep_apply H12. rewrite Heqfn in v.
        sep_apply (outlier_rep_single_rep _ _ _ H8 H4). Intros. gather_SEP 0 2.
        change (Vptr b i) with (GC_Pointer2val (GCPtr b i)) in v.
        pose proof (generation_share_writable (nth_gen g from)).
        change (generation_sh (nth_gen g from)) with (nth_sh g from) in H13.
        rewrite <- Heqfsh in H13. unfold generation_data_at_.
        sep_apply (single_outlier_rep_memory_block_FF (GCPtr b i) fp gn fsh H13 v).
        assert_PROP False by entailer!. contradiction.
      * apply semax_if_seq. forward_if. 1: exfalso; apply H13'; reflexivity.
        forward. Exists g t_info roots. rewrite <- Heqroot. entailer!.
        -- unfold roots_compatible. intuition. simpl. constructor.
        -- unfold thread_info_rep. entailer!.
    + specialize (H9 _ H8). destruct (vertex_address g v) eqn:? ; try contradiction.
      apply semax_if_seq. forward_if.
      2: exfalso; apply Int.one_not_zero in H14; assumption.
      clear H14 H14'. simpl in H11, H10. forward_call (Vptr b i).
      rewrite <- Heqv0 in *. gather_SEP 3 6 2. rewrite <- sepcon_assoc, <- HeqP.
      replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
          (entailer; assumption). clear H13. Intros. assert (graph_has_v g v). {
        destruct H4. rewrite Forall_forall in H13. apply H13.
        rewrite <- filter_sum_right_In_iff. assumption. }
      assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
        apply weak_derives_strong. subst. sep_apply (graph_rep_vertex_rep g v H13).
        Intros shh. unfold vertex_rep, vertex_at. remember (make_fields_vals g v).
        sep_apply (data_at_valid_ptr shh (tarray int_or_ptr_type (Zlength l)) l
                                     (vertex_address g v)).
        - apply readable_nonidentity, writable_readable_share. assumption.
        - subst l. simpl. rewrite fields_eq_length.
          rewrite Z.max_r; pose proof (raw_fields_range (vlabel g v)); omega.
        - rewrite Heqv0; cancel. }
      replace_SEP 1 (weak_derives P (valid_pointer (Vptr b i) * TT) && emp * P)
        by (entailer; assumption). clear H14. Intros. rewrite <- Heqv0 in *.
      forward_call (fsh, fp, fn, (vertex_address g v), P). Intros vv. rewrite HeqP.
      sep_apply (graph_and_heap_rest_v_in_range_iff _ _ _ _ H H1 H13). Intros.
      rewrite <- Heqfp, <- Heqgn, <- Heqfn in H14. destruct vv.
      * Intros. rewrite H14 in v0. clear H14. apply semax_if_seq. forward_if.
        2: exfalso; inversion H14. deadvars!. freeze [1; 2; 3; 4; 5; 6] FR.
        clear H14 H14'.
        localize [vertex_rep (nth_sh g (vgeneration v)) g v].
        unfold vertex_rep, vertex_at. Intros. rewrite v0.
        assert (readable_share (nth_sh g from)) by
            (unfold nth_sh; apply writable_readable, generation_share_writable).
        assert_PROP (force_val
                       (sem_add_ptr_int tuint Signed (vertex_address g v)
                                        (eval_unop Oneg tint (vint 1))) =
                     field_address tuint []
                                   (offset_val (- WORD_SIZE) (vertex_address g v))). {
          rewrite WORD_SIZE_eq. entailer!. unfold field_address.
          rewrite if_true by assumption. simpl. rewrite offset_offset_val.
          reflexivity. } forward.
        gather_SEP 0 1. replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v)) g v) by
            (unfold vertex_rep, vertex_at; entailer!).
        unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H13).
        apply semax_if_seq. forward_if; rewrite make_header_int_rep_mark_iff in H16.
        -- deadvars!. localize [vertex_rep (nth_sh g (vgeneration v)) g v].
           rewrite v0. unfold vertex_rep, vertex_at. Intros.
           unfold make_fields_vals at 2. rewrite H16.
           assert (0 <= 0 < Zlength (make_fields_vals g v)). {
             split. 1: omega. rewrite fields_eq_length.
             apply (proj1 (raw_fields_range (vlabel g v))). }
           assert (is_pointer_or_integer
                     (vertex_address g (copied_vertex (vlabel g v)))). {
             apply isptr_is_pointer_or_integer. unfold vertex_address.
             rewrite isptr_offset_val.
             apply graph_has_gen_start_isptr, HC; assumption. }
           forward. rewrite Znth_0_cons. gather_SEP 0 1.
           replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v)) g v). {
             unfold vertex_rep, vertex_at. unfold make_fields_vals at 3.
             rewrite H16. entailer!. }
           unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H13).
           thaw FR. forward. forward. rewrite <- Heqroot.
           rewrite if_true by reflexivity. rewrite H16.
           Exists g (upd_thread_info_arg
                       t_info
                       (Znth z (live_roots_indices f_info))
                       (vertex_address g (copied_vertex (vlabel g v))) HB)
                  (upd_Znth z roots (inr (copied_vertex (vlabel g v)))).
           unfold thread_info_rep. simpl. entailer!. split; [split|].
           ++ red. unfold upd_thread_info_arg. simpl. admit.
           ++ admit.
           ++ apply fr_v_in_forwarded; [reflexivity | assumption].
        -- admit.
      * apply semax_if_seq. forward_if. 1: exfalso; apply H15'; reflexivity.
        rewrite H14 in n. forward. rewrite <- Heqroot. rewrite if_false by assumption.
        Exists g t_info roots. simpl. entailer!.
        -- constructor. assumption.
        -- unfold thread_info_rep. entailer!.
Abort.
