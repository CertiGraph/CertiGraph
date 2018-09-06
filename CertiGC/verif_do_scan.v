Require Import RamifyCoq.CertiGC.gc_spec.
Require Import RamifyCoq.floyd_ext.weak_valid_pointer.

Lemma body_do_scan: semax_body Vprog Gprog f_do_scan do_scan_spec.
Proof.
  start_function.
  forward.
  forward_loop (EX index: nat, EX g': LGraph, EX t_info': thread_info,
                PROP (super_compatible (g', t_info', roots) f_info outlier;
                      forward_condition g' t_info' from to;
                      thread_info_relation t_info t_info' from;
                      closure_has_index g' to index)
                LOCAL
                (temp _s (offset_val (- WORD_SIZE) (vertex_address g' (to, index)));
                 temp _from_start (gen_start g' from);
                 temp _from_limit (limit_address g' t_info' from);
                 temp _next (next_address t_info' to))
                SEP (all_string_constants rsh gv; outlier_rep outlier;
                     graph_rep g'; thread_info_rep sh t_info' ti))
  break: (EX g' : LGraph, EX t_info' : thread_info,
          PROP (super_compatible (g', t_info', roots) f_info outlier;
                forward_condition g' t_info' from to;
                do_scan_relation from to to_index g g';
                thread_info_relation t_info t_info' from)
          LOCAL ()
          SEP (all_string_constants rsh gv; outlier_rep outlier;
               graph_rep g'; thread_info_rep sh t_info' ti)).
  - Exists to_index g t_info. destruct H as [? [? [? ?]]]. entailer!.
    apply tir_id.
  - Intros index g' t_info'. unfold next_address, thread_info_rep. Intros.
    unfold heap_struct_rep. destruct H4 as [? [? [? ?]]].
    destruct H5 as [? [? [? [? ?]]]].
    assert (0 <= Z.of_nat to < 12). {
      clear -H4 H12. destruct H4 as [_ [_ ?]]. red in H12.
      pose proof (spaces_size (ti_heap t_info')).
      rewrite Zlength_correct in H0. rep_omega. } assert (0 < Z.of_nat to) by omega.
    destruct (gt_gs_compatible _ _ H4 _ H12) as [? [? ?]]. rewrite nth_space_Znth in *.
    remember (Znth (Z.of_nat to) (spaces (ti_heap t_info'))) as sp_to.
    assert (isptr (space_start sp_to)) by (rewrite <- H17; apply start_isptr).
    remember ((space_start (heap_head (ti_heap t_info')),
               (Vundef,
                offset_val (WORD_SIZE * total_space (heap_head (ti_heap t_info')))
                           (space_start (heap_head (ti_heap t_info')))))
                :: map space_tri (tl (spaces (ti_heap t_info')))).
    assert (Znth (Z.of_nat to) l = space_tri sp_to). {
      subst l sp_to. rewrite Znth_pos_cons by assumption.
      rewrite map_tl, Znth_tl by omega.
      replace (Z.of_nat to - 1 + 1) with (Z.of_nat to) by omega.
      rewrite Znth_map by (rewrite spaces_size; rep_omega). reflexivity. }
    unfold Inhabitant_pair, Inhabitant_val, Inhabitant in H21.
    forward; rewrite H21; unfold space_tri. 1: entailer!.
    unfold vertex_address, vertex_offset. rewrite offset_offset_val. simpl vgeneration.
    simpl vindex.
    replace (WORD_SIZE * (previous_vertices_size g' to index + 1) + - WORD_SIZE) with
        (WORD_SIZE * (previous_vertices_size g' to index))%Z by rep_omega.
    unfold gen_start at 1. rewrite if_true by assumption. rewrite H17.
    remember (WORD_SIZE * used_space sp_to)%Z as used_offset.
    remember (WORD_SIZE * previous_vertices_size g' to index)%Z as index_offset.
    freeze [0; 1; 3; 4] FR. gather_SEP 1 2. forward_if (gen_has_index g' to index).
    + remember (Znth (Z.of_nat to) (spaces (ti_heap t_info'))) as sp_to.
      sep_apply (graph_and_heap_rest_data_at_ _ _ _ H12 H4).
      unfold generation_data_at_.
      assert (gen_start g' to = space_start sp_to) by
          (subst; unfold gen_start; rewrite if_true; assumption). rewrite H28.
      rewrite data_at__memory_block. Intros. rewrite sizeof_tarray_int_or_ptr.
      2: unfold gen_size; apply (proj1 (total_space_range (nth_space t_info' to))).
      remember (WORD_SIZE * used_space sp_to)%Z as used_offset.
      remember (WORD_SIZE * previous_vertices_size g' to index)%Z as index_offset.
      destruct (space_start sp_to); try contradiction. simpl. unfold test_order_ptrs.
      simpl. case (peq b b); intros. 2: contradiction. simpl.
      assert (sepalg.nonidentity (nth_sh g' to)). {
        apply readable_nonidentity, writable_readable_share. unfold nth_sh.
        apply generation_share_writable. } apply andp_right.
      * change (Vptr b (Ptrofs.add i (Ptrofs.repr index_offset))) with
            (offset_val index_offset (Vptr b i)).
        sep_apply (memory_block_weak_valid_pointer
                     (nth_sh g' to) (WORD_SIZE * gen_size t_info' to)
                     (Vptr b i) index_offset); auto.
        3: apply extend_weak_valid_pointer.
        -- subst. unfold gen_size. split.
           ++ pose proof (pvs_ge_zero g' to index). rep_omega.
           ++ apply Zmult_le_compat_l. 2: rep_omega.
              transitivity (used_space (nth_space t_info' to)).
              2: apply (proj2 (space_order _)). rewrite nth_space_Znth, <- H19.
              apply pvs_mono. assumption.
        -- admit.
      * admit.
    + admit.
    + admit.
    + admit.
  - Intros g' t_info'. forward. Exists g' t_info'. entailer!.
Abort.
