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

Lemma single_outlier_rep_memory_block_FF: forall gp p n wsh,
    writable_share wsh -> v_in_range (GC_Pointer2val gp) p (WORD_SIZE * n) ->
    single_outlier_rep gp * data_at_ wsh (tarray int_or_ptr_type n) p |-- FF.
Proof.
  intros. unfold single_outlier_rep. Intros rsh. remember (GC_Pointer2val gp) as ggp.
  clear gp Heqggp. rename ggp into gp. destruct H0 as [o [? ?]].
  rewrite !data_at__memory_block. Intros. clear H3. destruct H4 as [? [_ [? _]]].
  destruct p; try contradiction. subst gp. inv_int i. simpl offset_val.
  assert (0 <= n) by rep_omega. rewrite ptrofs_add_repr.
  rewrite sizeof_tarray_int_or_ptr by assumption. simpl sizeof. simpl in H4.
  rewrite Ptrofs.unsigned_repr in H4 by rep_omega. rewrite Z.max_r in H4 by assumption.
  rewrite WORD_SIZE_eq in *. rewrite sepcon_assoc, (sepcon_comm TT), <- sepcon_assoc.
  assert (4 * n = o + (4 * n - o))%Z by omega. remember (4 * n - o) as m.
  rewrite H6 in *. rewrite (memory_block_split wsh b ofs o m) by omega.
  clear Heqm n H6 H2. assert (0 < m <= Ptrofs.max_unsigned) by rep_omega.
  assert (0 < 4 <= Ptrofs.max_unsigned) by rep_omega.
  rewrite (sepcon_comm (memory_block wsh o (Vptr b (Ptrofs.repr ofs)))),
  <- sepcon_assoc. remember (Vptr b (Ptrofs.repr (ofs + o))) as p.

  (* memory_block_conflict *)
Admitted.

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
    assert_PROP (valid_int_or_ptr (root2val g root)). {
      gather_SEP 3 2. sep_apply (root_valid_int_or_ptr _ _ _ _ H8 H4). entailer!.
    } forward_call (root2val g root). destruct root as [[? | ?] | ?]; simpl root2val.
    + unfold odd_Z2val. forward_if True.
      1: exfalso; apply H11'. reflexivity. 1: forward; entailer!.
      forward. Exists g t_info roots. entailer!.
      * unfold roots_compatible. intuition. rewrite <- Heqroot. simpl. constructor.
      * unfold thread_info_rep. entailer!.
    + unfold GC_Pointer2val. destruct g0. forward_if True.
      2: exfalso; apply Int.one_not_zero in H11; assumption.
      * forward_call (Vptr b i). gather_SEP 3 6 2. rewrite <- sepcon_assoc.
        remember (graph_rep g * heap_rest_rep (ti_heap t_info) * outlier_rep outlier)
          as P. destruct H4. pose proof (graph_and_heap_rest_data_at_ _ _ _ H1 H).
        remember (nth_gen g from).(generation_sh) as fsh.
        remember (gen_start g from) as fp. remember (gen_size t_info from) as gn.
        remember (WORD_SIZE * gn)%Z as fn.
        assert (P |-- (weak_derives P (memory_block fsh fn fp * TT) && emp) * P). {
          subst. cancel. apply andp_right. 2: cancel.
          assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
          apply derives_weak. sep_apply H13. rewrite data_at__memory_block.
          rewrite sizeof_tarray_int_or_ptr; [Intros; cancel | unfold gen_size].
          destruct (total_space_tight_range (nth_space t_info from)). assumption.
        } replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
            (entailer; assumption). clear H14. Intros. simpl root2val in *.
        assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
          subst. cancel. apply andp_right. 2: cancel.
          assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
          apply derives_weak.
          sep_apply (outlier_rep_valid_pointer roots outlier (GCPtr b i) H8 H4).
          simpl GC_Pointer2val. cancel. }
        replace_SEP 1 ((weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P) by
            (entailer; assumption). Intros. clear H14.
        forward_call (fsh, fp, fn, (Vptr b i), P). Intros v. destruct v.
        -- rewrite HeqP. Intros. gather_SEP 0 1. sep_apply H13. rewrite Heqfn in v.
           sep_apply (outlier_rep_single_rep _ _ _ H8 H4). Intros. gather_SEP 0 2.
           change (Vptr b i) with (GC_Pointer2val (GCPtr b i)) in v.
           pose proof (generation_share_writable (nth_gen g from)).
           rewrite <- Heqfsh in H14.
           sep_apply (single_outlier_rep_memory_block_FF (GCPtr b i) fp gn fsh H14 v).
           assert_PROP False by entailer!. contradiction.
        -- forward_if. 1: exfalso; apply H14'; reflexivity. forward. entailer!.
      * forward. Exists g t_info roots. entailer!.
        -- unfold roots_compatible. intuition. rewrite <- Heqroot. simpl. constructor.
        -- unfold thread_info_rep. entailer!.
    +
Abort.
