Require Import CertiGraph.CertiGC.gc_spec.

Lemma int64_ltu_ptrofs_to_int_64:
  forall x y, Archi.ptr64 = true ->
    Int64.ltu (Ptrofs.to_int64 x) (Ptrofs.to_int64 y) =  Ptrofs.ltu x y.
Proof.
  intros.
  unfold Int64.ltu, Ptrofs.ltu.
  rewrite <- (Ptrofs.repr_unsigned x), <- (Ptrofs.repr_unsigned y).
  rewrite !ptrofs_to_int64_repr by auto.
  pose proof Ptrofs.unsigned_range.
  unfold Ptrofs.max_unsigned in H0.
  unfold Ptrofs.modulus, Ptrofs.wordsize, 
    Wordsize_Ptrofs.wordsize in H0. rewrite H in H0.
  change (two_power_nat 64) with (Int64.max_unsigned + 1) in H0.
  rewrite !Int64.unsigned_repr.
    2: specialize (H0 y); lia.
    2: specialize (H0 x); lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  auto.
Qed.

Lemma int_ltu_ptrofs_to_int:
  forall x y, Archi.ptr64 = false ->
    Int.ltu (Ptrofs.to_int x) (Ptrofs.to_int y) =  Ptrofs.ltu x y.
Proof.
  intros.
  unfold Int.ltu, Ptrofs.ltu.
  rewrite <- (Ptrofs.repr_unsigned x), <- (Ptrofs.repr_unsigned y).
  rewrite !ptrofs_to_int_repr by auto.
  pose proof Ptrofs.unsigned_range.
  unfold Ptrofs.max_unsigned in H0.
  unfold Ptrofs.modulus, Ptrofs.wordsize, 
    Wordsize_Ptrofs.wordsize in H0. rewrite H in H0.
  change (two_power_nat 32) with (Int.max_unsigned + 1) in H0.
  rewrite !Int.unsigned_repr.
  2: specialize (H0 y); lia.
  2: specialize (H0 x); lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  auto.
Qed.

Lemma body_resume: semax_body Vprog Gprog f_resume resume_spec.
Proof.
  start_function.
  unfold thread_info_rep, heap_rep, heap_struct_rep. Intros.
  forward. forward.
  forward_if True.
  - forward; entailer!.
  - remember (ti_heap_p t_info). rewrite (data_at_isptr sh heap_type).
    Intros. exfalso. destruct t_info. simpl in *. subst. contradiction.
  - Intros. destruct (heap_head_cons (ti_heap t_info)) as [hs [hl [? ?]]].
    rewrite H1, <- H2, map_cons.
    destruct (gt_gs_compatible _ _ H _ (graph_has_gen_O _)) as [? [? ?]].
    assert (isptr (space_start (heap_head (ti_heap t_info)))). {
      rewrite H2. unfold nth_space in H3. rewrite H1 in H3. simpl in H3.
      rewrite <- H3. apply start_isptr. } unfold space_tri at 1.
    do 2 forward; try solve [entailer!].
    rewrite Znth_0_cons.
    destruct (space_start (heap_head (ti_heap t_info))) eqn:? ; try contradiction.
    forward_if (Ptrofs.unsigned (ti_nalloc t_info) <= total_space hs).
    + unfold denote_tc_samebase. simpl. entailer!.
    + unfold all_string_constants; Intros; forward_call; contradiction.
    + forward. entailer!.
      unfold sem_sub_pp in H7. destruct eq_block in H7; [|easy]; simpl in H7.
      inv_int i.
      clear -H7.
      rewrite <- (Ptrofs.repr_unsigned (ti_nalloc t_info)) in H7.
      rewrite ?int64_ltu_ptrofs_to_int_64,
        ?int_ltu_ptrofs_to_int in H7 by reflexivity.
      remember (heap_head (ti_heap t_info)) as h.
      rewrite ptrofs_add_repr, ptrofs_sub_repr, Z.add_comm, Z.add_simpl_r in H7.
      unfold Ptrofs.divs in H7.
      first [rewrite (Ptrofs.signed_repr 8) in H7 by rep_lia |
             rewrite (Ptrofs.signed_repr 4) in H7 by rep_lia].
      rewrite Ptrofs.signed_repr in H7 by (pose proof (total_space_signed_range h); lia).
      unfold WORD_SIZE in H7. rewrite Z.mul_comm, Z.quot_mul in H7 by lia.
      unfold Ptrofs.ltu in H7.
      rewrite !Ptrofs.unsigned_repr in H7
        by (first [apply total_space_range | apply word_size_range]).
      if_tac in H7; try discriminate; clear H7.
      rewrite Ptrofs.repr_unsigned in H.
      pose proof total_space_range h.
      destruct Archi.ptr64 eqn:Hx; try discriminate Hx; clear Hx.
      lia.
    + rewrite <- Heqv in H6|-*. red in H0. rewrite H0 in H5.
      unfold previous_vertices_size in H5. simpl in H5. unfold nth_space in H5.
      rewrite H1 in H5. simpl in H5. rewrite <- H2 in H5.
      replace_SEP
        4 (heap_struct_rep
             sh ((space_start (heap_head (ti_heap t_info)),
                  (offset_val (WORD_SIZE * used_space (heap_head (ti_heap t_info)))
                              (space_start (heap_head (ti_heap t_info))),
                   (offset_val (WORD_SIZE * total_space (heap_head (ti_heap t_info)))
                              (space_start (heap_head (ti_heap t_info))),
                    offset_val (WORD_SIZE * total_space (heap_head (ti_heap t_info)))
                              (space_start (heap_head (ti_heap t_info))))))
                   :: map space_tri hl) (ti_heap_p t_info))
         by (unfold heap_struct_rep; entailer!).
      do 2 forward.
      unfold before_gc_thread_info_rep. rewrite !heap_struct_rep_eq. rewrite <- H5.
      simpl fold_left.
      replace (WORD_SIZE * 0)%Z with 0 by lia.
      rewrite !isptr_offset_val_zero by assumption.
      entailer!. rewrite H1. simpl tl.
      assert (MAX_SPACES = Zlength (map space_tri hl) + 1). {
        pose proof (spaces_size (ti_heap t_info)).
        rewrite <- H2, H1, Zlength_cons, Zlength_map. lia. } rewrite !H2.
      rewrite !data_at_tarray_split_1 by reflexivity. cancel.
      do 2 (unfold_data_at (data_at _ _ _ _)). cancel.
Qed.
