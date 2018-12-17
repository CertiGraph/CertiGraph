Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_resume: semax_body Vprog Gprog f_resume resume_spec.
Proof.
  start_function.
  unfold thread_info_rep, heap_struct_rep. Intros.
  forward. unfold fun_info_rep. forward. 1: entailer!. rewrite Znth_0_cons.
  replace_SEP 1 (fun_info_rep rsh f_info fi) by (unfold fun_info_rep; entailer!).
  forward_if True.
  - forward; entailer!.
  - remember (ti_heap_p t_info). rewrite (data_at_isptr sh heap_type).
    Intros. exfalso. destruct t_info. simpl in *. subst. contradiction.
  - Intros. destruct (heap_head_cons (ti_heap t_info)) as [hs [hl [? ?]]]. 
    rewrite H1, <- H2, map_cons.
    destruct (gt_gs_compatible _ _ H _ (graph_has_gen_O _)) as [? [? ?]].
    assert (isptr (space_start (heap_head (ti_heap t_info)))). {
      rewrite H2. unfold nth_space in H3. rewrite H1 in H3. simpl in H3.
      rewrite <- H3. apply start_isptr. } unfold space_tri at 1. do 2 forward.
    rewrite Znth_0_cons.
    destruct (space_start (heap_head (ti_heap t_info))) eqn:? ; try contradiction.
    forward_if (fun_word_size f_info <= total_space hs).
    + unfold denote_tc_samebase. simpl. entailer!.
    + unfold all_string_constants. Intros.
      forward_call ((gv ___stringlit_11),
                    (map init_data2byte (gvar_init v___stringlit_11)), rsh).
      exfalso; assumption.
    + forward. entailer!. unfold sem_sub in H7. simpl in H7. rewrite if_true in H7.
      2: reflexivity. inv_int i. clear -H7. remember (heap_head (ti_heap t_info)) as h.
      rewrite ptrofs_add_repr, ptrofs_sub_repr, Z.add_comm, Z.add_simpl_r in H7.
      simpl in H7. unfold Ptrofs.divs in H7.
      rewrite (Ptrofs.signed_repr 4) in H7 by rep_omega.
      rewrite Ptrofs.signed_repr in H7 by (apply total_space_signed_range).
      rewrite WORD_SIZE_eq in H7. rewrite Z.mul_comm, Z.quot_mul in H7 by omega.
      rewrite ptrofs_to_int_repr in H7. hnf in H7.
      destruct (Int.ltu (Int.repr (total_space h))
                        (Int.repr (fun_word_size f_info))) eqn:? ; simpl in H7.
      1: inversion H7. apply ltu_repr_false in Heqb;
                         [omega | apply total_space_range | apply word_size_range].
    + rewrite <- Heqv in *. red in H0. rewrite H0 in H5.
      unfold previous_vertices_size in H5. simpl in H5. unfold nth_space in H5.
      rewrite H1 in H5. simpl in H5. rewrite <- H2 in H5.
      replace_SEP
        4 (heap_struct_rep
             sh ((space_start (heap_head (ti_heap t_info)),
                  (offset_val (WORD_SIZE * used_space (heap_head (ti_heap t_info)))
                              (space_start (heap_head (ti_heap t_info))),
                   offset_val (WORD_SIZE * total_space (heap_head (ti_heap t_info)))
                              (space_start (heap_head (ti_heap t_info)))))
                   :: map space_tri hl) (ti_heap_p t_info)) by
          (unfold heap_struct_rep; entailer!). do 3 forward.
      unfold before_gc_thread_info_rep. rewrite !heap_struct_rep_eq. rewrite <- H5.
      replace (WORD_SIZE * 0)%Z with 0 by omega.
      rewrite !isptr_offset_val_zero by assumption. cancel. rewrite H1. simpl tl.
      assert (12 = Zlength (map space_tri hl) + 1). {
        pose proof (spaces_size (ti_heap t_info)). rewrite MAX_SPACES_eq in H2.
        rewrite <- H2, H1, Zlength_cons, Zlength_map. omega. } rewrite !H2.
      rewrite !data_at_tarray_split_1 by reflexivity. cancel.
      do 2 (unfold_data_at (data_at _ _ _ _)). cancel.
Qed.
