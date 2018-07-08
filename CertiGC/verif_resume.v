Require Import RamifyCoq.CertiGC.gc_spec.

Lemma reset_0_graph_rep_eq: forall (g: LGraph) g0 l,
    g_gen (glabel g) = g0 :: l ->
    iter_sepcon (nat_seq 1 (length l)) (generation_rep g) = 
    graph_rep (reset_nth_gen_graph 0 g).
Proof.
  intros. unfold graph_rep. unfold reset_nth_gen_graph at 1. simpl. rewrite H. simpl.
  unfold generation_rep at 2. unfold reset_nth_gen_graph at 1. unfold nth_gen at 1.
  simpl. rewrite H. simpl. rewrite emp_sepcon. apply iter_sepcon_func_strong. intros.
  rewrite nat_seq_In_iff in H0. unfold generation_rep. unfold nth_sh.
  replace (nth_gen (reset_nth_gen_graph 0 g) x) with (nth_gen g x).
  - apply iter_sepcon_func_strong. intros. apply list_in_map_inv in H1.
    destruct H1 as [n [? ?]]. subst x0. unfold vertex_rep. f_equal.
    + apply vertex_address_reset.
    + apply make_fields_reset.
  - unfold nth_gen. simpl. rewrite H. simpl. destruct x; [exfalso; omega|reflexivity].
Qed.

Lemma body_resume: semax_body Vprog Gprog f_resume resume_spec.
Proof.
  start_function.
  unfold thread_info_rep. Intros. unfold heap_struct_rep.
  forward. unfold fun_info_rep. forward. 1: entailer!. rewrite Znth_0_cons.
  replace_SEP 1 (fun_info_rep rsh f_info fi) by (unfold fun_info_rep; entailer!).
  forward_if True.
  - forward; entailer!.
  - remember (ti_heap_p t_info). rewrite (data_at_isptr sh heap_type). Intros.
    exfalso. destruct t_info. simpl in *. subst. contradiction.
  - destruct H. destruct (g_gen (glabel g)) eqn: ?.
    1: exfalso; apply (g_gen_not_nil (glabel g)); assumption.
    remember (ti_heap_p t_info) as h. remember (ti_heap t_info) as th.
    destruct (heap_head_cons th) as [hs [hl [? ?]]]. rewrite H1, H2 in *. simpl in H.
    rewrite Forall_forall in H. assert (generation_space_compatible g (O, g0, hs)). {
      apply H; left; reflexivity. } destruct H3 as [? [? ?]]. rewrite <- H3 in *.
    pose proof (start_isptr g0). forward. rewrite Znth_0_cons. forward.
    rewrite Znth_0_cons. simpl tl. remember (start_address g0).
    destruct v; try contradiction.
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
      rewrite ptrofs_to_int_repr in H7. hnf in H7. unfold strict_bool_val in H7.
      simpl in H7.
      remember (Int.ltu (Int.repr (total_space h)) (Int.repr (fun_word_size f_info))).
      unfold Val.of_bool in H7. destruct b; simpl in H7. 1: discriminate.
      symmetry in Heqb. apply ltu_repr_false in Heqb;
                          [omega | apply total_space_range | apply word_size_range].
    + Intros. forward. forward. deadvars!. unfold graph_rep. rewrite Heql.
      simpl length. unfold nat_inc_list. simpl nat_seq. simpl iter_sepcon. Intros.
      sep_apply (generation_rep_data_at_ g O  (graph_has_gen_O g)).
      unfold generation_size. unfold nth_gen. rewrite Heql. simpl nth. rewrite H5.
      unfold gen_start, nth_gen. if_tac. 2: exfalso; apply H8; apply graph_has_gen_O.
      clear H8. rewrite Heql. simpl nth. rewrite <- Heqv.
      unfold heap_rest_rep. rewrite H1. simpl iter_sepcon. Intros.
      unfold space_rest_rep at 1. rewrite <- H3, <- H4, if_false. 2: discriminate.
      freeze [1; 2; 3; 4; 5] FR. gather_SEP 1 2.
      replace (nth_sh g 0) with (generation_sh g0) by
          (unfold nth_sh, nth_gen; rewrite Heql; simpl; reflexivity).
      remember (generation_sh g0) as sh0.
      assert (0 <= used_space hs <= total_space hs) by (apply space_order).
      sep_apply (data_at__tarray_value_fold
                   sh0 (total_space hs) (used_space hs) (Vptr b i) H8). thaw FR.
      forward. Exists (reset_nth_gen_graph O g) (reset_nth_heap_thread_info O t_info).
      entailer!.
      1: split; [apply reset_resume_g_relation | apply reset_resume_t_relation].
      rewrite (reset_0_graph_rep_eq _ _ _ Heql). entailer!.
      unfold reset_nth_heap_thread_info. unfold thread_info_rep. simpl.
      rewrite H1. simpl tl. unfold heap_rest_rep. simpl.
      rewrite H1. simpl iter_sepcon. cancel.
      destruct (heap_head_cons (reset_nth_heap 0 (ti_heap t_info))) as [rs [rl [? ?]]].
      rewrite H14. unfold reset_nth_heap in H2. simpl in H2. rewrite H1 in H2.
      inversion H2. subst rl. clear rs H2 H14 H16.
      remember (heap_head (ti_heap t_info)).
      unfold reset_space. simpl. unfold space_rest_rep. simpl. rewrite <- H3.
      if_tac. 1: discriminate.
      rewrite H4, Z.mul_0_r, Z.sub_0_r, isptr_offset_val_zero by (exact I).
      unfold heap_struct_rep. entailer!.
Qed.
