Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_resume: semax_body Vprog Gprog f_resume resume_spec.
Proof.
  start_function.
  unfold thread_info_rep. if_tac. 1: contradiction. clear H2. Intros.
  unfold heap_struct_rep. forward. 
  unfold fun_info_rep. forward. 1: entailer!. rewrite Znth_0_cons.
  replace_SEP 1 (fun_info_rep rsh f_info fi) by (unfold fun_info_rep; entailer!).
  forward_if True; [forward; entailer!| exfalso; destruct t_info; simpl in *; tauto|].
  destruct H as [? [? ?]]. destruct (glabel g) eqn: ?.
  1: exfalso; apply H1; rewrite <- H; reflexivity.
  remember (ti_heap_p t_info) as h. remember (ti_heap t_info) as th.
  destruct (heap_head_cons th) as [hs [hl [? ?]]]. simpl in H2. rewrite H4 in *.
  rewrite Forall_forall in H2. assert (generation_space_compatible g (O, g0, hs)). {
    apply H2; left; reflexivity. } destruct H6 as [? ?]. rewrite H5 in *.
  rewrite <- H6 in *. pose proof (start_isptr g0). forward. rewrite Znth_0_cons.
  forward. rewrite Znth_0_cons. simpl tl.
  remember (start_address g0). destruct v; try contradiction.
  forward_if (fun_word_size f_info <= total_space hs).
  - unfold denote_tc_samebase. simpl. entailer!.
  - unfold all_string_constants. Intros.
    forward_call ((gv ___stringlit_11),
                  (map init_data2byte (gvar_init v___stringlit_11)), rsh).
    exfalso; assumption.
  - forward. entailer!. unfold sem_sub in H9. simpl in H9. if_tac in H9.
    2: contradiction. inv_int i. clear -H9. remember (heap_head (ti_heap t_info)) as h.
    rewrite ptrofs_add_repr, ptrofs_sub_repr, Z.add_comm, Z.add_simpl_r in H9.
    simpl in H9. unfold Ptrofs.divs in H9.
    rewrite (Ptrofs.signed_repr 4) in H9 by rep_omega.
    rewrite Ptrofs.signed_repr in H9 by (apply total_space_signed_range).
    rewrite WORD_SIZE_eq in H9. rewrite Z.mul_comm, Z.quot_mul in H9 by omega.
    rewrite ptrofs_to_int_repr in H9. hnf in H9. unfold strict_bool_val in H9.
    simpl in H9.
    remember (Int.ltu (Int.repr (total_space h)) (Int.repr (fun_word_size f_info))).
    unfold Val.of_bool in H9. destruct b; simpl in H9. 1: discriminate.
    symmetry in Heqb. apply ltu_repr_false in Heqb;
                        [omega | apply total_space_range | apply word_size_range].
  - Intros. forward. forward. deadvars. unfold graph_rep. rewrite Heqg0, map_cons.
    simpl length. simpl combine. simpl iter_sepcon. Intros.
    replace_SEP 2 (generation_rep sh g (O, number_of_vertices g0)) by entailer!.
    sep_apply (generation_rep_data_at_ sh g O (number_of_vertices g0)). rewrite H7.
    unfold gen_start. rewrite Heqg0. simpl nth. rewrite <- Heqv. unfold heap_rest_rep.
    rewrite H4. simpl iter_sepcon. Intros. unfold space_rest_rep at 1. rewrite <- H6.
    rewrite if_false. 2: discriminate. freeze [1; 2; 3; 4; 5] FR. gather_SEP 1 2.
    assert (0 <= used_space hs <= total_space hs) by (apply space_order).
    sep_apply (data_at__tarray_value_join
                 sh (total_space hs) (used_space hs) (Vptr b i) H10).

    
Abort.
