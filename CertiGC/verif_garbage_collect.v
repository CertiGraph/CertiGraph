Require Import RamifyCoq.CertiGC.gc_spec.

Lemma sem_sub_pp_total_space: forall s,
    isptr (space_start s) ->
    force_val
      (sem_sub_pp int_or_ptr_type
                  (offset_val (WORD_SIZE * total_space s) (space_start s)) 
                  (space_start s)) = Vint (Int.repr (total_space s)).
Proof.
  intros. destruct (space_start s); try contradiction. simpl. destruct (eq_block b b).
  2: exfalso; apply n; reflexivity. inv_int i.
  rewrite ptrofs_add_repr, ptrofs_sub_repr.
  replace (ofs + WORD_SIZE * total_space s - ofs) with
      (WORD_SIZE * total_space s)%Z by omega. simpl.
  pose proof (total_space_signed_range s). unfold Ptrofs.divs.
  rewrite !Ptrofs.signed_repr by rep_omega. unfold vptrofs, Archi.ptr64.
  rewrite WORD_SIZE_eq, Z.mul_comm, Z.quot_mul, ptrofs_to_int_repr by omega.
  reflexivity.  
Qed.

Lemma body_garbage_collect:
  semax_body Vprog Gprog f_garbage_collect garbage_collect_spec.
Proof.
  start_function.
  unfold before_gc_thread_info_rep, heap_struct_rep. Intros. forward. pose proof H.
  destruct H as [? _]. pose proof (gt_gs_compatible _ _ H _ (graph_has_gen_O _)).
  destruct H2 as [? [? ?]].
  replace (heap_head (ti_heap t_info)) with (nth_space t_info 0) by
      (destruct (heap_head_cons (ti_heap t_info)) as [hs [hl [? ?]]];
       unfold nth_space; rewrite H5, H6; simpl; reflexivity).
  assert (isptr (space_start (nth_space t_info 0))) by
      (rewrite <- H2; apply start_isptr). do 2 forward. deadvars!.
  rewrite upd_Znth0, sublist_1_cons, Zlength_cons, sublist_same by omega.
  fold (space_tri (nth_space t_info 0)). rewrite <- map_cons.
  replace (nth_space t_info 0 :: tl (spaces (ti_heap t_info))) with
      (spaces (ti_heap t_info)) by
      (destruct (heap_head_cons (ti_heap t_info)) as [hs [hl [? ?]]];
       unfold nth_space; rewrite H6; simpl; reflexivity).
  gather_SEP 4 5 6. replace_SEP 0 (thread_info_rep sh t_info ti) by
      (unfold thread_info_rep, heap_struct_rep; entailer! ;
       do 2 (unfold_data_at 1%nat); cancel).
  forward_for_simple_bound
    11
    (EX i: Z, EX g': LGraph, EX roots': roots_t, EX t_info': thread_info,
     PROP (super_compatible (g', t_info', roots') f_info outlier;
           firstn_gen_clear g' (Z.to_nat i);
           garbage_collect_loop f_info (nat_inc_list (Z.to_nat i)) roots g roots' g';
           ti_size_spec t_info'; graph_has_gen g' (Z.to_nat i))
     LOCAL (temp _h (ti_heap_p t_info'); temp _fi fi; temp _ti ti;
            gvars gv)
     SEP (thread_info_rep sh t_info' ti;
          all_string_constants rsh gv;
          fun_info_rep rsh f_info fi;
          outlier_rep outlier;
          graph_rep g')).
  - Exists g roots t_info. destruct H1 as [? [? [? ?]]]. destruct H0 as [?[?[?[? ?]]]].
    pose proof (graph_has_gen_O g). entailer!. split.
    + red. intros. omega.
    + unfold nat_inc_list. simpl. constructor.
  - cbv beta. Intros g' roots' t_info'. unfold thread_info_rep. Intros.
    unfold heap_struct_rep. assert (0 <= i + 1 < Zlength (spaces (ti_heap t_info'))) by
        (rewrite spaces_size; rep_omega).
    pose proof (space_start_is_pointer_or_null _ _ _ (proj1 H7) H12). forward.
    1: entailer!; rewrite Znth_map by assumption; unfold space_tri; assumption.
    rewrite Znth_map by assumption. unfold space_tri at 1.
    forward_if
      (EX g1: LGraph, EX t_info1: thread_info,
       PROP (super_compatible (g1, t_info1, roots') f_info outlier;
             firstn_gen_clear g1 (Z.to_nat i);
             new_gen_relation (Z.to_nat (i + 1)) g' g1)
       LOCAL (temp _h (ti_heap_p t_info1); temp _fi fi; temp _ti ti;
            gvars gv)
       SEP (thread_info_rep sh t_info1 ti;
            all_string_constants rsh gv;
            fun_info_rep rsh f_info fi;
            outlier_rep outlier;
            graph_rep g1)).
    + remember (space_start (Znth (i + 1) (spaces (ti_heap t_info')))).
      Transparent denote_tc_test_eq. destruct v0; try contradiction.
      * simpl in H13. subst i0. simpl. entailer!.
      * simpl. entailer!. assert (isptr (Vptr b i0)) by exact I. rewrite Heqv0 in *.
        pull_left (heap_rest_rep (ti_heap t_info')). pull_left (graph_rep g').
        destruct H7. rewrite <- (space_start_isptr_iff g') in H21 by assumption.
        sep_apply (graph_and_heap_rest_valid_ptr g' t_info' _ H21); auto.
        rewrite nth_space_Znth, Z2Nat.id by omega.
        sep_apply (valid_pointer_weak
                     (space_start (Znth (i + 1) (spaces (ti_heap t_info'))))).
        apply extend_weak_valid_pointer. Opaque denote_tc_test_eq.
    + assert (0 <= i < Zlength (spaces (ti_heap t_info'))) by omega.
      pose proof (space_start_isptr _ _ _ (proj1 H7) H15 H11). forward.
      1: entailer!; rewrite Znth_map by assumption; unfold space_tri;
        apply isptr_is_pointer_or_null, isptr_offset_val'; assumption.
      rewrite Znth_map by assumption. unfold space_tri at 1. forward.
      1: entailer!; rewrite Znth_map by assumption; unfold space_tri;
        apply isptr_is_pointer_or_null; assumption.
      rewrite Znth_map by assumption. unfold space_tri at 1. forward.
      1: entailer!; destruct (space_start (Znth i (spaces (ti_heap t_info'))));
        try contradiction; simpl; unfold denote_tc_samebase;
          apply prop_right; simpl; destruct (peq b b); simpl; [|apply n]; auto.
      simpl sem_binary_operation'.
      change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 2%N |})
        with int_or_ptr_type. remember (Znth i (spaces (ti_heap t_info'))).
      rewrite sem_sub_pp_total_space by assumption. subst s.
      pose proof (ti_size_gen _ _ _ (proj1 H7) H11 H10). unfold gen_size in H17.
      rewrite nth_space_Znth, Z2Nat.id in H17 by omega. rewrite H17. clear H17.
Abort.
