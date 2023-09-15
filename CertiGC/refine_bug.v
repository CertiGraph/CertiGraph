Require Import CertiGraph.CertiGC.gc_spec.

Local Open Scope logic.

Lemma typed_true_tag: forall (to : nat) (g : LGraph) (index : nat),
    typed_true tint
               (force_val
                  (option_map (fun b : bool => Val.of_bool (negb b))
                              (bool_val_i
                                 (Val.of_bool
                                    (negb (Int.lt (Int.repr (raw_tag
                                                               (vlabel g (to, index))))
                                                  (Int.repr 251))))))) ->
    ~ no_scan g (to, index).
Proof.
  intros. remember (Int.lt (Int.repr (raw_tag (vlabel g (to, index)))) (Int.repr 251)).
  unfold typed_true in H. destruct b; simpl in H; [|inversion H].
  symmetry in Heqb. apply lt_repr in Heqb.
  - unfold no_scan. rep_lia.
  - red. pose proof (raw_tag_range (vlabel g (to, index))). rep_lia.
  - red. rep_lia.
Qed.

Lemma typed_false_tag: forall (to : nat) (g : LGraph) (index : nat),
    typed_false tint
               (force_val
                  (option_map (fun b : bool => Val.of_bool (negb b))
                              (bool_val_i
                                 (Val.of_bool
                                    (negb (Int.lt (Int.repr (raw_tag
                                                               (vlabel g (to, index))))
                                                  (Int.repr 251))))))) ->
    no_scan g (to, index).
Proof.
  intros. remember (Int.lt (Int.repr (raw_tag (vlabel g (to, index)))) (Int.repr 251)).
  unfold typed_false in H. destruct b; simpl in H; [inversion H|].
  symmetry in Heqb. apply lt_repr_false in Heqb.
  - unfold no_scan. rep_lia.
  - red. pose proof (raw_tag_range (vlabel g (to, index))). rep_lia.
  - red. rep_lia.
Qed.

Lemma body_do_scan: semax_body Vprog Gprog f_do_scan do_scan_spec.
Proof.
  start_function.
  forward.
  forward_loop (EX n: nat, EX g': LGraph, EX t_info': thread_info,
                PROP (super_compatible (g', t_info', roots) f_info outlier;
                      forward_condition g' t_info' from to;
                      thread_info_relation t_info t_info';
                      closure_has_index g' to (to_index + n);
                      scan_vertex_while_loop from to (nat_seq to_index n) g g')
                LOCAL
                (temp _s (offset_val (- WORD_SIZE)
                                     (vertex_address g' (to, (to_index + n)%nat)));
                 temp _from_start (gen_start g' from);
                 temp _from_limit (limit_address g' t_info' from);
                 temp _next (next_address t_info' to))
                SEP (all_string_constants rsh gv; fun_info_rep rsh f_info fi;
               outlier_rep outlier; graph_rep g'; thread_info_rep sh t_info' ti))
  break: (EX g' : LGraph, EX t_info' : thread_info,
          PROP (super_compatible (g', t_info', roots) f_info outlier;
                forward_condition g' t_info' from to;
                do_scan_relation from to to_index g g';
                thread_info_relation t_info t_info')
          LOCAL ()
          SEP (all_string_constants rsh gv; fun_info_rep rsh f_info fi;
               outlier_rep outlier; graph_rep g'; thread_info_rep sh t_info' ti)).
  - Exists O g t_info. destruct H as [? [? [? ?]]].
    replace (to_index + 0)%nat with to_index by lia. entailer!.
    split; [|split]; [red; auto | apply tir_id | constructor].
  - Intros n g' t_info'. remember (to_index + n)%nat as index.
    unfold next_address, thread_info_rep. Intros.
    unfold heap_struct_rep. destruct H5 as [? [? [? ?]]].
    destruct H6 as [? [? [? [? ?]]]].
    assert (0 <= Z.of_nat to < 12). {
      clear -H5 H14. destruct H5 as [_ [_ ?]]. red in H14.
      pose proof (spaces_size (ti_heap t_info')).
      rewrite Zlength_correct in H0. rep_lia. }
    destruct (gt_gs_compatible _ _ H5 _ H14) as [? [? ?]]. rewrite nth_space_Znth in *.
    remember (Znth (Z.of_nat to) (spaces (ti_heap t_info'))) as sp_to.
    assert (isptr (space_start sp_to)) by (rewrite <- H18; apply start_isptr).
    remember (map space_tri (spaces (ti_heap t_info'))).
    assert (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef))
                  (Z.of_nat to) l = space_tri sp_to). {
      subst l sp_to. now rewrite Znth_map by (rewrite spaces_size; rep_lia). }
    forward; rewrite H22; unfold space_tri. 1: entailer!.
    unfold vertex_address, vertex_offset. rewrite offset_offset_val.
    simpl vgeneration; simpl vindex.
    replace (WORD_SIZE * (previous_vertices_size g' to index + 1) + - WORD_SIZE) with
        (WORD_SIZE * (previous_vertices_size g' to index))%Z by rep_lia.
    unfold gen_start at 1. rewrite if_true by assumption. rewrite H18.
    remember (WORD_SIZE * used_space sp_to)%Z as used_offset.
    remember (WORD_SIZE * previous_vertices_size g' to index)%Z as index_offset.
    freeze [0; 1; 2; 4; 5] FR.
    gather_SEP (graph_rep g') (heap_rest_rep (ti_heap t_info')).
    assert (
        forall b i,
          Vptr b i = space_start sp_to ->
          graph_rep g' * heap_rest_rep (ti_heap t_info') |--
      !! (WORD_SIZE * total_space sp_to + Ptrofs.unsigned i <= Ptrofs.max_unsigned)). {
      intros. sep_apply (graph_and_heap_rest_data_at_ _ _ _ H14 H5).
      assert (space_start sp_to = gen_start g' to) by
          (unfold gen_start; rewrite if_true by assumption;
           rewrite <- H18; reflexivity). rewrite H24 in H23.
      sep_apply (generation_data_at__ptrofs g' t_info' to b i H23).
      unfold gen_size; rewrite nth_space_Znth; entailer!. }
    assert_PROP (force_val
                   (sem_cmp_pp Clt (offset_val index_offset (space_start sp_to))
                               (offset_val used_offset (space_start sp_to))) =
                 Vint (if if zlt index_offset used_offset then true else false
                       then Int.one else Int.zero)). {
      remember (space_start sp_to). destruct v; try contradiction. inv_int i.
      specialize (H23 b (Ptrofs.repr ofs) eq_refl).
      rewrite Ptrofs.unsigned_repr in H23 by rep_lia. sep_apply H23. Intros.
      assert (0 <= ofs + used_offset <= Ptrofs.max_unsigned). {
        subst.
        pose proof (space_order (Znth (Z.of_nat to) (spaces (ti_heap t_info')))).
        unfold WORD_SIZE in *. rep_lia. }
      assert (0 <= ofs + index_offset <= Ptrofs.max_unsigned). {
        subst. red in H8. pose proof (pvs_ge_zero g' to (to_index + n)%nat).
        pose proof (pvs_mono g' to _ _ H8). unfold WORD_SIZE in *. rep_lia. }
      apply prop_right.
      rewrite force_sem_cmp_pp; [|rewrite isptr_offset_val; assumption..].
      simpl. rewrite !ptrofs_add_repr, if_true. 2: reflexivity.
      unfold Ptrofs.ltu. rewrite !Ptrofs.unsigned_repr; auto. f_equal.
      if_tac; if_tac; try reflexivity; lia. }
    forward_if (gen_has_index g' to index).
    + remember (Znth (Z.of_nat to) (spaces (ti_heap t_info'))) as sp_to.
      sep_apply (graph_and_heap_rest_data_at_ _ _ _ H14 H5).
      unfold generation_data_at_.
      assert (gen_start g' to = space_start sp_to) by
          (subst; unfold gen_start; rewrite if_true; assumption). rewrite H31.
      rewrite data_at__memory_block. Intros. rewrite sizeof_tarray_int_or_ptr.
      2: unfold gen_size; apply total_space_range.
      remember (WORD_SIZE * used_space sp_to)%Z as used_offset.
      remember (to_index + n)%nat as index.
      remember (WORD_SIZE * previous_vertices_size g' to index)%Z as index_offset.
      destruct (space_start sp_to); try contradiction. simpl. unfold test_order_ptrs.
      simpl. case (peq b b); intros. 2: contradiction. simpl.
      assert (sepalg.nonidentity (nth_sh g' to)). {
        apply readable_nonidentity, writable_readable_share. unfold nth_sh.
        apply generation_share_writable. }
      assert (forall offset,
                 0 <= offset <= used_offset ->
                 memory_block (nth_sh g' to) (WORD_SIZE * gen_size t_info' to)
                              (Vptr b i) * TT * FRZL FR |--
        weak_valid_pointer (Vptr b (Ptrofs.add i (Ptrofs.repr offset)))). {
        intros. change (Vptr b (Ptrofs.add i (Ptrofs.repr offset))) with
            (offset_val offset (Vptr b i)).
        sep_apply (memory_block_weak_valid_pointer
                     (nth_sh g' to) (WORD_SIZE * gen_size t_info' to)
                     (Vptr b i) offset); auto.
        3: apply extend_weak_valid_pointer.
        - subst. unfold gen_size. split. 1: apply (proj1 H34).
          transitivity (WORD_SIZE * used_space (nth_space t_info' to))%Z.
          + rewrite nth_space_Znth. apply (proj2 H34).
          + apply Zmult_le_compat_l. apply (proj2 (space_order _)).
            unfold WORD_SIZE. lia.
        - clear -H3 H7. destruct H7 as [? [? ?]].
          rewrite <- H0. unfold WORD_SIZE. lia. }
      apply andp_right; apply H34.
      * subst. split.
        1: pose proof (pvs_ge_zero g' to (to_index + n)%nat); unfold WORD_SIZE; lia.
        apply Zmult_le_compat_l. 2: unfold WORD_SIZE; lia. rewrite <- H20.
        apply pvs_mono. assumption.
      * split; [|lia]; subst; apply Z.mul_nonneg_nonneg;
                                  [unfold WORD_SIZE; lia | apply space_order].
    + assert (index_offset < used_offset). {
        destruct (zlt index_offset used_offset); trivial.
        try solve [ (* this version works in Coq 8.17 with VST 2.12 *)
           match type of H24 with force_val ?x = _ => destruct x; simpl in H24; subst; easy end];
        (* this version worked in Coq 8.16 with VST 2.11 *)
            rewrite H24 in H25; unfold typed_true in H25; easy. }
      forward. entailer!. red. rewrite <- H20 in H26.
      rewrite <- Z.mul_lt_mono_pos_l in H26 by (unfold WORD_SIZE; lia).
      apply pvs_lt_rev in H26. assumption.
    + assert (~ index_offset < used_offset). {
        destruct (zlt index_offset used_offset); trivial.
        try solve [ (* this version works in Coq 8.17 with VST 2.12 *)
           match type of H24 with force_val ?x = _ => destruct x; simpl in H24; subst; easy end];
        (* this version worked in Coq 8.16 with VST 2.11 *)
        now rewrite H24 in H25; unfold typed_false in H25. }
      forward. thaw FR. unfold thread_info_rep, heap_struct_rep.
      Exists g' t_info'. unfold forward_condition. entailer!.
      split; [red; auto | exists n; split; trivial].
      unfold gen_has_index. rewrite <- H20 in H26.
      rewrite <- Z.mul_lt_mono_pos_l in H26 by (unfold WORD_SIZE; lia).
      intro; apply H26. now apply pvs_mono_strict.
    + clear H8 H23 H24. Intros. thaw FR. freeze [1;2;3;4;5;6] FR.
      assert (graph_has_v g' (to, index)) by easy.
      (* annotation theta 7 *)
      localize [vertex_rep (nth_sh g' to) g' (to, index)].
      assert (readable_share (nth_sh g' to)) by
          (unfold nth_sh; apply writable_readable_share, generation_share_writable).
      unfold vertex_rep, vertex_at. Intros.
      assert (offset_val (- WORD_SIZE) (vertex_address g' (to, index)) =
              offset_val index_offset (space_start sp_to)). {
        unfold vertex_address. rewrite offset_offset_val. unfold vertex_offset.
        simpl vgeneration. simpl vindex.
        replace (WORD_SIZE * (previous_vertices_size g' to index + 1) + - WORD_SIZE)
          with index_offset by rep_lia.
        f_equal. unfold gen_start.
        rewrite if_true by assumption; now rewrite H18. }
      rewrite H25. forward. rewrite <- H25.
      gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
      replace_SEP 0 (vertex_rep (nth_sh g' to) g' (to, index)) by
          (unfold vertex_rep, vertex_at; entailer!).

(* How to reproduce the "refine" bug in Coq 8.17 *)
Fail  (* This is what worked before Coq 8.17 *)
      unlocalize [graph_rep g'];
        [ apply graph_vertex_ramif_stable; assumption | ].

eapply (unlocalize_triple [graph_rep g']); [ prove_split_FRZ_in_SEP | | ].
{


(* REMARK: if you uncomment this, you see it clears most hypotheses above the line,
  which did not happen in Coq 8.16  and before 
  refine (ex_intro _ _ eq_refl).
*)

set (J := fst (RamG, H23)).
change RamG with J.
clear.

(* Nothing crazy has happened yet *)

refine (ex_intro _ _ eq_refl).

(* BUG:   H23 is a free variable. *)

