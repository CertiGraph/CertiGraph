Require Import RamifyCoq.CertiGC.gc_spec.

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
  intros. remember (Int.lt (Int.repr (raw_tag (vlabel g (to, index))))
                           (Int.repr 251)). unfold typed_true in H.
  destruct b; simpl in H. 2: inversion H. symmetry in Heqb. apply lt_repr in Heqb.
  - unfold no_scan. rep_omega.
  - red. pose proof (raw_tag_range (vlabel g (to, index))). rep_omega.
  - red. rep_omega.
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
  intros. remember (Int.lt (Int.repr (raw_tag (vlabel g (to, index))))
                           (Int.repr 251)). unfold typed_false in H.
  destruct b; simpl in H. 1: inversion H. symmetry in Heqb.
  apply lt_repr_false in Heqb.
  - unfold no_scan. rep_omega.
  - red. pose proof (raw_tag_range (vlabel g (to, index))). rep_omega.
  - red. rep_omega.
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
    replace (to_index + 0)%nat with to_index by omega. entailer!.
    split; [|split]; [red; auto | apply tir_id | constructor].
  - Intros n g' t_info'. remember (to_index + n)%nat as index.
    unfold next_address, thread_info_rep. Intros.
    unfold heap_struct_rep. destruct H5 as [? [? [? ?]]].
    destruct H6 as [? [? [? [? ?]]]].
    assert (0 <= Z.of_nat to < 12). {
      clear -H5 H14. destruct H5 as [_ [_ ?]]. red in H14.
      pose proof (spaces_size (ti_heap t_info')).
      rewrite Zlength_correct in H0. rep_omega. }
    destruct (gt_gs_compatible _ _ H5 _ H14) as [? [? ?]]. rewrite nth_space_Znth in *.
    remember (Znth (Z.of_nat to) (spaces (ti_heap t_info'))) as sp_to.
    assert (isptr (space_start sp_to)) by (rewrite <- H18; apply start_isptr).
    remember (map space_tri (spaces (ti_heap t_info'))).
    assert (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef))
                  (Z.of_nat to) l = space_tri sp_to). {
      subst l sp_to. now rewrite Znth_map by (rewrite spaces_size; rep_omega). }
    forward; rewrite H22; unfold space_tri. 1: entailer!.
    unfold vertex_address, vertex_offset. rewrite offset_offset_val.
    simpl vgeneration; simpl vindex.
    replace (WORD_SIZE * (previous_vertices_size g' to index + 1) + - WORD_SIZE) with
        (WORD_SIZE * (previous_vertices_size g' to index))%Z by rep_omega.
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
                       then Int.one else Int.zero)). { (**)
      remember (space_start sp_to). destruct v; try contradiction. inv_int i.
      specialize (H23 b (Ptrofs.repr ofs) eq_refl).
      rewrite Ptrofs.unsigned_repr in H23 by rep_omega. sep_apply H23. Intros.
      assert (0 <= ofs + used_offset <= Ptrofs.max_unsigned). {
        subst.
        pose proof (space_order (Znth (Z.of_nat to) (spaces (ti_heap t_info')))).
        rep_omega. }
      assert (0 <= ofs + index_offset <= Ptrofs.max_unsigned). {
        subst. red in H8. pose proof (pvs_ge_zero g' to (to_index + n)%nat).
        pose proof (pvs_mono g' to _ _ H8). rep_omega. } apply prop_right.
      rewrite force_sem_cmp_pp; [|rewrite isptr_offset_val; assumption..].
      simpl. rewrite !ptrofs_add_repr, if_true. 2: reflexivity.
      unfold Ptrofs.ltu. rewrite !Ptrofs.unsigned_repr; auto. f_equal.
      if_tac; if_tac; try reflexivity; omega. }
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
          + apply Zmult_le_compat_l. apply (proj2 (space_order _)). rep_omega.
        - clear -H3 H7. destruct H7 as [? [? ?]].
          rewrite <- H0.
          rep_omega. }
      apply andp_right; apply H34.
      * subst. split. 1: pose proof (pvs_ge_zero g' to (to_index + n)%nat); rep_omega.
        apply Zmult_le_compat_l. 2: rep_omega. rewrite <- H20.
        apply pvs_mono. assumption.
      * split; [|omega]; subst; apply Z.mul_nonneg_nonneg;
                                  [rep_omega | apply space_order].
    + assert (index_offset < used_offset). {
        now destruct (zlt index_offset used_offset); [|rewrite H24 in H25; unfold typed_true in H25]. }
      forward. entailer!. red. rewrite <- H20 in H26.
      rewrite <- Z.mul_lt_mono_pos_l in H26 by rep_omega.
      apply pvs_lt_rev in H26. assumption.
    + assert (~ index_offset < used_offset). {
        destruct (zlt index_offset used_offset); trivial. 
        now rewrite H24 in H25; unfold typed_false in H25. }
      forward. thaw FR. unfold thread_info_rep, heap_struct_rep.
      Exists g' t_info'. unfold forward_condition. entailer!.
      split; [red; auto | exists n; split; trivial].
      unfold gen_has_index. rewrite <- H20 in H26.
      rewrite <- Z.mul_lt_mono_pos_l in H26 by rep_omega. intro; apply H26.
      now apply pvs_mono_strict.
    + clear H8 H23 H24. Intros. thaw FR. freeze [1;2;3;4;5;6] FR.
      assert (graph_has_v g' (to, index)) by easy. 
      localize [vertex_rep (nth_sh g' to) g' (to, index)].
      assert (readable_share (nth_sh g' to)) by
          (unfold nth_sh; apply writable_readable_share, generation_share_writable).
      unfold vertex_rep, vertex_at. Intros.
      assert (offset_val (- WORD_SIZE) (vertex_address g' (to, index)) =
              offset_val index_offset (space_start sp_to)). {
        unfold vertex_address. rewrite offset_offset_val. unfold vertex_offset.
        simpl vgeneration. simpl vindex.
        replace (WORD_SIZE * (previous_vertices_size g' to index + 1) + - WORD_SIZE)
          with index_offset by rep_omega.
        f_equal. unfold gen_start.
        rewrite if_true by assumption; now rewrite H18. }
      rewrite H25. forward. rewrite <- H25.
      gather_SEP (data_at (nth_sh g' to) tuint (Z2val (make_header g' (to, index)))
            (offset_val (- WORD_SIZE) (vertex_address g' (to, index))))
     (data_at (nth_sh g' to)
       (tarray int_or_ptr_type (Zlength (make_fields_vals g' (to, index))))
       (make_fields_vals g' (to, index)) (vertex_address g' (to, index))). 
      replace_SEP 0 (vertex_rep (nth_sh g' to) g' (to, index)) by
          (unfold vertex_rep, vertex_at; entailer!).
      unlocalize [graph_rep g']. 1: apply graph_vertex_ramif_stable; assumption.
      forward. forward. assert (gen_unmarked g' to). {
        eapply (svwl_gen_unmarked from to _ g); eauto.
        destruct H0 as [_ [_ [? _]]]. assumption. }
      specialize (H26 H14 _ H8).
      rewrite make_header_Wosize, make_header_tag by assumption. deadvars!.
      fold (next_address t_info' to). thaw FR.
      fold (heap_struct_rep sh l (ti_heap_p t_info')). 
      (* gather_SEP 5 6 1. *)
      gather_SEP
        (data_at sh thread_info_type _ _)
        (heap_struct_rep sh l _ ) (heap_rest_rep _).
      replace_SEP 0 (thread_info_rep sh t_info' ti) by
          (unfold thread_info_rep; entailer!).
      forward_if
        (EX g'': LGraph, EX t_info'': thread_info,
         PROP (super_compatible (g'', t_info'', roots) f_info outlier;
               forward_condition g'' t_info'' from to;
               thread_info_relation t_info t_info'';
               (no_scan g' (to, index) /\ g'' = g') \/
               (~ no_scan g' (to, index) /\
                scan_vertex_for_loop
                  from to (to, index)
                  (nat_inc_list (length (vlabel g' (to, index)).(raw_fields))) g' g''))
         LOCAL (temp _tag (vint (raw_tag (vlabel g' (to, index))));
                temp _sz (vint (Zlength (raw_fields (vlabel g' (to, index)))));
                temp _s (offset_val (- WORD_SIZE) (vertex_address g'' (to, index)));
                temp _from_start (gen_start g'' from);
                temp _from_limit (limit_address g'' t_info'' from);
                temp _next (next_address t_info'' to))
         SEP (thread_info_rep sh t_info'' ti; graph_rep g'';
              fun_info_rep rsh f_info fi;
              all_string_constants rsh gv; outlier_rep outlier)).
      * apply typed_true_tag in H27.
        remember (Zlength (raw_fields (vlabel g' (to, index)))).
        assert (1 <= z < Int.max_signed). {
          subst z. pose proof (raw_fields_range (vlabel g' (to, index))). split; [omega|].
          transitivity (two_power_nat 22); [omega | vm_compute; reflexivity]. }
        forward_loop
          (EX i: Z, EX g3: LGraph, EX t_info3: thread_info,
           PROP (scan_vertex_for_loop
                   from to (to, index)
                   (sublist 0 (i - 1)
                            (nat_inc_list
                               (length (vlabel g' (to, index)).(raw_fields)))) g' g3;
                super_compatible (g3, t_info3, roots) f_info outlier;
                forward_condition g3 t_info3 from to;
                thread_info_relation t_info t_info3;
                1 <= i <= z + 1)
           LOCAL (temp _tag (vint (raw_tag (vlabel g' (to, index))));
                  temp _j (vint i);
                  temp _sz (vint z);
                  temp _s (offset_val (- WORD_SIZE) (vertex_address g3 (to, index)));
                  temp _from_start (gen_start g3 from);
                  temp _from_limit (limit_address g3 t_info3 from);
                  temp _next (next_address t_info3 to))
           SEP (all_string_constants rsh gv;
                outlier_rep outlier;
                fun_info_rep rsh f_info fi;
                graph_rep g3;
                thread_info_rep sh t_info3 ti))
          continue: (EX i: Z, EX g3: LGraph, EX t_info3: thread_info,
           PROP (scan_vertex_for_loop
                   from to (to, index)
                   (sublist 0 i
                            (nat_inc_list
                               (length (vlabel g' (to, index)).(raw_fields)))) g' g3;
                super_compatible (g3, t_info3, roots) f_info outlier;
                forward_condition g3 t_info3 from to;
                thread_info_relation t_info t_info3;
                1 <= i + 1 <= z + 1)
           LOCAL (temp _tag (vint (raw_tag (vlabel g' (to, index))));
                  temp _j (vint i);
                  temp _sz (vint z);
                  temp _s (offset_val (- WORD_SIZE) (vertex_address g3 (to, index)));
                  temp _from_start (gen_start g3 from);
                  temp _from_limit (limit_address g3 t_info3 from);
                  temp _next (next_address t_info3 to))
           SEP (all_string_constants rsh gv;
                fun_info_rep rsh f_info fi;
                outlier_rep outlier;
                graph_rep g3;
                thread_info_rep sh t_info3 ti)).
        -- forward. Exists 1 g' t_info'. replace (1 - 1) with 0 by omega.
           autorewrite with sublist. unfold forward_condition. entailer!.
           split; [apply svfl_nil | red; auto].
        -- Intros i g3 t_info3. forward_if (i <= z).
           ++ forward. entailer!.
           ++ forward. assert (i = z + 1) by omega. subst i. clear H33 H34.
              replace (z + 1 - 1) with z in H29 by omega.
              remember (raw_fields (vlabel g' (to, index))) as r.
              replace (sublist 0 z (nat_inc_list (Datatypes.length r))) with
                  (nat_inc_list (Datatypes.length r)) in H29.
              ** Exists g3 t_info3. entailer!.
              ** rewrite sublist_all; trivial. rewrite Z.le_lteq. right.
                 subst z. rewrite !Zlength_correct, nat_inc_list_length. reflexivity.
           ++ Intros.
              change (Tpointer tvoid {| attr_volatile := false;
                                        attr_alignas := Some 2%N |}) with
                  int_or_ptr_type.
              assert (isptr (vertex_address g3 (to, index))). {
                erewrite <- svfl_vertex_address; eauto. rewrite <- H18 in H21.
                2: apply graph_has_v_in_closure; assumption. clear -H21 H14.
                unfold vertex_address. unfold gen_start. simpl.
                rewrite if_true by assumption. rewrite isptr_offset_val. assumption. }
              assert (graph_has_gen g3 to) by
                  (eapply svfl_graph_has_gen in H29; [rewrite <- H29|]; assumption).
              assert (graph_has_v g3 (to, index)) by
                  (eapply svfl_graph_has_v in H29; [apply H29| assumption..]).
              forward_call (rsh, sh, gv, fi, ti, g3, t_info3, f_info, roots,
                            outlier, from, to, 0, (@inr Z _ ((to, index), i - 1))).
              ** simpl snd. apply prop_right.
                 split; [split; [split|]|]; [|reflexivity..].
                 rewrite sem_add_pi_ptr_special;
                   [| rewrite isptr_offset_val; assumption | rep_omega]. simpl.
                 rewrite offset_offset_val. do 2 f_equal. rep_omega.
              ** split; [|split; [|split; [|split; [|split; [|split]]]]];
                   try assumption. 2: rep_omega. red. split; [|split;[|split]].
                 --- assumption.
                 --- eapply svfl_raw_fields in H29;
                       [rewrite <- H29; omega | assumption..].
                 --- rewrite <- H26. symmetry.
                     eapply svfl_raw_mark in H29; [apply H29 | assumption..|].
                     simpl. omega.
                 --- simpl; auto.
              ** Intros vret. destruct vret as [[g4 t_info4] roots']. simpl fst in *.
                 simpl snd in *. simpl in H37. subst roots'. Exists i g4 t_info4.
                 destruct H38 as [? [? [? ?]]].
                 assert (gen_start g3 from = gen_start g4 from) by
                     (eapply fr_gen_start; eauto).
                 assert (limit_address g3 t_info3 from =
                         limit_address g4 t_info4 from). {
                   unfold limit_address. rewrite H45.
                   do 2 f_equal. apply (proj2 H42). }
                 assert (next_address t_info3 to = next_address t_info4 to) by
                     (unfold next_address; f_equal; apply (proj1 H42)). entailer!.
                 split; [|split; [|split]]; try easy.
                 --- remember (nat_inc_list
                                 (Datatypes.length
                                    (raw_fields (vlabel g' (to,
                                                            (to_index + n)%nat))))).
                     assert (i <= Zlength l). {
                       subst l. rewrite Zlength_correct, nat_inc_list_length.
                       rewrite Zlength_correct in H34. omega. }
                     rewrite (sublist_split 0 (i - 1) i) by omega.
                     rewrite (sublist_one (i - 1) i) by omega.
                     apply svfl_add_tail with roots g3; trivial. 
                     assert (Z.of_nat (Znth (i - 1) l) = i - 1). {
                       rewrite <- nth_Znth by omega. subst l.
                       rewrite nat_inc_list_nth; [rewrite Z2Nat.id; omega|].
                       rewrite <- ZtoNat_Zlength. rewrite Zlength_correct in H52.
                       rewrite nat_inc_list_length in H52. rewrite Nat2Z.inj_lt.
                       rewrite !Z2Nat.id; omega. } rewrite H53. assumption.
                 --- apply tir_trans with t_info3; assumption.
                 --- f_equal. symmetry. eapply fr_vertex_address; eauto.
                     apply graph_has_v_in_closure; assumption.
        -- Intros i g3 t_info3. forward. rewrite add_repr. Exists (i + 1) g3 t_info3.
           replace (i + 1 - 1) with i by omega. entailer!.
      * apply typed_false_tag in H27. forward. Exists g' t_info'.
        unfold forward_condition. entailer!. easy.
      * Intros g'' t_info''. assert (isptr (vertex_address g'' (to, index))). {
          assert (isptr (vertex_address g' (to, index))). {
            unfold vertex_address. rewrite isptr_offset_val. unfold gen_start.
            rewrite <- H18 in H21. rewrite if_true; assumption. }
          destruct H30 as [[? ?] | [? ?]]. 1: subst g''; assumption.
          eapply svfl_vertex_address in H32;
            [rewrite <- H32 | | apply graph_has_v_in_closure]; assumption. }
        pose proof (raw_fields_range (vlabel g' (to, index))). forward.
        -- entailer!. split. 1: rep_omega.
           assert (two_power_nat 22 < Int.max_signed) by (vm_compute; reflexivity).
           rewrite Int.signed_repr; rep_omega.
        -- change (Tpointer tvoid {| attr_volatile := false;
                                     attr_alignas := Some 2%N |}) with int_or_ptr_type.
           simpl sem_binary_operation'. rewrite add_repr.
           assert (force_val (sem_add_ptr_int
                                int_or_ptr_type Unsigned
                                (offset_val (- WORD_SIZE)
                                            (vertex_address g'' (to, index)))
                                (vint (1 + Zlength
                                             (raw_fields (vlabel g' (to, index))))))
                   = offset_val (- WORD_SIZE)
                                (vertex_address g''
                                                (to, (to_index + (n + 1))%nat))). {
             rewrite sem_add_pi_ptr_special.
             - assert (Zlength (raw_fields (vlabel g' (to, index))) =
                       Zlength (raw_fields (vlabel g'' (to, index)))). {
                 destruct H30 as [[? ?] | [? ?]]. 1: subst g''; reflexivity.
                 erewrite svfl_raw_fields; eauto. } rewrite H33.
               simpl. replace (to_index + (n + 1))%nat with (S index) by omega.
               unfold vertex_address. rewrite !offset_offset_val.
               unfold vertex_offset. simpl vgeneration. simpl vindex. f_equal.
               rewrite pvs_S. unfold vertex_size. rep_omega.
             - rewrite isptr_offset_val. assumption.
             - split. 1: rep_omega.
               assert (two_power_nat 22 < Int.max_unsigned) by
                   (vm_compute; reflexivity). omega. } rewrite H33. clear H33.
           assert (closure_has_index g'' to (to_index + (n + 1))). {
             replace (to_index + (n + 1))%nat with (index + 1)%nat by omega.
             cut (gen_has_index g'' to index). 1: red; intros; red in H33; omega.
             destruct H30 as [[? ?] | [? ?]].
             - subst g''. destruct H23. assumption.
             - eapply svfl_graph_has_v in H33; eauto. destruct H33. assumption. }
           Exists (n + 1)%nat g'' t_info''. destruct H27 as [? [? [? ?]]]. entailer!.
           clear H37 H38 H39 H40. replace (n + 1)%nat with (S n) by omega.
           rewrite nat_seq_S, Nat.add_comm. destruct H30 as [[? ?] | [? ?]].
           ++ subst g''. split; [| apply svwl_add_tail_no_scan]; easy.
           ++ split; [|apply svwl_add_tail_scan with g']; easy.
  - Intros g' t_info'. forward. Exists g' t_info'. entailer!.
Qed.
