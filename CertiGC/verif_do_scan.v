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
  forward_loop (EX n: nat, EX g': LGraph, EX h': heap,
                PROP (super_compatible g' h' rootpairs roots outlier;
                      forward_condition g' h' from to;
                      heap_relation h h';
                      closure_has_index g' to (to_index + n);
                      scan_vertex_while_loop from to (nat_seq to_index n) g g')
                LOCAL
                (temp _s (offset_val (- WORD_SIZE)
                                     (vertex_address g' (to, (to_index + n)%nat)));
                 temp _from_start (gen_start g' from);
                 temp _from_limit (limit_address g' h' from);
                 temp _next (heap_next_address hp to))
                SEP (all_string_constants rsh gv;
               outlier_rep outlier; graph_rep g'; 
               roots_rep sh rootpairs;
               heap_rep sh h' hp))
  break: (EX g' : LGraph, EX h': heap,
          PROP (super_compatible g' h' rootpairs roots outlier;
                forward_condition g' h' from to;
                do_scan_relation from to to_index g g';
                heap_relation h h')
          LOCAL ()
          SEP (all_string_constants rsh gv;
               outlier_rep outlier; graph_rep g'; 
               roots_rep sh rootpairs;
               heap_rep sh h' hp)).
  - Exists O g h. destruct H as [? [? [? ?]]].
    simpl fst in *; simpl snd in *; 
    replace (to_index + 0)%nat with to_index by lia. entailer!.
    split; [|split]; [ split3; simpl; auto | apply hr_refl | constructor].
  - Intros n g' h'. remember (to_index + n)%nat as index.
    unfold heap_next_address, heap_rep. Intros.
    unfold heap_struct_rep. destruct H5 as [? [? [? ?]]].
    destruct H6 as [? [? [? [? ?]]]]; simpl fst in *; simpl snd in *.
    assert (0 <= Z.of_nat to < MAX_SPACES). {
      clear -H5 H14. destruct H5 as [_ [_ ?]]. red in H14.
      pose proof (spaces_size h').
      rewrite Zlength_correct in H0. rep_lia. }
    destruct (gt_gs_compatible _ _ H5 _ H14) as [? [? ?]]. rewrite nth_space_Znth in *.
    remember (Znth (Z.of_nat to) (spaces h')) as sp_to.
    assert (isptr (space_start sp_to)) by (rewrite <- H18; apply start_isptr).
    remember (map space_tri (spaces h')).
    assert (@Znth (val * (val * (val*val))) (Vundef, (Vundef, (Vundef,Vundef)))
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
    freeze [0; 1; 3; 4] FR.
    gather_SEP (graph_rep g') (heap_rest_rep h').
    assert (
        forall b i,
          Vptr b i = space_start sp_to ->
          graph_rep g' * heap_rest_rep h' |--
      !! (WORD_SIZE * total_space sp_to + Ptrofs.unsigned i <= Ptrofs.max_unsigned)). {
      intros. sep_apply (graph_and_heap_rest_data_at_ _ _ _ H14 H5).
      assert (space_start sp_to = gen_start g' to) by
          (unfold gen_start; rewrite if_true by assumption;
           rewrite <- H18; reflexivity). rewrite H24 in H23.
      sep_apply (generation_data_at__ptrofs g' h' to b i H23).
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
        pose proof (space_order (Znth (Z.of_nat to) (spaces h'))).
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
    + remember (Znth (Z.of_nat to) (spaces h')) as sp_to.
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
                 memory_block (nth_sh g' to) (WORD_SIZE * gen_size h' to)
                              (Vptr b i) * TT * FRZL FR |--
        weak_valid_pointer (Vptr b (Ptrofs.add i (Ptrofs.repr offset)))). {
        intros. change (Vptr b (Ptrofs.add i (Ptrofs.repr offset))) with
            (offset_val offset (Vptr b i)).
        sep_apply (memory_block_weak_valid_pointer
                     (nth_sh g' to) (WORD_SIZE * gen_size h' to)
                     (Vptr b i) offset); auto.
        3: apply extend_weak_valid_pointer.
        - subst. unfold gen_size. split. 1: apply (proj1 H34).
          transitivity (WORD_SIZE * used_space (nth_space h' to))%Z.
          + rewrite nth_space_Znth. apply (proj2 H34).
          + apply Zmult_le_compat_l. apply (proj2 (space_order _)).
            unfold WORD_SIZE. lia.
        - clear -H3 H7. destruct H7.
          rewrite <- H. unfold WORD_SIZE. lia. }
      apply andp_right; apply H34.
      * subst. split.
        1: pose proof (pvs_ge_zero g' to (to_index + n)%nat); unfold WORD_SIZE; lia.
        apply Zmult_le_compat_l. 2: unfold WORD_SIZE; lia. rewrite <- H20.
        apply pvs_mono. assumption.
      * split; [|lia]; subst; apply Z.mul_nonneg_nonneg;
                                  [unfold WORD_SIZE; lia | apply space_order].
    + assert (index_offset < used_offset). {
        destruct (zlt index_offset used_offset); trivial.
        match type of H24 with force_val ?A = _ => destruct A; inv H24 end. simpl in H26; subst. inv H25. 
      }
      forward. entailer!. red. rewrite <- H20 in H26.
      rewrite <- Z.mul_lt_mono_pos_l in H26 by (unfold WORD_SIZE; lia).
      apply pvs_lt_rev in H26. assumption.
    + assert (~ index_offset < used_offset). {
        destruct (zlt index_offset used_offset); trivial.
        match type of H24 with force_val ?A = _ => destruct A; inv H24 end. simpl in H26; subst. inv H25. 
      }
      forward. thaw FR. unfold thread_info_rep, heap_rep, heap_struct_rep.
      Exists g' h'. unfold forward_condition. entailer!.
      split; [split3; auto | exists n; split; trivial].
      unfold gen_has_index. rewrite <- H20 in H26.
      rewrite <- Z.mul_lt_mono_pos_l in H26 by (unfold WORD_SIZE; lia).
      intro; apply H26. now apply pvs_mono_strict.
    + clear H8 H23 H24. Intros. thaw FR. freeze [1;2;3;4;5] FR.
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
      unlocalize [graph_rep g']. 1: apply graph_vertex_ramif_stable; assumption.
      forward. forward. assert (gen_unmarked g' to). {
        eapply (svwl_gen_unmarked from to _ g); eauto.
        destruct H0 as [_ [_ [? _]]]. assumption. }
      specialize (H26 H14 _ H8).
      rewrite make_header_Wosize, make_header_tag by assumption.
      fold (heap_next_address hp to). thaw FR.
      fold (heap_struct_rep sh l hp).
      gather_SEP
        (heap_struct_rep _ _ _ ) (heap_rest_rep _).
      replace_SEP 0 (heap_rep sh h' hp) by
          (unfold thread_info_rep, heap_rep; entailer!).
      forward_if
        (EX g'': LGraph, EX h'': heap,
         PROP (super_compatible g'' h'' rootpairs roots outlier;
               forward_condition g'' h'' from to;
               heap_relation h h'';
               (no_scan g' (to, index) /\ g'' = g') \/
               (~ no_scan g' (to, index) /\
                scan_vertex_for_loop
                  from to (to, index)
                  (nat_inc_list (length (vlabel g' (to, index)).(raw_fields))) g' g''))
         LOCAL (temp _tag (vint (raw_tag (vlabel g' (to, index))));
                temp _sz
                     (if Archi.ptr64 then
                        Vlong (Int64.repr
                                 (Zlength (raw_fields (vlabel g' (to, index)))))
                      else vint (Zlength (raw_fields (vlabel g' (to, index)))));
                temp _s (offset_val (- WORD_SIZE) (vertex_address g'' (to, index)));
                temp _from_start (gen_start g'' from);
                temp _from_limit (limit_address g'' h'' from);
                temp _next (heap_next_address hp to))
         SEP (roots_rep sh rootpairs;
              heap_rep sh h'' hp; graph_rep g'';
              all_string_constants rsh gv; outlier_rep outlier)).
      * rewrite Int64.unsigned_repr in H27;
             [|pose proof (raw_tag_range (vlabel g' (to, index))); rep_lia].
        pose proof typed_true_tag to g' index as Hxx.
        destruct (negb (Int.lt (Int.repr (raw_tag (vlabel g' (to, index)))) (Int.repr 251))); try discriminate.
        clear H27; rename Hxx into H27.
        specialize (H27 (eq_refl _)).
        remember (Zlength (raw_fields (vlabel g' (to, index)))).
        assert (1 <= z < (if Archi.ptr64 then Int64.max_signed else Int.max_signed)).
        {
          subst z. pose proof (raw_fields_range (vlabel g' (to, index))).
          split; [lia|]. transitivity (two_p (WORD_SIZE * 8 - 10));
                           [lia | vm_compute; reflexivity]. }
        forward_loop
          (EX i: Z, EX g3: LGraph, EX h3: heap,
           PROP (scan_vertex_for_loop
                   from to (to, index)
                   (sublist 0 (i - 1)
                            (nat_inc_list
                               (length (vlabel g' (to, index)).(raw_fields)))) g' g3;
                super_compatible g3 h3 rootpairs roots outlier;
                forward_condition g3 h3 from to;
                heap_relation h h3;
                1 <= i <= z + 1)
           LOCAL (temp _tag (vint (raw_tag (vlabel g' (to, index))));
                  temp _j (if Archi.ptr64 then (Vlong (Int64.repr i)) else vint i);
                  temp _sz (if Archi.ptr64 then (Vlong (Int64.repr z)) else vint z);
                  temp _s (offset_val (- WORD_SIZE) (vertex_address g3 (to, index)));
                  temp _from_start (gen_start g3 from);
                  temp _from_limit (limit_address g3 h3 from);
                  temp _next (heap_next_address hp to))
           SEP (all_string_constants rsh gv;
                outlier_rep outlier;
                graph_rep g3;
                roots_rep sh rootpairs;
                heap_rep sh h3 hp))
          continue: (EX i: Z, EX g3: LGraph, EX h3: heap,
           PROP (scan_vertex_for_loop
                   from to (to, index)
                   (sublist 0 i
                            (nat_inc_list
                               (length (vlabel g' (to, index)).(raw_fields)))) g' g3;
                super_compatible g3 h3 rootpairs roots outlier;
                forward_condition g3 h3 from to;
                heap_relation h h3;
                1 <= i + 1 <= z + 1)
           LOCAL (temp _tag (vint (raw_tag (vlabel g' (to, index))));
                  temp _j (if Archi.ptr64 then (Vlong (Int64.repr i)) else vint i);
                  temp _sz (if Archi.ptr64 then (Vlong (Int64.repr z)) else vint z);
                  temp _s (offset_val (- WORD_SIZE) (vertex_address g3 (to, index)));
                  temp _from_start (gen_start g3 from);
                  temp _from_limit (limit_address g3 h3 from);
                  temp _next (heap_next_address hp to))
           SEP (all_string_constants rsh gv;
                outlier_rep outlier;
                graph_rep g3;
                roots_rep sh rootpairs;
                heap_rep sh h3 hp)).
        -- forward. Exists 1 g' h'. replace (1 - 1) with 0 by lia.
           autorewrite with sublist. unfold forward_condition. entailer!.
           try (rewrite Int64.unsigned_repr;
                [| pose proof (raw_tag_range (vlabel g' (to, (to_index + n)%nat)));
                   rep_lia]).
           split; [apply svfl_nil | split3; auto]. split3; auto.
        -- Intros i g3 h3. forward_if (i <= z).
           ++ forward. entailer!.
              first [rewrite !Int.unsigned_repr in H34 |
                     apply ltu64_repr_false in H34]; try lia.
              ** clear -H28 H33. simpl in H28. split. 1: lia.
                 transitivity
                   (Zlength (raw_fields (vlabel g' (to, (to_index + n)%nat))) + 1);
                   rep_lia.
              ** clear -H28. simpl in H28. rep_lia.
           ++ forward. assert (i = z + 1). {
                try unfold Int64.ltu in H34.
                first [rewrite !Int.unsigned_repr in H34 |
                       rewrite !Int64.unsigned_repr in H34].
                - try (if_tac in H34; [|inversion H34]). lia.
                - simpl in H28. clear -H28 H33. rep_lia.
                - simpl in H28. clear -H28. rep_lia. } subst i. clear H33 H34.
              replace (z + 1 - 1) with z in H29 by lia.
              remember (raw_fields (vlabel g' (to, index))) as r.
              replace (sublist 0 z (nat_inc_list (Datatypes.length r))) with
                  (nat_inc_list (Datatypes.length r)) in H29.
              ** Exists g3 h3. entailer!.
              ** rewrite sublist_same; trivial.
                 subst z. rewrite !Zlength_correct, nat_inc_list_length. reflexivity.
           ++ Intros.
              change (Tpointer tvoid {| attr_volatile := false;
                                        attr_alignas := Some 2%N |}) with
                  int_or_ptr_type.
              change (Tpointer tvoid {| attr_volatile := false;
                                        attr_alignas := Some 3%N |}) with
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
              forward_call (rsh, sh, gv, g3, h3, hp, rootpairs, roots,
                            outlier, from, to, 0, (@inr Z _ ((to, index), i - 1))).
              ** simpl snd. apply prop_right. simpl.
                 do 4 f_equal.
                 first [rewrite sem_add_pi_ptr_special' |
                        rewrite sem_add_pl_ptr_special]; try easy;
                   [|rewrite isptr_offset_val; assumption].
                 simpl. rewrite offset_offset_val. f_equal. unfold WORD_SIZE; lia.
              ** repeat (split; try assumption). lia.
                 --- eapply svfl_raw_fields in H29;
                       [rewrite <- H29; lia | assumption..].
                 --- rewrite <- H26. symmetry.
                     eapply svfl_raw_mark in H29; [apply H29 | assumption..|].
                     simpl. lia.
                 --- simpl; auto.
              ** Intros vret. destruct vret as [[g4 h4] roots']. simpl fst in *.
                 simpl snd in *. simpl in H37.
                 simpl in H39.
                 subst roots'.
                 Exists i g4 h4.
                 revert H38.
                 replace (update_rootpairs _ _) with rootpairs. 2:{
                   replace (map (root2val g4) roots) with (map (root2val g) roots).
                   destruct H as [_ [? _]]; rewrite H. symmetry. apply update_rootpairs_same.
                   destruct H as [_ [? _]]. rewrite H.
                   destruct H30 as [_ [? [[_ ?] _]]]. red in H30. rewrite <- H30.
                   apply Znth_eq_ext. list_solve. intros.
                   rewrite !Znth_map by list_solve.
                   destruct (Znth i0 roots) eqn:?H; auto.
                   simpl.
                   eapply fr_vertex_address; try eassumption.
                   red in H38. rewrite Forall_forall in H38.
                   apply graph_has_v_in_closure. apply H38.
                   apply filter_sum_right_In_iff. rewrite <- H43. apply Znth_In.
                   rewrite Zlength_map in H39. auto. 
                 }
                 intros H38.
                 destruct H38 as [? [? [? ?]]].
                 assert (gen_start g3 from = gen_start g4 from) by
                     (eapply fr_gen_start; eauto).
                 assert (limit_address g3 h3 from =
                         limit_address g4 h4 from). {
                   unfold limit_address. rewrite H45.
                   do 2 f_equal. apply H42. }
                 entailer!.
                 split; [|split; [|split]]; try easy.
                 --- remember (nat_inc_list
                                 (Datatypes.length
                                    (raw_fields (vlabel g' (to,
                                                            (to_index + n)%nat))))).
                     assert (i <= Zlength l). {
                       subst l. rewrite Zlength_correct, nat_inc_list_length.
                       rewrite Zlength_correct in H34. lia. }
                     rewrite (sublist_split 0 (i - 1) i) by lia.
                     rewrite (sublist_one (i - 1) i) by lia.
                     apply svfl_add_tail with roots g3; trivial.
                     assert (Z.of_nat (Znth (i - 1) l) = i - 1). {
                       rewrite <- nth_Znth by lia. subst l.
                       rewrite nat_inc_list_nth; [rewrite Z2Nat.id; lia|].
                       rewrite <- ZtoNat_Zlength. rewrite Zlength_correct in H51.
                       rewrite nat_inc_list_length in H51. rewrite Nat2Z.inj_lt.
                       rewrite !Z2Nat.id; lia. } rewrite H52. assumption.                     
                 --- apply hr_trans with h3; assumption.
                 --- f_equal. symmetry. eapply fr_vertex_address; eauto.
                     apply graph_has_v_in_closure; assumption.
        -- Intros i g3 h3. cbv [Archi.ptr64]. forward.
           ++ entailer!. clear -H28 H33. simpl in H28.
              first [rewrite !Int.signed_repr | rewrite Int64.signed_repr]; rep_lia.
           ++ Exists (i + 1) g3 h3. replace (i + 1 - 1) with i by lia. entailer!.
      * rewrite Int64.unsigned_repr in H27;
             [|pose proof (raw_tag_range (vlabel g' (to, index))); rep_lia].
        pose proof typed_false_tag to g' index as Hxx.
        destruct (negb (Int.lt (Int.repr (raw_tag (vlabel g' (to, index)))) (Int.repr 251))).
        2: simpl in H27; contradiction H27; reflexivity.
        clear H27; rename Hxx into H27.
        specialize (H27 (eq_refl _)). 
        forward. Exists g' h'.
        unfold forward_condition. entailer!.
        try (rewrite Int64.unsigned_repr;
             [|pose proof (raw_tag_range (vlabel g' (to, (to_index + n)%nat)));
               rep_lia]). easy.
      * Intros g'' h''. assert (isptr (vertex_address g'' (to, index))). {
          assert (isptr (vertex_address g' (to, index))). {
            unfold vertex_address. rewrite isptr_offset_val. unfold gen_start.
            rewrite <- H18 in H21. rewrite if_true; assumption. }
          destruct H30 as [[? ?] | [? ?]]. 1: subst g''; assumption.
          eapply svfl_vertex_address in H32;
            [rewrite <- H32 | | apply graph_has_v_in_closure]; assumption. }
        pose proof (raw_fields_range (vlabel g' (to, index))). forward.
           change (Tpointer tvoid {| attr_volatile := false;
                                     attr_alignas := Some 2%N |}) with int_or_ptr_type.
           change (Tpointer tvoid {| attr_volatile := false;
                                     attr_alignas := Some 3%N |}) with int_or_ptr_type.
           cbv [Archi.ptr64]. simpl sem_binary_operation'.
           first [rewrite add_repr | rewrite add64_repr].
           try (rewrite Int.signed_repr; [|rep_lia]).
           assert (force_val
                     (if Archi.ptr64 then
                        (sem_add_ptr_long
                           int_or_ptr_type
                           (offset_val (-8) (vertex_address g'' (to, index)))
                           (Vlong
                              (Int64.repr
                                 (1 + Zlength (raw_fields (vlabel g' (to, index)))))))
                      else
                        (sem_add_ptr_int
                           int_or_ptr_type Unsigned
                           (offset_val (-4)
                                       (vertex_address g'' (to, index)))
                           (vint (1 + Zlength
                                        (raw_fields (vlabel g' (to, index)))))))
                   = offset_val (- WORD_SIZE)
                                (vertex_address g''
                                                (to, (to_index + (n + 1))%nat))). {
             cbv [Archi.ptr64].
             first [rewrite sem_add_pi_ptr_special' |
                    rewrite sem_add_pl_ptr_special']; try easy.
             - assert (Zlength (raw_fields (vlabel g' (to, index))) =
                       Zlength (raw_fields (vlabel g'' (to, index)))). {
                 destruct H30 as [[? ?] | [? ?]]. 1: subst g''; reflexivity.
                 erewrite svfl_raw_fields; eauto. } rewrite H33.
               simpl. replace (to_index + (n + 1))%nat with (S index) by lia.
               unfold vertex_address. rewrite !offset_offset_val.
               unfold vertex_offset. simpl vgeneration. simpl vindex. f_equal.
               rewrite pvs_S. unfold vertex_size. unfold WORD_SIZE. lia.
             - rewrite isptr_offset_val. assumption. }
           cbv [Archi.ptr64] in H33. rewrite H33. clear H33.
           assert (closure_has_index g'' to (to_index + (n + 1))). {
             replace (to_index + (n + 1))%nat with (index + 1)%nat by lia.
             cut (gen_has_index g'' to index). 1: red; intros; red in H33; lia.
             destruct H30 as [[? ?] | [? ?]].
             - subst g''. destruct H23. assumption.
             - eapply svfl_graph_has_v in H33; eauto. destruct H33. assumption. }
           Exists (n + 1)%nat g'' h''. destruct H27 as [? [? [? ?]]]. entailer!.
           clear H37 H38 H39 H40. replace (n + 1)%nat with (S n) by lia.
           rewrite nat_seq_S, Nat.add_comm. destruct H30 as [[? ?] | [? ?]].
           ++ subst g''. split; [| apply svwl_add_tail_no_scan]; easy.
           ++ split; [|apply svwl_add_tail_scan with g']; easy.
  - Intros g' h'. Exists g' h'. entailer!.
Qed.
