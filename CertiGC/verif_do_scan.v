Require Import VST.veric.rmaps.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import Coq.Program.Basics.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.CertiGC.GCGraph.
Require Import VST.msl.wand_frame.
Require Import CertiGraph.CertiGC.env_graph_gc.
Require Import CertiGraph.CertiGC.spatial_gcgraph.
Require Import CertiGraph.msl_ext.iter_sepcon.
Require Import CertiGraph.CertiGC.gc_spec.
Require Import CertiGraph.msl_ext.ramification_lemmas.

Local Opaque Int64.repr.

Local Open Scope logic.

Lemma weak_derives_elim: forall P Q : mpred,
  (weak_derives P Q && emp) * P |-- Q.
Proof.
  intros P Q.
  unfold weak_derives.
  unseal_derives.
  intros a H.
  destruct H as [x [z [J [[Hweak Hemp] HP]]]].
  destruct Hemp as [e [Hid Hext]].
  destruct (predicates_sl.join_ext_commut Hext J) as [a0 [J0 Hexta]].
  apply Hid in J0. subst a0.
  pose proof (predicates_hered.pred_upclosed P _ _ Hexta HP) as HPa.
  simpl in Hweak.
  destruct (age_sepalg.join_level _ _ _ J) as [Hlx _].
  eapply (Hweak a); [rewrite Hlx; lia | apply ageable.necR_refl |
                      apply predicates_hered.ext_refl | exact HPa].
Qed.

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
  - red. pose proof raw_tag_range (vlabel g (to, index)). rep_lia.
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
  - red. pose proof raw_tag_range (vlabel g (to, index)). rep_lia.
  - red. rep_lia.
Qed.

Lemma body_do_scan: semax_body Vprog Gprog f_do_scan do_scan_spec.
Proof.
  start_function.
  rename SH into SHr. rename SH0 into SHw. rename H into Hghc. rename H0 into Hoc.
  rename H1 into Hfc. rename H2 into Hft. rename H3 into Hchi. rename H4 into Hunmk.
  forward.
  forward_loop (EX n: nat, EX g': LGraph, EX h': part_heap,
                PROP (graph_heap_compatible g' h';
                      outlier_compatible g' outlier;
                      forward_condition g' h' from to;
                      heap_relation h h';
                      closure_has_index g' to (to_index + n);
                      scan_vertex_while_loop from to (seq to_index n) g g')
                LOCAL
                (temp _s (offset_val (- WORD_SIZE)
                                     (vertex_address g' (to, (to_index + n)%nat)));
                 temp _from_start (gen_start g' from);
                 temp _from_limit (limit_address g' h' from);
                 temp _next (heap_next_address hp to))
                SEP (all_string_constants rsh gv;
                     outlier_rep outlier;
                     graph_rep g';
                     heap_rep sh h' hp;
                     if zlt 0 (available_size h' to) then emp
                     else weak_derives P (weak_valid_pointer (gen_start g' to) * TT) && emp;
                     P))
  break: (EX g' : LGraph, EX h': part_heap,
          PROP (graph_heap_compatible g' h';
                outlier_compatible g' outlier;
                forward_condition g' h' from to;
                do_scan_relation from to to_index g g';
                heap_relation h h')
          LOCAL ()
          SEP (all_string_constants rsh gv;
               outlier_rep outlier;
               graph_rep g';
               heap_rep sh h' hp;
               if zlt 0 (available_size h' to) then emp
               else weak_derives P (weak_valid_pointer (gen_start g' to) * TT) && emp;
               P)).
  - Exists O g h. rewrite Nat.add_0_r. entailer !!. constructor.
  - Intros n g' h'. rename H into Hghc'. rename H0 into Hoc'. rename H1 into Hfc'.
    rename H2 into Hhr. rename H3 into Hchi'. rename H4 into Hsvwl.
    remember (to_index + n)%nat as index. unfold heap_next_address, heap_rep. Intros.
    unfold heap_struct_rep. destruct Hfc' as [Hesto [Hfrom [Hto [Hcp Hnodg]]]].
    pose proof gen_range _ _ _ Hghc' Hto as Htrange.
    destruct (gt_gs_compatible _ _ Hghc' _ Hto) as [Has [Hgen Hpre]].
    rewrite nth_space_Znth in *. remember (Znth (Z.of_nat to) (spaces h')) as sp_to.
    assert (isptr (space_start sp_to)) by (rewrite <- Has; apply start_isptr).
    remember (map space_quad (spaces h')) as l.
    assert (Hst: @Znth (val * (val * (val*val))) (Vundef, (Vundef, (Vundef, Vundef)))
                   (Z.of_nat to) l = space_quad sp_to). {
      subst l sp_to. now rewrite Znth_map by (rewrite spaces_size; rep_lia). }
    forward; rewrite Hst; unfold space_quad. 1: entailer !!.
    unfold vertex_address, vertex_offset. rewrite offset_offset_val.
    simpl vgeneration; simpl vindex.
    replace (WORD_SIZE * (previous_vertices_size g' to index + 1) + - WORD_SIZE) with
        (WORD_SIZE * (previous_vertices_size g' to index))%Z by rep_lia.
    unfold gen_start at 1. rewrite if_true by assumption. rewrite Has.
    remember (WORD_SIZE * used_space sp_to)%Z as used_offset.
    remember (WORD_SIZE * previous_vertices_size g' to index)%Z as index_offset.
    freeze [0; 1; 3] FR. gather_SEP (graph_rep g') (heap_unused_rep h').
    assert (Hspto: space_start sp_to = gen_start g' to) by
      (unfold gen_start; rewrite if_true by assumption; rewrite <- Has; reflexivity).
    assert (
        forall b i,
          Vptr b i = space_start sp_to ->
          graph_rep g' * heap_unused_rep h' |--
      !! (WORD_SIZE * available_space sp_to + Ptrofs.unsigned i <= Ptrofs.max_unsigned)) as Hf. {
      intros b i Hf. sep_apply (graph_and_heap_rest_data_at_ _ _ _ Hto Hghc').
      rewrite Hspto in Hf. sep_apply (generation_data_at__ptrofs g' h' to b i Hf).
      unfold available_size; rewrite nth_space_Znth; entailer !!. }
    assert_PROP (force_val
                   (sem_cmp_pp Clt (offset_val index_offset (space_start sp_to))
                      (offset_val used_offset (space_start sp_to))) =
                   Vint (if if zlt index_offset used_offset then true else false
                         then Int.one else Int.zero)) as Hforce. {
      remember (space_start sp_to) as v. destruct v; try contradiction. inv_int i.
      specialize (Hf b (Ptrofs.repr ofs) eq_refl).
      rewrite Ptrofs.unsigned_repr in Hf by rep_lia. sep_apply Hf. Intros.
      assert (Hrg1: 0 <= ofs + used_offset <= Ptrofs.max_unsigned). {
        subst. pose proof used_leq_available (Znth (Z.of_nat to) (spaces h')).
        unfold WORD_SIZE in *. rep_lia. }
      assert (Hrg2: 0 <= ofs + index_offset <= Ptrofs.max_unsigned). {
        subst. red in Hchi'. pose proof pvs_ge_zero g' to (to_index + n)%nat.
        pose proof pvs_mono g' to _ _ Hchi'. unfold WORD_SIZE in *. rep_lia. }
      apply prop_right. rewrite force_sem_cmp_pp; [|rewrite isptr_offset_val; assumption..].
      simpl. rewrite !ptrofs_add_repr, if_true by reflexivity. unfold Ptrofs.ltu.
      rewrite !Ptrofs.unsigned_repr; auto. f_equal. if_tac; if_tac; try reflexivity; lia. }
    forward_if (gen_has_index g' to index).
    + remember (Znth (Z.of_nat to) (spaces h')) as sp_to.
      sep_apply (graph_and_heap_rest_data_at_ _ _ _ Hto Hghc').
      unfold generation_data_at_. rewrite <- Hspto.
      rewrite data_at__memory_block. Intros. rewrite sizeof_tarray_int_or_ptr.
      2: unfold available_size; apply available_space_range.
      remember (WORD_SIZE * used_space sp_to)%Z as used_offset.
      remember (to_index + n)%nat as index.
      remember (WORD_SIZE * previous_vertices_size g' to index)%Z as index_offset.
      destruct (space_start sp_to); try contradiction. simpl. unfold test_order_ptrs.
      simpl. case (peq b b); intros. 2: contradiction. simpl.
      assert (Hnoid: sepalg.nonidentity (nth_sh g' to)). {
        apply readable_nonidentity, writable_readable_share. unfold nth_sh.
        apply generation_share_writable. }
      assert (Hoffmem: forall offset,
                 0 <= offset <= used_offset ->
                 memory_block (nth_sh g' to) (WORD_SIZE * available_size h' to)
                   (Vptr b i) * TT *
                   (FRZL FR *
                    ((if zlt 0 (available_size h' to) then emp
                      else weak_derives P (weak_valid_pointer (Vptr b i) * TT) && emp) *
                     P)) |--
        weak_valid_pointer (Vptr b (Ptrofs.add i (Ptrofs.repr offset)))). {
        intros offset Hofsrg.
        destruct (Z_lt_dec 0 (WORD_SIZE * available_size h' to)) as [Hpos | Hnpos].
        - change (Vptr b (Ptrofs.add i (Ptrofs.repr offset))) with
              (offset_val offset (Vptr b i)).
          sep_apply (memory_block_weak_valid_pointer
                       (nth_sh g' to) (WORD_SIZE * available_size h' to)
                       (Vptr b i) offset); auto.
          subst. unfold available_size. split. 1: apply (proj1 Hofsrg).
          transitivity (WORD_SIZE * used_space (nth_space h' to))%Z.
          + rewrite nth_space_Znth. apply (proj2 Hofsrg).
          + apply Zmult_le_compat_l. apply (proj2 (used_leq_available _)).
            unfold WORD_SIZE. lia.
          + apply extend_weak_valid_pointer.
        - assert (Hav0: (WORD_SIZE * available_size h' to = 0)%Z). {
            pose proof available_space_range (nth_space h' to).
            unfold available_size in *. unfold WORD_SIZE in *. lia. }
          assert (Hused0: used_offset = 0). {
            subst used_offset sp_to. unfold available_size in Hav0.
            rewrite nth_space_Znth in Hav0.
            pose proof used_leq_available (Znth (Z.of_nat to) (spaces h')).
            unfold WORD_SIZE in *. lia. }
          assert (offset = 0) by lia. subst offset.
          rewrite Ptrofs.add_zero. destruct (zlt 0 (available_size h' to));
            [unfold available_size in *; unfold WORD_SIZE in *; lia |].
          sep_apply (weak_derives_elim P (weak_valid_pointer (Vptr b i) * TT)).
          eapply derives_trans.
          2: apply (extend_weak_valid_pointer (Vptr b i)
                      (TT * (memory_block (nth_sh g' to)
                               (WORD_SIZE * available_size h' to) (Vptr b i) *
                             (TT * FRZL FR)))).
          rewrite sepcon_assoc. apply derives_refl. }
      apply andp_right; apply Hoffmem.
      * subst. split.
        1: pose proof pvs_ge_zero g' to (to_index + n)%nat; unfold WORD_SIZE; lia.
        apply Zmult_le_compat_l. 2: unfold WORD_SIZE; lia. rewrite <- Hpre.
        apply pvs_mono. assumption.
      * split; [|lia]; subst; apply Z.mul_nonneg_nonneg;
          [unfold WORD_SIZE; lia | apply used_leq_available].
    + assert (Hidl: index_offset < used_offset). {
        destruct (zlt index_offset used_offset); trivial.
        match type of Hforce with force_val ?A = _ =>
                                    destruct A; inv Hforce end.
        simpl in H1; subst. inversion H0. }
      forward. entailer !!. red. rewrite <- Hpre in Hidl.
      rewrite <- Z.mul_lt_mono_pos_l in Hidl by (unfold WORD_SIZE; lia).
      apply pvs_lt_rev in Hidl. assumption.
    + assert (Hidl: ~ index_offset < used_offset). {
        destruct (zlt index_offset used_offset); trivial.
        match type of Hforce with force_val ?A = _ =>
                                    destruct A; inv Hforce end.
        simpl in H1; subst. inversion H0. }
      forward. thaw FR. unfold thread_info_rep, heap_rep, heap_struct_rep.
      Exists g' h'. unfold forward_condition. entailer !!. exists n. split; trivial.
      unfold gen_has_index. rewrite <- Hpre in Hidl.
      rewrite <- Z.mul_lt_mono_pos_l in Hidl by (unfold WORD_SIZE; lia).
      intro; apply Hidl. now apply pvs_mono_strict.
    + clear Hchi' Hf Hforce. Intros. rename H0 into Hghi. thaw FR. freeze [1;2;3;4;5] FR.
      assert (Hhv: graph_has_v g' (to, index)) by easy.
      freeze [0;2] FR2.
      localize [vertex_rep (nth_sh g' to) g' (to, index)].
      assert (Hrt: readable_share (nth_sh g' to)) by
          (unfold nth_sh; apply writable_readable_share, generation_share_writable).
      unfold vertex_rep, vertex_at. Intros.
      assert (Hofs: offset_val (- WORD_SIZE) (vertex_address g' (to, index)) =
                      offset_val index_offset (space_start sp_to)). {
        unfold vertex_address. rewrite offset_offset_val. unfold vertex_offset.
        simpl vgeneration. simpl vindex.
        replace (WORD_SIZE * (previous_vertices_size g' to index + 1) + - WORD_SIZE)
          with index_offset by rep_lia. f_equal. unfold gen_start.
        rewrite if_true by assumption. now rewrite Has. }
      rewrite Hofs. forward. rewrite <- Hofs.
      gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
      replace_SEP 0 (vertex_rep (nth_sh g' to) g' (to, index)) by
          (unfold vertex_rep, vertex_at; entailer !!).
      unlocalize [graph_rep g']. 1: apply graph_vertex_ramif_stable; assumption.
      thaw FR2.
      forward. forward. assert (Hgu: gen_unmarked g' to). {
        eapply (svwl_gen_unmarked from to _ g); eauto.
        destruct Hfc as [_ [_ [? _]]]. assumption. } specialize (Hgu Hto _ Hghi).
      rewrite make_header_Wosize, make_header_tag by assumption.
      fold (heap_next_address hp to). thaw FR. fold (heap_struct_rep sh l hp).
      gather_SEP (heap_struct_rep _ _ _ ) (heap_unused_rep _).
      replace_SEP 0 (heap_rep sh h' hp) by (unfold thread_info_rep, heap_rep; entailer !!).
      forward_if
        (EX g'': LGraph, EX h'': part_heap,
         PROP (graph_heap_compatible g'' h'';
               outlier_compatible g'' outlier;
               forward_condition g'' h'' from to;
               heap_relation h h'';
               (no_scan g' (to, index) /\ g'' = g') \/
               (~ no_scan g' (to, index) /\
                scan_vertex_for_loop
                  from to (to, index)
                  (nat_inc_list (length (vlabel g' (to, index)).(raw_fields))) g' g''))
         LOCAL (temp _tag (Vint (Int.repr (raw_tag (vlabel g' (to, index)))));
                temp _sz
                     (if Archi.ptr64 then
                        Vlong (Int64.repr
                                 (Zlength (raw_fields (vlabel g' (to, index)))))
                      else (Vint (Int.repr (Zlength (raw_fields (vlabel g' (to, index)))))));
                temp _s (offset_val (- WORD_SIZE) (vertex_address g'' (to, index)));
                temp _from_start (gen_start g'' from);
                temp _from_limit (limit_address g'' h'' from);
                temp _next (heap_next_address hp to))
         SEP (heap_rep sh h'' hp;
              graph_rep g'';
              all_string_constants rsh gv;
              outlier_rep outlier;
              if zlt 0 (available_size h'' to) then emp
              else weak_derives P (weak_valid_pointer (gen_start g'' to) * TT) && emp;
              P)).
      * rewrite Int64.unsigned_repr in H0;
          [| pose proof raw_tag_range (vlabel g' (to, index)); rep_lia].
        pose proof typed_true_tag to g' index as Hxx.
        destruct (negb (Int.lt (Int.repr (raw_tag (vlabel g' (to, index)))) (Int.repr 251)));
          [discriminate |]. clear H0. specialize (Hxx (eq_refl _)).
        remember (Zlength (raw_fields (vlabel g' (to, index)))) as z.
        assert (Hzr: 1 <= z < (if Archi.ptr64 then Int64.max_signed else Int.max_signed)). {
          subst z. pose proof raw_fields_range (vlabel g' (to, index)).
          split; [lia|]. transitivity (two_p (WORD_SIZE * 8 - 10));
                           [lia | vm_compute; reflexivity]. }
        forward_loop
          (EX i: Z, EX g3: LGraph, EX h3: part_heap,
           PROP (scan_vertex_for_loop
                   from to (to, index)
                   (sublist 0 (i - 1)
                            (nat_inc_list
                               (length (vlabel g' (to, index)).(raw_fields)))) g' g3;
                 graph_heap_compatible g3 h3;
                 outlier_compatible g3 outlier;
                 forward_condition g3 h3 from to;
                 heap_relation h h3;
                1 <= i <= z + 1)
           LOCAL (temp _tag (Vint (Int.repr (raw_tag (vlabel g' (to, index)))));
                  temp _j (if Archi.ptr64 then (Vlong (Int64.repr i)) else Vint (Int.repr i));
                  temp _sz (if Archi.ptr64 then (Vlong (Int64.repr z)) else Vint (Int.repr z));
                  temp _s (offset_val (- WORD_SIZE) (vertex_address g3 (to, index)));
                  temp _from_start (gen_start g3 from);
                  temp _from_limit (limit_address g3 h3 from);
                  temp _next (heap_next_address hp to))
           SEP (all_string_constants rsh gv;
                outlier_rep outlier;
                graph_rep g3;
                heap_rep sh h3 hp;
                if zlt 0 (available_size h3 to) then emp
                else weak_derives P (weak_valid_pointer (gen_start g3 to) * TT) && emp;
                P))
          continue: (EX i: Z, EX g3: LGraph, EX h3: part_heap,
           PROP (scan_vertex_for_loop
                   from to (to, index)
                   (sublist 0 i
                            (nat_inc_list
                               (length (vlabel g' (to, index)).(raw_fields)))) g' g3;
                 graph_heap_compatible g3 h3;
                 outlier_compatible g3 outlier;
                 forward_condition g3 h3 from to;
                 heap_relation h h3;
                 1 <= i + 1 <= z + 1)
           LOCAL (temp _tag (Vint (Int.repr  (raw_tag (vlabel g' (to, index)))));
                  temp _j (if Archi.ptr64 then (Vlong (Int64.repr i)) else Vint (Int.repr i));
                  temp _sz (if Archi.ptr64 then (Vlong (Int64.repr z)) else Vint (Int.repr z));
                  temp _s (offset_val (- WORD_SIZE) (vertex_address g3 (to, index)));
                  temp _from_start (gen_start g3 from);
                  temp _from_limit (limit_address g3 h3 from);
                  temp _next (heap_next_address hp to))
           SEP (all_string_constants rsh gv;
                outlier_rep outlier;
                graph_rep g3;
                heap_rep sh h3 hp;
                if zlt 0 (available_size h3 to) then emp
                else weak_derives P (weak_valid_pointer (gen_start g3 to) * TT) && emp;
                P)).
        -- forward. Exists 1 g' h'. replace (1 - 1) with 0 by lia.
           autorewrite with sublist. unfold forward_condition. entailer!!.
           try (rewrite Int64.unsigned_repr;
                [| pose proof raw_tag_range (vlabel g' (to, (to_index + n)%nat));
                   rep_lia]). split; [apply svfl_nil | reflexivity].
        -- Intros i g3 h3. rename H0 into Hsvfl. rename H1 into Hghc3. rename H2 into Hoc3.
           rename H3 into Hfc3. rename H4 into Hhr3. rename H5 into Hir.
           forward_if (i <= z).
           ++ forward. entailer!!.
              first [rewrite !Int.unsigned_repr in H0 |
                      apply ltu64_repr_false in H0]; try lia.
              ** clear -Hzr Hir. simpl in Hzr. split. 1: lia.
                 transitivity (Zlength (raw_fields (vlabel g' (to, (to_index + n)%nat))) + 1);
                   rep_lia.
              ** clear -Hzr. simpl in Hzr. rep_lia.
           ++ forward. assert (i = z + 1). {
                try unfold Int64.ltu in H0.
                first [rewrite !Int.unsigned_repr in H0|rewrite !Int64.unsigned_repr in H0].
                - try (if_tac in H0; [|inversion H0]). lia.
                - simpl in Hzr. clear -Hzr Hir. rep_lia.
                - simpl in Hzr. clear -Hzr. rep_lia. } subst i. clear H0 Hir.
              replace (z + 1 - 1) with z in Hsvfl by lia.
              remember (raw_fields (vlabel g' (to, index))) as r.
              replace (sublist 0 z (nat_inc_list (length r))) with
                  (nat_inc_list (Datatypes.length r)) in Hsvfl.
              ** Exists g3 h3. entailer !!.
              ** rewrite sublist_same; trivial. subst z.
                 rewrite !Zlength_correct, nat_inc_list_length. reflexivity.
           ++ Intros. rename H0 into Hiz.
              change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 3%N |})
                with int_or_ptr_type.
              assert (Hipr3: isptr (vertex_address g3 (to, index))). {
                erewrite <- svfl_vertex_address; eauto. rewrite <- Has in H.
                2: apply graph_has_v_in_closure; assumption. clear -H Hto.
                unfold vertex_address. unfold gen_start. simpl.
                rewrite if_true by assumption. rewrite isptr_offset_val. assumption. }
              assert (Hghg: graph_has_gen g3 to) by
                  (eapply svfl_graph_has_gen in Hsvfl; [rewrite <- Hsvfl|]; assumption).
              assert (Hhv3: graph_has_v g3 (to, index)) by
                  (eapply svfl_graph_has_v in Hsvfl; [apply Hsvfl| assumption..]).
              forward_call (rsh, sh, gv, g3, h3, hp, outlier, from, to, 0,
                             FwdPntIntr (InteriorVertexPos (to, index) (i - 1)), @None val).
              ** simpl snd. apply prop_right. simpl.
                 do 4 f_equal.
                 first [rewrite sem_add_pi_ptr_special' |
                        rewrite sem_add_pl_ptr_special]; try easy;
                   [|rewrite isptr_offset_val; assumption].
                 simpl. rewrite offset_offset_val. f_equal. unfold WORD_SIZE; lia.
              ** simpl forward_p_rep. entailer !!.
              ** repeat (split; try assumption); try lia; auto.
                 --- eapply svfl_raw_fields in Hsvfl; [rewrite <- Hsvfl; lia | assumption..].
                 --- rewrite <- Hgu; symmetry; eapply svfl_raw_mark in Hsvfl;
                       [apply Hsvfl | assumption..|]. simpl. lia.
                 --- eapply svfl_raw_tag in Hsvfl; try eassumption; auto.
                     rewrite <- Hsvfl. unfold no_scan in Hxx. lia.
              ** Intros vret. destruct vret as [g4 h4]. simpl fst in *. simpl snd in *.
                 Exists i g4 h4. rename H0 into Hgh. simpl forward_p2forward_t in Hgh.
                 pose proof fr_forward_graph_and_heap from to O
                   (field2forward (Znth (i - 1) (make_fields g3 (to, index)))) g3 h3 as Hfr.
                 simpl Z.to_nat in Hgh. rewrite <- Hgh in Hfr. simpl fst in Hfr.
                 pose proof heaprel_forward_graph_and_heap from to O
                   (field2forward (Znth (i - 1) (make_fields g3 (to, index)))) g3 h3 as Hhr4.
                 rewrite <- Hgh in Hhr4. simpl snd in Hhr4.
                 assert (Hgsf: gen_start g3 from = gen_start g4 from) by
                   (eapply fr_gen_start; eassumption).
                 assert (Hgst: gen_start g3 to = gen_start g4 to) by
                   (eapply fr_gen_start; eassumption).
                 assert (Hla: limit_address g3 h3 from = limit_address g4 h4 from). {
                   unfold limit_address. rewrite Hgsf. do 2 f_equal. apply (proj1 Hhr4). }
                 simpl forward_p_rep. entailer !!.
                 assert (Hcpt: forward_t_compatible
                                 (field2forward
                                    (Znth (i - 1)
                                       (make_fields g3 (to, (to_index + n)%nat)))) g3). {
                   apply vertex_pos_forward_t_compatible; auto.
                   erewrite <- svfl_raw_fields with (g := g'); eauto. lia. }
                 split; [|split; [|split; [|split; [|split]]]].
                 --- remember (nat_inc_list
                                 (length (raw_fields (vlabel g' (to, (to_index + n)%nat))))).
                     assert (Hi: i <= Zlength l). {
                       subst l. rewrite Zlength_correct, nat_inc_list_length.
                       rewrite Zlength_correct in Hiz. lia. }
                     rewrite (sublist_split 0 (i - 1) i) by lia.
                     rewrite (sublist_one (i - 1) i) by lia.
                     apply svfl_add_tail with g3; trivial.
                     assert (Him: Z.of_nat (Znth (i - 1) l) = i - 1). {
                       rewrite <- nth_Znth by lia. subst l.
                       rewrite nat_inc_list_nth; [rewrite Z2Nat.id; lia|].
                       rewrite <- ZtoNat_Zlength. rewrite Zlength_correct in Hi.
                       rewrite nat_inc_list_length in Hi. rewrite Nat2Z.inj_lt.
                       rewrite !Z2Nat.id; lia. } rewrite Him. assumption.
                 --- destruct Hfc3 as [? [? [? [? ?]]]].
                     eapply forward_graph_and_heap_ghc with (g := g3); eassumption.
                 --- destruct Hfc3 as [? [? [? [? ?]]]].
                     eapply fr_outlier_compatible with (g1 := g3); eassumption.
                 --- eapply forward_graph_and_heap_fc; eassumption.
                 --- apply hr_trans with h3; assumption.
                 --- f_equal. symmetry. eapply fr_vertex_address; eauto.
                     apply graph_has_v_in_closure; assumption.
                 --- rewrite Hgst. rewrite <- (proj1 Hhr4 to). apply derives_refl.
        -- Intros i g3 h3. cbv [Archi.ptr64]. forward.
           ++ entailer !!. simpl in Hzr.
              first [rewrite !Int.signed_repr | rewrite Int64.signed_repr]; rep_lia.
           ++ Exists (i + 1) g3 h3. replace (i + 1 - 1) with i by lia. entailer !!.
      * rename H0 into Hneq; rewrite Int64.unsigned_repr in Hneq;
          [|pose proof raw_tag_range (vlabel g' (to, index)); rep_lia].
        pose proof typed_false_tag to g' index as Hxx.
        destruct (negb (Int.lt (Int.repr (raw_tag (vlabel g' (to, index)))) (Int.repr 251))).
        2: simpl in Hneq; contradiction Hneq; reflexivity. clear Hneq.
        specialize (Hxx (eq_refl _)). forward. Exists g' h'. unfold forward_condition.
        entailer !!.
        try (rewrite Int64.unsigned_repr;
             [|pose proof raw_tag_range (vlabel g' (to, (to_index + n)%nat));rep_lia]). easy.
      * Intros g'' h''. rename H0 into Hghc''. rename H1 into Hoc''. rename H2 into Hfc''.
        rename H3 into Hhr''. rename H4 into Hscan.
        assert (Hti: isptr (vertex_address g'' (to, index))). {
          assert (isptr (vertex_address g' (to, index))). {
            unfold vertex_address. rewrite isptr_offset_val. unfold gen_start.
            rewrite <- Has in H. rewrite if_true; assumption. }
          destruct Hscan as [[? ?] | [? Hsvfl]]. 1: subst g''; assumption.
          eapply svfl_vertex_address in Hsvfl;
            [rewrite <- Hsvfl | | apply graph_has_v_in_closure]; assumption. }
        pose proof raw_fields_range (vlabel g' (to, index)) as Hrr. forward.
        change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 3%N |})
          with int_or_ptr_type. cbv [Archi.ptr64]. simpl sem_binary_operation'.
        first [rewrite add_repr | rewrite add64_repr].
        try (rewrite Int.signed_repr; [|rep_lia]).
        assert (Hsdp: force_val
                        (if Archi.ptr64 then
                           (sem_add_ptr_long
                              int_or_ptr_type
                              (offset_val (-8) (vertex_address g'' (to, index)))
                              (Vlong (Int64.repr
                                        (1 + Zlength (raw_fields (vlabel g' (to, index)))))))
                         else
                           (sem_add_ptr_int
                              int_or_ptr_type Unsigned
                              (offset_val (-4) (vertex_address g'' (to, index)))
                              (Vint (Int.repr
                                       (1 + Zlength
                                              (raw_fields (vlabel g' (to, index))))))))
                      = offset_val (- WORD_SIZE)
                          (vertex_address g'' (to, (to_index + (n + 1))%nat))). {
             cbv [Archi.ptr64].
             first [rewrite sem_add_pi_ptr_special' | rewrite sem_add_pl_ptr_special'];
               try easy.
             - assert (Hlr: Zlength (raw_fields (vlabel g' (to, index))) =
                              Zlength (raw_fields (vlabel g'' (to, index)))). {
                 destruct Hscan as [[? ?] | [? ?]]. 1: subst g''; reflexivity.
                 erewrite svfl_raw_fields; eauto. } rewrite Hlr.
               simpl. replace (to_index + (n + 1))%nat with (S index) by lia.
               unfold vertex_address. rewrite !offset_offset_val.
               unfold vertex_offset. simpl vgeneration. simpl vindex. f_equal.
               rewrite pvs_S. unfold vertex_size. unfold WORD_SIZE. lia.
             - rewrite isptr_offset_val. assumption. }
        cbv [Archi.ptr64] in Hsdp. rewrite Hsdp. clear Hsdp.
        assert (Hchi': closure_has_index g'' to (to_index + (n + 1))). {
          replace (to_index + (n + 1))%nat with (index + 1)%nat by lia.
          cut (gen_has_index g'' to index). 1: red; intro Hchi'; red in Hchi'; lia.
          destruct Hscan as [[? ?] | [? Hsvfl]].
          - subst g''. destruct Hhv. assumption.
          - eapply svfl_graph_has_v in Hsvfl; eauto. destruct Hsvfl. assumption. }
        Exists (n + 1)%nat g'' h''. entailer !!. replace (n + 1)%nat with (S n) by lia.
        rewrite seq_S. destruct Hscan as [[? ?] | [? ?]].
        -- subst g''. apply svwl_add_tail_no_scan; assumption.
        -- apply svwl_add_tail_scan with g'; assumption.
  - Intros g' h'. Exists g' h'. entailer !!.
Qed.
