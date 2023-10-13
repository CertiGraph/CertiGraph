Require Import CertiGraph.CertiGC.gc_spec.

Local Open Scope logic.

Lemma body_do_generation: semax_body Vprog Gprog f_do_generation do_generation_spec.
Proof.
  start_function.
  pose proof H. pose proof H0. destruct H2 as [? _]. destruct H3 as [? [? [? _]]].
  assert (generation_space_compatible
            g (from, nth_gen g from, nth_space h from)) by
      (apply gt_gs_compatible; assumption). destruct H6 as [? [? ?]].
  assert (generation_space_compatible g (to, nth_gen g to, nth_space h to)) by
      (apply gt_gs_compatible; assumption). destruct H9 as [? [? ?]].
  assert (isptr (space_start (nth_space h from))) by
      (rewrite <- H6; apply start_isptr).
  assert (isptr (space_start (nth_space h to))) by
      (rewrite <- H9; apply start_isptr).
  assert (HS: forall gen, graph_has_gen g gen -> Z.of_nat gen < MAX_SPACES). {
    intros. unfold graph_has_gen in H14. destruct H as [[_ [_ ?]] _].
    rewrite <- (spaces_size h). rewrite Zlength_correct.
    apply inj_lt. apply Nat.lt_le_trans with
                      (Datatypes.length (g_gen (glabel g))); assumption. }
  assert (Z.of_nat from < MAX_SPACES) by (apply HS; assumption).
  assert (Z.of_nat to < MAX_SPACES) by (apply HS; assumption). clear HS.
  freeze [0;1;2;3] FR.
  localize [space_struct_rep sh hp h from; 
            space_struct_rep sh hp h to].
  unfold space_struct_rep. unfold space_tri.
  forward.
  gather_SEP
    (data_at sh space_type
             _ (space_address hp from))
    (data_at sh space_type
             _ (space_address hp to)).
  replace_SEP 0 (space_struct_rep sh hp h from 
                  * space_struct_rep sh hp h to) by
    (unfold space_struct_rep; entailer!).
  unlocalize [heap_rep sh h hp].
  1: apply heap_rep_ramif_stable;  assumption.
  assert_PROP (isptr (space_address hp to)). {
    unfold thread_info_rep, heap_rep. unfold heap_struct_rep.
    unfold space_address. Intros.
    entailer!.
  }
  forward_call. clear H16. 
    localize [space_struct_rep sh hp h from].
    unfold space_struct_rep, space_tri. 
    forward.
    forward.
    replace_SEP 0 (space_struct_rep sh hp h from) by
        (unfold space_struct_rep, space_tri; entailer!).
    unlocalize [heap_rep sh h hp].
    1: apply heap_rep_ramif_stable_1; assumption. apply dgc_imply_fc in H0.
    remember (space_start (nth_space h from)) as from_p.
    remember (space_start (nth_space h to)) as to_p.
    remember (WORD_SIZE * used_space (nth_space h to))%Z as to_used.
    remember (WORD_SIZE * total_space (nth_space h to))%Z as to_total.
    remember (WORD_SIZE * used_space (nth_space h from))%Z as from_used.
    destruct H0 as [? [? ?]]. 
    replace from_p with (gen_start g from) by
        (subst; unfold gen_start; rewrite if_true; assumption).
    replace (offset_val (WORD_SIZE * total_space (nth_space h from))
                        (gen_start g from)) with (limit_address g h from) by
        (unfold limit_address, gen_size; reflexivity).
    assert_PROP (isptr (space_address hp to)). {
      unfold space_address. rewrite isptr_offset_val. unfold thread_info_rep, heap_rep.
      Intros. unfold heap_struct_rep. entailer!. }
    assert_PROP (offset_val WORD_SIZE (space_address hp to) =
                 heap_next_address hp to). {
      unfold heap_rep. unfold heap_struct_rep. Intros. entailer!.
      unfold space_address, heap_next_address, field_address. rewrite if_true.
      - simpl. rewrite offset_offset_val. f_equal.
      - destruct H as [[_ [_ ?]] _]. unfold field_compatible in *.
        simpl in *. unfold in_members. simpl. intuition auto with *. } thaw FR.
    forward_call (rsh, sh, gv, g, h, hp, fr, roots, outlier, from, to).
    Intros vret. destruct vret as [[g1 h1] roots1]. simpl fst in *. simpl snd in *.
    freeze [0;1;2;3] FR.
    set (fr1 := update_frames fr (map (root2val g1) roots1))  in *.
    assert (space_start (nth_space h1 from) = gen_start g1 from). {
      destruct H20 as [? _]. destruct H22 as [_ [? _]]. 
      destruct (gt_gs_compatible _ _ H20 _ H22) as [H24 _]. simpl in H24. rewrite <- H24.
      unfold gen_start. rewrite if_true by assumption. reflexivity. }
    assert (isptr (space_start (nth_space h1 from))). {
      rewrite H24. unfold gen_start. destruct H22 as [_ [? _]].
      rewrite if_true by assumption. apply start_isptr. }
    localize [space_struct_rep sh hp h1 from].
    unfold space_struct_rep, space_tri. 
    do 2 forward.
    replace_SEP 0 (space_struct_rep sh hp h1 from) by
        (unfold space_struct_rep, space_tri; entailer!).
    unlocalize [heap_rep sh h1 hp].
    1: apply heap_rep_ramif_stable_1; assumption. thaw FR. rewrite H24.
    replace (offset_val (WORD_SIZE * total_space (nth_space h1 from))
                        (gen_start g1 from)) with (limit_address g1 h1 from) by
        (unfold limit_address, gen_size; reflexivity).
    pose proof I.
    assert (closure_has_v g (to, number_of_vertices (nth_gen g to))) by
        (red; simpl; unfold closure_has_index; split; [assumption | lia]).
    replace (offset_val to_used to_p) with
        (offset_val (- WORD_SIZE)
                    (vertex_address g1 (to, number_of_vertices (nth_gen g to)))) by
        (rewrite <- (frr_vertex_address _ _ _ _ _ _ H5 H21 _ H27); subst;
         unfold vertex_address, vertex_offset, gen_start; simpl;
         rewrite offset_offset_val, H11, H9, if_true by assumption;
         f_equal; unfold WORD_SIZE; lia). eapply frr_closure_has_v in H27; eauto.
    destruct H27. simpl in H27, H28.
    assert (0 < gen_size h1 to) by (rewrite <- (proj1 H23); assumption).
    assert (gen_unmarked g1 to) by (eapply (frr_gen_unmarked _ _ _ g _ g1); eauto).
    sep_apply frames_rep_localize. Intros.
    forward_call (rsh, sh, gv, g1, h1, hp, frames2rootpairs fr1, roots1, outlier,
                  from, to, number_of_vertices (nth_gen g to)).
    Intros vret.
    destruct vret as [g2 h2]. simpl fst in *. simpl snd in *. 
    sep_apply frames_rep_unlocalize.
    rewrite <- frames2roots_eq,  update_frames_same.
    assert (space_start (nth_space h2 from) = gen_start g2 from). {
      destruct H31 as [? _]. destruct H32 as [_ [? _]].
      destruct (gt_gs_compatible _ _ H31 _ H32) as [? _]. simpl in H35.
      rewrite <- H35.
      unfold gen_start. rewrite if_true by assumption. reflexivity. }
    assert (isptr (space_start (nth_space h2 from))). {
      rewrite H35. unfold gen_start. destruct H32 as [_ [? _]].
      rewrite if_true by assumption. apply start_isptr. } 
    freeze [0;1;2;3] FR. localize [space_struct_rep sh hp h2 from].
    unfold space_struct_rep, space_tri.
    forward.
    replace_SEP 0 (space_struct_rep sh hp h2 from) by
        (unfold space_struct_rep, space_tri; entailer!).
    unlocalize [heap_rep sh h2 hp].
    1: apply heap_rep_ramif_stable_1; assumption. thaw FR.
    unfold thread_info_rep, heap_rep. Intros.
    freeze [1;2;3;5] FR. rewrite heap_struct_rep_eq.
    assert_PROP (space_address hp from =
                 field_address (tarray space_type MAX_SPACES) [ArraySubsc (Z.of_nat from)]
                               hp). {
      entailer!. unfold space_address. unfold field_address. rewrite if_true.
      - simpl. f_equal.
      - unfold field_compatible in *. simpl in *. intuition auto with *. }
    rewrite H37. clear H37. Opaque Znth. forward. Transparent Znth.
    rewrite Znth_map by (rewrite spaces_size; rep_lia).
    rewrite <- nth_space_Znth. unfold space_tri at 2 3.
    simpl fst. simpl snd.
    assert (FROM_MAX: 0 <= Z.of_nat from < Zlength (map space_tri (spaces h2))). {
        rewrite Zlength_map.
        destruct H20 as [[_ [_ ?]] _]; destruct H31 as [[_ [_ H31]] _]. simpl in H31.
        apply frr_graph_has_gen with (gen:=from) in H21; auto.
        rewrite H21 in H4.
        destruct H33 as [n [? _]].
        apply svwl_graph_has_gen with (gen:=from) in H33; auto.
        rewrite H33 in H4.
        clear - H31 H4.
        red in H4. split. lia. rewrite Zlength_correct.
        lia. 
    }
    Opaque fst. Opaque snd.
    forward; rewrite upd_Znth_same by assumption. entailer!.
    forward; rewrite upd_Znth_same by assumption.
    rewrite !upd_Znth_twice by assumption.
    Transparent fst. Transparent snd.
    thaw FR.
    assert (graph_has_gen g2 from) by (destruct H32 as [_ [? _]]; assumption).
    rewrite (graph_rep_reset g2 from) by assumption. Intros.     
    sep_apply (heap_rest_rep_reset g2 h2 from (proj1 H31) H37).
        rewrite <- heap_struct_rep_eq.
    simpl fst. simpl snd.
    gather_SEP 0 4. 
    replace_SEP 0 (heap_rep sh (reset_nth_heap from h2) hp).
    + unfold heap_rep. entailer!.
      assert (from < length (spaces h2))%nat by
          (destruct H31 as [[_ [_ ?]] _]; simpl in H31; red in H37; lia). simpl.
      rewrite (reset_nth_space_Znth _ _ H48), <- nth_space_Znth, <- upd_Znth_map.
      unfold space_tri at 3. simpl. replace (WORD_SIZE * 0)%Z with 0 by lia.
      rewrite isptr_offset_val_zero by assumption. cancel.
    + apply super_compatible_reset with (gen := from) in H31.
      2: { apply (frr_not_pointing from to roots g roots1 g1); auto.
           - clear -H0. destruct H0 as [_ [_ [_ [? _]]]]. assumption.
           - clear -H. destruct H as [_ [_ [[_ ?] _]]]. assumption.
           - apply frr_roots_fi_compatible in H21; auto. 
      }
      remember (reset_nth_heap from h2) as h3.
      remember (reset_graph from g2) as g3.
      assert (do_generation_relation from to roots roots1 g g3) by
          (exists g1, g2; split; [|split]; assumption).
      assert (heap_relation h h3). {
        apply hr_trans with h2.
        - apply hr_trans with h1; try assumption.
        - subst h3. apply heaprel_reset. }      
      Exists g3 h3 roots1.
      destruct H32 as [? [? [? ?]]].
      replace (update_frames fr (map _ _)) with fr1.
      entailer!.
      unfold fr1 in *.
      destruct H31 as [_ [? _]]. red in H31.
      destruct H20 as [_ [? _]]. red in H20.
      f_equal.
      rewrite H31.
      rewrite <- frames2roots_eq.
      symmetry; apply frames2roots_update_frames.
      apply invariants.Zlength_eq.
      destruct H as [_ [? _]]. red in H. rewrite frames2roots_eq.
      rewrite <- H.
      rewrite !Zlength_map.
      apply frr_roots_fi_compatible in H21; auto.
Qed.

