Require Import VST.veric.rmaps.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import Stdlib.Program.Basics.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.CertiGC.GCGraph.
Require Import VST.msl.wand_frame.
Require Import CertiGraph.CertiGC.env_graph_gc.
Require Import CertiGraph.CertiGC.spatial_gcgraph.
Require Import CertiGraph.msl_ext.iter_sepcon.
Require Import CertiGraph.CertiGC.gc_spec.
Require Import CertiGraph.CertiGC.forward_lemmas.
Require Import CertiGraph.msl_ext.ramification_lemmas.

Local Open Scope logic.

Lemma fri_rootpairs_compatible:
  forall from to g h rh rmst item g' h' rh' rmst' rootpairs roots,
    graph_has_gen g to ->
    roots_graph_compatible roots g ->
    rootpairs_compatible g rootpairs roots ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    rootpairs_compatible g' rootpairs roots.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' rootpairs roots Hto Hrgc Hrpc Hfri.
  unfold forward_remset_item in Hfri.
  destruct (negb (remset_item_in_gen item rmst g from)) eqn:Hgen.
  - destruct (forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h)
      as [newg newh] eqn:Hfgh.
    simpl in Hfri. inversion Hfri; subst; clear Hfri.
    pose proof fr_forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h as Hfr.
    rewrite Hfgh in Hfr. simpl in Hfr.
    unfold rootpairs_compatible in *. rewrite <- Hrpc. apply map_ext_in.
    intros x Hin. destruct x; simpl; auto.
    symmetry. eapply fr_vertex_address; eauto. apply graph_has_v_in_closure.
    red in Hrgc. rewrite Forall_forall in Hrgc.
    apply Hrgc. now rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec).
  - now inversion Hfri.
Qed.

Lemma fri_closure_has_v:
  forall from to g h rh rmst item g' h' rh' rmst' x,
    graph_has_gen g to ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    closure_has_v g x ->
    closure_has_v g' x.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' x Hto Hfri Hcl.
  unfold forward_remset_item in Hfri.
  destruct (negb (remset_item_in_gen item rmst g from)) eqn:Hgen.
  - destruct (forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h)
      as [newg newh] eqn:Hfgh.
    simpl in Hfri. inversion Hfri; subst; clear Hfri.
    pose proof fr_forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h as Hfr.
    rewrite Hfgh in Hfr. simpl in Hfr.
    eapply fr_closure_has_v; eauto.
  - now inversion Hfri.
Qed.

Lemma fri_vertex_address:
  forall from to g h rh rmst item g' h' rh' rmst' x,
    graph_has_gen g to ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    closure_has_v g x ->
    vertex_address g x = vertex_address g' x.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' x Hto Hfri Hcl.
  unfold forward_remset_item in Hfri.
  destruct (negb (remset_item_in_gen item rmst g from)) eqn:Hgen.
  - destruct (forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h)
      as [newg newh] eqn:Hfgh.
    simpl in Hfri. inversion Hfri; subst; clear Hfri.
    pose proof fr_forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h as Hfr.
    rewrite Hfgh in Hfr. simpl in Hfr.
    eapply fr_vertex_address; eauto.
  - now inversion Hfri.
Qed.

Lemma forward_remset_item_fold_closure_has_v:
  forall from to g h rh rmst r g' h' rh' rmst' x,
    graph_has_gen g to ->
    (g', h', rh', rmst') = fold_left (forward_remset_item from to) r (g, h, rh, rmst) ->
    closure_has_v g x ->
    closure_has_v g' x.
Proof.
  intros from to g h rh rmst r. revert g h rh rmst.
  induction r; intros g h rh rmst g' h' rh' rmst' x Hto Hfold Hcl; simpl in Hfold.
  - now inversion Hfold.
  - destruct (forward_remset_item from to (g, h, rh, rmst) a) as [[[g2 h2] rh2] rmst2] eqn:Hfri2.
    pose proof Hfri2 as Hfri2'. unfold forward_remset_item in Hfri2'. simpl in Hfri2'.
    rewrite Hfri2' in Hfold. symmetry in Hfri2.
    assert (Hto2: graph_has_gen g2 to).
    { rewrite <- (forward_remset_item_ghg _ _ _ _ _ _ _ _ _ _ _ Hto Hfri2 to). exact Hto. }
    eapply (IHr g2 h2 rh2 rmst2 g' h' rh' rmst' x Hto2 Hfold).
    eapply (fri_closure_has_v from to g h rh rmst a g2 h2 rh2 rmst2 x); eauto.
Qed.

Lemma forward_remset_item_fold_vertex_address:
  forall from to g h rh rmst r g' h' rh' rmst' x,
    graph_has_gen g to ->
    (g', h', rh', rmst') = fold_left (forward_remset_item from to) r (g, h, rh, rmst) ->
    closure_has_v g x ->
    vertex_address g x = vertex_address g' x.
Proof.
  intros from to g h rh rmst r. revert g h rh rmst.
  induction r; intros g h rh rmst g' h' rh' rmst' x Hto Hfold Hcl; simpl in Hfold.
  - now inversion Hfold.
  - destruct (forward_remset_item from to (g, h, rh, rmst) a) as [[[g2 h2] rh2] rmst2] eqn:Hfri2.
    pose proof Hfri2 as Hfri2'. unfold forward_remset_item in Hfri2'. simpl in Hfri2'.
    rewrite Hfri2' in Hfold. symmetry in Hfri2.
    assert (Hto2: graph_has_gen g2 to).
    { rewrite <- (forward_remset_item_ghg _ _ _ _ _ _ _ _ _ _ _ Hto Hfri2 to). exact Hto. }
    assert (Hcl2: closure_has_v g2 x) by
        (eapply (fri_closure_has_v from to g h rh rmst a g2 h2 rh2 rmst2 x); eauto).
    rewrite <- (IHr g2 h2 rh2 rmst2 g' h' rh' rmst' x Hto2 Hfold Hcl2).
    eapply (fri_vertex_address from to g h rh rmst a g2 h2 rh2 rmst2 x); eauto.
Qed.

Lemma forward_remset_item_fold_rootpairs_compatible:
  forall from to g h rh rmst r g' h' rh' rmst' rootpairs roots,
    from <> to ->
    graph_has_gen g to ->
    copy_compatible g ->
    remset_nodup rmst ->
    remset_graph_compatible g rmst ->
    remset_and_remset_space_compatible g from rmst r ->
    roots_graph_compatible roots g ->
    rootpairs_compatible g rootpairs roots ->
    (g', h', rh', rmst') = fold_left (forward_remset_item from to) r (g, h, rh, rmst) ->
    rootpairs_compatible g' rootpairs roots.
Proof.
  intros from to g h rh rmst r. revert g h rh rmst.
  induction r; intros g h rh rmst g' h' rh' rmst' rootpairs roots Hneq Hto Hcc Hrnd Hrc Hrrsc Hrgc Hrpc Hfri;
    simpl in Hfri.
  - now inversion Hfri.
  - hnf in Hrrsc. rewrite Forall_cons_iff in Hrrsc. destruct Hrrsc as [Hrica Hricr].
    destruct (forward_remset_item from to (g, h, rh, rmst) a) as [[[g2 h2] rh2] rmst2] eqn:Hfri2.
    pose proof Hfri2 as Hfri2'. unfold forward_remset_item in Hfri2'. simpl in Hfri2'.
    rewrite Hfri2' in Hfri. symmetry in Hfri2.
    eapply (IHr g2 h2 rh2 rmst2 g' h' rh' rmst' rootpairs roots); eauto.
    + eapply forward_remset_item_ghg with (g := g); eassumption.
    + eapply fri_copy_compatible; eauto.
    + eapply fri_remset_nodup; eassumption.
    + eapply fri_remset_graph_compatible; eauto.
    + hnf. rewrite Forall_forall in Hricr |- *. intros x Hin. specialize (Hricr _ Hin).
      eapply fri_remset_item_compatible with (rmst := rmst) (item := a); eassumption.
    + eapply (forward_remset_item_roots_graph_compatible_pres
                from to g h rh rmst a g2 h2 rh2 rmst2 roots); eauto.
    + eapply (fri_rootpairs_compatible from to g h rh rmst a g2 h2 rh2 rmst2 rootpairs roots); eauto.
Qed.

Lemma heap_remset_zero_available_weak_valid: forall g h rh gen,
    graph_heap_compatible g h ->
    graph_has_gen g gen ->
    remset_heap_and_heap_compatible rh h ->
    ti_size_spec h ->
    available_size h gen = 0 ->
    heap_remset_rep g h rh |-- weak_valid_pointer (gen_start g gen) * TT.
Proof.
  intros g h rh gen Hghc Hghg Hrhhc Htsc Hav0.
  sep_apply (heap_space_remset_rep g h rh gen Hghg Hghc Hrhhc).
  sep_apply (space_remset_rep_data_at_ g h rh gen Hghg Hghc).
  rewrite data_at__memory_block. Intros. rewrite sizeof_tarray_int_or_ptr.
  - replace (offset_val (WORD_SIZE * available_size h gen) (gen_start g gen))
      with (gen_start g gen) by
      (rewrite Hav0, Z.mul_0_r; symmetry; apply isptr_offset_val_zero;
       unfold gen_start; rewrite if_true by assumption; apply start_isptr).
    sep_apply (memory_block_weak_valid_pointer
                 (nth_sh g gen)
                 (WORD_SIZE * (total_size h gen - available_size h gen))
                 (gen_start g gen) 0).
    + split; [lia|]. apply Z.mul_nonneg_nonneg; [unfold WORD_SIZE; lia|].
      pose proof total_space_tight_range (nth_space h gen).
      pose proof available_space_tight_range (nth_space h gen).
      unfold total_size, available_size in *. lia.
    + pose proof ti_size_gt_0 _ _ _ Hghc Hghg Htsc.
      rewrite Hav0. unfold WORD_SIZE. lia.
    + unfold nth_sh. apply readable_nonidentity, writable_readable, generation_share_writable.
    + entailer!.
  - unfold total_size, available_size.
    pose proof total_space_tight_range (nth_space h gen).
    pose proof available_leq_total (nth_space h gen).
    pose proof available_space_tight_range (nth_space h gen).
    rep_lia.
Qed.

Lemma heap_unused_rep_reset_with_remset:
  forall g h rg rhh rh gen,
    graph_heap_compatible g h ->
    graph_has_gen g gen ->
    graph_heap_compatible rg rhh ->
    graph_has_gen rg gen ->
    remset_heap_and_heap_compatible rh rhh ->
    gen_start rg gen = gen_start g gen ->
    nth_sh rg gen = nth_sh g gen ->
    available_size rhh gen = available_size h gen ->
    total_size rhh gen = total_size h gen ->
    heap_unused_rep h * generation_rep g gen *
    heap_remset_rep rg rhh rh |--
    heap_unused_rep (reset_nth_heap gen h) *
    heap_remset_rep_except rg rhh rh gen.
Proof.
  intros g h rg rhh rh gen Hghc Hghg Hrghc Hrghg Hrhhc
         Hstart_eq Hsh_eq Hav_eq Htot_eq.
  unfold heap_unused_rep at 1 2. simpl.
  assert (Hlt: (gen < length (spaces h))%nat) by
      (red in Hghg; destruct Hghc as [_ [_ Hlen]]; lia).
  destruct (reset_nth_space_Permutation _ _ Hlt) as [l [Hreset Hold]].
  rewrite (iter_sepcon_permutation _ Hreset).
  rewrite (iter_sepcon_permutation _ Hold).
  assert (Hrlen: length rh = length (spaces rhh)) by
      (apply rhhc_length_eq; exact Hrhhc).
  assert (Hrlt: (gen < length (spaces rhh))%nat) by
      (red in Hrghg; destruct Hrghc as [_ [_ Hlen]]; lia).
  Opaque space_remset_rep.
  rewrite (heap_remset_rep_split rg rhh rh gen Hrlen Hrlt).
  simpl. cancel.
  Transparent space_remset_rep.
  destruct (gt_gs_compatible _ _ Hghc _ Hghg) as [Hstart [Hsh Hused]].
  fold (nth_space h gen). unfold space_unused_rep. unfold reset_space at 1.
  assert (Hptr: isptr (space_start (nth_space h gen))) by
      (rewrite <- Hstart; apply start_isptr).
  assert (Hnonnull: space_start (nth_space h gen) <> nullval). {
    destruct (space_start (nth_space h gen)); try contradiction.
    intro Hbad; inversion Hbad.
  }
  simpl space_start. rewrite !if_false by assumption.
  sep_apply (generation_rep_data_at_ g gen Hghg).
  sep_apply (space_remset_rep_data_at_ rg rhh rh gen Hrghg Hrghc).
  rewrite Hstart_eq, Hsh_eq, Hav_eq, Htot_eq.
  unfold graph_gen_size, gen_start, nth_sh.
  rewrite if_true by assumption.
  rewrite Hstart, Hsh, Hused.
  unfold available_size, total_size.
  remember (nth_space h gen) as s.
  replace (WORD_SIZE * 0)%Z with 0 by lia.
  rewrite isptr_offset_val_zero by (subst; assumption).
  simpl.
  replace (total_space s - 0) with (total_space s) by lia.
  rewrite (data_at__tarray_value
             (space_sh s) (total_space s) (available_space s)
             (space_start s))
    by (pose proof available_space_tight_range s;
        pose proof available_leq_total s; lia).
  rewrite (data_at__tarray_value
             (space_sh s) (available_space s) (used_space s)
             (space_start s))
    by apply used_leq_available.
  cancel.
Qed.

Lemma frr_gen_start: forall from to roots roots' g g',
    graph_has_gen g to ->
    forward_roots_relation from to roots g roots' g' ->
    forall x, gen_start g x = gen_start g' x.
Proof.
  intros from to roots roots' g g' Hto Hfrr.
  induction Hfrr; intros x; auto.
  transitivity (gen_start g2 x).
  - eapply fr_gen_start; eauto.
  - apply IHHfrr. erewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma body_do_generation: semax_body Vprog Gprog f_do_generation do_generation_spec.
Proof.
  start_function.
  rename H0 into Hremset.
  rename H1 into H0.
  rename H2 into H1.
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
    intros. eapply gen_range; eassumption. }
  assert (Z.of_nat from < MAX_SPACES) by (apply HS; assumption).
  assert (Z.of_nat to < MAX_SPACES) by (apply HS; assumption). clear HS.
  freeze [0;1;2;3;5;6] FR.
  localize [space_struct_rep sh hp h from;
            space_struct_rep sh hp h to].
  unfold space_struct_rep. unfold space_quad.
  forward.
  gather_SEP
    (data_at sh space_type
             _ (space_address hp from))
    (data_at sh space_type
             _ (space_address hp to)).
  replace_SEP 0 (space_struct_rep sh hp h from
                  * space_struct_rep sh hp h to) by
    (unfold space_struct_rep; entailer!!).
  unlocalize [heap_rep sh h hp].
  1: apply heap_rep_ramif_stable;  assumption.
  assert_PROP (isptr (space_address hp to)). {
    unfold thread_info_rep, heap_rep. unfold heap_struct_rep.
    unfold space_address. Intros.
    entailer!.
  }
  assert_PROP (offset_val WORD_SIZE (space_address hp to) =
               heap_next_address hp to) as Hnext_eq. {
    unfold heap_rep. unfold heap_struct_rep. Intros. entailer!.
    unfold space_address, heap_next_address, field_address. rewrite if_true.
    - simpl. rewrite offset_offset_val. f_equal.
    - destruct H as [[_ [_ ?]] _]. unfold field_compatible in *.
      simpl in *. unfold in_members. simpl. intuition auto with *.
  }
  pose proof H as Hsc. destruct Hsc as [Hghc [Hrpc [Hroc Hoc]]].
  pose proof H0 as Hdgc.
  destruct Hdgc as [Hese [Hfrom [Hto [Hcc [Hndd [Havail [Hunmk Htsc]]]]]]].
  pose proof Hremset as Hrs. destruct Hrs as [Hrgoc Hrhc].
  assert (Hrcw: remset_graph_compatible g rmst) by
      (eapply remset_graph_outlier_compatible_weakened; eassumption).
  thaw FR.
  assert_PROP (remset_nodup rmst) as Hrmnd. {
    sep_apply remset_rep_nodup.
    - apply readable_nonidentity, writable_readable. assumption.
    - entailer !!.
  }
  forward_call (rsh, sh, gv, g, h, hp, outlier, rh, rmst, from, to);
    [ unfold forward_remset_condition;
      do 5 (split; [assumption|]);
      exact Htsc
    | try idtac ].
  Intros vret. destruct vret as [[[g0 h0] rh0] rmst0].
  simpl fst in *. simpl snd in *.
  match goal with
  | Hfrg0 : (g0, h0, rh0, rmst0) = forward_remset_gh from to g h rh rmst |- _ =>
      pose proof Hfrg0 as Hfrg0'
  end.
  assert (Hrrsc: remset_and_remset_space_compatible g from rmst (Znth (Z.of_nat from) rh)) by
      (eapply rrhc_forall_rrsc; exact (proj1 Hrhc)).
  assert (Hfc0: forward_condition g0 h0 from to). {
    eapply fri_forward_condition_fold with
        (r := Znth (Z.of_nat from) rh) (size := remset_gen_size h from).
    - exact H1.
    - exact Hfrom.
    - exact Hto.
    - exact Hndd.
    - exact Hcc.
    - exact Hrcw.
    - exact Hrmnd.
    - exact Hrrsc.
    - exact Hese.
    - rewrite <- (compatible_remset_gen_size g h rh from Hghc Hfrom (proj2 Hrhc)).
      lia.
    - exact Hfrg0'.
  }
  assert (Hsc0: super_compatible g0 h0 (frames2rootpairs fr) roots outlier). {
    destruct Hroc as [Hrooc Hrgc].
    split.
    - eapply forward_remset_gh_ghc; eauto.
    - split.
      + eapply (forward_remset_item_fold_rootpairs_compatible
                  from to g h rh rmst (Znth (Z.of_nat from) rh)
                  g0 h0 rh0 rmst0 (frames2rootpairs fr) roots).
        * exact H1.
        * exact Hto.
        * exact Hcc.
        * exact Hrmnd.
        * exact Hrcw.
        * exact Hrrsc.
        * exact Hrgc.
        * exact Hrpc.
        * exact Hfrg0'.
      + split.
        * split; [exact Hrooc|].
          eapply (forward_remset_item_fold_roots_graph_compatible_pres
                    from to g h rh rmst (Znth (Z.of_nat from) rh)
                    g0 h0 rh0 rmst0 roots).
          -- exact Hto.
          -- exact Hfrg0'.
          -- exact Hrgc.
        * eapply (forward_remset_item_fold_oc
                    from to g h rh rmst (Znth (Z.of_nat from) rh)
                    g0 h0 rh0 rmst0 outlier).
          -- exact H1.
          -- exact Hrmnd.
          -- exact Hto.
          -- exact Hcc.
          -- exact Hndd.
          -- exact Hrcw.
          -- exact Hrrsc.
          -- exact Hoc.
          -- exact Hfrg0'.
  }
  assert (Hptrf0: isptr (space_start (nth_space h0 from))). {
    destruct Hsc0 as [Hghc0 _]. destruct Hfc0 as [_ [Hfrom0 _]].
    eapply space_start_isptr; eauto.
  }
  freeze [0;1;2;4;5;6] FR.
    localize [space_struct_rep sh hp h0 from].
    unfold space_struct_rep, space_quad.
    forward.
    forward.
    replace_SEP 0 (space_struct_rep sh hp h0 from) by
        (unfold space_struct_rep, space_quad; entailer!!).
    unlocalize [heap_rep sh h0 hp].
    1: apply heap_rep_ramif_stable_1; assumption.
    remember (space_start (nth_space h from)) as from_p.
    remember (space_start (nth_space h to)) as to_p.
    remember (WORD_SIZE * used_space (nth_space h to))%Z as to_used.
    remember (WORD_SIZE * available_space (nth_space h to))%Z as to_total.
    remember (WORD_SIZE * used_space (nth_space h from))%Z as from_used.
    replace from_p with (gen_start g from) by
        (subst; unfold gen_start; rewrite if_true; assumption).
    replace (offset_val (WORD_SIZE * available_space (nth_space h from))
                        (gen_start g from)) with (limit_address g h from) by
        (unfold limit_address, available_size; reflexivity).
    assert_PROP (isptr (space_address hp to)). {
      unfold space_address. rewrite isptr_offset_val. unfold thread_info_rep, heap_rep.
      Intros. unfold heap_struct_rep. entailer!. }
    assert_PROP (offset_val WORD_SIZE (space_address hp to) =
                 heap_next_address hp to). {
      unfold heap_rep. unfold heap_struct_rep. Intros. entailer!. } thaw FR.
    forward_call (rsh, sh, gv, g0, h0, hp, fr, roots, outlier, from, to).
    { entailer!; simpl; repeat f_equal.
      - destruct Hsc0 as [Hghc0 _]. destruct Hfc0 as [_ [Hfrom0 _]].
        destruct (gt_gs_compatible _ _ Hghc0 _ Hfrom0) as [Haddr0 _]. simpl in Haddr0.
        unfold gen_start. rewrite if_true by assumption. symmetry. exact Haddr0.
      - destruct Hsc0 as [Hghc0 _]. destruct Hfc0 as [_ [Hfrom0 _]].
        destruct (gt_gs_compatible _ _ Hghc0 _ Hfrom0) as [Haddr0 _]. simpl in Haddr0.
        unfold limit_address, available_size, gen_start.
        rewrite if_true by assumption. rewrite Haddr0. reflexivity.
      - exact H19. }
    Intros vret. destruct vret as [[g1 h1] roots1]. simpl fst in *. simpl snd in *.
    freeze [0;1;2;3;5;6] FR.
    set (fr1 := update_frames fr (map (exterior2val g1) roots1))  in *.
    assert (space_start (nth_space h1 from) = gen_start g1 from). {
      destruct H20 as [? _]. destruct H22 as [_ [? _]].
      destruct (gt_gs_compatible _ _ H20 _ H22) as [H24 _]. simpl in H24. rewrite <- H24.
      unfold gen_start. rewrite if_true by assumption. reflexivity. }
    assert (isptr (space_start (nth_space h1 from))). {
      rewrite H24. unfold gen_start. destruct H22 as [_ [? _]].
      rewrite if_true by assumption. apply start_isptr. }
    localize [space_struct_rep sh hp h1 from].
    unfold space_struct_rep, space_quad.
    do 2 forward.
    replace_SEP 0 (space_struct_rep sh hp h1 from) by
        (unfold space_struct_rep, space_quad; entailer!!).
    unlocalize [heap_rep sh h1 hp].
    1: apply heap_rep_ramif_stable_1; assumption. thaw FR. rewrite H24.
    replace (offset_val (WORD_SIZE * available_space (nth_space h1 from))
                        (gen_start g1 from)) with (limit_address g1 h1 from) by
        (unfold limit_address, available_size; reflexivity).
    pose proof I.
    assert (Hto0 : graph_has_gen g0 to). {
      destruct Hfc0 as [_ [_ [Hto0 _]]]. exact Hto0.
    }
    assert (H27 : closure_has_v g (to, number_of_vertices (nth_gen g to))) by
        (red; simpl; unfold closure_has_index; split; [assumption | lia]).
    assert (H27g0 : closure_has_v g0 (to, number_of_vertices (nth_gen g to))). {
      eapply (forward_remset_item_fold_closure_has_v
                from to g h rh rmst (Znth (Z.of_nat from) rh)
                g0 h0 rh0 rmst0 (to, number_of_vertices (nth_gen g to))); eauto.
    }
    replace (offset_val to_used to_p) with
        (offset_val (- WORD_SIZE)
                    (vertex_address g1 (to, number_of_vertices (nth_gen g to)))) by
        (rewrite <- (frr_vertex_address _ _ _ _ _ _ Hto0 H21 _ H27g0);
         rewrite <- (forward_remset_item_fold_vertex_address
                       from to g h rh rmst (Znth (Z.of_nat from) rh)
                       g0 h0 rh0 rmst0 (to, number_of_vertices (nth_gen g to))
                       Hto Hfrg0' H27);
         subst;
         unfold vertex_address, vertex_offset, gen_start; simpl;
         rewrite offset_offset_val, H11, H9, if_true by assumption;
         f_equal; unfold WORD_SIZE; lia).
    eapply frr_closure_has_v in H27g0; eauto.
    destruct H27g0 as [H27g0 H28]. simpl in H27g0, H28.
    assert (Hunk0 : gen_unmarked g0 to). {
      eapply (forward_remset_item_fold_gen_unmarked_pres
                from to g h rh rmst (Znth (Z.of_nat from) rh)
                g0 h0 rh0 rmst0 to); eauto.
    }
    assert (Hunk1: gen_unmarked g1 to) by
        (eapply (frr_gen_unmarked _ _ _ g0 _ g1); eauto).
    sep_apply frames_rep_localize. Intros.
    assert (Hgst01: gen_start g0 to = gen_start g1 to) by
        (eapply frr_gen_start; [exact Hto0 | exact H21]).
    assert (Hrhhc0: remset_heap_and_heap_compatible rh0 h0). {
      eapply (forward_remset_item_fold_rhhc
                from to g h rh rmst g0 h0 rh0 rmst0
                (Znth (Z.of_nat from) rh)).
      - exact H1.
      - exact Hrmnd.
      - exact Hghc.
      - exact Hcc.
      - exact Hndd.
      - exact Hfrom.
      - exact Hto.
      - exact Hrcw.
      - exact Hrrsc.
      - exact (proj2 Hrhc).
      - exact Hfrg0'.
      - unfold enough_space_enhanced in Hese.
        rewrite (compatible_remset_gen_size g h rh from
                 Hghc Hfrom (proj2 Hrhc)) in Hese.
        exact Hese.
    }
    assert (HPscan: heap_remset_rep g0 h0 rh0 |--
              (if zlt 0 (available_size h1 to) then emp
               else weak_derives (heap_remset_rep g0 h0 rh0)
                      (weak_valid_pointer (gen_start g1 to) * TT) && emp) *
              heap_remset_rep g0 h0 rh0). {
      destruct (zlt 0 (available_size h1 to)) as [Hav1|Hav1].
      - cancel.
      - assert (Hzero0: available_size h0 to = 0). {
          rewrite (proj1 H23 to).
          pose proof available_space_range (nth_space h1 to).
          unfold available_size in *. lia.
        }
        assert (Hghc0: graph_heap_compatible g0 h0) by
            (destruct Hsc0; assumption).
        assert (Htoh0: graph_has_gen g0 to) by
            (destruct Hfc0 as [_ [_ [? _]]]; assumption).
        assert (Hwhr0: weak_heap_relation h h0) by
            (eapply forward_remset_item_fold_whr; eauto).
        assert (Htsc0: ti_size_spec h0) by
            (eapply weak_heap_relation_size_spec; eauto).
        apply weak_derives_strong.
        rewrite <- Hgst01.
        sep_apply (heap_remset_zero_available_weak_valid g0 h0 rh0 to
                     Hghc0 Htoh0 Hrhhc0 Htsc0 Hzero0).
        cancel.
    }
    replace_SEP 6
      ((if zlt 0 (available_size h1 to) then emp
        else weak_derives (heap_remset_rep g0 h0 rh0)
               (weak_valid_pointer (gen_start g1 to) * TT) && emp) *
       heap_remset_rep g0 h0 rh0)
      by (entailer!; apply HPscan).
    Intros.
    forward_call (rsh, sh, gv, g1, h1, hp, outlier,
                   from, to, number_of_vertices (nth_gen g to),
                   heap_remset_rep g0 h0 rh0).
    - destruct H20 as [Hghc1 [_ [_ Hoc1]]].
      split; [exact Hghc1|exact Hoc1].
    - Intros vret. destruct vret as [g2 h2]. simpl fst in *. simpl snd in *.
      assert (Hsp: super_compatible g2 h2 (frames2rootpairs fr1) roots1 outlier). {
        destruct H20 as [? [? [Hrc ?]]]. split; [|split; [|split]]; auto.
        + destruct Hrc. eapply do_scan_rootpairs_compatible; eassumption.
        + eapply do_scan_roots_compatible; eassumption. } clear H29 H30.
      rename H33 into H34. rename H32 into H33. rename H31 into H32. rename Hsp into H31.
      sep_apply frames_rep_unlocalize.
      rewrite update_frames_same.
      assert (Hstart2_from: space_start (nth_space h2 from) = gen_start g2 from). {
        destruct H31 as [Hghc2 _]. destruct H32 as [_ [Hfrom2 _]].
        destruct (gt_gs_compatible _ _ Hghc2 _ Hfrom2) as [Hstart2 _]. simpl in Hstart2.
        rewrite <- Hstart2.
        unfold gen_start. rewrite if_true by assumption. reflexivity. }
      assert (isptr (space_start (nth_space h2 from))). {
        rewrite Hstart2_from. unfold gen_start. destruct H32 as [_ [Hfrom2 _]].
        rewrite if_true by exact Hfrom2. apply start_isptr. }
      freeze [0;1;2;3] FR. freeze [0;2;3;4] FR2.
      localize [space_struct_rep sh hp h2 from].
      unfold space_struct_rep, space_quad.
      forward.
      replace_SEP 0 (space_struct_rep sh hp h2 from) by
          (unfold space_struct_rep, space_quad; entailer!!).
      unlocalize [heap_rep sh h2 hp].
      1: apply heap_rep_ramif_stable_1; assumption. thaw FR2. thaw FR.
      unfold thread_info_rep, heap_rep. Intros.
      freeze [1;2;3;5] FR. rewrite heap_struct_rep_eq.
      assert_PROP (space_address hp from =
                   field_address (tarray space_type MAX_SPACES) [ArraySubsc (Z.of_nat from)]
                                 hp) as Hspace_addr_from. {
        entailer!. unfold space_address. unfold field_address. rewrite if_true.
        - simpl. f_equal.
        - unfold field_compatible in *. simpl in *. intuition auto with *. }
      rewrite Hspace_addr_from. clear Hspace_addr_from.
      deadvars!.
      forward.
      rewrite Znth_map by (rewrite spaces_size; rep_lia).
      rewrite <- nth_space_Znth. unfold space_quad at 2 3.
      simpl fst. simpl snd.
      assert (FROM_MAX: 0 <= Z.of_nat from < Zlength (map space_quad (spaces h2))). {
        rewrite Zlength_map.
        destruct H31 as [[_ [_ Hlen2]] _].
        destruct H32 as [_ [Hfrom2 _]].
        red in Hfrom2. split. lia. rewrite Zlength_correct. lia.
      }
      Opaque fst. Opaque snd.
      forward; rewrite upd_Znth_same by assumption. entailer!.
      forward; rewrite upd_Znth_same by assumption.
      rewrite !upd_Znth_twice by assumption.
      Transparent fst. Transparent snd.
      thaw FR.
      assert (Hfrom_g2: graph_has_gen g2 from) by
          (destruct H32 as [_ [? _]]; assumption).
      pose proof H31 as Hsc2.
      assert (Hghc2: graph_heap_compatible g2 h2) by
          (destruct Hsc2 as [? _]; assumption).
      rewrite (graph_rep_reset g2 from) by exact Hfrom_g2. Intros.
      assert (Hghc0: graph_heap_compatible g0 h0) by
          (destruct Hsc0 as [? _]; assumption).
      assert (Hfrom_g0: graph_has_gen g0 from) by
          (destruct Hfc0 as [_ [? _]]; assumption).
      assert (Hhr02: heap_relation h0 h2) by
          (eapply hr_trans; [exact H23 | exact H34]).
      assert (Hstart02: gen_start g0 from = gen_start g2 from). {
        destruct (gt_gs_compatible _ _ Hghc0 _ Hfrom_g0) as [Hs0 _].
        destruct Hhr02 as [_ [Hss _]].
        unfold gen_start at 1. rewrite if_true by exact Hfrom_g0.
        rewrite Hs0, Hss. exact Hstart2_from.
      }
      assert (Hsh02: nth_sh g0 from = nth_sh g2 from). {
        destruct (gt_gs_compatible _ _ Hghc0 _ Hfrom_g0) as [_ [Hsh0 _]].
        destruct (gt_gs_compatible _ _ Hghc2 _ Hfrom_g2) as [_ [Hsh2 _]].
        destruct Hhr02 as [_ [_ [_ Hshh]]].
        unfold nth_sh. rewrite Hsh0, Hshh, <- Hsh2. reflexivity.
      }
      assert (Hav02: available_size h0 from = available_size h2 from) by
          (destruct Hhr02 as [Hav _]; apply Hav).
      assert (Htot02: total_size h0 from = total_size h2 from) by
          (destruct Hhr02 as [_ [_ [Htot _]]]; apply Htot).
      sep_apply (heap_unused_rep_reset_with_remset
                   g2 h2 g0 h0 rh0 from Hghc2 Hfrom_g2
                   Hghc0 Hfrom_g0 Hrhhc0 Hstart02 Hsh02 Hav02 Htot02).
      rewrite <- heap_struct_rep_eq.
      simpl fst. simpl snd.
      gather_SEP
        (heap_unused_rep _ * heap_remset_rep_except _ _ _ _)
        (heap_struct_rep _ _ _).
      replace_SEP 0 (heap_rep sh (reset_nth_heap from h2) hp *
                     heap_remset_rep_except g0 h0 rh0 from).
      + unfold heap_rep. entailer!!.
        assert (Hfrom_len: (from < length (spaces h2))%nat) by
            (destruct Hghc2 as [_ [_ Hlen]]; red in Hfrom_g2; lia). simpl.
        rewrite (reset_nth_space_Znth _ _ Hfrom_len), <- nth_space_Znth, <- upd_Znth_map.
        unfold space_quad at 3. simpl. replace (WORD_SIZE * 0)%Z with 0 by lia.
        rewrite isptr_offset_val_zero by assumption. cancel.
      + apply super_compatible_reset with (gen := from) in Hsc2.
        2: { apply (frr_not_pointing from to roots g0 roots1 g1).
             - destruct Hfc0 as [_ [_ [_ [? _]]]]. assumption.
             - destruct Hsc0 as [_ [_ [[_ ?] _]]]. assumption.
             - exact H1.
             - exact Hto0.
             - exact H21.
        }
        remember (reset_nth_heap from h2) as h3.
        remember (reset_graph from g2) as g3.
        assert (do_generation_relation from to roots roots1 g h rh rmst
                  g0 h0 rh0 rmst0 g3 h3). {
          split.
          - exists g1, g2.
            split; [exact Hfrg0'|].
            split; [exact H21|].
            split; [exact H33|].
            exact Heqg3.
          - split.
            + intros gen Hgen.
              eapply forward_remset_gh_available_size_not_to; eauto.
            + exists h2. split; [exact Hhr02 | exact Heqh3].
        }
        assert (weak_heap_relation h h3). {
          apply whr_trans with h0.
          - eapply forward_remset_item_fold_whr; eauto.
          - apply whr_trans with h1.
            + apply heap_relation_weakened. exact H23.
            + apply whr_trans with h2.
              * apply heap_relation_weakened. exact H34.
              * subst h3. apply weak_heap_relation_reset.
        }
        Exists g0 h0 rh0 rmst0 g3 h3 roots1.
        destruct H32 as [? [? [? ?]]].
        replace (update_frames fr (map _ _)) with fr1.
        entailer!!.
        destruct (zlt 0 (available_size h2 to)); entailer!!.
        apply andp_left2. apply derives_refl.
        unfold fr1 in *.
        destruct Hsc2 as [_ [Hrpc3 _]].
        destruct H20 as [_ [Hrpc1 _]].
        red in Hrpc3. red in Hrpc1.
        rewrite Hrpc1, Hrpc3.
        reflexivity.
Qed.
