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

#[local] Open Scope logic.

Lemma body_forward_remset: semax_body Vprog Gprog f_forward_remset forward_remset_spec.
Proof.
  start_function.
  rename H into Hghc. rename H0 into Hoc. rename H1 into Hfrc. rename H2 into Hrc.
  rename H3 into Hrhc. rename H4 into Hftneq. destruct Hfrc as [Hese [Hghgf [Hghgt [Hcc [Hndd Htsc]]]]].
  assert (Hgsc: generation_space_compatible g (from, nth_gen g from, nth_space h from)) by
    (apply gt_gs_compatible; assumption). destruct Hgsc as [Haddrf [Hshf Hsizef]].
  assert (Hgsc: generation_space_compatible g (to, nth_gen g to, nth_space h to)) by
    (apply gt_gs_compatible; assumption). destruct Hgsc as [Haddrt [Hsht Hsizet]].
  assert (Hptrf: isptr (space_start (nth_space h from))) by
    (rewrite <- Haddrf; apply start_isptr).
  assert (Hptrt: isptr (space_start (nth_space h to))) by
    (rewrite <- Haddrt; apply start_isptr).
  assert (Hrcw: remset_graph_compatible g rmst) by
    (eapply remset_graph_outlier_compatible_weakened; eassumption).
  assert_PROP (remset_nodup rmst) as Hrmnd. {
    sep_apply remset_rep_nodup.
    - apply readable_nonidentity, writable_readable. assumption.
    - entailer !!. }
  freeze [0; 1; 2; 4; 5] FR.
  assert (HS: forall gen, graph_has_gen g gen -> Z.of_nat gen < MAX_SPACES). {
    intros. eapply gen_range; eassumption. }
  assert (HMf: Z.of_nat from < MAX_SPACES) by (apply HS; assumption).
  assert (HMt: Z.of_nat to < MAX_SPACES) by (apply HS; assumption). clear HS.
  localize [space_struct_rep sh hp h from; space_struct_rep sh hp h to].
  unfold space_struct_rep, space_quad.
  forward.
  forward.
  forward.
  forward.
  forward.
  gather_SEP (data_at sh space_type _ (space_address hp from))
    (data_at sh space_type _ (space_address hp to)).
  replace_SEP 0 (space_struct_rep sh hp h from * space_struct_rep sh hp h to) by
    (unfold space_struct_rep; entailer !!).
  unlocalize [heap_rep sh h hp]. 1: apply heap_rep_ramif_stable; assumption. clear HMf HMt.
  forward_if True.
  - entailer !!. rewrite !sameblock_offset_val by assumption. simpl. tauto.
  - forward. entailer !!.
  - change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 3%N |})
      with int_or_ptr_type in H.
    remember (space_start (nth_space h from)) as from_start.
    remember (space_start (nth_space h to)) as to_start.
    destruct from_start; inversion Hptrf. destruct to_start; inversion Hptrt.
    unfold sem_sub_pp in H. simpl in H. unfold eq_block. rewrite !peq_true in H.
    simpl in H. rewrite !(Ptrofs.add_commut i), !(Ptrofs.add_commut i0),
      !Ptrofs.sub_shifted, !ptrofs_sub_repr, !ptrofs_divs_repr in H. 3, 5: rep_lia.
    2: apply remset_space_signed_range. 2: apply rest_space_signed_range.
    rewrite <- !Z.mul_sub_distr_l, !(Z.mul_comm WORD_SIZE), !Z.quot_mul,
      !ptrofs_to_int64_repr in H; [| reflexivity | reflexivity | lia..].
    apply typed_false_of_bool in H. rewrite negb_false_iff in H. apply lt64_repr in H.
    2: apply rest_space_repable_signed. 2: apply remset_space_repable_signed.
    exfalso. unfold enough_space_enhanced, general_enough_space_to_copy in Hese.
    fold (rest_gen_size h to) (available_size h from) (total_size h from) (remset_gen_size h from) in H.
    pose proof unmarked_gen_size_nonneg g from. lia.
  - Intros. thaw FR.
    forward_loop (EX n: Z, EX g': LGraph, EX h': part_heap, EX rh': remset_heap, EX rmst': remset,
                  PROP ((g', h', rh', rmst') = fold_left (forward_remset_item from to)
                        (sublist 0 n (Znth (Z.of_nat from) rh)) (g, h, rh, rmst);
                        0 <= n <= total_size h from - available_size h from)
                  LOCAL (temp _q
                           (offset_val (WORD_SIZE * (available_size h' from + n))
                              (space_start (nth_space h' from)));
                         temp _from_rem_limit
                           (offset_val (WORD_SIZE * total_size h' from)
                              (space_start (nth_space h' from)));
                         temp _from_limit
                           (offset_val (WORD_SIZE * available_size h' from)
                              (space_start (nth_space h' from)));
                         temp _from_start (space_start (nth_space h' from));
                         temp _from (space_address hp from);
                         temp _to (space_address hp to);
                         temp _next (heap_next_address hp to))
                  SEP (heap_rep sh h' hp; all_string_constants rsh gv; outlier_rep outlier;
                       graph_rep g'; heap_remset_rep g' h' rh'; remset_rep sh g' rmst')).
    + forward. Exists 0 g h rh rmst. entailer !!. unfold total_size, available_size.
      pose proof available_leq_total (nth_space h from). lia.
    + Intros n g' h' rh' rmst'. rename H into Hfric. rename H0 into Hnrange.
      destruct Hrhc as [Hrrhc Hrhhc].
      assert (Hsub_rrsc:
               remset_and_remset_space_compatible g from rmst (sublist 0 n (Znth (Z.of_nat from) rh))). {
        apply Forall_sublist. eapply rrhc_forall_rrsc; try eassumption. }
      assert (Hsub_gesc: general_enough_space_to_copy g h from to
                           (Zlength (sublist 0 n (Znth (Z.of_nat from) rh)))). {
        unfold enough_space_enhanced in Hese. erewrite compatible_remset_gen_size in Hese; eauto.
        eapply gestc_decay; eauto. apply sublist_max_length. }
      assert (Hghc': graph_heap_compatible g' h'). {
        eapply forward_remset_item_fold_ghc with (r := sublist 0 n (Znth (Z.of_nat from) rh)); eauto. }
      assert (Hghgf': graph_has_gen g' from) by
        now rewrite <- (forward_remset_item_fold_ghg _ _ _ _ _ _ _ _ _ _ _ Hghgt Hfric).
      assert (Hghgt': graph_has_gen g' to) by
        now rewrite <- (forward_remset_item_fold_ghg _ _ _ _ _ _ _ _ _ _ _ Hghgt Hfric).
      assert (Hlen': length rh' = length (spaces h')). {
        apply rhhc_length_eq in Hrhhc. eapply forward_remset_item_fold_len; eassumption. }
      pose proof space_start_isptr _ _ _ Hghc' Hghgf' as Hptrf'.
      assert (Hweakhr: weak_heap_relation h h') by (eapply forward_remset_item_fold_whr; eassumption).
      assert (Htsc': ti_size_spec h') by (now apply (weak_heap_relation_size_spec h)).
      assert (Hrgseq: remset_gen_size h' from = remset_gen_size h from) by
        (eapply fold_fri_remset_gen_size; eassumption).
      assert (Hrg: 0 <= WORD_SIZE * (available_space (nth_space h' from) + n) <=
                     WORD_SIZE * total_size h' from). {
        clear -Hnrange Hrgseq. unfold WORD_SIZE.
        pose proof available_space_tight_range (nth_space h' from). fold (available_size h' from) in *.
        unfold remset_gen_size in Hrgseq. lia. }
      assert (Hrhhc': remset_heap_and_heap_compatible rh' h'). {
        eapply forward_remset_item_fold_rhhc with (g := g); eauto. }
      assert (Hgsc': generation_space_compatible g' (from, nth_gen g' from, nth_space h' from)) by
        (apply gt_gs_compatible; assumption). destruct Hgsc' as [Haddrf' [Hshf' Hsizef']].
      assert (Hrrhc': remset_and_remset_heap_compatible g' from rmst' rh'). {
        eapply forward_remset_item_fold_rrhc with (g := g); eauto. }
      assert (Hoc': outlier_compatible g' outlier) by
        (eapply forward_remset_item_fold_oc with (g := g); eassumption).
      assert (Hfc: forward_condition g' h' from to). {
        eapply fri_forward_condition_fold with (g := g); eauto. lia. }
      assert (Hrc': remset_graph_outlier_compatible g' outlier rmst') by
        (eapply fri_remset_graph_outlier_compatible_fold with (g := g); eassumption).
      assert (Hrmnd': remset_nodup rmst') by (eapply fri_remset_nodup_fold; eassumption).
      assert (Hcc': copy_compatible g') by (destruct Hfc as [_ [_ [_ [? _]]]]; assumption).
      assert (Hndd': no_dangling_dst g') by (destruct Hfc as [_ [_ [_ [_ ?]]]]; assumption).
      assert (Hesc: enough_space_to_copy g' h' from to) by (destruct Hfc as [? _]; assumption).
      assert (Hgesc: general_enough_space_to_copy g' h' from to (remset_gen_size h' from - n)). {
        pose proof compatible_remset_gen_size _ _ _ _ Hghc Hghgf Hrhhc. rewrite Hrgseq.
        unfold enough_space_enhanced in Hese. clear Hsub_gesc.
        assert (n <= Zlength (Znth (Z.of_nat from) rh)) by
          (rewrite <- H; unfold remset_gen_size; destruct Hnrange; assumption).
        eapply forward_remset_item_fold_gestc in Hfric; eauto;
        rewrite H, Zlength_sublist, Z.sub_0_r in *; auto; lia. }
      assert (Hd: remset_rep sh g' rmst' |-- !! (forall v, In v (map extract_address rmst') -> isptr v)). {
        rewrite prop_forall. apply allp_right. intros. rewrite prop_impl_imp. apply imp_andp_adjoint.
        Intros. now apply remset_rep_isptr. } sep_apply Hd. Intros. rename H into Hrisptr. clear Hd.
      forward_if.
      * change (Tpointer Tvoid {| attr_volatile := false; attr_alignas := Some 3%N |})
          with int_or_ptr_type in *. remember (space_start (nth_space h' from)) as vs.
        remember (offset_val _ vs) as va.
        remember (offset_val (WORD_SIZE * total_size h' from) vs) as vt.
        assert (Hva: isptr va) by now subst va; apply isptr_offset_val'.
        assert (Hvt: isptr vt) by now subst vt; apply isptr_offset_val'.
        Transparent denote_tc_test_eq. unfold denote_tc_test_eq. destruct va; try contradiction.
        destruct vt; try contradiction. rewrite Heqva, Heqvt. unfold test_eq_ptrs.
        rewrite sameblock_offset_val by assumption. unfold heap_rep. apply andp_right.
        -- sep_apply (graph_and_heap_remset_weak_valid_ptr g' h' rh' from
                        (WORD_SIZE * (available_size h' from + n))). entailer !!.
        -- sep_apply (graph_and_heap_remset_weak_valid_ptr g' h' rh' from
                        (WORD_SIZE * (total_size h' from))). 2: entailer !!.
           pose proof total_space_tight_range (nth_space h' from). unfold total_size, WORD_SIZE. lia.
      * change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 3%N |})
          with int_or_ptr_type in *. freeze [0; 1; 2; 3; 4] FR. rename H into Hneq.
        assert (Hin: In (nth_space h' from, nth_remset_space rh' from) (combine (spaces h') rh')). {
          assert (HZlen: Zlength (spaces h') = Zlength rh') by (rewrite !Zlength_correct; lia).
          rewrite nth_space_Znth, nth_remset_space_Znth, <- Znth_combine by easy.
          clear -HZlen Hghgf' Hghc'. destruct Hghc' as [_ [_ ?]]. hnf in Hghgf'.
          apply Znth_In. rewrite Zlength_combine, <- HZlen, Z.min_id, Zlength_correct. lia. }
        assert (0 <= n < total_size h' from - available_size h' from). {
          clear -Hrg Hneq Hnrange. fold (available_size h' from) in *. fold (total_size h' from) in *.
          cut (available_size h' from + n <> total_size h' from).
          - intros; unfold WORD_SIZE in *; lia.
          - intro Hn. apply Hneq. rewrite Hn. reflexivity. } clear Hnrange. rename H into Hnrange.
        remember (total_size h' _ - available_size h' _) as rh_size.
        remember (map (remset_item_val g') (nth_remset_space rh' from)) as rh_value.
        assert (Hrhs: rh_size = Zlength rh_value). {
          subst. rewrite Zlength_map. symmetry. eapply rhhc_rssc_len; eassumption. }
        assert (Hrdb: readable_share (space_sh (nth_space h' from))). {
          rewrite <- Hshf'. apply writable_readable, generation_share_writable. }
        assert (Hprt: isptr (Znth n rh_value)). {
          cut (Forall isptr rh_value).
          - intros HF. rewrite Forall_Znth in HF. apply HF. lia.
          - subst rh_value. apply rrhc_forall_rrsc in Hrrhc'. hnf in Hrrhc'.
            rewrite nth_remset_space_Znth. rewrite Forall_map. eapply Forall_impl. 2: eassumption.
            intros item Hric. hnf in Hric. destruct item.
            * simpl. now apply Hrisptr.
            * simpl. destruct i. apply isptr_offset_val'. apply graph_has_v_addr_isptr.
                destruct Hric as [Hric _]. assumption. }
        localize [space_remset_rep g' (nth_space h' from, nth_remset_space rh' from)].
        assert (Hlocal1: space_remset_rep g' (nth_space h' from, nth_remset_space rh' from) =
                data_at (space_sh (nth_space h' from)) (tarray int_or_ptr_type n)
                  (sublist 0 n rh_value)
                  (offset_val (WORD_SIZE * available_size h' from) (space_start (nth_space h' from))) *
                data_at (space_sh (nth_space h' from))
                  (tarray int_or_ptr_type (Zlength (sublist n rh_size rh_value)))
                  (sublist n rh_size rh_value)
                  (offset_val (WORD_SIZE * available_size h' from + WORD_SIZE * n)
                     (space_start (nth_space h' from)))). {
            unfold space_remset_rep. destruct (Val.eq _ _). 1: rewrite e in Hptrf'; contradiction.
          fold (total_size h' from) in *. fold (available_size h' from) in *.
          rewrite <- Heqrh_size. rewrite <- Heqrh_value.
          rewrite data_at_tarray_value with
            (n1 := n) (v' := rh_value) (v1 := sublist 0 n rh_value) (v2 := sublist n rh_size rh_value);
            [| lia | lia | list_solve  | reflexivity | reflexivity ]. rewrite offset_offset_val.
          replace (rh_size - n) with (Zlength (sublist n rh_size rh_value)) by list_solve. reflexivity. }
        rewrite Hlocal1, Z.mul_add_distr_l. Intros.
        assert (Hlocal2: data_at (space_sh (nth_space h' from))
                (tarray int_or_ptr_type (Zlength (sublist n rh_size rh_value)))
                (sublist n rh_size rh_value)
                (offset_val (WORD_SIZE * available_size h' from + WORD_SIZE * n)
                   (space_start (nth_space h' from))) =
                data_at (space_sh (nth_space h' from)) int_or_ptr_type (Znth n rh_value)
                  (offset_val (WORD_SIZE * available_size h' from + WORD_SIZE * n)
                     (space_start (nth_space h' from))) *
                data_at (space_sh (nth_space h' from))
                  (tarray int_or_ptr_type (Zlength (sublist n rh_size rh_value) - 1))
                  (tl (sublist n rh_size rh_value))
                  (offset_val WORD_SIZE
                     (offset_val (WORD_SIZE * available_size h' from + WORD_SIZE * n)
                        (space_start (nth_space h' from))))). {
        rewrite data_at_tarray_value_split_1 by list_solve.
        replace (hd Vundef (sublist n rh_size rh_value)) with (Znth n rh_value) by
          (transitivity (Znth 0 (sublist n rh_size rh_value));
           [rewrite Znth_sublist; list_solve | now rewrite <- hd_Znth]). reflexivity. }
        rewrite Hlocal2. Intros.
        forward. 1: entailer !!; now apply isptr_is_pointer_or_integer.
        gather_SEP (data_at _ _ _ _) (data_at _ _ _ _) (data_at _ _ _ _).
        rewrite sepcon_assoc, <- Hlocal2, <- Hlocal1.
        unlocalize [heap_remset_rep g' h' rh']. 1: apply heap_remset_rep_ramif_stable_1; assumption.
        forward_call (Znth n rh_value).
        forward. destruct (Z_lt_dec n 0). 1: lia.
        replace (nth (Z.to_nat n) rh_value Inhabitant_val) with (Znth n rh_value).
        2: rewrite <- Z2Nat.id at 1 by lia; rewrite <- nth_Znth'; reflexivity.
        thaw FR. clear Hlocal1 Hlocal2 n0. unfold heap_rep. Intros.
        replace (space_start (nth_space h from)) with (space_start (nth_space h' from)) by
          (destruct Hweakhr as [Hw _]; symmetry; apply Hw).
        remember (graph_rep g' * heap_unused_rep h' * remset_rep sh g' rmst') as P.
        pose proof graph_and_heap_rest_data_at_ _ _ _ Hghgf' Hghc' as Hgenat.
        unfold generation_data_at_ in Hgenat. fold (available_size h' from).
        assert (Hgens: gen_start g' from = start_address (nth_gen g' from)) by
          (unfold gen_start; now rewrite if_true). rewrite <- !Haddrf'. rewrite Hgens in Hgenat.
        remember (start_address (nth_gen g' from)) as fp.
        remember (nth_sh g' from) as fsh. remember (available_size h' from) as gn.
        remember (WORD_SIZE * gn)%Z as fn.
        assert (Pweak: P |-- (weak_derives P (memory_block fsh fn fp * TT) && emp) * P). {
          apply weak_derives_strong. subst. sep_apply Hgenat.
          rewrite data_at__memory_block.
          rewrite sizeof_tarray_int_or_ptr; [Intros; cancel | unfold available_size].
          destruct (available_space_tight_range (nth_space h' from)). assumption. }
        subst rh_value. remember (Znth n (map _ _)) as rh_value. rewrite Znth_map in Heqrh_value.
        2: rewrite Zlength_map in Hrhs; rewrite <- Hrhs; assumption.
        remember (Znth n (nth_remset_space rh' from)) as item. rewrite Zlength_map in Hrhs.
        assert (Hric: remset_item_compatible g' from rmst' item). {
          hnf in Hrrhc'. rewrite Forall_forall_Znth in Hrrhc'.
          assert (0 <= (Z.of_nat from) < Zlength rh') by (eapply gen_range_remset_heap; eassumption).
          specialize (Hrrhc' _ H). hnf in Hrrhc'. rewrite Forall_forall_Znth in Hrrhc'.
          rewrite <- nth_remset_space_Znth in Hrrhc'. rewrite Hrhs in Hnrange.
          specialize (Hrrhc' _ Hnrange). rewrite <- Heqitem in Hrrhc'. assumption. } destruct item.
        -- simpl in Heqrh_value. subst rh_value. simpl in Hric. rename Hric into Hinv.
           gather_SEP (graph_rep _) (heap_unused_rep _) (remset_rep _ _ _). rewrite <- HeqP.
           replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
             (entailer !!; assumption). Intros.
           assert (P |-- (weak_derives P (valid_pointer v * TT) && emp) * P) as Hweakp. {
             subst. cancel. apply andp_right. 2: cancel.
             assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS. apply derives_weak.
             sep_apply (remset_rep_valid_pointer sh g' rmst' v SH0 Hinv). cancel. }
           replace_SEP 1 ((weak_derives P (valid_pointer v * TT) && emp) * P) by
             (entailer !!; assumption). Intros.
           forward_call (fsh, fp, fn, v, P). Intros vret. destruct vret as [Hvin | Hvnot].
           ++ subst. sep_apply (v_in_range_graph_remset_rep_FF sh g' h' rmst' from v).
              assert_PROP False by entailer !. contradiction.
           ++ forward_if (EX g3: LGraph, EX h3: part_heap, EX rh3: remset_heap, EX rmst3: remset,
                          PROP ((g3, h3, rh3, rmst3) = forward_remset_item from to
                                                         (g', h', rh', rmst') (RemSetExterior v))
                          LOCAL (temp _q
                                   (offset_val (WORD_SIZE * (available_size h' from + n))
                                      (space_start (nth_space h' from)));
                                 temp _from_rem_limit
                                   (offset_val (WORD_SIZE * total_size h' from)
                                      (space_start (nth_space h' from)));
                                 temp _from_limit
                                   (offset_val (WORD_SIZE * available_size h' from)
                                      (space_start (nth_space h' from)));
                                 temp _from_start (space_start (nth_space h' from));
                                 temp _from (space_address hp from);
                                 temp _to (space_address hp to);
                                 temp _next (heap_next_address hp to))
                  SEP (heap_rep sh h3 hp; all_string_constants rsh gv; outlier_rep outlier;
                       graph_rep g3; heap_remset_rep g3 h3 rh3; remset_rep sh g3 rmst3)).
              2: contradiction.
              ** subst P. clear H Pweak Hweakp Hgenat. Intros.
                 gather_SEP (heap_struct_rep _ _ _) (heap_unused_rep _). fold (heap_rep sh h' hp).
                 pose proof get_remset_ext_In v rmst' Hinv as Hrin.
                 pose proof get_remset_ext_address v rmst' Hinv as Hraddr.
                 sep_apply (remset_rep_ext_ramif sh from to g' rmst' _ _ Hrin Hraddr).
                 Intros. set (OTHERS := _ -* _).
                 rewrite remset_ext_rep_forward_p_rep, get_remset_ext_address.
                 rewrite <- Hgens, Heqfn, Heqgn. fold (limit_address g' h' from).
                 remember (get_remset_ext _ _ _) as rext. remember (FwdPntExtr _) as fpe.
                 assert (Hpc: forward_p_compatible fpe outlier g' from). {
                   subst fpe. simpl. fold (remset_ext_compatible g' outlier rext).
                   eapply remset_graph_outlier_compatible_In; eauto. } rewrite Heqfpe.
                 forward_call (rsh, sh, gv, g', h', hp, outlier, from, to, 0,
                                FwdPntExtr (remset_ext2exterior_t rext), Some v).
                 Intros vret. destruct vret as [g2 h2]. rename H into Hfgh.
                 Opaque forward_graph_and_heap. simpl in Hfgh. subst fpe. simpl in Hpc.
                 simpl forward_p_rep. simpl fst. simpl snd. fold (remset_ext2forward_t rext) in Hfgh.
                 assert (Hd: data_at sh int_or_ptr_type
                               (exterior2val g2 (upd_exterior from to g' (remset_ext2exterior_t rext))) v
                             = remset_ext_rep sh g' (upd_remset_ext from to g' rext)). {
                   erewrite fgh_remset_ext_rep_upd_eq; eauto.
                   - destruct rext; simpl in Hraddr |- *; [subst v0 | subst v1]; auto.
                   - destruct rext; simpl in Hpc |- *; auto. }
                 rewrite Hd. clear Hd. subst OTHERS.
                 gather_SEP (remset_ext_rep _ _ _) (_ -* _). sep_apply wand_frame_elim''.
                 erewrite fgh_O_remset_rep_update_eq; eauto.
                 2: eapply remset_graph_outlier_compatible_weakened; eassumption.
                 assert (Hftc: forward_t_compatible (remset_ext2forward_t rext) g'). {
                   unfold remset_ext2forward_t. eapply exterior_forward_t_compatible; eassumption. }
                 assert (Hghc2: graph_heap_compatible g2 h2). {
                   eapply forward_graph_and_heap_O_ghc with (g := g'); eauto. }
                 assert (Hghgt2: graph_has_gen g2 to). {
                   pose proof (fr_forward_graph_and_heap_eq from to O
                     (remset_ext2forward_t rext) g' h' g2 h2 Hfgh) as Hfr.
                   erewrite <- fr_graph_has_gen; eassumption. }
                 assert (Hgsc: generation_space_compatible g2 (to, nth_gen g2 to, nth_space h2 to)) by
                   (apply gt_gs_compatible; assumption). destruct Hgsc as [Haddrt2 [Hsht2 Hsizet2]].
                 assert (Hptrt2: isptr (space_start (nth_space h2 to))) by
                   (rewrite <- Haddrt2; apply start_isptr). unfold heap_rep. Intros.
                 freeze [0; 1; 2; 3; 5; 6] FR.
                 localize [space_struct_rep sh hp h2 to].
                 unfold space_struct_rep, space_quad.
                 forward.
                 forward.
                 simpl force_val. rewrite sem_sub_pi_available_space_minus; auto.
                 forward.
                 replace_SEP 0 (space_struct_rep sh hp (incr_remset_heap h2 (Z.of_nat to)) to). {
                   entailer !!. unfold space_struct_rep, space_quad.
                   rewrite irh_used_space, irh_space_start, irh_total_space, irh_available_space_same.
                   - cancel.
                   - eapply gen_range_heap; eassumption.
                   - assert (0 < remset_gen_size h' from - n) by (unfold remset_gen_size; lia).
                     eapply forward_graph_and_heap_O_gestc in Hfgh; eauto. 2: lia. clear -Hfgh H.
                     red in Hfgh. pose proof unmarked_gen_size_nonneg g2 from.
                     unfold rest_gen_size in Hfgh. lia. }
                 unlocalize [heap_struct_rep sh
                               (map space_quad (spaces (incr_remset_heap h2 (Z.of_nat to)))) hp].
                 1: pose proof gen_range _ _ _ Hghc Hghgt; apply heap_rem_ramif; lia. thaw FR.
                 assert (Htemp: heap_remset_rep g' h' rh' = heap_remset_rep g2 h2 rh') by
                   (eapply fgh_heap_remset_rep; eassumption). rewrite Htemp. clear Htemp.
                 assert (Htemp: 0 < remset_gen_size h' from - n). {
                   unfold remset_gen_size. rewrite <- Heqgn, <- Heqrh_size. lia. }
                 assert (Hgesc2: general_enough_space_to_copy g2 h2 from to
                                   (remset_gen_size h' from - n)) by
                   (eapply forward_graph_and_heap_O_gestc; try eassumption; lia).
                 assert (Hulta: used_space (nth_space h2 to) < available_space (nth_space h2 to)). {
                   red in Hgesc2. pose proof unmarked_gen_size_nonneg g2 from.
                   unfold rest_gen_size in Hgesc2. lia. } clear Htemp Hgesc2.
                 sep_apply (heap_unused_rep_incr g2 h2 to). Intros.
                 gather_SEP (heap_struct_rep _ _ _) (heap_unused_rep _).
                 replace_SEP 0 (heap_rep sh (incr_remset_heap h2 (Z.of_nat to)) hp) by
                   (unfold heap_rep; entailer !!).
                 pose proof generation_share_writable (nth_gen g2 to) as Hws. rewrite Hsht2 in Hws.
                 gather_SEP (data_at_ _ _ _) (heap_remset_rep _ _ _). Intros.
                 assert (Hrhhc2: remset_heap_and_heap_compatible rh' h2). {
                   apply heap_relation_rhhc with h'; auto.
                   eapply heaprel_forward_graph_and_heap_eq; exact Hfgh. }
                 assert ((g2, incr_remset_heap h2 (Z.of_nat to),
                           upd_remset_heap (RemSetExterior v) rh' to,
                           upd_remset from to g' (RemSetExterior v) rmst') =
                           forward_remset_item from to (g', h', rh', rmst') (RemSetExterior v)). {
                   simpl. rewrite get_remset_ext_fact with (Hin := Hinv). rewrite <- Heqrext.
                   rewrite <- Hfgh. reflexivity. }
                 forward.
                 Exists g2 (incr_remset_heap h2 (Z.of_nat to))
                   (upd_remset_heap (RemSetExterior v) rh' to)
                   (upd_remset from to g' (RemSetExterior v) rmst'). unfold limit_address.
                 clear Heqfp. rewrite <- Hgens in Haddrf'.
                 entailer !!. 2: sep_apply remset_rep_upd_ext; auto.
                 rewrite Haddrf'; unfold available_size; f_equal. lia.
              ** Intros g3 h3 rh3 rmst3. rename H into Hfri. forward.
                 Exists (n + 1) g3 h3 rh3 rmst3.
                 pose proof fri_available_size _ _ _ _ _ _ _ _ _ _ _ Hftneq Hfri as Hfas.
                 pose proof fri_total_size _ _ _ _ _ _ _ _ _ _ _ Hftneq Hfri as Hfts.
                 assert (Hfss: space_start (nth_space h3 from) = space_start (nth_space h' from)). {
                   apply forward_remset_item_whr in Hfri. hnf in Hfri. destruct Hfri as [Hfri _].
                   rewrite Hfri. reflexivity. } rewrite Hfas, Hfts, Hfss.
                 assert (Hrheq: nth_remset_space rh from = nth_remset_space rh' from). {
                       eapply fri_fold_rh_same; eauto. pose proof gen_range_heap _ _ _ Hghc Hghgt.
                       clear -H Hrhhc. hnf in Hrhhc. rewrite Forall2_forall_Znth in Hrhhc. lia. }
                 entailer !!. split; [|split].
                 --- rewrite <- nth_remset_space_Znth in *.
                     rewrite Hrheq in *. rewrite sublist_last_1 by lia.
                     rewrite fold_left_app, <- Hfric. auto. rewrite <- Heqitem.
                     Opaque forward_remset_item. simpl. Transparent forward_remset_item. assumption.
                 --- rewrite Hrhs, <- Hrheq in Hnrange.
                     rewrite (rhhc_rssc_len g h rh) in Hnrange; auto. lia.
                 --- f_equal. simpl. unfold WORD_SIZE. lia.
        -- simpl in Heqrh_value. destruct i as [v pos]. subst rh_value. simpl in Hric.
           destruct Hric as [Hghv' [Hpos Hvfrom]].
           gather_SEP (graph_rep _) (heap_unused_rep _) (remset_rep _ _ _). rewrite <- HeqP.
           replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
             (entailer !!; assumption). Intros.
           assert (P |-- (weak_derives P (valid_pointer (offset_val (pos * WORD_SIZE)
                                                           (vertex_address g' v)) * TT) && emp) * P)
             as Hweakp. {
             subst. cancel. apply andp_right. 2: cancel.
             assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS. apply derives_weak.
             sep_apply (graph_rep_interiro_vptr g' v pos). cancel. }
           replace_SEP 1 ((weak_derives P (valid_pointer (offset_val (pos * WORD_SIZE)
                                                            (vertex_address g' v)) * TT) && emp) * P) by
             (entailer !!; assumption). Intros.
           forward_call (fsh, fp, fn, (offset_val (pos * WORD_SIZE)
                                         (vertex_address g' v)), P). Intros vret.
           forward_if (EX g3: LGraph, EX h3: part_heap, EX rh3: remset_heap, EX rmst3: remset,
                       PROP ((g3, h3, rh3, rmst3) =
                               forward_remset_item from to
                                 (g', h', rh', rmst') (RemSetInterior (InteriorVertexPos v pos)))
                       LOCAL (temp _q
                                (offset_val (WORD_SIZE * (available_size h' from + n))
                                   (space_start (nth_space h' from)));
                              temp _from_rem_limit
                                (offset_val (WORD_SIZE * total_size h' from)
                                   (space_start (nth_space h' from)));
                              temp _from_limit
                                (offset_val (WORD_SIZE * available_size h' from)
                                   (space_start (nth_space h' from)));
                              temp _from_start (space_start (nth_space h' from));
                              temp _from (space_address hp from);
                              temp _to (space_address hp to);
                              temp _next (heap_next_address hp to))
                       SEP (heap_rep sh h3 hp; all_string_constants rsh gv; outlier_rep outlier;
                            graph_rep g3; heap_remset_rep g3 h3 rh3; remset_rep sh g3 rmst3)).
           ++ destruct vret as [Hvin | Hvnot].
              1: fold Int.one in H; exfalso; revert H; apply Int.one_not_zero. subst P.
              clear Pweak Hweakp H. Intros.
              sep_apply (graph_and_heap_rest_v_in_range_iff_offset g' h' from v pos). Intros.
              rewrite <- Hgens, Heqfn, Heqgn, H in Hvnot. clear H. specialize (Hvfrom Hvnot).
              gather_SEP (heap_struct_rep _ _ _) (heap_unused_rep _). fold (heap_rep sh h' hp).
              remember (FwdPntIntr (InteriorVertexPos v pos)) as fpi.
              assert (Hpam: forward_p_addr_match fpi None) by (subst; simpl; auto).
              assert (Hpc: forward_p_compatible fpi outlier g' from). {
                subst fpi. simpl. destruct Hvfrom. split; auto. }
              assert (Hfpr: forward_p_rep sh fpi None g' = emp) by (subst fpi; simpl; reflexivity).
              rewrite <- (emp_sepcon (heap_rep sh h' hp)). Intros. rewrite <- Hfpr.
              assert (Hfpa: forward_p_address fpi None g' =
                              offset_val (pos * WORD_SIZE) (vertex_address g' v)). {
                subst fpi. simpl. f_equal; lia. } rewrite <- Hfpa.
              rewrite <- Hgens, Heqfn, Heqgn. fold (limit_address g' h' from).
              forward_call (rsh, sh, gv, g', h', hp, outlier, from, to, 0, fpi, @None val).
              Intros vret. destruct vret as [g2 h2]. rename H into Hfgh. clear Hpam Hpc Hfpr Hfpa.
              subst fpi. simpl in Hfgh. simpl. remember (field2forward _) as ft.
              gather_SEP (all_string_constants _ _) emp. rewrite sepcon_emp.
              erewrite fgh_O_remset_rep_int_eq; eauto. 2: eapply remset_graph_outlier_compatible_weakened; eassumption.
              assert (Hftc: forward_t_compatible ft g'). {
                subst ft; apply vertex_pos_forward_t_compatible; assumption. }
              assert (Hghc2: graph_heap_compatible g2 h2). {
                eapply forward_graph_and_heap_O_ghc with (g := g'); eauto. }
              assert (Hghgt2: graph_has_gen g2 to). {
                pose proof (fr_forward_graph_and_heap_eq from to O ft
                  g' h' g2 h2 Hfgh) as Hfr.
                erewrite <- fr_graph_has_gen; eassumption. }
              assert (Hgsc: generation_space_compatible g2 (to, nth_gen g2 to, nth_space h2 to)) by
                (apply gt_gs_compatible; assumption). destruct Hgsc as [Haddrt2 [Hsht2 Hsizet2]].
              assert (Hptrt2: isptr (space_start (nth_space h2 to))) by
                (rewrite <- Haddrt2; apply start_isptr). unfold heap_rep. Intros.
              freeze [0; 1; 2; 4; 5; 6] FR.
              localize [space_struct_rep sh hp h2 to].
              unfold space_struct_rep, space_quad.
              forward.
              forward.
              simpl force_val. rewrite sem_sub_pi_available_space_minus; auto.
              forward.
              replace_SEP 0 (space_struct_rep sh hp (incr_remset_heap h2 (Z.of_nat to)) to). {
                entailer !!. unfold space_struct_rep, space_quad.
                rewrite irh_used_space, irh_space_start, irh_total_space, irh_available_space_same.
                - cancel.
                - eapply gen_range_heap; eassumption.
                - assert (0 < remset_gen_size h' from - n) by (unfold remset_gen_size; lia).
                  eapply forward_graph_and_heap_O_gestc in Hfgh; eauto. 2: lia. clear -Hfgh H.
                  red in Hfgh. pose proof unmarked_gen_size_nonneg g2 from.
                  unfold rest_gen_size in Hfgh. lia. }
              unlocalize [heap_struct_rep sh
                            (map space_quad (spaces (incr_remset_heap h2 (Z.of_nat to)))) hp].
              1: pose proof gen_range _ _ _ Hghc Hghgt; apply heap_rem_ramif; lia. thaw FR.
              assert (Htemp: heap_remset_rep g' h' rh' = heap_remset_rep g2 h2 rh'). {
                eapply (fgh_heap_remset_rep _ _ _ from _); eassumption. } rewrite Htemp. clear Htemp.
              assert (Htemp: 0 < remset_gen_size h' from - n). {
                unfold remset_gen_size. rewrite <- Heqgn, <- Heqrh_size. lia. }
              assert (Hgesc2: general_enough_space_to_copy g2 h2 from to
                                (remset_gen_size h' from - n)) by
                (eapply forward_graph_and_heap_O_gestc; try eassumption; lia).
              assert (Hulta: used_space (nth_space h2 to) < available_space (nth_space h2 to)). {
                red in Hgesc2. pose proof unmarked_gen_size_nonneg g2 from.
                unfold rest_gen_size in Hgesc2. lia. } clear Htemp Hgesc2.
              sep_apply (heap_unused_rep_incr g2 h2 to). Intros.
              gather_SEP (heap_struct_rep _ _ _) (heap_unused_rep _).
              replace_SEP 0 (heap_rep sh (incr_remset_heap h2 (Z.of_nat to)) hp) by
                (unfold heap_rep; entailer !!).
              pose proof generation_share_writable (nth_gen g2 to) as Hws. rewrite Hsht2 in Hws.
              gather_SEP (data_at_ _ _ _) (heap_remset_rep _ _ _). Intros.
              assert (Hrhhc2: remset_heap_and_heap_compatible rh' h2). {
                apply heap_relation_rhhc with h'; auto.
                eapply heaprel_forward_graph_and_heap_eq; exact Hfgh. }
              assert ((g2, incr_remset_heap h2 (Z.of_nat to),
                        upd_remset_heap (RemSetInterior (InteriorVertexPos v pos)) rh' to,
                        upd_remset from to g' (RemSetInterior (InteriorVertexPos v pos)) rmst') =
                        forward_remset_item from to (g', h', rh', rmst')
                          (RemSetInterior (InteriorVertexPos v pos))). {
                simpl. rewrite <- Nat.eqb_neq in Hvnot. rewrite Hvnot. simpl. rewrite <- Heqft.
                rewrite <- Hfgh. reflexivity. }
              forward.
              Exists g2 (incr_remset_heap h2 (Z.of_nat to))
                (upd_remset_heap (RemSetInterior (InteriorVertexPos v pos)) rh' to)
                (upd_remset from to g' (RemSetInterior (InteriorVertexPos v pos)) rmst').
              unfold limit_address. clear Heqfp. rewrite <- Hgens in Haddrf'.
              entailer !!. 1: rewrite Haddrf'; unfold available_size; f_equal. lia. simpl. cancel.
              pose proof (fr_forward_graph_and_heap_eq from to 0
                (field2forward (Znth pos (make_fields g' v)))
                g' h' g2 h2 Hfgh) as Hfr.
              replace (vertex_address g' v) with (vertex_address g2 v).
              2: { symmetry. eapply fr_vertex_address; eauto. apply graph_has_v_in_closure; assumption. }
              sep_apply remset_rep_upd_int; auto.
           ++ destruct vret as [Hvin | Hvnot]. 2: contradiction. subst P. clear Pweak Hweakp H. Intros.
              sep_apply (graph_and_heap_rest_v_in_range_iff_offset g' h' from v pos). Intros.
              rewrite <- Hgens, Heqfn, Heqgn, H in Hvin. forward. Exists g' h' rh' rmst'.
              entailer !!.
              ** split. 2: f_equal; lia. simpl. rewrite Nat.eqb_refl. simpl. reflexivity.
              ** unfold heap_rep. cancel.
           ++ Intros g3 h3 rh3 rmst3. rename H into Hfri. forward.
              Exists (n + 1) g3 h3 rh3 rmst3.
              pose proof fri_available_size _ _ _ _ _ _ _ _ _ _ _ Hftneq Hfri as Hfas.
              pose proof fri_total_size _ _ _ _ _ _ _ _ _ _ _ Hftneq Hfri as Hfts.
              assert (Hfss: space_start (nth_space h3 from) = space_start (nth_space h' from)). {
                apply forward_remset_item_whr in Hfri. hnf in Hfri. destruct Hfri as [Hfri _].
                rewrite Hfri. reflexivity. } rewrite Hfas, Hfts, Hfss.
              assert (Hrheq: nth_remset_space rh from = nth_remset_space rh' from). {
                eapply fri_fold_rh_same; eauto. pose proof gen_range_heap _ _ _ Hghc Hghgt.
                clear -H Hrhhc. hnf in Hrhhc. rewrite Forall2_forall_Znth in Hrhhc. lia. }
              entailer !!. split; [|split].
              ** rewrite <- nth_remset_space_Znth in *.
                 rewrite Hrheq in *. rewrite sublist_last_1 by lia.
                 rewrite fold_left_app, <- Hfric. auto. rewrite <- Heqitem.
                 Opaque forward_remset_item. simpl. Transparent forward_remset_item. assumption.
              ** rewrite Hrhs, <- Hrheq in Hnrange. rewrite (rhhc_rssc_len g h rh) in Hnrange; auto. lia.
              ** f_equal. simpl. unfold WORD_SIZE. lia.
      * forward. Exists g' h' rh' rmst'. entailer !!. fold (remset_gen_size h from) in Hnrange.
        rewrite <- Hrgseq in Hnrange. unfold remset_gen_size in Hnrange.
        assert (Hn: n = total_size h' from - available_size h' from). {
          clear -H Hnrange Hptrf'. remember (space_start (nth_space h' from)).
          destruct v; try contradiction. simpl in H.
          inversion H. rewrite !Ptrofs.Z_mod_modulus_eq in H1.
          rewrite !(Z.add_comm (Ptrofs.unsigned i)) in H1. assert (Ptrofs.modulus > 0) by rep_lia.
          apply Zmod_plus_inv in H1; auto. rewrite !Ptrofs.unsigned_repr_eq in H1.
          rewrite <- (Z.add_0_r ((WORD_SIZE * (available_size h' from + n)) mod Ptrofs.modulus)) in H1.
          rewrite <- (Z.add_0_r ((WORD_SIZE * (total_size h' from)) mod Ptrofs.modulus)) in H1.
          rewrite !Z.add_mod_idemp_l in H1 by lia. rewrite !Z.add_0_r in H1.
          pose proof total_space_unsigned_range (nth_space h' from). fold (total_size h' from) in H2.
          rewrite !Z.mod_small in H1; [unfold WORD_SIZE in H1; lia | assumption |].
          assert (0 <= available_size h' from + n <= total_size h' from). {
            split. 2: lia. unfold available_size.
            pose proof used_leq_available (nth_space h' from). lia. }
          unfold WORD_SIZE in *; lia. } fold (remset_gen_size h' from) in Hn.
        rewrite Hrgseq in Hn. erewrite compatible_remset_gen_size in Hn; eauto.
        unfold forward_remset_gh. rewrite sublist_same in Hfric; easy.
Qed.

(* Print Assumptions body_forward_remset. *)
