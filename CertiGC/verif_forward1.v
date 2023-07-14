Require Import CertiGraph.CertiGC.gc_spec.
Require Import CertiGraph.msl_ext.ramification_lemmas.
Require Import CertiGraph.CertiGC.forward_lemmas.

Local Open Scope logic.

Lemma body_forward_inL:
 forall (Espec : OracleKind)
      (rsh sh : share) (gv : globals) (ti : val) (g : LGraph)
      (t_info : thread_info)
      (roots : roots_t) (outlier : outlier_t)
      (from to : nat)
      (depth z : Z)
      (SH : readable_share rsh) (SH0 : writable_share sh)
      (H : super_compatible (g, t_info, roots) outlier)
      (H0 : forward_p_compatible (inl z) roots g from)
      (H1 : forward_condition g t_info from to)
      (H2 : 0 <= depth <= Int.max_signed)
      (H3 : from <> to),
 semax (func_tycontext f_forward Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _from_start (gen_start g from);
   temp _from_limit (limit_address g t_info from);
   temp _next (next_address t_info to);
   temp _p (forward_p_address (inl z) t_info g); 
   temp _depth (vint depth))
   SEP (all_string_constants rsh gv;
   outlier_rep outlier; graph_rep g; thread_info_rep sh t_info ti))
  (fn_body f_forward)
  (normal_ret_assert
     ((EX (g' : LGraph) (t_info' : thread_info) (roots' : roots_t),
       PROP (super_compatible (g', t_info', roots') outlier;
       roots' = upd_roots from to (inl z) g roots;
       forward_relation from to (Z.to_nat depth)
         (forward_p2forward_t (inl z) roots g) g g';
       forward_condition g' t_info' from to;
       thread_info_relation t_info t_info')
       RETURN ( ) SEP (all_string_constants rsh gv; outlier_rep outlier; 
                  graph_rep g'; thread_info_rep sh t_info' ti))%argsassert
        * stackframe_of f_forward)).
Proof.
intros.
simpl fn_body.
abbreviate_semax.
  destruct H as [? [? [? ?]]]. destruct H1 as [? [? [? [? ?]]]].
  unfold limit_address, next_address, forward_p_address.
  unfold thread_info_rep. Intros.
  pose (H11:=True).
  pose (H12 := True).
  remember (Znth z roots) as root.
  red in H0.
  pose proof (Znth_In _ _ H0).
  rewrite <- Heqroot in H13.
  assert (forall v, In (inr v) roots -> isptr (vertex_address g v)). { (**)
      intros. destruct H5. unfold vertex_address. red in H15.
      rewrite Forall_forall in H15.
      rewrite (filter_sum_right_In_iff v roots) in H14. apply H15 in H14.
      destruct H14. apply graph_has_gen_start_isptr in H14.
      remember (gen_start g (vgeneration v)) as vv. destruct vv; try contradiction.
      simpl. exact I. }
  assert (is_pointer_or_integer (root2val g root)). {
    destruct root as [[? | ?] | ?]; simpl; auto.
    - destruct g0. simpl. exact I.
    - specialize (H14 _ H13). apply isptr_is_pointer_or_integer. assumption. }
  red in H4.
  sep_apply (isolate_frame sh (ti_frames t_info) z);
      [rewrite <- H4, Zlength_map; assumption | ].
    set (W := allp _).
    Intros.
    rewrite <- H4. rewrite Znth_map by lia. rewrite <- Heqroot.
    pose proof I. (*
    assert (0 <= Znth z (live_roots_indices f_info) < MAX_ARGS) by
        (apply (fi_index_range f_info), Znth_In; assumption).*)
    forward. (*1: entailer!.*)
    assert_PROP (valid_int_or_ptr (root2val g root)). {
      gather_SEP (graph_rep _) (outlier_rep _).
      sep_apply (root_valid_int_or_ptr _ _ _ _ H13 H5). entailer!. }
    forward_call (root2val g root).
    remember (graph_rep g * heap_rest_rep (ti_heap t_info) * outlier_rep outlier)
      as P. pose proof (graph_and_heap_rest_data_at_ _ _ _ H7 H).
    unfold generation_data_at_ in H18. remember (gen_start g from) as fp.
    remember (nth_sh g from) as fsh. remember (gen_size t_info from) as gn.
    remember (WORD_SIZE * gn)%Z as fn.
    assert (P |-- (weak_derives P (memory_block fsh fn fp * TT) && emp) * P). {
      apply weak_derives_strong. subst. sep_apply H18.
      rewrite data_at__memory_block.
      rewrite sizeof_tarray_int_or_ptr; [Intros; cancel | unfold gen_size].
      destruct (total_space_tight_range (nth_space t_info from)). assumption. }
    destruct root as [[? | ?] | ?]; simpl root2val.
    + unfold odd_Z2val. forward_if.
      1: exfalso; apply H20'; reflexivity.
      forward. Exists g t_info roots.
      entailer!.
      * simpl; split3; [easy | | ].
        unfold upd_root. rewrite <- Heqroot, -> Heqroot, upd_Znth_unchanged'; auto.
        rewrite <- Heqroot.
        split3; [constructor | easy | apply tir_id].
      * subst W.
        repeat sep_apply allp_sepcon1.
        apply allp_left with (Vlong (Int64.repr (2*z0+1))).
        set (P := data_at _ int_or_ptr_type (Vlong _) _).
        set (Q := frames_rep _ _).
        sep_apply (modus_ponens_wand P Q). clear P. subst Q.
        unfold thread_info_rep.
        replace (Vlong (Int64.repr (2 * z0 + 1))) with (Znth z (frames2roots (ti_frames t_info))).
           2:{ rewrite <- H4. rewrite Znth_map by auto. rewrite <- Heqroot. reflexivity.  }
        rewrite upd_Znth_unchanged by (rewrite <- H4, Zlength_map; auto).
        rewrite update_frames_same.        
        cancel.
    + unfold GC_Pointer2val. destruct g0. forward_if.
      2: exfalso; apply Int.one_not_zero in H20; assumption.
      forward_call (Vptr b i).
      gather_SEP (graph_rep _) (heap_rest_rep _) (outlier_rep _).
      rewrite <- HeqP. destruct H5.
      replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
          (entailer; assumption). clear H19. Intros. simpl root2val in *.
      assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
        subst. cancel. apply andp_right. 2: cancel.
        assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
        apply derives_weak.
        sep_apply (roots_outlier_rep_valid_pointer _ _ _ H13 H5).
        simpl GC_Pointer2val. cancel. }
      replace_SEP 1 ((weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P) by
          (entailer; assumption). Intros. clear H19.
      forward_call (fsh, fp, fn, (Vptr b i), P). Intros v. destruct v.
      * rewrite HeqP. Intros.
        gather_SEP (graph_rep g) (heap_rest_rep _).
        sep_apply H18. rewrite Heqfn in v.
        sep_apply (roots_outlier_rep_single_rep _ _ _ H13 H5). Intros.
        gather_SEP (single_outlier_rep _) (data_at_ _ _ _).
        change (Vptr b i) with (GC_Pointer2val (GCPtr b i)) in v.
        pose proof (generation_share_writable (nth_gen g from)).
        change (generation_sh (nth_gen g from)) with (nth_sh g from) in H19.
        rewrite <- Heqfsh in H19. unfold generation_data_at_.
        sep_apply (single_outlier_rep_memory_block_FF (GCPtr b i) fp gn fsh H19 v).
        assert_PROP False by entailer!. contradiction.
      * forward_if. 1: exfalso; apply H19'; reflexivity.
        forward. Exists g t_info roots.
        entailer!.
        -- split3; [| |split3]; simpl; try rewrite <- Heqroot;
             [ easy |  | constructor | hnf; intuition | apply tir_id].
             unfold upd_root. rewrite  Heqroot. rewrite upd_Znth_unchanged'; auto.
        -- subst W.
        repeat sep_apply allp_sepcon1.
        apply allp_left with (Vptr b i).
        set (P := data_at _ int_or_ptr_type (Vptr b i) _).
        set (Q := frames_rep _ _).
        sep_apply (modus_ponens_wand P Q). clear P. subst Q.
        unfold thread_info_rep.
        replace (Vptr b i) with (Znth z (frames2roots (ti_frames t_info))).
         2:{ rewrite <- H4. rewrite Znth_map by auto. rewrite <- Heqroot. reflexivity.  }
      rewrite upd_Znth_unchanged by (rewrite <- H4, Zlength_map; auto).
      rewrite update_frames_same.        
      cancel.
    + assert (W * data_at sh int_or_ptr_type (vertex_address g v)
                            (frame_root_address (ti_frames t_info) z)
              |-- frames_rep sh
              (update_frames (ti_frames t_info)
                 (upd_Znth z (frames2roots (ti_frames t_info)) (vertex_address g v)))). {
         subst W. sep_apply allp_sepcon1. apply allp_left with (vertex_address g v).
         rewrite sepcon_comm. apply modus_ponens_wand.
                 }
     sep_apply H20. clear H20 W.
    specialize (H14 _ H13). destruct (vertex_address g v) eqn:? ; try contradiction.
      forward_if. 2: exfalso; apply Int.one_not_zero in H20; assumption.
      clear H20 H20'. simpl in H15, H17. forward_call (Vptr b i).
      rewrite <- Heqv0 in *.
      gather_SEP (graph_rep _) (heap_rest_rep _) (outlier_rep _).
      rewrite <- HeqP.
      replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
          (entailer; assumption). clear H19. Intros. assert (graph_has_v g v). {
        destruct H5. red in H19. rewrite Forall_forall in H19. apply H19.
        rewrite <- filter_sum_right_In_iff. assumption. }
      assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
        apply weak_derives_strong. subst. sep_apply (graph_rep_vertex_rep g v H19).
        Intros shh. unfold vertex_rep, vertex_at. remember (make_fields_vals g v).
        sep_apply (data_at_valid_ptr shh (tarray int_or_ptr_type (Zlength l)) l
                                     (vertex_address g v)).
        - apply readable_nonidentity, writable_readable_share. assumption.
        - subst l. simpl. rewrite fields_eq_length.
          rewrite Z.max_r; pose proof (raw_fields_range (vlabel g v)); lia.
        - rewrite Heqv0. cancel.
      }
      replace_SEP 1 (weak_derives P (valid_pointer (Vptr b i) * TT) && emp * P)
        by (entailer; assumption). clear H20. Intros. rewrite <- Heqv0 in *.
      forward_call (fsh, fp, fn, (vertex_address g v), P). Intros vv. rewrite HeqP.
      sep_apply (graph_and_heap_rest_v_in_range_iff _ _ _ _ H H7 H19). Intros.
      rewrite <- Heqfp, <- Heqgn, <- Heqfn in H20. destruct vv.
      * Intros. rewrite H20 in v0. clear H20. forward_if.
        2: exfalso; inversion H20. freeze [1; 2; 3; 4; 5; 6] FR.
        clear H20 H20'. localize [vertex_rep (nth_sh g (vgeneration v)) g v].
        unfold vertex_rep, vertex_at. Intros. rewrite v0.
        assert (readable_share (nth_sh g from)) by
            (unfold nth_sh; apply writable_readable, generation_share_writable).
        sep_apply (data_at_minus1_address (nth_sh g from) (Z2val (make_header g v))
                                          (vertex_address g v)).
        Intros. forward. clear H21.
        gather_SEP (data_at _ (if Archi.ptr64 then tulong else tuint) _ _)
                   (data_at _ _ _ _).
        replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v)) g v) by
            (unfold vertex_rep, vertex_at; entailer!).
        unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H19).
        forward_if.
        -- try apply Int64.same_if_eq in H21.
           pose proof (make_header_int_rep_mark_iff g v). simpl in H22.
           rewrite H22 in H21. clear H22.
           localize [vertex_rep (nth_sh g (vgeneration v)) g v].
           rewrite v0. unfold vertex_rep, vertex_at. Intros.
           unfold make_fields_vals at 2. rewrite H21.
           assert (0 <= 0 < Zlength (make_fields_vals g v)). {
             split. 1: lia. rewrite fields_eq_length.
             apply (proj1 (raw_fields_range (vlabel g v))). }
           assert (is_pointer_or_integer
                     (vertex_address g (copied_vertex (vlabel g v)))). {
             apply isptr_is_pointer_or_integer. unfold vertex_address.
             rewrite isptr_offset_val.
             apply graph_has_gen_start_isptr, H9; assumption. }
           forward. rewrite Znth_0_cons.
           gather_SEP (data_at _ _ _ _)
                      (data_at _ _ _ _).
           replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v)) g v). {
             unfold vertex_rep, vertex_at. unfold make_fields_vals at 3.
             rewrite H21. entailer!. }
           unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H19).
           thaw FR.
           set (fr := update_frames _ _).
           sep_apply (isolate_frame sh fr z).
           {clear - H0 H4. subst fr.
           rewrite <- (Zlength_map _ _ (root2val g)) in H0. rewrite H4 in H0.
           rewrite frames2roots_update_frames. list_solve.
           apply invariants.Zlength_eq. list_solve.
           }
           Intros.
           assert (frame_root_address fr z = frame_root_address (ti_frames t_info) z). {
              subst fr; clear - H0 H4.
              rewrite frame_root_address_same; list_solve. 
           }
           rewrite H24.
           forward. rewrite <- H24 at 2.
           pose (fr' := update_frames (ti_frames t_info)
                    (upd_Znth z (frames2roots (ti_frames t_info)) 
                        (vertex_address g (copied_vertex (vlabel g v))))).
           Exists g (update_thread_info_frames t_info fr')
                  (upd_Znth z roots (inr (copied_vertex (vlabel g v)))).
           unfold thread_info_rep.
           entailer!.
           2:{ simpl; entailer!.
           replace (ti_fp (update_thread_info_frames t_info fr')) with (ti_fp t_info)
             by(unfold ti_fp, fr'; destruct (ti_frames t_info) as [|[? ? ?] ?]; reflexivity).
           cancel.
           sep_apply allp_sepcon2. apply allp_left with (vertex_address g (copied_vertex (vlabel g v))).
           rewrite <- H24.
           eapply derives_trans; [apply modus_ponens_wand| ].
           unfold fr'. unfold fr.
           rewrite frames2roots_update_frames by (apply invariants.Zlength_eq; list_solve).
           rewrite update_update_frames by (apply invariants.Zlength_eq; list_solve).
           rewrite upd_Znth_twice. auto.
           rewrite <- H4, Zlength_map; auto.             
           }
           simpl.
           split; split; [|split; [|split] | |split]; auto.
           ++ red. unfold fr'.
           rewrite frames2roots_update_frames by (apply invariants.Zlength_eq; list_solve).
            rewrite <- upd_Znth_map. f_equal. auto.
           ++ specialize (H9 _ H19 H21). destruct H9 as [? _].
              now apply upd_roots_compatible.
           ++ unfold upd_root. rewrite <- Heqroot, H21.
              now rewrite if_true by reflexivity.
           ++ rewrite <- Heqroot. apply fr_v_in_forwarded; [reflexivity | assumption].
           ++ easy.
        -- forward. thaw FR. freeze [0; 1; 2; 3; 4; 5] FR.
           try apply Int64_eq_false in H21.
           pose proof (make_header_int_rep_mark_iff g v). simpl in H22.
           rewrite H22 in H21. clear H22. apply not_true_is_false in H21.
           rewrite make_header_Wosize by assumption.
           assert (0 <= Z.of_nat to < MAX_SPACES). {
             clear -H H8. destruct H as [_ [_ ?]]. red in H8.
             pose proof (spaces_size (ti_heap t_info)).
             rewrite Zlength_correct in H0. rep_lia. } unfold heap_struct_rep.
           destruct (gt_gs_compatible _ _ H _ H8) as [? [? ?]].
           rewrite nth_space_Znth in *.
           remember (Znth (Z.of_nat to) (spaces (ti_heap t_info))) as sp_to.
           assert (isptr (space_start sp_to)) by (rewrite <- H23; apply start_isptr).
           remember (map space_tri (spaces (ti_heap t_info))) as l.
           assert (@Znth (val * (val * (val*val))) (Vundef, (Vundef, (Vundef,Vundef)))
                         (Z.of_nat to) l = space_tri sp_to). {
             subst l sp_to. rewrite Znth_map by (rewrite spaces_size; rep_lia).
             reflexivity. }
           forward; rewrite H27; unfold space_tri. 1: entailer!.
           forward. simpl sem_binary_operation'.
           rewrite sapi_ptr_val; [|assumption | rep_lia].
           Opaque Znth. forward. Transparent Znth.
           rewrite sapil_ptr_val by assumption. rewrite H27. unfold space_tri.
           rewrite <- Z.add_assoc.
           replace (1 + Zlength (raw_fields (vlabel g v))) with (vertex_size g v) by
               (unfold vertex_size; lia). thaw FR. freeze [0; 2; 3; 4; 5; 6] FR.
           assert (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info))) by
               (rewrite spaces_size; rep_lia).
           assert (Hh: has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info)))
                                 (vertex_size g v)). {
             red. split. 1: pose proof (svs_gt_one g v); lia.
             transitivity (unmarked_gen_size g (vgeneration v)).
             - apply single_unmarked_le; assumption.
             - red in H1. unfold rest_gen_size in H1. subst from.
               rewrite nth_space_Znth in H1. assumption. }
           assert (Hn: space_start (Znth (Z.of_nat to) (spaces (ti_heap t_info))) <>
                       nullval). {
             rewrite <- Heqsp_to. destruct (space_start sp_to); try contradiction.
             intro Hn. inversion Hn. }
           rewrite (heap_rest_rep_cut
                      (ti_heap t_info) (Z.of_nat to) (vertex_size g v) Hi Hh Hn).
           rewrite <- Heqsp_to. thaw FR.
           gather_SEP (data_at _ thread_info_type _ _)
                      (data_at _ heap_type _ _)
                      (heap_rest_rep _)
                      (frames_rep _ _).
           replace_SEP 0 (thread_info_rep sh 
                            (update_thread_info_frames
                             (cut_thread_info t_info _ _ Hi Hh)
                             (update_frames (ti_frames t_info)
                               (upd_Znth z (frames2roots (ti_frames t_info))
                                  (vertex_address g v)))) ti). {
             entailer. unfold thread_info_rep. simpl ti_heap. simpl ti_heap_p. cancel.
             simpl spaces. rewrite <- upd_Znth_map. unfold cut_space.
             unfold space_tri at 3. simpl. unfold heap_struct_rep. cancel.
             apply derives_refl'. do 5 f_equal.
             f_equal. unfold ti_fp.
             destruct (ti_frames t_info) as [|[? ? ?]?]; simpl; auto.
           }
           sep_apply (graph_vertex_ramif_stable _ _ H19). Intros.
           freeze [1; 2; 3; 4] FR. rewrite v0.
           remember (nth_sh g from) as shv.
           assert (writable_share (space_sh sp_to)) by
               (rewrite <- H24; apply generation_share_writable).
           remember (space_sh sp_to) as sht.
           rewrite (data_at__tarray_value _ _ 1). 2: unfold vertex_size; rep_lia.
           Intros.
           remember (offset_val (WORD_SIZE * used_space sp_to) (space_start sp_to)).
           rewrite (data_at__int_or_ptr_integer sht v1).
           assert_PROP
             (force_val (sem_add_ptr_int
                           (if Archi.ptr64 then tulong else tuint) Signed
                           (offset_val (WORD_SIZE * (used_space sp_to + 1))
                                       (space_start sp_to))
                           (eval_unop Oneg tint (vint 1))) =
              field_address (if Archi.ptr64 then tulong else tuint) [] v1). {
             subst v1. entailer!. simpl. rewrite neg_repr.
             rewrite sem_add_pi_ptr_special; auto. 2: rep_lia. simpl in *.
             unfold field_address. rewrite if_true by assumption.
             simpl. rewrite !offset_offset_val. f_equal. unfold WORD_SIZE. lia. }
           forward. sep_apply (field_at_data_at_cancel
                                 sht (if Archi.ptr64 then tulong else tuint)
                                 (Z2val (make_header g v)) v1). clear H29.
           subst v1. rewrite offset_offset_val.
           replace (vertex_size g v - 1) with (Zlength (raw_fields (vlabel g v)))
             by (unfold vertex_size; lia).
           replace (WORD_SIZE * used_space sp_to + WORD_SIZE * 1) with
               (WORD_SIZE * (used_space sp_to + 1))%Z by rep_lia.
           remember (offset_val (WORD_SIZE * (used_space sp_to + 1))
                                (space_start sp_to)) as nv.
           thaw FR. freeze [0; 1; 2; 3; 4] FR. rename i into j.
           remember (Zlength (raw_fields (vlabel g v))) as n.
           assert (isptr nv) by (subst nv; rewrite isptr_offset_val; assumption).
           remember (frame_root_address (ti_frames t_info) z) as p_addr.
           remember (field_address heap_type
                                   [StructField _next; ArraySubsc (Z.of_nat to);
                                    StructField _spaces] (ti_heap_p t_info)) as n_addr.
           forward_for_simple_bound
             n
             (EX i: Z,
              PROP ( )
              LOCAL (temp _new nv;
                     temp _sz (if Archi.ptr64 then Vlong (Int64.repr n) else vint n);
                     temp _v (vertex_address g v);
                     temp _from_start fp;
                     temp _from_limit (offset_val fn fp);
                     temp _next n_addr;
                     temp _p p_addr;
                     temp _depth (vint depth))
              SEP (vertex_rep shv g v;
                   data_at sht (tarray int_or_ptr_type i)
                           (sublist 0 i (make_fields_vals g v)) nv;
                   data_at_ sht (tarray int_or_ptr_type (n - i))
                            (offset_val (WORD_SIZE * i) nv); FRZL FR))%assert.
           ++ pose proof (raw_fields_range2 (vlabel g v)). simpl in H30.
              now rewrite <- Heqn in H30.
           ++ rewrite sublist_nil. replace (n - 0) with n by lia.
              replace (WORD_SIZE * 0)%Z with 0 by lia.
              rewrite isptr_offset_val_zero by assumption.
              rewrite data_at_zero_array_eq;
                [|reflexivity | assumption | reflexivity]. entailer!.
           ++ unfold vertex_rep, vertex_at. Intros.
              rewrite fields_eq_length, <- Heqn. forward.
              ** entailer!. pose proof (mfv_all_is_ptr_or_int _ _ H9 H10 H19).
                 rewrite Forall_forall in H43. apply H43, Znth_In.
                 rewrite fields_eq_length. assumption.
              ** rewrite (data_at__tarray_value _ _ 1) by lia. Intros.
                 rewrite data_at__singleton_array_eq.
                 assert_PROP
                   (field_compatible int_or_ptr_type []
                                     (offset_val (WORD_SIZE * i) nv)) by
                     (sep_apply (data_at__local_facts
                                   sht int_or_ptr_type
                                   (offset_val (WORD_SIZE * i) nv)); entailer!).
                 assert_PROP
                   ((if Archi.ptr64 then
                      force_val (sem_add_ptr_long int_or_ptr_type
                                                  nv (Vlong (Int64.repr i)))
                     else force_val (sem_add_ptr_int int_or_ptr_type
                                                     Signed nv (vint i)))=
                    field_address int_or_ptr_type []
                                  (offset_val (WORD_SIZE * i) nv)). {
                   unfold field_address. rewrite if_true by assumption.
                   clear. entailer!. } simpl in H32.
                 gather_SEP (data_at _ _ _
                                     (offset_val (- WORD_SIZE) (vertex_address g v)))
                            (data_at _ _ _ (vertex_address g v)).
                 replace_SEP 0 (vertex_rep shv g v) by
                     (unfold vertex_rep, vertex_at;
                      rewrite fields_eq_length; entailer!). forward.
                 rewrite offset_offset_val.
                 replace (n - i - 1) with (n - (i + 1)) by lia.
                 replace (WORD_SIZE * i + WORD_SIZE * 1) with
                     (WORD_SIZE * (i + 1))%Z by lia.
                 gather_SEP (data_at sht _ _ nv) (field_at _ _ _ _ _).
                 rewrite data_at_mfs_eq. 2: assumption.
                 2: subst n; assumption. entailer!.
           ++ thaw FR. rewrite v0, <- Heqshv.
              gather_SEP (vertex_rep _ _ _) (_ -* _).
              replace_SEP 0 (graph_rep g) by (entailer!; apply wand_frame_elim).
              rewrite sublist_same by (rewrite ?fields_eq_length; lia).
              replace_SEP 2 emp. {
                replace (n - n) with 0 by lia. clear. entailer.
                apply data_at__value_0_size. }
              assert (nv = vertex_address g (new_copied_v g to)). {
                subst nv. unfold vertex_address. unfold new_copied_v. simpl. f_equal.
                - unfold vertex_offset. simpl. rewrite H25. reflexivity.
                - unfold gen_start. rewrite if_true by assumption.
                  rewrite H23. reflexivity. }
              gather_SEP (data_at _ _ _ nv) (emp)
              (data_at sht (if Archi.ptr64 then tulong else tuint) _ _).
              replace_SEP
                0 (vertex_at (nth_sh g to)
                             (vertex_address g (new_copied_v g to))
                             (make_header g v) (make_fields_vals g v)). {
                normalize. rewrite <- H24.
                change (generation_sh (nth_gen g to)) with (nth_sh g to).
                rewrite <- fields_eq_length in Heqn.
                replace (offset_val (WORD_SIZE * used_space sp_to) (space_start sp_to))
                  with (offset_val (- WORD_SIZE) nv) by
                    (rewrite Heqnv; rewrite offset_offset_val; f_equal; rep_lia).
                rewrite <- H30. unfold vertex_at; entailer!. }
              gather_SEP (vertex_at _ _ _ _) (graph_rep _).
              rewrite (copied_v_derives_new_g g v to) by assumption.
              freeze [1; 2; 3] FR. remember (lgraph_add_copied_v g v to) as g'.
              assert (vertex_address g' v = vertex_address g v) by
                  (subst g'; apply lacv_vertex_address_old; assumption).
              assert (vertex_address g' (new_copied_v g to) =
                      vertex_address g (new_copied_v g to)) by
                  (subst g'; apply lacv_vertex_address_new; assumption).
              rewrite <- H31. rewrite <- H32 in H30.
              assert (writable_share (nth_sh g' (vgeneration v))) by
                  (unfold nth_sh; apply generation_share_writable).
              assert (graph_has_v g' (new_copied_v g to)) by
                  (subst g'; apply lacv_graph_has_v_new; assumption).
              sep_apply (graph_rep_valid_int_or_ptr _ _ H34). Intros.
              rewrite <- H30 in H35. assert (graph_has_v g' v) by
                  (subst g'; apply lacv_graph_has_v_old; assumption).
              remember (nth_sh g' (vgeneration v)) as sh'.
              sep_apply (graph_vertex_lmc_ramif g' v (new_copied_v g to) H36).
              rewrite <- Heqsh'. Intros. freeze [1; 2] FR1.
              unfold vertex_rep, vertex_at. Intros.
              sep_apply (data_at_minus1_address
                           sh' (Z2val (make_header g' v)) (vertex_address g' v)).
              Intros. forward. clear H37. try rewrite Int.signed_repr by rep_lia.
              sep_apply (field_at_data_at_cancel
                           sh' (if Archi.ptr64 then tulong else tuint)
                           (if Archi.ptr64 then (Vlong (Int64.repr 0)) else (vint 0))
                           (offset_val (- WORD_SIZE) (vertex_address g' v))).
              forward_call (nv). remember (make_fields_vals g' v) as l'.
              assert (0 < Zlength l'). {
                subst l'. rewrite fields_eq_length.
                apply (proj1 (raw_fields_range (vlabel g' v))). }
              rewrite data_at_tarray_value_split_1 by assumption. Intros.
              assert_PROP (force_val (sem_add_ptr_int int_or_ptr_type Signed
                                                      (vertex_address g' v) (vint 0)) =
                           field_address int_or_ptr_type [] (vertex_address g' v)). {
                clear. entailer!. unfold field_address. rewrite if_true by assumption.
                simpl. rewrite isptr_offset_val_zero. 1: reflexivity.
                destruct H7. assumption. } forward. clear H38.
              sep_apply (field_at_data_at_cancel
                           sh' int_or_ptr_type nv (vertex_address g' v)).
              gather_SEP
                (data_at _ (if Archi.ptr64 then tulong else tuint) _ _)
                (data_at _ int_or_ptr_type nv _)
                (data_at _ _ _ _).
              rewrite H30. subst l'.
              rewrite <- lmc_vertex_rep_eq.
              thaw FR1.
              gather_SEP (vertex_rep _ _ _) (_ -* _).
              sep_apply
                (wand_frame_elim
                   (vertex_rep sh' (lgraph_mark_copied g' v (new_copied_v g to)) v)
                   (graph_rep (lgraph_mark_copied g' v (new_copied_v g to)))).
              rewrite <- (lmc_vertex_address g' v (new_copied_v g to)) in *. subst g'.
              change (lgraph_mark_copied
                        (lgraph_add_copied_v g v to) v (new_copied_v g to))
                with (lgraph_copy_v g v to) in *.
              remember (lgraph_copy_v g v to) as g'. rewrite <- H30 in *. thaw FR.
              forward_call (nv). subst p_addr.
              remember (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh)
                as t_info'.
              set (fr' := update_frames _ _).
              unfold thread_info_rep. Intros.
              simpl ti_frames.
              sep_apply (isolate_frame sh fr' z). {
                subst fr'. clear - H4 H0. rewrite <- H4.
                rewrite frames2roots_update_frames. list_solve.
                rewrite <- H4. apply invariants.Zlength_eq.
                list_solve.
              }
              set (W := allp _).
              Intros.
              assert (frame_root_address fr' z = frame_root_address (ti_frames t_info) z). {
                     apply frame_root_address_same.
                     clear - H0 H4. rewrite <- H4. list_solve.
                     rewrite <- H4. list_solve.
              }
              rewrite H38.
              forward.
              subst W.
              match goal with |- context [SEPx (?A :: ?B :: _)] =>
                assert (A * B |-- frames_rep sh (update_frames fr' (upd_Znth z (frames2roots fr') nv)))
              end. {
                 sep_apply allp_sepcon2. apply allp_left with nv.
                 rewrite H38.
                 apply modus_ponens_wand.
              }
              sep_apply H39. clear H39. 
              gather_SEP
                (data_at sh thread_info_type _ ti)
                (heap_struct_rep sh _ _)
                (heap_rest_rep _ )
                (frames_rep _ _).
              replace_SEP 0 (thread_info_rep sh
                              (update_thread_info_frames t_info' 
                               (update_frames fr' (upd_Znth z (frames2roots fr') nv))) ti). {
                unfold thread_info_rep. simpl heap_head. simpl ti_heap_p.
                simpl ti_args. simpl ti_heap.
                entailer!. simpl.
                apply derives_refl'. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal.
                unfold cut_thread_info. 
                destruct (ti_frames t_info) as [|[???]]; simpl; try reflexivity.
              }

              subst fr'.
              rewrite frames2roots_update_frames by (apply invariants.Zlength_eq; list_solve).
              rewrite upd_Znth_twice by list_solve.
              rewrite update_update_frames by (apply invariants.Zlength_eq; list_solve).
              set (t :=  update_thread_info_frames _ _). subst t_info'. rename t into t_info'.
              rewrite H30 in H32.
              assert (forward_relation from to 0 (inl (inr v)) g g') by
                  (subst g'; constructor; assumption).
              assert (forward_condition g' t_info' from to). {
                subst g' t_info' from.
                apply lcv_forward_condition; try assumption.
                red. intuition. }
              remember (upd_Znth z roots (inr (new_copied_v g to))) as roots'.
              assert (super_compatible (g', t_info', roots') outlier). {
                subst g' t_info' roots'. rewrite H30, H32.
                apply lcv_super_compatible; try assumption. red. intuition. }
              assert (thread_info_relation t_info t_info'). {
                subst t_info'. split; [|split]; [reflexivity| |]; intros m.
                - rewrite utiacti_gen_size. reflexivity.
                - rewrite utiacti_space_start. reflexivity. }
              forward_if.
              ** destruct H42 as [? [? ?]]. replace fp with (gen_start g' from) by
                     (subst fp g'; apply lcv_gen_start; assumption).
                 replace (offset_val fn (gen_start g' from)) with
                     (limit_address g' t_info' from) by
                     (subst fn gn; rewrite H44; reflexivity).
                 replace n_addr with (next_address t_info' to) by
                     (subst n_addr; reflexivity).
                 change (ti_frames (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh))
                     with (ti_frames t_info). 
                 forward_for_simple_bound
                   n
                   (EX i: Z, EX g3: LGraph, EX t_info3: thread_info,
                    PROP (super_compatible (g3, t_info3, roots') outlier;
                          forward_loop
                            from to (Z.to_nat (depth - 1))
                            (sublist 0 i (vertex_pos_pairs g' (new_copied_v g to)))
                            g' g3;
                          forward_condition g3 t_info3 from to;
                          thread_info_relation t_info' t_info3)
                    LOCAL (temp _new nv;
                           temp _sz (if Archi.ptr64 then
                                       Vlong (Int64.repr n) else vint n);
                           temp _from_start (gen_start g3 from);
                           temp _from_limit (limit_address g3 t_info3 from);
                           temp _next (next_address t_info3 to);
                           temp _depth (vint depth))
                    SEP (all_string_constants rsh gv;
                         outlier_rep outlier;
                         graph_rep g3;
                         thread_info_rep sh t_info3 ti))%assert.
                 --- pose proof (raw_fields_range2 (vlabel g v)). simpl in H46.
                     now rewrite <- Heqn in H46.
                 --- Exists g' t_info'. autorewrite with sublist.
                     assert (forward_loop from to (Z.to_nat (depth - 1)) [] g' g') by
                         constructor. unfold thread_info_relation. entailer!.
                 --- change (Tpointer tvoid {| attr_volatile := false;
                                               attr_alignas := Some 2%N |})
                       with (int_or_ptr_type). Intros.
                     assert (graph_has_gen g' to) by
                         (rewrite Heqg', <- lcv_graph_has_gen; assumption).
                     assert (graph_has_v g' (new_copied_v g to)) by
                         (rewrite Heqg'; apply lcv_graph_has_v_new; assumption).
                     forward_call (rsh, sh, gv, ti, g3, t_info3, roots',
                                   outlier, from, to, depth - 1,
                                   (@inr Z _ (new_copied_v g to, i))).
                     +++ apply prop_right. simpl. rewrite sub_repr, H30.
                         do 4 f_equal.
                         first [rewrite sem_add_pi_ptr_special' |
                                rewrite sem_add_pl_ptr_special']; auto.
                         *** simpl. f_equal. erewrite fl_vertex_address; eauto.
                             subst g'. apply graph_has_v_in_closure. assumption.
                         *** rewrite <- H30. assumption.
                     +++ split3; [| |split].
                         *** apply (fl_graph_has_v _ _ _ _ _ _ H51 H48 _ H52).
                         *** erewrite <- fl_raw_fields; eauto. subst g'.
                             unfold lgraph_copy_v. subst n.
                             rewrite <- lmc_raw_fields, lacv_vlabel_new.
                             assumption.
                         *** erewrite <- fl_raw_mark; eauto. subst g' from.
                             rewrite lcv_vlabel_new. auto. assumption.
                         *** simpl. lia.
                     +++ Intros vret. destruct vret as [[g4 t_info4] roots4].
                         simpl fst in *. simpl snd in *. Exists g4 t_info4.
                         simpl in H54. subst roots4.
                         assert (gen_start g3 from = gen_start g4 from). {
                           eapply fr_gen_start; eauto.
                           erewrite <- fl_graph_has_gen; eauto. } rewrite H54.
                         assert (limit_address g3 t_info3 from =
                                 limit_address g4 t_info4 from). {
                           unfold limit_address. f_equal. 2: assumption. f_equal.
                           destruct H57 as [? [? _]]. rewrite H58. reflexivity. }
                         rewrite H58.
                         assert (next_address t_info3 to = next_address t_info4 to). {
                           unfold next_address. f_equal. destruct H57. assumption. }
                         rewrite H59. clear H54 H58 H59.
                         assert (thread_info_relation t_info' t_info4) by
                             (apply tir_trans with t_info3; assumption).
                         assert (forward_loop
                                   from to (Z.to_nat (depth - 1))
                                   (sublist 0 (i + 1)
                                            (vertex_pos_pairs g' (new_copied_v g to)))
                                   g' g4). {
                           eapply forward_loop_add_tail_vpp; eauto. subst n g' from.
                           rewrite lcv_vlabel_new; assumption. }
                         entailer!.
                 --- Intros g3 t_info3.
                     assert (thread_info_relation t_info t_info3) by
                         (apply tir_trans with t_info';
                          [split; [|split]|]; assumption).
                     rewrite sublist_same in H47; auto.
                     2: { subst n g' from.
                          rewrite vpp_Zlength, lcv_vlabel_new; auto. }
                     Opaque super_compatible.
                     Exists g3 t_info3 roots'. entailer!. simpl.
                     unfold upd_root.
                     rewrite <- Heqroot, H21, if_true by reflexivity. split; auto.
                     replace (Z.to_nat depth) with (S (Z.to_nat (depth - 1))) by
                         (rewrite <- Z2Nat.inj_succ; [f_equal|]; lia).
                     constructor; easy.
                     Transparent super_compatible.
              ** assert (depth = 0) by lia. subst depth. clear H43.
                 clear Heqnv. forward.
                 remember (cut_thread_info
                             t_info (Z.of_nat to) (vertex_size g v) Hi Hh).
                 Exists (lgraph_copy_v g v to) t_info'
                        (upd_Znth z roots (inr (new_copied_v g to))).
                 entailer!. unfold upd_roots, upd_root. simpl; rewrite <- Heqroot.
                 rewrite if_true by reflexivity. rewrite H21; easy.
      * forward_if. 1: exfalso; apply H21'; reflexivity.
        rewrite H20 in n. forward.
        assert (update_frames (ti_frames t_info)
                  (upd_Znth z (frames2roots (ti_frames t_info)) (vertex_address g v))
                = ti_frames t_info). {
                  change (vertex_address g v) with (root2val g (inr v)).
                  rewrite Heqroot. rewrite <- H4.
                  rewrite upd_Znth_map, upd_Znth_unchanged by lia.
                  rewrite H4. Search update_frames frames2roots.
                  rewrite update_frames_same; auto.
                }
        set (t_info' := update_thread_info_frames t_info 
                 (update_frames (ti_frames t_info)
                 (upd_Znth z (frames2roots (ti_frames t_info)) (vertex_address g v)))).
        replace t_info' with t_info.
        2:{ subst t_info'.
           transitivity (update_thread_info_frames t_info (ti_frames t_info)).
           destruct t_info; reflexivity.
           f_equal. auto.           
        }
        Exists g t_info roots. entailer!; simpl.
        -- unfold upd_root.
           rewrite <- Heqroot, if_false by assumption.
           split3; [| |simpl root2forward; constructor]; try easy.
           rewrite Heqroot, upd_Znth_unchanged'; auto.
           now constructor.
        -- unfold thread_info_rep. entailer!.
        rewrite H22; auto.
Qed.
