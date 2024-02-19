Require Import VST.veric.rmaps.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import Coq.Program.Basics.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.CertiGC.GCGraph.
Require Import VST.msl.wand_frame.
Require Import VST.concurrency.conclib.
Require Import CertiGraph.CertiGC.env_graph_gc.
Require Import CertiGraph.CertiGC.spatial_gcgraph.
Require Import CertiGraph.msl_ext.iter_sepcon. 
Require Import CertiGraph.CertiGC.gc_spec.
Require Import CertiGraph.msl_ext.ramification_lemmas.
Require Import CertiGraph.CertiGC.forward_lemmas.

Local Open Scope logic.

Lemma body_forward_inL:
 forall (Espec : OracleKind)
      (rsh sh : share) (gv : globals) (g : LGraph)
      (h: heap) (hp: val) (rootpairs: list rootpair)
      (roots : roots_t) (outlier : outlier_t)
      (from to : nat)
      (depth z : Z)
      (SH : readable_share rsh) (SH0 : writable_share sh)
      (H: super_compatible g h rootpairs roots outlier)
      (H0 : forward_p_compatible (inl z) roots g from)
      (H1 : forward_condition g h from to)
      (H2 : 0 <= depth <= Int.max_signed)
      (H3 : from <> to),
 semax (func_tycontext f_forward Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _from_start (gen_start g from);
   temp _from_limit (limit_address g h from);
   temp _next (heap_next_address hp to);
   temp _p (forward_p_address' (inl z) rootpairs g); 
   temp _depth (vint depth))
   SEP (all_string_constants rsh gv;
   outlier_rep outlier; graph_rep g; 
   roots_rep sh rootpairs;
   heap_rep sh h hp))
  (fn_body f_forward)
  (normal_ret_assert
     ((EX (g' : LGraph) (h': heap) (roots' : roots_t),
       PROP (super_compatible g' h' (update_rootpairs rootpairs (map (root2val g') roots')) roots' outlier;
       roots' = upd_roots from to (inl z) g roots;
       forward_relation from to (Z.to_nat depth)
         (forward_p2forward_t (inl z) roots g) g g';
       forward_condition g' h' from to;
       heap_relation h h')
       RETURN ( ) SEP (all_string_constants rsh gv; outlier_rep outlier; 
                  graph_rep g'; 
                  roots_rep sh (update_rootpairs rootpairs (map (root2val g') roots'));
                  heap_rep sh h' hp))%argsassert
        * stackframe_of f_forward)).
Proof.
intros.
simpl fn_body.
abbreviate_semax.
  destruct H as [? [? [? ?]]]. destruct H1 as [? [? [? [? ?]]]].
  unfold limit_address, next_address, forward_p_address.
  assert (Zlength rootpairs = Zlength roots)
     by (apply (@f_equal (list val) Z (@Zlength val)) in H4;  list_solve).
  pose (H12 := True).
  remember (Znth z roots) as root.
  red in H0.
  pose proof (Znth_In _ _ H0).
  rewrite <- Heqroot in H13.
     assert (forall v, In (inr v) roots -> isptr (vertex_address g v)). { (**)
      intros. destruct H5. unfold vertex_address. red in H15.
      rewrite Forall_forall in H15.
      rewrite (filter_sum_right_In_iff v roots) in H14. apply H15 in H14.
      destruct H14. apply graph_has_gen_start_isptr in H14. simpl in H14.
      remember (gen_start g (vgeneration v)) as vv. destruct vv; try contradiction.
      simpl. exact I. }
  assert (is_pointer_or_integer (root2val g root)). {
    destruct root as [[? | ?] | ?]; simpl; auto.
    - destruct g0. simpl. exact I.
    - specialize (H14 _ H13). apply isptr_is_pointer_or_integer. assumption. }
  red in H4.
  unfold roots_rep.
  rewrite (sepcon_isolate_nth _ _ z) by list_solve.
  set (OTHER_ROOTS := iter_sepcon _ _).
  rewrite <- (Znth_map _ rp_val) by list_solve.
  rewrite <- H4. rewrite Znth_map by list_solve.
  Intros.
  pose proof I.
  forward. 
    assert_PROP (valid_int_or_ptr (root2val g root)). {
      gather_SEP (graph_rep _) (outlier_rep _).
      sep_apply (root_valid_int_or_ptr _ _ _ _ H13 H5). entailer!. }
    rewrite <- Heqroot.
    forward_call (root2val g root).
    remember (graph_rep g * heap_rest_rep h * outlier_rep outlier)
      as P. pose proof (graph_and_heap_rest_data_at_ _ _ _ H7 H).
    unfold generation_data_at_ in H18. remember (gen_start g from) as fp.
    remember (nth_sh g from) as fsh. remember (gen_size h from) as gn.
    remember (WORD_SIZE * gn)%Z as fn.
    assert (P |-- (weak_derives P (memory_block fsh fn fp * TT) && emp) * P). {
      apply weak_derives_strong. subst. sep_apply H18.
      rewrite data_at__memory_block.
      rewrite sizeof_tarray_int_or_ptr; [Intros; cancel | unfold gen_size].
      destruct (total_space_tight_range (nth_space h from)). assumption. }
    destruct root as [[? | ?] | ?]; simpl root2val.
    + unfold odd_Z2val. forward_if.
      1: exfalso; apply H20'; reflexivity.
      forward. Exists g h roots. rewrite H4, update_rootpairs_same.
      entailer!.
      * simpl; split3. easy.
        unfold upd_root. rewrite <- Heqroot, -> Heqroot, upd_Znth_unchanged'; auto.
        rewrite <- Heqroot.
        split3. constructor. easy. split; reflexivity.
      * unfold roots_rep. 
        rewrite (sepcon_isolate_nth _ _ z) by list_solve.
        fold OTHER_ROOTS.
        apply derives_refl'; f_equal. f_equal. 
        rewrite <- Znth_map, <- H4, Znth_map, <- Heqroot by list_solve. reflexivity.
    + unfold GC_Pointer2val. destruct g0. forward_if.
      2: exfalso; apply Int.one_not_zero in H20; assumption.
      forward_call (Vptr b i).
      unfold heap_rep; Intros.
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
        forward. Exists g h roots.
        rewrite H4, update_rootpairs_same.
        entailer!.
        -- split3; [| |split3]; simpl; try rewrite <- Heqroot;
           [easy | | constructor | hnf; intuition | split; reflexivity ].
             unfold upd_root. rewrite  Heqroot. rewrite upd_Znth_unchanged'; auto.
        -- unfold roots_rep. 
        rewrite (sepcon_isolate_nth _ _ z) by list_solve.
        fold OTHER_ROOTS.
        unfold heap_rep.
        cancel.
        apply derives_refl'; f_equal. 
        rewrite <- Znth_map, <- H4, Znth_map, <- Heqroot by list_solve. reflexivity.
    + assert (OTHER_ROOTS * data_at sh int_or_ptr_type (vertex_address g v) (rp_adr (Znth z rootpairs))
              |-- roots_rep sh 
                  (update_rootpairs rootpairs 
                     (upd_Znth z (map rp_val rootpairs) (vertex_address g v)))). {
              unfold roots_rep.
              rewrite (sepcon_isolate_nth _ _ z) 
                  by (rewrite Zlength_update_rootpairs; list_solve).
              rewrite !Znth_update_rootpairs by list_solve.
              rewrite upd_Znth_same by list_solve.
              simpl.
              cancel.
              unfold OTHER_ROOTS.
              apply derives_refl'. f_equal.
              rewrite Zlength_update_rootpairs by list_solve.
              f_equal; apply Znth_eq_ext; 
               rewrite ?Zlength_update_rootpairs, ?Zlength_sublist by list_solve.
               1,3: rewrite Zlength_sublist by (rewrite ?Zlength_update_rootpairs; list_solve); auto.
               1,2: intros;  rewrite ?Znth_sublist by lia;
               rewrite Znth_update_rootpairs by list_solve;
               rewrite upd_Znth_diff by list_solve;
               rewrite Znth_map by list_solve;
               destruct (Znth _ rootpairs); try reflexivity.
          }
     sep_apply H20. clear H20 OTHER_ROOTS.
    specialize (H14 _ H13). destruct (vertex_address g v) eqn:? ; try contradiction.
      forward_if. 2: exfalso; apply Int.one_not_zero in H20; assumption.
      clear H20 H20'. simpl in H15, H17. forward_call (Vptr b i).
      rewrite <- Heqv0 in *. unfold heap_rep; Intros.
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
        2: exfalso; inversion H20. freeze [1; 2; 3; 4; 5] FR.
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
           unfold roots_rep. 
           rewrite (sepcon_isolate_nth _ _ z) 
           by (rewrite Zlength_update_rootpairs; list_solve).
           rewrite !Znth_update_rootpairs by list_solve.
           rewrite upd_Znth_same by list_solve.
           simpl.
           rewrite ?Zlength_update_rootpairs by list_solve.
           replace (sublist (Z.succ z) _ _) with (sublist (Z.succ z) (Zlength rootpairs) rootpairs).
           replace (sublist 0 z _) with (sublist 0 z rootpairs).
           2,3:
                apply Znth_eq_ext; 
             rewrite ?Zlength_update_rootpairs, ?Zlength_sublist by list_solve;
             rewrite ?Zlength_sublist by (rewrite ?Zlength_update_rootpairs; list_solve); auto;
             intros;  rewrite ?Znth_sublist by lia;
             rewrite Znth_update_rootpairs by list_solve;
             rewrite upd_Znth_diff by list_solve;
             rewrite Znth_map by list_solve;
             destruct (Znth _ rootpairs); try reflexivity.
           set (OTHER_ROOTS := iter_sepcon _ _).
           Intros.
           forward.
           pose (cv := copied_vertex (vlabel g v)).
           pose (rootvals' := upd_Znth z (map (root2val g) roots) (vertex_address g cv)).
           pose (roots' := upd_Znth z roots (inr cv)).
           pose (rootpairs' := update_rootpairs rootpairs (map (root2val g) roots')).
           Exists g h roots'.
           fold rootpairs'.
           entailer!.
           2:{ 
          unfold heap_rep.
           cancel.          
          assert (Zlength rootpairs' = Zlength rootpairs) 
            by (unfold rootpairs', roots'; apply Zlength_update_rootpairs; list_solve). 
          unfold roots_rep.
          rewrite (sepcon_isolate_nth _ _ z) by list_solve.
          rewrite H33.
          unfold rootpairs', roots'.
          rewrite !Znth_update_rootpairs by list_solve. simpl.
          rewrite Znth_map by list_solve.
          rewrite upd_Znth_same by list_solve. fold cv.
          simpl root2val.
          apply sepcon_derives; auto.
          subst OTHER_ROOTS.
          apply derives_refl'.
             f_equal. f_equal;
             apply Znth_eq_ext; 
             rewrite ?Zlength_update_rootpairs, ?Zlength_sublist by list_solve;
             rewrite ?Zlength_sublist by (rewrite ?Zlength_update_rootpairs; list_solve); auto;
             intros;  rewrite ?Znth_sublist by lia;
             rewrite Znth_update_rootpairs by list_solve;
             rewrite <- upd_Znth_map, H4;
             rewrite upd_Znth_diff by list_solve;
             rewrite Znth_map by list_solve;
             destruct (Znth (_ + _) rootpairs); try reflexivity.
           }
           simpl.
           split; split; [|split; [|split] | |split]; auto.
           ++ red. simpl. unfold rootpairs', roots'.
            rewrite <- upd_Znth_map.
            rewrite rp_val_update_rootpairs by list_solve. reflexivity.
           ++ specialize (H9 _ H19 H21). destruct H9 as [? _].
              now apply upd_roots_compatible.
           ++ unfold upd_root. rewrite <- Heqroot, H21.
              now rewrite if_true by reflexivity.
           ++ rewrite <- Heqroot. apply fr_v_in_forwarded; [reflexivity | assumption].
           ++ easy.
        -- forward. thaw FR. freeze [0; 1; 2; 3; 4] FR.
           try apply Int64_eq_false in H21.
           pose proof (make_header_int_rep_mark_iff g v). simpl in H22.
           rewrite H22 in H21. clear H22. apply not_true_is_false in H21.
           rewrite make_header_Wosize by assumption.
           assert (0 <= Z.of_nat to < MAX_SPACES). {
             clear -H H8. destruct H as [_ [_ ?]]. red in H8.
             pose proof (spaces_size h).
             rewrite Zlength_correct in H0. rep_lia. } unfold heap_struct_rep.
           destruct (gt_gs_compatible _ _ H _ H8) as [? [? ?]].
           rewrite nth_space_Znth in *.
           remember (Znth (Z.of_nat to) (spaces h)) as sp_to.
           assert (isptr (space_start sp_to)) by (rewrite <- H23; apply start_isptr).
           remember (map space_tri (spaces h)) as l.
           assert (@Znth (val * (val * (val*val))) (Vundef, (Vundef, (Vundef,Vundef)))
                         (Z.of_nat to) l = space_tri sp_to). {
             subst l sp_to. rewrite Znth_map by (rewrite spaces_size; rep_lia).
             reflexivity. }
           unfold heap_next_address.
           forward; rewrite H27; unfold space_tri. 1: entailer!.
           forward. simpl sem_binary_operation'.
           rewrite sapi_ptr_val; [|assumption | rep_lia].
           Opaque Znth. forward. Transparent Znth.
           rewrite sapil_ptr_val by assumption. rewrite H27. unfold space_tri.
           rewrite <- Z.add_assoc.
           replace (1 + Zlength (raw_fields (vlabel g v))) with (vertex_size g v) by
               (unfold vertex_size; lia). thaw FR. freeze [0; 2; 3; 4; 5] FR.
           assert (Hi : 0 <= Z.of_nat to < Zlength (spaces h)) by
               (rewrite spaces_size; rep_lia).
           assert (Hh: has_space (Znth (Z.of_nat to) (spaces h))
                                 (vertex_size g v)). {
             red. split. 1: pose proof (svs_gt_one g v); lia.
             transitivity (unmarked_gen_size g (vgeneration v)).
             - apply single_unmarked_le; assumption.
             - red in H1. unfold rest_gen_size in H1. subst from.
               rewrite nth_space_Znth in H1. assumption. }
           assert (Hn: space_start (Znth (Z.of_nat to) (spaces h)) <>
                       nullval). {
             rewrite <- Heqsp_to. destruct (space_start sp_to); try contradiction.
             intro Hn. inversion Hn. }
           rewrite (heap_rest_rep_cut
                      h (Z.of_nat to) (vertex_size g v) Hi Hh Hn).
           rewrite <- Heqsp_to. thaw FR. simpl snd. simpl fst.
           gather_SEP (data_at _ heap_type _ _)
                      (heap_rest_rep _).
           replace_SEP 0 (heap_rep sh 
                        (cut_heap h (Z.of_nat to)
                                    (vertex_size g v) Hi Hh)
                         hp). {
             entailer!!.
             unfold heap_rep, heap_struct_rep.
             apply sepcon_derives; [ | apply derives_refl].
             apply derives_refl'; f_equal.
             unfold space_tri at 2. simpl spaces.
             rewrite <- upd_Znth_map. f_equal.
           }
           sep_apply (graph_vertex_ramif_stable _ _ H19). Intros.
           freeze [1; 2; 3; 4; 5] FR. rewrite v0.
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
           thaw FR. freeze [0; 1; 2; 3; 4; 5] FR. rename i into j.
           remember (Zlength (raw_fields (vlabel g v))) as n.
           assert (isptr nv) by (subst nv; rewrite isptr_offset_val; assumption).
           set (p_addr := forward_p_address' _ _ _).
           remember (field_address heap_type
                                   [StructField _next; ArraySubsc (Z.of_nat to);
                                    StructField _spaces] hp) as n_addr.
           forward_for_simple_bound
             n
             (EX i: Z,
              PROP ( )
              LOCAL (temp _newv nv;
                     temp _sz (if Archi.ptr64 then Vlong (Int64.repr n) else vint n);
                     temp _hd (Z2val (make_header g v));
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
                 rewrite Forall_forall in H45. apply H45, Znth_In.
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
              freeze [1; 2; 3; 4] FR. remember (lgraph_add_copied_v g v to) as g'.
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
              remember (cut_heap h (Z.of_nat to) (vertex_size g v) Hi Hh)
                as h'.
              set (fr' := update_rootpairs _ _).
              assert (rp_adr (Znth z fr') = rp_adr (Znth z rootpairs)).
                {subst fr'. rewrite Znth_update_rootpairs by list_solve. reflexivity. }
              unfold forward_p_address'.
              unfold roots_rep.
              rewrite (sepcon_isolate_nth _ _ z)
                 by (unfold fr'; rewrite Zlength_update_rootpairs;  list_solve).
              set (OTHER_ROOTS := iter_sepcon _ _).
              rewrite <- H38.
              Intros.
              forward.
              assert (data_at sh int_or_ptr_type nv (rp_adr (Znth z fr')) * OTHER_ROOTS 
                        |-- roots_rep sh (update_rootpairs rootpairs 
                               (upd_Znth z (map rp_val rootpairs) nv))). {
                  unfold roots_rep.
                  rewrite (sepcon_isolate_nth _ _ z) by 
                     (rewrite Zlength_update_rootpairs; list_solve).
                  rewrite ?Znth_update_rootpairs by list_solve;
                  simpl. rewrite upd_Znth_same by list_solve.
                  rewrite <- H38.
                  cancel.
                  unfold OTHER_ROOTS, fr'.
                  apply derives_refl'; f_equal; f_equal.
                  1,2: apply Znth_eq_ext;
                    rewrite ?Zlength_sublist by (rewrite ?Zlength_update_rootpairs; list_solve);
                    rewrite ?Zlength_update_rootpairs by list_solve; auto.
                  1,2: intros;  rewrite ?Znth_sublist by lia;
                  rewrite ?Znth_update_rootpairs by list_solve;
                  rewrite ?upd_Znth_diff by list_solve;
                  rewrite Znth_map by list_solve;
                  destruct (Znth (_ + _) rootpairs); try reflexivity.
               }
              sep_apply H39; clear H39 OTHER_ROOTS H38.
              drop_LOCAL 10%nat. clear fr'. do 2 drop_LOCAL 0%nat.
              set (rootpairs' := update_rootpairs _ _).
              rewrite H30 in H32.
              assert (forward_relation from to 0 (inl (inr v)) g g') by
                  (subst g'; constructor; assumption).
              assert (forward_condition g' h' from to). {
                subst g' h' from.
                apply lcv_forward_condition; try assumption.
                red. intuition. }
              remember (upd_Znth z roots (inr (new_copied_v g to))) as roots'.
              assert (super_compatible g' h' rootpairs'  roots' outlier). {
                subst g' h' rootpairs' roots'. rewrite H30, H32.
                 apply lcv_super_compatible; try assumption.
                  split3; auto. }
              assert (heap_relation h h'). {
                subst h'. split; intros m.
                - simpl. rewrite utiacti_gen_size. reflexivity.
                - simpl. rewrite utiacti_space_start. reflexivity. }
              forward_if.
              ** forward_if.
                 assert (SCAN': raw_tag (vlabel g v) < NO_SCAN_TAG). {
                   rename H43 into H56. clear - H56 H21. rename H21 into H22.
                   pose proof raw_fields_range (vlabel g v) as H10.
                   pose proof raw_color_range (vlabel g v) as H11.
                   pose proof raw_tag_range (vlabel g v) as H12.
                   destruct (Int.ltu _ _) eqn:?H in H56; try discriminate.
                   clear H56.
                   unfold make_header in H. rewrite H22 in  H; clear H22.
                   forget (raw_color (vlabel g v)) as c.
                   forget (Zlength (raw_fields (vlabel g v))) as f.
                   forget (raw_tag (vlabel g v)) as tag.
                   rewrite !Z.shiftl_mul_pow2 in H by (intro; discriminate).
                   change WORD_SIZE with 8 in *.
                   simpl in *.
                   revert H; really_simplify (Z.pow_pos 2 8);
                     really_simplify (Z.pow_pos 2 10); intro.
                   rewrite and64_repr in H.
                   change 255 with (Z.ones 8) in H.
                   rewrite Z.land_ones in H by (intro; discriminate).
                   simpl in H.
                   change (Z.pow_pos 2 8) with 256 in H.
                   rewrite Z.add_mod in H by (intro; discriminate).
                   change 1024 with (4 * 256)%Z in H.
                   rewrite Z.mul_assoc, Z_mod_mult, Z.add_0_r, Z.mod_mod in H by (intro; discriminate).
                   rewrite Z.add_mod in H by (intro; discriminate).
                   rewrite Z_mod_mult, Z.add_0_r, Z.mod_mod in H by (intro; discriminate).
                   assert (0 <= tag mod 256 < 256) by (apply Z_mod_lt; reflexivity).
                   rewrite Int64.unsigned_repr in H by rep_lia.
                   apply ltu_repr in H; auto; try rep_lia.
                   rewrite Zmod_small in H by auto.
                   auto.
                } clear H43.
                 destruct H41. replace fp with (gen_start g' from) by
                     (subst fp g'; apply lcv_gen_start; assumption).
                 replace (offset_val fn (gen_start g' from)) with
                     (limit_address g' h' from) by
                     (subst fn gn; rewrite H41; reflexivity).
                 forward_for_simple_bound
                   n
                   (EX i: Z, EX g3: LGraph, EX h3: heap,
                    PROP (super_compatible g3 h3 (update_rootpairs rootpairs (map (root2val g3) roots')) roots' outlier;
                          forward_loop
                            from to (Z.to_nat (depth - 1))
                            (sublist 0 i (vertex_pos_pairs g' (new_copied_v g to)))
                            g' g3;
                          forward_condition g3 h3 from to;
                          heap_relation h' h3)
                    LOCAL (temp _newv nv;
                           temp _sz (if Archi.ptr64 then
                                       Vlong (Int64.repr n) else vint n);
                           temp _from_start (gen_start g3 from);
                           temp _from_limit (limit_address g3 h3 from);
                           temp _next (heap_next_address hp to);
                           temp _depth (vint depth))
                    SEP (all_string_constants rsh gv;
                         outlier_rep outlier;
                         graph_rep g3;
                         roots_rep sh (update_rootpairs rootpairs (map (root2val g3) roots'));
                         heap_rep sh h3 hp))%assert.
                 --- pose proof (raw_fields_range2 (vlabel g v)). simpl in H44.
                     now rewrite <- Heqn in H44.
                 --- Exists g' h'.
                     unfold rootpairs'.
                     autorewrite with sublist.
                     assert (upd_Znth z (map rp_val rootpairs) nv = map (root2val g') roots'). {
                      destruct H40 as [_ [H40 _]]. red in H40.
                      rewrite H40. unfold rootpairs'.
                      rewrite rp_val_update_rootpairs by list_solve. auto.
                     }
                     rewrite <- H44.
                     fold rootpairs'.
                     assert (forward_loop from to (Z.to_nat (depth - 1)) [] g' g') by
                         constructor. unfold heap_relation. entailer!.
                 --- change (Tpointer tvoid {| attr_volatile := false;
                                               attr_alignas := Some 2%N |})
                       with (int_or_ptr_type). Intros.
                     assert (graph_has_gen g' to) by
                         (rewrite Heqg', <- lcv_graph_has_gen; assumption).
                     assert (graph_has_v g' (new_copied_v g to)) by
                         (rewrite Heqg'; apply lcv_graph_has_v_new; assumption).
                     set (rootpairs3 := update_rootpairs _ _) in H45|-*.
                     forward_call (rsh, sh, gv, g3, h3, hp, rootpairs3, roots',
                                   outlier, from, to, depth - 1,
                                   (@inr Z _ (new_copied_v g to, i))).
                     +++ apply prop_right. simpl. rewrite sub_repr, H30.
                         do 4 f_equal.
                         first [rewrite sem_add_pi_ptr_special' |
                                rewrite sem_add_pl_ptr_special']; auto.
                         *** simpl. f_equal. erewrite fl_vertex_address; eauto.
                             subst g'. apply graph_has_v_in_closure. assumption.
                         *** rewrite <- H30. assumption.
                     +++ split3; [| |split3].
                         *** apply (fl_graph_has_v _ _ _ _ _ _ H49 H46 _ H50).
                         *** erewrite <- fl_raw_fields; eauto. subst g'.
                             unfold lgraph_copy_v. subst n.
                             rewrite <- lmc_raw_fields, lacv_vlabel_new.
                             assumption.
                         *** erewrite <- fl_raw_mark; eauto. subst g' from.
                             rewrite lcv_vlabel_new. auto. assumption.
                         *** erewrite <- fl_raw_tag; try eassumption.
                             change (raw_tag _) with (raw_tag (vlabel g' (new_copied_v g to))).
                             rewrite Heqg'.
                             rewrite lcv_vlabel_new; try assumption. lia. simpl. auto.
                         *** simpl. lia.
                     +++ Intros vret. destruct vret as [[g4 h4] roots4].
                         simpl fst in *. simpl snd in *.
                        simpl in H52. subst roots4.
                        Exists g4 h4.
                         assert (gen_start g3 from = gen_start g4 from). {
                           eapply fr_gen_start; eauto.
                           erewrite <- fl_graph_has_gen; eauto. } rewrite H52.
                         assert (limit_address g3 h3 from =
                                 limit_address g4 h4 from). {
                           unfold limit_address. f_equal. 2: assumption. f_equal.
                           destruct H55 as [H57 _]. rewrite H57. reflexivity. }
                         rewrite H56.
                         assert (heap_relation h' h4) by
                             (apply hr_trans with h3; assumption).
                         assert (forward_loop
                                   from to (Z.to_nat (depth - 1))
                                   (sublist 0 (i + 1)
                                            (vertex_pos_pairs g' (new_copied_v g to)))
                                   g' g4). {
                           eapply forward_loop_add_tail_vpp; eauto. subst n g' from.
                           rewrite lcv_vlabel_new; assumption. }
                         subst rootpairs3.
                         revert H51.
                         rewrite update_update_rootpairs by (subst roots'; list_solve).
                         entailer!.
                 --- Intros g3 h3.
                     assert (heap_relation h h3) by
                         (apply hr_trans with h';
                          [split |]; assumption).
                     rewrite sublist_same in H45; auto.
                     2: { subst n g' from.
                          rewrite vpp_Zlength, lcv_vlabel_new; auto. }
                     Local Opaque super_compatible.
                     Exists g3 h3 roots'. entailer!. simpl.
                     unfold upd_root.
                     rewrite <- Heqroot, H21, if_true by reflexivity. split; auto.
                     replace (Z.to_nat depth) with (S (Z.to_nat (depth - 1))) by
                         (rewrite <- Z2Nat.inj_succ; [f_equal|]; lia).
                     apply fr_v_in_not_forwarded_Sn; easy.
                     Local Transparent super_compatible.
                 ---
                 assert (SCAN': raw_tag (vlabel g v) >= NO_SCAN_TAG). {
                   rename H43 into H56.
                   pose proof raw_fields_range (vlabel g v).
                   pose proof raw_color_range (vlabel g v).
                   pose proof raw_tag_range (vlabel g v).
                   clear - H56 H21 H43 H44 H45.
                   destruct (Int.ltu _ _) eqn:?H in H56.
                   contradiction H56; reflexivity.
                   clear H56.
                   unfold make_header in H. rewrite H21 in  H; clear H21.
                   forget (raw_color (vlabel g v)) as c.
                   forget (Zlength (raw_fields (vlabel g v))) as f.
                   forget (raw_tag (vlabel g v)) as tag.
                   rewrite !Z.shiftl_mul_pow2 in H by (intro; discriminate).
                   change WORD_SIZE with 8 in *.
                   simpl in *.
                   revert H; really_simplify (Z.pow_pos 2 8);
                     really_simplify (Z.pow_pos 2 10); intro.
                   rewrite and64_repr in H.
                   change 255 with (Z.ones 8) in H.
                   rewrite Z.land_ones in H by (intro; discriminate).
                   simpl in H.
                   change (Z.pow_pos 2 8) with 256 in H.
                   rewrite Z.add_mod in H by (intro; discriminate).
                   change 1024 with (4 * 256)%Z in H.
                   rewrite Z.mul_assoc, Z_mod_mult, Z.add_0_r, Z.mod_mod in H by (intro; discriminate).
                   rewrite Z.add_mod in H by (intro; discriminate).
                   rewrite Z_mod_mult, Z.add_0_r, Z.mod_mod in H by (intro; discriminate).
                   assert (0 <= tag mod 256 < 256) by (apply Z_mod_lt; reflexivity).
                   rewrite Int64.unsigned_repr in H by rep_lia.
                   apply ltu_repr_false in H; auto; try rep_lia.
                   rewrite Zmod_small in H by auto.
                   auto.
                 } clear H43.
                 forward.
                 Exists g' h'  (upd_Znth z roots (inr (new_copied_v g to))).
                 subst rootpairs'. rewrite <- Heqroots'.
                 assert (upd_Znth z (map rp_val rootpairs) nv = (map (root2val g') roots')). { 
                  subst g' nv. rewrite Heqroots'. rewrite <- upd_Znth_map.
                  simpl root2val. rewrite <- H4.
                  apply Znth_eq_ext. list_solve. intros.
                  rewrite Zlength_upd_Znth, Zlength_map in H43.
                  destruct (zeq i z).
                  subst i. list_simplify.
                  rewrite !upd_Znth_diff by list_solve.
                  rewrite !Znth_map by list_solve.
                  destruct (Znth i roots) eqn:?H; simpl; auto.
                  symmetry; apply lcv_vertex_address; auto.
                  apply graph_has_v_in_closure.
                  clear - H44 H43 H5. destruct H5 as [_ ?].
                  red in H. rewrite Forall_forall in H. apply H.
                  apply filter_sum_right_In_iff. rewrite <- H44.
                  apply Znth_In; auto.
                 } rewrite H43.
                 entailer!!.
                 unfold upd_roots, upd_root. simpl. rewrite <- Heqroot.
                 rewrite if_true by auto. rewrite H21. split; auto.
                 replace (Z.to_nat depth) with (S (Z.to_nat (depth-1))) by (clear - H42; lia).
                 apply fr_v_in_not_forwarded_noscan; easy.
              ** assert (depth = 0) by lia. subst depth. clear H42.
                 clear Heqnv. forward.
                 Exists g' h' (upd_Znth z roots (inr (new_copied_v g to))).
                 subst rootpairs'.
                 rewrite <- Heqroots'.
                 assert (upd_Znth z (map rp_val rootpairs) nv = (map (root2val g') roots')). { 
                  subst g' nv. rewrite Heqroots'. rewrite <- upd_Znth_map.
                  simpl root2val. rewrite <- H4.
                  apply Znth_eq_ext. list_solve. intros.
                  rewrite Zlength_upd_Znth, Zlength_map in H30.
                  destruct (zeq i z).
                  subst i. list_simplify.
                  rewrite !upd_Znth_diff by list_solve.
                  rewrite !Znth_map by list_solve.
                  destruct (Znth i roots) eqn:?H; simpl; auto.
                  symmetry; apply lcv_vertex_address; auto.
                  apply graph_has_v_in_closure.
                  clear - H42 H30 H5. destruct H5 as [_ ?].
                  red in H. rewrite Forall_forall in H. apply H.
                  apply filter_sum_right_In_iff. rewrite <- H42.
                  apply Znth_In; auto.
                 }
                 rewrite H42.
                 entailer!. clear PNn_addr H45 H46 H44 H43.
                 unfold upd_roots, upd_root. simpl. rewrite <- Heqroot.
                 rewrite if_true by auto. rewrite H21. split; auto.
      * forward_if. 1: exfalso; apply H21'; reflexivity.
        rewrite H20 in n. forward.
        Exists g h roots. entailer!; simpl.
        -- unfold upd_root.
           rewrite <- Heqroot, if_false by assumption.
           clear H27 H26 H24 H25 H23 H22 H21.
           split3; [| |simpl root2forward; constructor]; try easy.
           split3; auto. red. rewrite rp_val_update_rootpairs by list_solve. auto.
           rewrite Heqroot, upd_Znth_unchanged'; auto.
           now constructor.
        -- unfold heap_rep. entailer!.
          apply derives_refl'. f_equal.
          apply Znth_eq_ext.
          rewrite !Zlength_update_rootpairs; list_solve.
          intros.
          rewrite Zlength_update_rootpairs in H28 by list_solve.
          rewrite Znth_update_rootpairs by list_solve.
          rewrite <- H4.
          replace (vertex_address g v) with (root2val g (Znth z roots)).
           rewrite upd_Znth_map, Znth_map by list_solve.
           rewrite upd_Znth_unchanged by list_solve.
           rewrite Znth_update_rootpairs, Znth_map by list_solve.
           replace (root2val g (Znth i0 roots)) with (rp_val (Znth i0 rootpairs)).
           destruct (Znth i0 _); auto.
           rewrite <- Znth_map by lia. rewrite <- H4.
           rewrite Znth_map by lia. auto.
           rewrite <- Heqroot. reflexivity.
Qed.


