Require Import CertiGraph.CertiGC.gc_spec.
Require Import CertiGraph.msl_ext.ramification_lemmas.
Require Import CertiGraph.CertiGC.forward_lemmas.

Local Open Scope logic.

Lemma body_forward_inR:
 forall (Espec : OracleKind)
    (rsh sh : share) (gv : globals) (fi ti : val) (g : LGraph)
    (t_info : thread_info) (roots : roots_t) 
    (outlier : outlier_t)
    (from to : nat) (depth : Z) (p : VType * Z)
    (SH : readable_share rsh)
    (SH0 : writable_share sh)
    (H : super_compatible (g, t_info, roots) outlier)
    (H0 : forward_p_compatible (inr p) roots g from)
    (H1 : forward_condition g t_info from to)
    (H2 : 0 <= depth <= Int.max_signed)
    (H3 : from <> to),
  semax (func_tycontext f_forward Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _from_start (gen_start g from);
   temp _from_limit (limit_address g t_info from);
   temp _next (next_address t_info to);
   temp _p (forward_p_address (inr p) t_info g); 
   temp _depth (vint depth))
   SEP (all_string_constants rsh gv;
   outlier_rep outlier; graph_rep g; thread_info_rep sh t_info ti))
  (fn_body f_forward)
  (normal_ret_assert
     ((EX (g' : LGraph) (t_info' : thread_info) (roots' : roots_t),
       PROP (super_compatible (g', t_info', roots') outlier;
       roots' = upd_roots from to (inr p) g roots;
       forward_relation from to (Z.to_nat depth)
         (forward_p2forward_t (inr p) roots g) g g';
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
  (* p is Vtype * Z, ie located in graph *)
    destruct p as [v n]. destruct H0 as [? [? [? ?]]]. freeze [0; 1; 3] FR.
    localize [vertex_rep (nth_sh g (vgeneration v)) g v].
    unfold vertex_rep, vertex_at. Intros.
    assert_PROP (offset_val (WORD_SIZE * n) (vertex_address g v) =
                 field_address (tarray int_or_ptr_type
                                       (Zlength (make_fields_vals g v)))
                               [ArraySubsc n] (vertex_address g v)). {
      entailer!. unfold field_address. rewrite if_true; [simpl; f_equal|].
      clear -H20 H11; rewrite <- fields_eq_length in H11.
      unfold field_compatible in *; simpl in *; intuition.
    }
    assert (readable_share (nth_sh g (vgeneration v))) by
      apply writable_readable, generation_share_writable.
    assert (is_pointer_or_integer (Znth n (make_fields_vals g v))). {
      pose proof (mfv_all_is_ptr_or_int g v H9 H10 H0). rewrite Forall_forall in H16.
      apply H16, Znth_In. rewrite fields_eq_length. assumption. } forward.
    gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
    replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v)) g v).
    1: unfold vertex_rep, vertex_at; entailer!.
    unlocalize [graph_rep g]. 1: apply graph_vertex_ramif_stable; assumption. thaw FR.
    unfold make_fields_vals.
    rewrite H12, Znth_map; [|rewrite make_fields_eq_length; assumption].
    assert_PROP (valid_int_or_ptr (field2val g (Znth n (make_fields g v)))). {
      destruct (Znth n (make_fields g v)) eqn:?; [destruct s|].
      - unfold field2val; unfold odd_Z2val.
        replace (2 * z + 1) with (z + z + 1) by lia.
        entailer!. apply valid_int_or_ptr_ii1.
      - unfold field2val, outlier_rep.
        apply in_gcptr_outlier with (gcptr:= g0) (outlier:=outlier) (n:=n) in H0;
          try assumption.
        apply (in_map single_outlier_rep outlier g0) in H0.
        replace_SEP 2 (single_outlier_rep g0). {
          clear -H0.
          apply (list_in_map_inv single_outlier_rep) in H0; destruct H0 as [? [? ?]].
          rewrite H.
          apply (in_map single_outlier_rep) in H0.
          destruct (log_normalize.fold_right_andp
                     (map single_outlier_rep outlier)
                     (single_outlier_rep x) H0).
          rewrite H1. entailer!; now apply andp_left1.
        }
        sep_apply (single_outlier_rep_valid_int_or_ptr g0); entailer!.
      - unfold field2val.
        unfold no_dangling_dst in H10.
        apply H10 with (e:=e) in H0.
        1: sep_apply (graph_rep_valid_int_or_ptr g (dst g e) H0); entailer!.
        unfold get_edges; rewrite <- filter_sum_right_In_iff, <- Heqf.
        now apply Znth_In; rewrite make_fields_eq_length. }
    forward_call (field2val g (Znth n (make_fields g v))).
    remember (graph_rep g * heap_rest_rep (ti_heap t_info) * outlier_rep outlier) as P.
    pose proof (graph_and_heap_rest_data_at_ _ _ _ H7 H).
    unfold generation_data_at_ in H18. remember (gen_start g from) as fp.
    remember (nth_sh g from) as fsh. remember (gen_size t_info from) as gn.
    remember (WORD_SIZE * gn)%Z as fn.
    assert (P |-- (weak_derives P (memory_block fsh fn fp * TT) && emp) * P). {
      apply weak_derives_strong. subst. sep_apply H18.
      rewrite data_at__memory_block.
      rewrite sizeof_tarray_int_or_ptr; [Intros; cancel | unfold gen_size].
      destruct (total_space_tight_range (nth_space t_info from)). assumption. }
    destruct (Znth n (make_fields g v)) eqn:? ; [destruct s|].
    (* Z + GC_Pointer + EType *)
    + (* Z *)
      unfold field2val, odd_Z2val. forward_if.
      1: exfalso; apply H20'; reflexivity.
      forward. Exists g t_info roots. entailer!. split.
      * easy.
      * unfold forward_condition, thread_info_relation.
        simpl. rewrite Heqf, H12. simpl. constructor; [constructor|easy].
    + (* GC_Pointer *)
      destruct g0. unfold field2val, GC_Pointer2val. forward_if.
      2: exfalso; apply Int.one_not_zero; assumption.
      forward_call (Vptr b i). 
      unfold thread_info_rep; Intros.
      gather_SEP (graph_rep _) (heap_rest_rep _) (outlier_rep _).
      rewrite <- HeqP. destruct H5.
      replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
          (entailer; assumption). clear H19. Intros.
      assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
        subst; cancel; apply andp_right; [|cancel].
        assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
        apply derives_weak. assert (In (GCPtr b i) outlier) by
            (eapply in_gcptr_outlier; eauto).
        sep_apply (outlier_rep_valid_pointer outlier (GCPtr b i) H19).
        simpl GC_Pointer2val. cancel. }
      replace_SEP 1 ((weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P) by
          (entailer; assumption). Intros. clear H19.
      forward_call (fsh, fp, fn, (Vptr b i), P).
      Intros vret. destruct vret. (* is_from? *)
      * (* yes *)
        rewrite HeqP. Intros.
        gather_SEP (graph_rep _) (heap_rest_rep _).
        sep_apply H18. rewrite Heqfn in v0.
        pose proof in_gcptr_outlier g (GCPtr b i) outlier n v H0 H6 H11 Heqf.
        sep_apply (outlier_rep_single_rep outlier (GCPtr b i)).
        Intros.
        gather_SEP (data_at_ _ _ _) (single_outlier_rep _).
        change (Vptr b i) with (GC_Pointer2val (GCPtr b i)) in v0.
        pose proof (generation_share_writable (nth_gen g from)).
        change (generation_sh (nth_gen g from)) with (nth_sh g from) in H22.
        rewrite <- Heqfsh in H22. unfold generation_data_at_.
        sep_apply (single_outlier_rep_memory_block_FF (GCPtr b i) fp gn fsh H22 v0).
        assert_PROP False by entailer!. contradiction.
      * (* no *)
        forward_if. 1: exfalso; apply H19'; reflexivity.
        forward. Exists g t_info roots. entailer!.
        -- split3.
           ++ unfold roots_compatible. easy.
           ++ simpl. rewrite Heqf, H12. simpl. constructor.
           ++ easy.
        -- unfold thread_info_rep. entailer!.
    + (* EType *)
      unfold field2val. remember (dst g e) as v'.
      assert (isptr (vertex_address g v')). { (**)
        unfold vertex_address; unfold offset_val.
        remember (vgeneration v') as n'.
        assert (graph_has_v g v'). {
          unfold no_dangling_dst in H10.
          subst. clear -H0 H10 H11 e Heqf.
          apply (H10 v H0).
          unfold get_edges;
          rewrite <- filter_sum_right_In_iff, <- Heqf; apply Znth_In.
          now rewrite make_fields_eq_length.
        }
        destruct H20. rewrite <- Heqn' in H20.
        pose proof (graph_has_gen_start_isptr g n' H20).
        destruct (gen_start g n'); try contradiction; auto.       }
      destruct (vertex_address g v') eqn:?; try contradiction.
      forward_if. 2: exfalso; apply Int.one_not_zero in H21; assumption.
      clear H21 H21'. forward_call (Vptr b i).
      unfold thread_info_rep; Intros.
      gather_SEP (graph_rep _) (heap_rest_rep _) (outlier_rep _).
      rewrite <- HeqP.
      replace_SEP 0
                  ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
          (entailer; assumption).
      clear H19. Intros. assert (graph_has_v g v'). { (**)
        rewrite Heqv'.
        unfold no_dangling_dst in H10.
        clear -H10 H0 e Heqf H11. apply (H10 v H0).
        unfold get_edges.
        rewrite <- filter_sum_right_In_iff.
        rewrite <- Heqf.
        apply Znth_In.
        rewrite make_fields_eq_length; assumption.
      }
      assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
        apply weak_derives_strong. subst.
        remember (dst g e) as v'.
        sep_apply (graph_rep_vertex_rep g v' H19).
        Intros shh. unfold vertex_rep, vertex_at. rewrite Heqv0.
        sep_apply (data_at_valid_ptr
                     shh (tarray int_or_ptr_type (Zlength (make_fields_vals g v')))
                     (make_fields_vals g v') (Vptr b i)).
        - apply readable_nonidentity, writable_readable_share; assumption.
        - simpl. rewrite fields_eq_length.
          pose proof (proj1 (raw_fields_range (vlabel g v'))). rewrite Z.max_r; lia.
        - cancel.
      }
      replace_SEP 1 (weak_derives P (valid_pointer (Vptr b i) * TT) && emp * P)
        by entailer!. clear H21. Intros.
      forward_call (fsh, fp, fn, (Vptr b i), P).
      (* is_from *)
      Intros vv. rewrite HeqP.
      sep_apply (graph_and_heap_rest_v_in_range_iff _ _ _ _ H H7 H19).
      Intros. rewrite <- Heqfp, <- Heqgn, <- Heqfn, Heqv0 in H21. destruct vv.
      * (* yes, is_from *)
        rewrite H21 in v0. clear H21. forward_if.
        2: exfalso; inversion H21.
        freeze [1; 2; 3; 4; 5; 6] FR.
        clear H21 H21'. localize [vertex_rep (nth_sh g (vgeneration v')) g v'].
        unfold vertex_rep, vertex_at. Intros. rewrite v0.
        assert (readable_share (nth_sh g from)) by
            (unfold nth_sh; apply writable_readable, generation_share_writable).
        rewrite <- Heqv0.
        sep_apply (data_at_minus1_address
                     (nth_sh g from) (Z2val (make_header g v')) (vertex_address g v')).
        Intros. forward. clear H22.
        gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
        replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v')) g v') by
            (unfold vertex_rep, vertex_at; entailer!).
        unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H19).
        forward_if.
        -- (* yes, already forwarded *)
          try apply Int64.same_if_eq in H22.
          pose proof (make_header_int_rep_mark_iff g v'). simpl in H23.
          rewrite H23 in H22. clear H23.
          localize [vertex_rep (nth_sh g (vgeneration v')) g v'].
          rewrite v0. unfold vertex_rep, vertex_at. Intros.
          unfold make_fields_vals at 2. rewrite H22.
          assert (0 <= 0 < Zlength (make_fields_vals g v')). {
             split. 1: lia. rewrite fields_eq_length.
             apply (proj1 (raw_fields_range (vlabel g v'))).
          }
          assert (is_pointer_or_integer
                    (vertex_address g (copied_vertex (vlabel g v')))). {
            apply isptr_is_pointer_or_integer. unfold vertex_address.
            rewrite isptr_offset_val.
            apply graph_has_gen_start_isptr, H9; assumption. }
          forward. rewrite Znth_0_cons.
          gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
          replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v')) g v'). {
            unfold vertex_rep, vertex_at. unfold make_fields_vals at 3.
            rewrite H22. entailer!. }
          unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H19).
          localize [vertex_rep (nth_sh g (vgeneration v)) g v].
          unfold vertex_rep, vertex_at. Intros.
          assert (writable_share (nth_sh g (vgeneration v))) by
               (unfold nth_sh; apply generation_share_writable).
          forward.
          sep_apply (field_at_data_at_cancel
                       (nth_sh g (vgeneration v))
                       (tarray int_or_ptr_type (Zlength (make_fields_vals g v)))
                       (upd_Znth n (make_fields_vals g v)
                       (vertex_address g (copied_vertex (vlabel g v'))))
                       (vertex_address g v)).
          gather_SEP (data_at _ _ _ _ ) (data_at _ _ _ _).
          remember (copied_vertex (vlabel g v')).
          remember (labeledgraph_gen_dst g e v1) as g'.
          replace_SEP 0 (vertex_rep (nth_sh g' (vgeneration v)) g' v).
          1: { unfold vertex_rep, vertex_at.
               replace (nth_sh g' (vgeneration v)) with
                   (nth_sh g (vgeneration v)) by (subst g'; reflexivity).
               replace (Zlength (make_fields_vals g' v)) with
                   (Zlength (make_fields_vals g v)) by
                   (subst g'; repeat rewrite fields_eq_length;
                    apply lgd_raw_fld_length_eq).
               rewrite (lgd_mfv_change_in_one_spot g v e v1 n);
                 [|rewrite make_fields_eq_length| | ]; try assumption.
               entailer!. }
          subst g'; subst v1.
          unlocalize [graph_rep (labeledgraph_gen_dst g e
                                                      (copied_vertex (vlabel g v')))].
          1: apply (graph_vertex_lgd_ramif g v e (copied_vertex (vlabel g v')) n);
            try (rewrite make_fields_eq_length); assumption.
          Exists (labeledgraph_gen_dst g e (copied_vertex (vlabel g (dst g e))))
                 t_info roots.
          entailer!.
          2: unfold thread_info_rep; thaw FR; entailer!.
          pose proof (lgd_no_dangling_dst_copied_vert g e (dst g e) H9 H19 H22 H10).
          split; [|split; [|split; [|split]]]; try reflexivity.
          ++ now constructor.
          ++ simpl forward_p2forward_t.
             rewrite H12, Heqf. simpl. now constructor.
          ++ now constructor.
          ++ easy.
        -- (* not yet forwarded *)
           forward. thaw FR.  freeze [0; 1; 2; 3; 4; 5] FR.
           try apply Int64_eq_false in H22.
           pose proof (make_header_int_rep_mark_iff g v'). simpl in H23.
           rewrite H23 in H22. clear H23. apply not_true_is_false in H22.
           rewrite make_header_Wosize by assumption.
           assert (0 <= Z.of_nat to < MAX_SPACES). {
             clear -H H8. destruct H as [_ [_ ?]]. red in H8.
             pose proof (spaces_size (ti_heap t_info)).
             rewrite Zlength_correct in H0. rep_lia. } unfold heap_struct_rep.
           destruct (gt_gs_compatible _ _ H _ H8) as [? [? ?]].
           rewrite nth_space_Znth in *.
           remember (Znth (Z.of_nat to) (spaces (ti_heap t_info))) as sp_to.
           assert (isptr (space_start sp_to)) by (rewrite <- H24; apply start_isptr).
           remember (map space_tri (spaces (ti_heap t_info))).
           assert (@Znth (val * (val * (val* val))) (Vundef, (Vundef, (Vundef, Vundef)))
                         (Z.of_nat to) l = space_tri sp_to). {
             subst l sp_to. rewrite Znth_map by (rewrite spaces_size; rep_lia).
             reflexivity. }
           forward; rewrite H28; unfold space_tri. 1: entailer!.
           forward. simpl sem_binary_operation'.
           rewrite sapi_ptr_val; [| assumption | rep_lia].
           Opaque Znth. forward. Transparent Znth.
           rewrite sapil_ptr_val by easy. rewrite H28. unfold space_tri.
           rewrite <- Z.add_assoc.
           replace (1 + Zlength (raw_fields (vlabel g v'))) with (vertex_size g v') by
               (unfold vertex_size; lia). thaw FR. freeze [0; 2; 3; 4; 5] FR.
           assert (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info))) by
               (rewrite spaces_size; rep_lia).
           assert (Hh: has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info)))
                                 (vertex_size g v')). {
             red. split. 1: pose proof (svs_gt_one g v'); lia.
             transitivity (unmarked_gen_size g (vgeneration v')).
             - apply single_unmarked_le; assumption.
             - red in H1. unfold rest_gen_size in H1. subst from.
               rewrite nth_space_Znth in H1. assumption. }
           assert (Hn: space_start (Znth (Z.of_nat to) (spaces (ti_heap t_info))) <>
                       nullval). {
             rewrite <- Heqsp_to. destruct (space_start sp_to); try contradiction.
             intro Hn. inversion Hn. }
           rewrite (heap_rest_rep_cut
                      (ti_heap t_info) (Z.of_nat to) (vertex_size g v') Hi Hh Hn).
           rewrite <- Heqsp_to. thaw FR.
           gather_SEP (data_at _ _ _ ti) (frames_rep _ _) (data_at _ _ _ _) (heap_rest_rep _).
           replace_SEP 0 (thread_info_rep
                            sh (cut_thread_info t_info _ _ Hi Hh) ti). {
             entailer. unfold thread_info_rep. simpl ti_heap. simpl ti_heap_p. cancel.
             simpl spaces. rewrite <- upd_Znth_map. unfold cut_space.
             unfold space_tri at 3. simpl. unfold heap_struct_rep. cancel.
             apply derives_refl'. do 5 f_equal. f_equal.
             rewrite Vptrofs_unfold_true, ptrofs_to_int64_repr by reflexivity.
             auto.              
             }
           sep_apply (graph_vertex_ramif_stable _ _ H19). Intros.
           freeze [1; 2; 3; 4] FR. rewrite v0.
           remember (nth_sh g from) as shv.
           assert (writable_share (space_sh sp_to)) by
               (rewrite <- H25; apply generation_share_writable).
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
             subst v1. entailer!. unfold field_address.
             simpl. rewrite neg_repr. rewrite sem_add_pi_ptr_special; auto. 2: rep_lia.
             rewrite if_true by assumption. simpl. rewrite !offset_offset_val.
             f_equal. unfold WORD_SIZE. lia. }
           forward. sep_apply (field_at_data_at_cancel
                                 sht (if Archi.ptr64 then tulong else tuint)
                                 (Z2val (make_header g v')) v1). clear H30.
           subst v1. rewrite offset_offset_val.
           replace (vertex_size g v' - 1) with (Zlength (raw_fields (vlabel g v')))
             by (unfold vertex_size; lia).
           replace (WORD_SIZE * used_space sp_to + WORD_SIZE * 1) with
               (WORD_SIZE * (used_space sp_to + 1))%Z by rep_lia.
           remember (offset_val (WORD_SIZE * (used_space sp_to + 1))
                                (space_start sp_to)) as nv.
           thaw FR. freeze [0; 1; 2; 3; 4] FR. rename i into j.
           remember (Zlength (raw_fields (vlabel g v'))) as n'.
           assert (isptr nv) by (subst nv; rewrite isptr_offset_val; assumption).
           remember (field_address heap_type
                                   [StructField _next; ArraySubsc (Z.of_nat to);
                                    StructField _spaces] (ti_heap_p t_info)) as n_addr.
           forward_for_simple_bound
             n'
             (EX i: Z,
              PROP ( )
              LOCAL (temp _new nv;
                     temp _sz (if Archi.ptr64 then Vlong (Int64.repr n') else vint n');
                     temp _v (vertex_address g v');
                     temp _from_start fp;
                     temp _from_limit (offset_val fn fp);
                     temp _next n_addr;
                     temp _p (offset_val (WORD_SIZE * n) (vertex_address g v));
                     temp _depth (vint depth))
              SEP (vertex_rep shv g v';
                   data_at sht (tarray int_or_ptr_type i)
                           (sublist 0 i (make_fields_vals g v')) nv;
                   data_at_ sht (tarray int_or_ptr_type (n' - i))
                            (offset_val (WORD_SIZE * i) nv); FRZL FR))%assert.
           ++ pose proof (raw_fields_range2 (vlabel g v')). simpl in H31.
              now rewrite <- Heqn' in H31.
           ++ rewrite sublist_nil. replace (n' - 0) with n' by lia.
              replace (WORD_SIZE * 0)%Z with 0 by lia.
              rewrite isptr_offset_val_zero by assumption.
              rewrite data_at_zero_array_eq; [entailer! | easy..].
           ++ unfold vertex_rep, vertex_at. Intros.
              rewrite fields_eq_length, <- Heqn'. forward.
              ** entailer!. pose proof (mfv_all_is_ptr_or_int _ _ H9 H10 H19).
                 rewrite Forall_forall in H46. apply H46, Znth_In.
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
                                                     Signed nv (vint i))) =
                    field_address int_or_ptr_type []
                                  (offset_val (WORD_SIZE * i) nv)). {
                   unfold field_address. rewrite if_true by assumption.
                   clear. entailer!. } simpl in H33.
                 gather_SEP (data_at shv _ _ _)
                            (data_at _ (_ n') _ _).
                 replace_SEP 0 (vertex_rep shv g v') by
                     (unfold vertex_rep, vertex_at;
                      rewrite fields_eq_length; entailer!). forward.
                 rewrite offset_offset_val.
                 replace (n' - i - 1) with (n' - (i + 1)) by lia.
                 replace (WORD_SIZE * i + WORD_SIZE * 1) with
                     (WORD_SIZE * (i + 1))%Z by rep_lia.
                 gather_SEP (data_at _ _ _ nv) (field_at _ _ _ _ _).
                 rewrite data_at_mfs_eq;
                                   [entailer! | assumption | subst n'; assumption].
           ++ thaw FR. rewrite v0, <- Heqshv.
              gather_SEP (vertex_rep _ _ _) (_ -* _).
              replace_SEP 0 (graph_rep g) by (entailer!; apply wand_frame_elim).
              rewrite sublist_same by (rewrite ?fields_eq_length; lia).
              replace_SEP 2 emp. {
                replace (n' - n') with 0 by lia. clear. entailer.
                apply data_at__value_0_size. }
              assert (nv = vertex_address g (new_copied_v g to)). {
                subst nv. unfold vertex_address. unfold new_copied_v. simpl. f_equal.
                - unfold vertex_offset. simpl. rewrite H26. reflexivity.
                - unfold gen_start. rewrite if_true by assumption.
                  rewrite H24. reflexivity. }
              gather_SEP (data_at sht _ _ nv) (emp) (data_at sht _ _ _).
              replace_SEP
                0 (vertex_at (nth_sh g to)
                             (vertex_address g (new_copied_v g to))
                             (make_header g v') (make_fields_vals g v')). {
                normalize. rewrite <- H25.
                change (generation_sh (nth_gen g to)) with (nth_sh g to).
                rewrite <- fields_eq_length in Heqn'.
                replace (offset_val (WORD_SIZE * used_space sp_to) (space_start sp_to))
                  with (offset_val (- WORD_SIZE) nv) by
                    (rewrite Heqnv; rewrite offset_offset_val; f_equal; rep_lia).
                rewrite <- H31. unfold vertex_at; entailer!. }
              gather_SEP (vertex_at _ _ _ _) (graph_rep _).
              rewrite (copied_v_derives_new_g g v' to) by assumption.
              freeze [1; 2; 3] FR. remember (lgraph_add_copied_v g v' to) as g'.
              assert (vertex_address g' v' = vertex_address g v') by
                  (subst g'; apply lacv_vertex_address_old; assumption).
              assert (vertex_address g' (new_copied_v g to) =
                      vertex_address g (new_copied_v g to)) by
                  (subst g'; apply lacv_vertex_address_new; assumption).
              rewrite <- H32. rewrite <- H33 in H31.
              assert (writable_share (nth_sh g' (vgeneration v'))) by
                  (unfold nth_sh; apply generation_share_writable).
              assert (graph_has_v g' (new_copied_v g to)) by
                  (subst g'; apply lacv_graph_has_v_new; assumption).
              sep_apply (graph_rep_valid_int_or_ptr _ _ H35). Intros.
              rewrite <- H31 in H36. assert (graph_has_v g' v') by
                  (subst g'; apply lacv_graph_has_v_old; assumption).
              remember (nth_sh g' (vgeneration v')) as sh'.
              sep_apply (graph_vertex_lmc_ramif g' v' (new_copied_v g to) H37).
              rewrite <- Heqsh'. Intros. freeze [1; 2] FR1.
              unfold vertex_rep, vertex_at. Intros.
              sep_apply (data_at_minus1_address
                           sh' (Z2val (make_header g' v')) (vertex_address g' v')).
              Intros. forward. clear H38.
              sep_apply (field_at_data_at_cancel
                           sh' (if Archi.ptr64 then tulong else tuint) (Z2val 0)
                           (offset_val (- WORD_SIZE) (vertex_address g' v'))).
              forward_call (nv). remember (make_fields_vals g' v') as l'.
              assert (0 < Zlength l'). {
                subst l'. rewrite fields_eq_length.
                apply (proj1 (raw_fields_range (vlabel g' v'))). }
              rewrite data_at_tarray_value_split_1 by assumption. Intros.
              assert_PROP (force_val (sem_add_ptr_int int_or_ptr_type Signed
                                                      (vertex_address g' v') (vint 0))
                           =
                           field_address int_or_ptr_type [] (vertex_address g' v')). {
                clear. entailer!. unfold field_address. rewrite if_true by assumption.
                simpl. rewrite isptr_offset_val_zero. 1: reflexivity.
                destruct H7. assumption. }
              forward. clear H39.
              sep_apply (field_at_data_at_cancel
                           sh' int_or_ptr_type nv (vertex_address g' v')).
              gather_SEP (data_at sh' (if Archi.ptr64 then tulong else tuint) _ _)
                         (data_at sh' int_or_ptr_type _ _) (data_at _ _ _ _).
              rewrite H31. subst l'.
              rewrite <- lmc_vertex_rep_eq.
              thaw FR1.
              gather_SEP (vertex_rep _ _ _) (_ -* _).
              sep_apply
                (wand_frame_elim
                   (vertex_rep sh' (lgraph_mark_copied g' v' (new_copied_v g to)) v')
                   (graph_rep (lgraph_mark_copied g' v' (new_copied_v g to)))).
              rewrite <- (lmc_vertex_address g' v' (new_copied_v g to)) in *. subst g'.
              change (lgraph_mark_copied
                        (lgraph_add_copied_v g v' to) v' (new_copied_v g to))
                with (lgraph_copy_v g v' to) in *.
              remember (lgraph_copy_v g v' to) as g'.

              assert (vertex_address g' v' = vertex_address g v') by
              (subst g'; apply lcv_vertex_address_old; assumption).
              assert (vertex_address g' (new_copied_v g to) =
                      vertex_address g (new_copied_v g to)) by
                  (subst g'; apply lcv_vertex_address_new; assumption).
              assert (writable_share (nth_sh g' (vgeneration v'))) by
                  (unfold nth_sh; apply generation_share_writable).
              assert (graph_has_v g' (new_copied_v g to)) by
                  (subst g'; apply lcv_graph_has_v_new; assumption).
              forward_call (nv).
              rewrite <- H31 in *.
              rewrite lacv_vertex_address;
                [|apply graph_has_v_in_closure|]; try assumption.
              rewrite <- H32.
              rewrite <- (lcv_vertex_address g v' to v);
                try rewrite <- (lcv_vertex_address g v' to v) in H14;
                try apply graph_has_v_in_closure; try assumption.
              rewrite (lcv_mfv_Zlen_eq g v v' to H8 H0) in H14. rewrite <- Heqg' in *.
              remember (nth_sh g' (vgeneration v)) as shh.
              remember (make_fields_vals g' v) as mfv.
              remember (new_copied_v g to).
              remember (labeledgraph_gen_dst g' e v1) as g1.
              assert (0 <= n < Zlength (make_fields_vals g' v)) by
                  (subst g'; rewrite fields_eq_length, <- lcv_raw_fields; assumption).
              assert (Znth n (make_fields g' v) = inr e) by
                  (subst g'; unfold make_fields in *;
                   rewrite <- lcv_raw_fields; assumption).
              assert (0 <= n < Zlength (make_fields g' v)) by
                  (rewrite make_fields_eq_length;
                   rewrite fields_eq_length in H43; assumption).
              assert (graph_has_v g' v) by
                  (subst g'; apply lcv_graph_has_v_old; assumption).
              assert (v <> v') by
                  (intro; subst v; clear -v0 H13; lia).
              assert (raw_mark (vlabel g' v) = false) by
                (subst g'; rewrite <- lcv_raw_mark; assumption).
              assert (writable_share shh) by
                  (rewrite Heqshh; unfold nth_sh; apply generation_share_writable).
              localize [vertex_rep (nth_sh g' (vgeneration v)) g' v].
              unfold vertex_rep, vertex_at. Intros.
              rewrite Heqmfv in *; rewrite <- Heqshh.
              forward.
              rewrite H31.
              sep_apply (field_at_data_at_cancel
                           shh
                           (tarray int_or_ptr_type (Zlength (make_fields_vals g' v)))
                           (upd_Znth n (make_fields_vals g' v) (vertex_address g' v1))
                           (vertex_address g' v)).
              gather_SEP (data_at shh _ _ _) (data_at shh _ _ _).
              replace_SEP 0 (vertex_rep (nth_sh g1 (vgeneration v)) g1 v).
              1: { unfold vertex_rep, vertex_at.
                   replace (nth_sh g1 (vgeneration v)) with shh by
                       (subst shh g1; reflexivity).
                   replace (Zlength (make_fields_vals g1 v)) with
                       (Zlength (make_fields_vals g' v)) by
                       (subst g1; repeat rewrite fields_eq_length;
                        apply lgd_raw_fld_length_eq).
                   rewrite (lgd_mfv_change_in_one_spot g' v e v1 n);
                     try assumption. entailer!. }
              subst g1; subst v1.
              unlocalize [graph_rep (labeledgraph_gen_dst g' e (new_copied_v g to))].
              1: apply (graph_vertex_lgd_ramif g' v e (new_copied_v g to) n);
                assumption.
              remember (new_copied_v g to).
              remember (labeledgraph_gen_dst g' e v1) as g1.
              thaw FR.
              remember (cut_thread_info t_info (Z.of_nat to) (vertex_size g v') Hi Hh)
                as t_info'.
              unfold thread_info_rep. Intros.
              assert (0 <= 0 < Zlength (ti_args t_info')) by
                  (rewrite arg_size; rep_lia).
              gather_SEP
                (data_at _ _ _ _)
                (frames_rep _ _ )
                (heap_struct_rep _ _ _)
                (heap_rest_rep _).
              replace_SEP 0 (thread_info_rep sh t_info' ti).
              { unfold thread_info_rep. simpl heap_head. simpl ti_heap_p.
                simpl ti_args. simpl ti_heap. entailer!. }
              rewrite H31 in H33.
                assert (forward_relation from to 0 (inr e) g g1) by
                    (subst g1 g' v1 v'; constructor; assumption).
                assert (In e (get_edges g v)). { (**)
                  unfold get_edges.
                  rewrite <- filter_sum_right_In_iff.
                  rewrite <- Heqf.
                  apply (Znth_In n (make_fields g v)).
                  rewrite make_fields_eq_length. assumption.
                }
                assert (forward_condition g1 t_info' from to). {
                  subst g1 g' t_info' from v'.
                  apply lgd_forward_condition; try assumption.
                  apply lcv_forward_condition_unchanged; try assumption.
                  red. intuition. }
                remember roots as roots'.
                assert (super_compatible (g1, t_info', roots') outlier). {

                  subst g1 g' t_info' roots'.
                  apply lgd_super_compatible, lcv_super_compatible_unchanged;
                    try assumption.
                  red; intuition. }
              assert (thread_info_relation t_info t_info'). {
                subst t_info'. split; [|split]; [reflexivity| |]; intros m.
                - rewrite cti_gen_size. reflexivity.
                - rewrite cti_space_start. reflexivity. }
                forward_if.
              ** destruct H55 as [? [? ?]]. replace fp with (gen_start g1 from) by
                     (subst fp g1 g'; apply lcv_gen_start; assumption).
                 replace (offset_val fn (gen_start g1 from)) with
                     (limit_address g1 t_info' from) by
                     (subst fn gn; rewrite H57; reflexivity).
                 replace n_addr with (next_address t_info' to) by
                     (subst n_addr; rewrite H55; reflexivity).
                 forward_for_simple_bound
                   n'
                   (EX i: Z, EX g3: LGraph, EX t_info3: thread_info,
                    PROP (super_compatible (g3, t_info3, roots') outlier;
                          forward_loop
                            from to (Z.to_nat (depth - 1))
                            (sublist 0 i (vertex_pos_pairs g1 (new_copied_v g to)))
                            g1 g3;
                          forward_condition g3 t_info3 from to;
                          thread_info_relation t_info' t_info3)
                    LOCAL (temp _new nv;
                           temp _sz (if Archi.ptr64 then Vlong (Int64.repr n')
                                     else vint n');
                           temp _from_start (gen_start g3 from);
                           temp _from_limit (limit_address g3 t_info3 from);
                           temp _next (next_address t_info3 to);
                           temp _depth (vint depth))
                    SEP (all_string_constants rsh gv;
                         outlier_rep outlier;
                         graph_rep g3;
                         thread_info_rep sh t_info3 ti))%assert.
                 --- pose proof (raw_fields_range2 (vlabel g v')). simpl in H59.
                     now rewrite <- Heqn' in H59.
                 --- Exists g1 t_info'. autorewrite with sublist.
                     assert (forward_loop from to (Z.to_nat (depth - 1)) [] g1 g1) by
                         constructor. unfold thread_info_relation.
                     destruct H54 as [? [? [? ?]]].
                     entailer!. easy.
                 --- Intros.
                     assert (graph_has_gen g1 to) by
                         (rewrite Heqg1, lgd_graph_has_gen; subst g';
                          rewrite <- lcv_graph_has_gen; assumption).
                     assert (graph_has_v g1 (new_copied_v g to)) by
                       (subst g1; rewrite <- lgd_graph_has_v;
                       rewrite Heqg'; apply lcv_graph_has_v_new; assumption).
                     forward_call (rsh, sh, gv, ti, g3, t_info3, roots',
                                   outlier, from, to, depth - 1,
                                   (@inr Z _ (new_copied_v g to, i))).
                     +++ apply prop_right. simpl. rewrite sub_repr.
                         do 4 f_equal. rewrite H31.
                         first [rewrite sem_add_pi_ptr_special' |
                                rewrite sem_add_pl_ptr_special']; auto.
                         *** simpl. f_equal.
                             rewrite <- (lgd_vertex_address_eq g' e v1), <- Heqg1.
                             subst v1. apply (fl_vertex_address _ _ _ _ _ _ H64 H61).
                             apply graph_has_v_in_closure; assumption.
                         *** rewrite <- H31. assumption.
                     +++ split3; [| |split].
                         *** destruct H53 as [_ [_ [? _]]].
                             apply (fl_graph_has_v _ _ _ _ _ _ H64 H61 _ H65).
                         *** erewrite <- fl_raw_fields; eauto. subst g1.
                             unfold lgraph_copy_v. subst n'.
                             rewrite <- lgd_raw_fld_length_eq.
                             subst g'. rewrite lcv_vlabel_new.
                             assumption. rewrite v0. lia.
                         *** erewrite <- fl_raw_mark; eauto. subst g1 from.
                             rewrite <- lgd_raw_mark_eq. subst g'.
                             rewrite lcv_vlabel_new; try assumption.
                         *** simpl; lia.
                     +++ Intros vret. destruct vret as [[g4 t_info4] roots4].
                         simpl fst in *. simpl snd in *. Exists g4 t_info4.
                         simpl in H67. subst roots4.
                         assert (gen_start g3 from = gen_start g4 from). {
                           eapply fr_gen_start; eauto.
                           erewrite <- fl_graph_has_gen; eauto. } rewrite H67.
                         assert (limit_address g3 t_info3 from =
                                 limit_address g4 t_info4 from). {
                           unfold limit_address. f_equal. 2: assumption. f_equal.
                           destruct H70 as [? [? _]]. rewrite H71. reflexivity. }
                         rewrite H71.
                         assert (next_address t_info3 to = next_address t_info4 to). {
                           unfold next_address. f_equal. destruct H70. assumption. }
                         rewrite H72. clear H67 H71 H72.
                         assert (thread_info_relation t_info' t_info4) by
                             (apply tir_trans with t_info3; assumption).
                         assert (forward_loop
                                   from to (Z.to_nat (depth - 1))
                                   (sublist 0 (i + 1)
                                            (vertex_pos_pairs g1 (new_copied_v g to)))
                                   g1 g4). {
                            eapply forward_loop_add_tail_vpp; eauto. subst n' g1 from.
                           rewrite <- lgd_raw_fld_length_eq. subst g'.
                           rewrite lcv_vlabel_new; assumption. }
                         entailer!.
                 --- Intros g3 t_info3.
                     assert (thread_info_relation t_info t_info3) by
                         (apply tir_trans with t_info';
                          [split; [| split]|]; assumption).
                     rewrite sublist_same in H60; auto.
                     2: { subst n' g1 from.
                          rewrite vpp_Zlength,  <- lgd_raw_fld_length_eq.
                          subst g'; rewrite lcv_vlabel_new; auto. }
                     Opaque super_compatible. Exists g3 t_info3 roots.
                     entailer!. simpl.
                     replace (Z.to_nat depth) with (S (Z.to_nat (depth - 1))) by
                         (rewrite <- Z2Nat.inj_succ; [f_equal|]; lia).
                     rewrite Heqf, H12. simpl.
                     constructor; [reflexivity | assumption..].
                     Transparent super_compatible.
              ** assert (depth = 0) by lia. subst depth. clear H56.
                 deadvars!. clear Heqnv. forward.
                 Exists g1 t_info' roots. entailer!. simpl. rewrite Heqf.
                 simpl field2forward. rewrite H12. simpl. now constructor.
      * forward_if. 1: exfalso; apply H22'; reflexivity.
        rewrite H21 in n0. forward.
        Exists g t_info roots. entailer!; simpl.
        -- rewrite H12, Heqf. simpl. split; auto. split; [|split].
           ++ constructor. auto.
           ++ split; auto.
           ++ apply tir_id.
        -- unfold thread_info_rep. entailer!.
Qed.