
Require Import RamifyCoq.CertiGC.gc_spec.
Require Import RamifyCoq.msl_ext.ramification_lemmas.

Lemma root_valid_int_or_ptr: forall g (roots: roots_t) root outlier,
    In root roots ->
    roots_compatible g outlier roots ->
    graph_rep g * outlier_rep outlier |-- !! (valid_int_or_ptr (root2val g root)).
Proof.
  intros. destruct H0. destruct root as [[? | ?] | ?].
  - simpl root2val. unfold odd_Z2val. replace (2 * z + 1) with (z + z + 1) by omega.
    apply prop_right, valid_int_or_ptr_ii1.
  - sep_apply (roots_outlier_rep_single_rep _ _ _ H H0).
    sep_apply (single_outlier_rep_valid_int_or_ptr g0). entailer!.
  - red in H1. rewrite Forall_forall in H1.
    rewrite (filter_sum_right_In_iff v roots) in H.
    apply H1 in H. simpl. sep_apply (graph_rep_valid_int_or_ptr _ _ H). entailer!.
Qed.

Lemma weak_derives_strong: forall (P Q: mpred),
    P |-- Q -> P |-- (weak_derives P Q && emp) * P.
Proof.
  intros. cancel. apply andp_right. 2: cancel.
  assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
  apply derives_weak. assumption.
Qed.

Lemma sapi_ptr_val: forall p m n,
    isptr p -> Int.min_signed <= n <= Int.max_signed ->
    (force_val
       (sem_add_ptr_int int_or_ptr_type Signed (offset_val (WORD_SIZE * m) p)
                        (vint n))) = offset_val (WORD_SIZE * (m + n)) p.
Proof.
  intros. rewrite sem_add_pi_ptr_special.
  - simpl. rewrite offset_offset_val. f_equal. rep_omega.
  - rewrite isptr_offset_val. assumption.
  - assumption.
Qed.

Lemma data_at_mfs_eq: forall g v i sh nv,
    field_compatible int_or_ptr_type [] (offset_val (WORD_SIZE * i) nv) ->
    0 <= i < Zlength (raw_fields (vlabel g v)) ->
    data_at sh (tarray int_or_ptr_type i) (sublist 0 i (make_fields_vals g v)) nv *
    field_at sh int_or_ptr_type [] (Znth i (make_fields_vals g v))
             (offset_val (WORD_SIZE * i) nv) =
    data_at sh (tarray int_or_ptr_type (i + 1))
            (sublist 0 (i + 1) (make_fields_vals g v)) nv.
Proof.
  intros. rewrite field_at_data_at. unfold field_address.
  rewrite if_true by assumption. simpl nested_field_type.
  simpl nested_field_offset. rewrite offset_offset_val.
  replace (WORD_SIZE * i + 0) with (WORD_SIZE * i)%Z by omega.
  rewrite <- (data_at_singleton_array_eq
                sh int_or_ptr_type _ [Znth i (make_fields_vals g v)]) by reflexivity.
  rewrite <- fields_eq_length in H0.
  rewrite (data_at_tarray_value
             sh (i + 1) i nv (sublist 0 (i + 1) (make_fields_vals g v))
             (make_fields_vals g v) (sublist 0 i (make_fields_vals g v))
             [Znth i (make_fields_vals g v)]).
  - replace (i + 1 - i) with 1 by omega. reflexivity.
  - omega.
  - omega.
  - autorewrite with sublist. reflexivity.
  - reflexivity.
  - rewrite sublist_one; [reflexivity | omega..].
Qed.

Lemma data_at__value_0_size: forall sh p,
    data_at_ sh (tarray int_or_ptr_type 0) p |-- emp.
Proof. intros. rewrite data_at__eq. apply data_at_zero_array_inv; reflexivity. Qed.

Lemma data_at_minus1_address: forall sh v p,
    data_at sh tuint v (offset_val (- WORD_SIZE) p) |--
   !! (force_val (sem_add_ptr_int tuint Signed p (eval_unop Oneg tint (vint 1))) =
       field_address tuint [] (offset_val (- WORD_SIZE) p)).
Proof.
  intros. unfold eval_unop. simpl. rewrite WORD_SIZE_eq. entailer!.
  unfold field_address. rewrite if_true by assumption. rewrite offset_offset_val.
  simpl. reflexivity.
Qed.

Lemma body_forward: semax_body Vprog Gprog f_forward forward_spec.
Proof.
  start_function.
  destruct H as [? [? [? ?]]]. destruct H1 as [? [? [? [? ?]]]].
  unfold limit_address, next_address, forward_p_address. destruct forward_p.
  - unfold thread_info_rep. Intros.
    assert (Zlength roots = Zlength (live_roots_indices f_info)) by
        (rewrite <- (Zlength_map _ _ (flip Znth (ti_args t_info))), <- H4, Zlength_map; trivial).
    pose proof (Znth_map _ (root2val g) _ H0). hnf in H0. rewrite H11 in H0.
    rewrite H4, Znth_map in H12 by assumption. unfold flip in H12.
    remember (Znth z roots) as root. rewrite <- H11 in H0.
    pose proof (Znth_In _ _ H0).
    rewrite <- Heqroot in H13. rewrite H11 in H0. unfold Inhabitant_val in H12.
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
    assert (0 <= Znth z (live_roots_indices f_info) < MAX_ARGS) by
        (apply (fi_index_range f_info), Znth_In; assumption).
    forward; rewrite H12. 1: entailer!.
    assert_PROP (valid_int_or_ptr (root2val g root)). {
      gather_SEP 3 2. (* no matching clauses for match *)
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
    + unfold odd_Z2val. apply semax_if_seq. forward_if.
      1: exfalso; apply H20'; reflexivity.
      forward. Exists g t_info roots.
      entailer!. 
      * simpl; split3; try rewrite <- Heqroot; [easy..|].
        split3; [constructor | easy | apply tir_id].
      * unfold thread_info_rep. entailer!.
    + unfold GC_Pointer2val. destruct g0. apply semax_if_seq. forward_if.
      2: exfalso; apply Int.one_not_zero in H20; assumption.
      forward_call (Vptr b i).
      gather_SEP (graph_rep g)
                 (heap_rest_rep (ti_heap t_info)) (outlier_rep outlier).
      (* gather_SEP 3 6 2. *)
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
        gather_SEP (graph_rep g) (heap_rest_rep (ti_heap t_info)).
        sep_apply H18. rewrite Heqfn in v.
        sep_apply (roots_outlier_rep_single_rep _ _ _ H13 H5). Intros.
        gather_SEP (single_outlier_rep (GCPtr b i))
                   (data_at_ fsh (tarray int_or_ptr_type gn) fp).
        change (Vptr b i) with (GC_Pointer2val (GCPtr b i)) in v.
        pose proof (generation_share_writable (nth_gen g from)).
        change (generation_sh (nth_gen g from)) with (nth_sh g from) in H19.
        rewrite <- Heqfsh in H19. unfold generation_data_at_.
        sep_apply (single_outlier_rep_memory_block_FF (GCPtr b i) fp gn fsh H19 v).
        assert_PROP False by entailer!. contradiction.
      * apply semax_if_seq. forward_if. 1: exfalso; apply H19'; reflexivity.
        forward. Exists g t_info roots.
        entailer!.
        -- split3; [| |split3]; simpl; try rewrite <- Heqroot;
             [easy.. | constructor | hnf; intuition | apply tir_id].
        -- unfold thread_info_rep. entailer!.
    + specialize (H14 _ H13). destruct (vertex_address g v) eqn:? ; try contradiction.
      apply semax_if_seq. forward_if.
      2: exfalso; apply Int.one_not_zero in H20; assumption.
      clear H20 H20'. simpl in H15, H17. forward_call (Vptr b i).
      rewrite <- Heqv0 in *.
      (* gather_SEP 3 6 2. *)
      gather_SEP (graph_rep g)
                 (heap_rest_rep _) (outlier_rep _).
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
          rewrite Z.max_r; pose proof (raw_fields_range (vlabel g v)); omega.
        - rewrite Heqv0. cancel.                    
      }
      replace_SEP 1 (weak_derives P (valid_pointer (Vptr b i) * TT) && emp * P)
        by (entailer; assumption). clear H20. Intros. rewrite <- Heqv0 in *.
      forward_call (fsh, fp, fn, (vertex_address g v), P). Intros vv. rewrite HeqP.
      sep_apply (graph_and_heap_rest_v_in_range_iff _ _ _ _ H H7 H19). Intros.
      rewrite <- Heqfp, <- Heqgn, <- Heqfn in H20. destruct vv.
      * Intros. rewrite H20 in v0. clear H20. apply semax_if_seq. forward_if.
        2: exfalso; inversion H20. deadvars!. freeze [1; 2; 3; 4; 5; 6] FR.
        clear H20 H20'. localize [vertex_rep (nth_sh g (vgeneration v)) g v].
        unfold vertex_rep, vertex_at. Intros. rewrite v0.
        assert (readable_share (nth_sh g from)) by
            (unfold nth_sh; apply writable_readable, generation_share_writable).
        sep_apply (data_at_minus1_address (nth_sh g from) (Z2val (make_header g v))
                                          (vertex_address g v)).
        Intros. forward. clear H21.
        gather_SEP
          (data_at (nth_sh g from) tuint (Z2val (make_header g v))
                   (offset_val (- WORD_SIZE) (vertex_address g v)) )
          (data_at (nth_sh g from)
                   (tarray int_or_ptr_type (Zlength (make_fields_vals g v)))
                   (make_fields_vals g v) (vertex_address g v)).
        replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v)) g v) by
            (unfold vertex_rep, vertex_at; entailer!).
        unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H19).
        apply semax_if_seq. forward_if; rewrite make_header_int_rep_mark_iff in H21.
        -- deadvars!. localize [vertex_rep (nth_sh g (vgeneration v)) g v].
           rewrite v0. unfold vertex_rep, vertex_at. Intros.
           unfold make_fields_vals at 2. rewrite H21.
           assert (0 <= 0 < Zlength (make_fields_vals g v)). {
             split. 1: omega. rewrite fields_eq_length.
             apply (proj1 (raw_fields_range (vlabel g v))). }
           assert (is_pointer_or_integer
                     (vertex_address g (copied_vertex (vlabel g v)))). {
             apply isptr_is_pointer_or_integer. unfold vertex_address.
             rewrite isptr_offset_val.
             apply graph_has_gen_start_isptr, H9; assumption. }
           forward. rewrite Znth_0_cons.
           gather_SEP
             (data_at (nth_sh g from) tuint (Z2val (make_header g v))
                      (offset_val (- WORD_SIZE) (vertex_address g v)) )
             (data_at (nth_sh g from)
                      (tarray int_or_ptr_type (Zlength (make_fields_vals g v)))
                      (vertex_address g (copied_vertex (vlabel g v))
                                      :: tl (map (field2val g) (make_fields g v)))
                      (vertex_address g v)).
           replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v)) g v). {
             unfold vertex_rep, vertex_at. unfold make_fields_vals at 3.
             rewrite H21. entailer!. }
           unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H19).
           thaw FR. forward. forward.
           Exists g (upd_thread_info_arg
                       t_info
                       (Znth z (live_roots_indices f_info))
                       (vertex_address g (copied_vertex (vlabel g v))) H16)
                  (upd_bunch z f_info roots (inr (copied_vertex (vlabel g v)))).
           unfold thread_info_rep. simpl. entailer!. split; split; [| | |split].
           ++ apply upd_fun_thread_arg_compatible. assumption.
           ++ specialize (H9 _ H19 H21). destruct H9 as [? _].
              apply upd_roots_compatible; assumption.
           ++ rewrite <- Heqroot, H21.
              now rewrite if_true by reflexivity.
           ++ rewrite <- Heqroot. apply fr_v_in_forwarded; [reflexivity | assumption].
           ++ easy.
        -- forward. thaw FR. freeze [0; 1; 2; 3; 4; 5] FR.
           apply not_true_is_false in H21. rewrite make_header_Wosize by assumption.
           assert (0 <= Z.of_nat to < 12). {
             clear -H H8. destruct H as [_ [_ ?]]. red in H8.
             pose proof (spaces_size (ti_heap t_info)).
             rewrite Zlength_correct in H0. rep_omega. } unfold heap_struct_rep.
           destruct (gt_gs_compatible _ _ H _ H8) as [? [? ?]].
           rewrite nth_space_Znth in *.
           remember (Znth (Z.of_nat to) (spaces (ti_heap t_info))) as sp_to.
           assert (isptr (space_start sp_to)) by (rewrite <- H23; apply start_isptr).
           remember (map space_tri (spaces (ti_heap t_info))) as l.
           assert (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef))
                         (Z.of_nat to) l = space_tri sp_to). {
             subst l sp_to. rewrite Znth_map by (rewrite spaces_size; rep_omega).
             reflexivity. }
           forward; rewrite H27; unfold space_tri. 1: entailer!.
           forward. simpl sem_binary_operation'.
           rewrite sapi_ptr_val; [|assumption | rep_omega].
           Opaque Znth. forward. Transparent Znth.
           assert (Hr: Int.min_signed <= Zlength (raw_fields (vlabel g v)) <=
                       Int.max_signed). {
             pose proof (raw_fields_range (vlabel g v)). destruct H28. split.
             1: rep_omega. transitivity (two_power_nat 22). 1: omega.
             compute; intro s; inversion s. }
           rewrite sapi_ptr_val by assumption. rewrite H27. unfold space_tri.
           rewrite <- Z.add_assoc.
           replace (1 + Zlength (raw_fields (vlabel g v))) with (vertex_size g v) by
               (unfold vertex_size; omega). thaw FR. freeze [0; 2; 3; 4; 5; 6] FR.
           assert (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info))) by
               (rewrite spaces_size; rep_omega).
           assert (Hh: has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info)))
                                 (vertex_size g v)). {
             red. split. 1: pose proof (svs_gt_one g v); omega.
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
           (* gather_SEP 4 5 7. *)
           gather_SEP (data_at sh thread_info_type _ ti) 
                      (data_at sh heap_type _ _) 
                      (heap_rest_rep _).
           replace_SEP 0 (thread_info_rep
                            sh (cut_thread_info t_info _ _ Hi Hh) ti). {
             entailer. unfold thread_info_rep. simpl ti_heap. simpl ti_heap_p. cancel.
             simpl spaces. rewrite <- upd_Znth_map. unfold cut_space.
             unfold space_tri at 3. simpl. unfold heap_struct_rep. cancel. }
           sep_apply (graph_vertex_ramif_stable _ _ H19). Intros.
           freeze [1; 2; 3; 4; 5] FR. deadvars!. rewrite v0.
           remember (nth_sh g from) as shv.
           assert (writable_share (space_sh sp_to)) by
               (rewrite <- H24; apply generation_share_writable).
           remember (space_sh sp_to) as sht.
           rewrite (data_at__tarray_value _ _ 1). 2: unfold vertex_size; rep_omega.
           Intros.
           remember (offset_val (WORD_SIZE * used_space sp_to) (space_start sp_to)).
           rewrite (data_at__int_or_ptr_tuint sht v1).
           assert_PROP
             (force_val (sem_add_ptr_int
                           tuint Signed
                           (offset_val (WORD_SIZE * (used_space sp_to + 1))
                                       (space_start sp_to))
                           (eval_unop Oneg tint (vint 1))) =
              field_address tuint [] v1). {
             subst v1. rewrite WORD_SIZE_eq. entailer!. simpl. rewrite neg_repr.
             rewrite sem_add_pi_ptr_special'; auto. simpl. unfold field_address.
             rewrite if_true by assumption. simpl. rewrite !offset_offset_val.
             f_equal. omega. }
           forward. sep_apply (field_at_data_at_cancel
                                 sht tuint (Z2val (make_header g v)) v1). clear H29.
           subst v1. rewrite offset_offset_val.
           replace (vertex_size g v - 1) with (Zlength (raw_fields (vlabel g v)))
             by (unfold vertex_size; omega).
           replace (WORD_SIZE * used_space sp_to + WORD_SIZE * 1) with
               (WORD_SIZE * (used_space sp_to + 1))%Z by rep_omega.
           remember (offset_val (WORD_SIZE * (used_space sp_to + 1))
                                (space_start sp_to)) as nv.
           thaw FR. freeze [0; 1; 2; 3; 4; 5] FR. rename i into j. deadvars!.
           remember (Zlength (raw_fields (vlabel g v))) as n.
           assert (isptr nv) by (subst nv; rewrite isptr_offset_val; assumption).
           remember (field_address thread_info_type
                                   [ArraySubsc (Znth z (live_roots_indices f_info));
                                    StructField _args] ti) as p_addr.
           remember (field_address heap_type
                                   [StructField _next; ArraySubsc (Z.of_nat to);
                                    StructField _spaces] (ti_heap_p t_info)) as n_addr.
           forward_for_simple_bound
             n
             (EX i: Z,
              PROP ( )
              LOCAL (temp _new nv;
                     temp _sz (vint n);
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
           ++ rewrite sublist_nil. replace (n - 0) with n by omega.
              replace (WORD_SIZE * 0)%Z with 0 by omega.
              rewrite isptr_offset_val_zero by assumption.
              rewrite data_at_zero_array_eq;
                [|reflexivity | assumption | reflexivity]. entailer!.
           ++ unfold vertex_rep, vertex_at. Intros.
              rewrite fields_eq_length, <- Heqn. forward.
              ** entailer!. pose proof (mfv_all_is_ptr_or_int _ _ H9 H10 H19).
                 rewrite Forall_forall in H45. apply H45, Znth_In.
                 rewrite fields_eq_length. assumption.
              ** rewrite (data_at__tarray_value _ _ 1) by omega. Intros.
                 rewrite data_at__singleton_array_eq.
                 assert_PROP
                   (field_compatible int_or_ptr_type []
                                     (offset_val (WORD_SIZE * i) nv)) by
                     (sep_apply (data_at__local_facts
                                   sht int_or_ptr_type
                                   (offset_val (WORD_SIZE * i) nv)); entailer!).
                 assert_PROP
                   (force_val (sem_add_ptr_int int_or_ptr_type
                                               Signed nv (vint i)) =
                    field_address int_or_ptr_type []
                                  (offset_val (WORD_SIZE * i) nv)). {
                   unfold field_address. rewrite if_true by assumption.
                   clear. entailer!. }
                 gather_SEP
                 (data_at shv tuint (Z2val (make_header g v))
                           (offset_val (- WORD_SIZE) (vertex_address g v)))
                    (data_at shv (tarray int_or_ptr_type n) (make_fields_vals g v)
                             (vertex_address g v)). 
                  replace_SEP 0 (vertex_rep shv g v) by
                      (unfold vertex_rep, vertex_at;
                       rewrite fields_eq_length; entailer!). forward.
                 rewrite offset_offset_val.
                 replace (n - i - 1) with (n - (i + 1)) by omega.
                 replace (WORD_SIZE * i + WORD_SIZE * 1) with
                     (WORD_SIZE * (i + 1))%Z by rep_omega.
                 gather_SEP 1 2.
                 (* gather_SEP *)
                 (*   (data_at sht *)
                 (*            (tarray int_or_ptr_type i) *)
                 (*            (sublist 0 i (make_fields_vals g v)) *)
                 (*            nv) *)
                 (*   (field_at sht int_or_ptr_type [] *)
                 (*             (Znth i (make_fields_vals g v)) *)
                 (*             (offset_val (WORD_SIZE * i) nv)). *)
                 (* no matching clauses *)
                 rewrite data_at_mfs_eq. 2: assumption.
                 2: subst n; assumption. entailer!.
           ++ thaw FR. rewrite v0, <- Heqshv.
              gather_SEP 0 4.
              (* gather_SEP (vertex_rep shv g v) (vertex_rep shv g v -* graph_rep g). *)
              (* no matching clauses *)
              replace_SEP 0 (graph_rep g) by (entailer!; apply wand_frame_elim).
              rewrite sublist_all by (rewrite fields_eq_length; omega).
              replace_SEP 2 emp. {
                replace (n - n) with 0 by omega. clear. entailer.
                apply data_at__value_0_size. }
              assert (nv = vertex_address g (new_copied_v g to)). {
                subst nv. unfold vertex_address. unfold new_copied_v. simpl. f_equal.
                - unfold vertex_offset. simpl. rewrite H25. reflexivity.
                - unfold gen_start. rewrite if_true by assumption.
                  rewrite H23. reflexivity. }
              (* gather_SEP 1 2 3. *)
              gather_SEP
              (data_at sht _ _ nv)
              (emp) (data_at sht tuint _ _).
              replace_SEP
                0 (vertex_at (nth_sh g to)
                             (vertex_address g (new_copied_v g to))
                             (make_header g v) (make_fields_vals g v)). {
                normalize. rewrite <- H24.
                change (generation_sh (nth_gen g to)) with (nth_sh g to).
                rewrite <- fields_eq_length in Heqn.
                replace (offset_val (WORD_SIZE * used_space sp_to) (space_start sp_to))
                  with (offset_val (- WORD_SIZE) nv) by
                    (rewrite Heqnv; rewrite offset_offset_val; f_equal; rep_omega).
                rewrite <- H30. unfold vertex_at; entailer!. }
              gather_SEP (vertex_at (nth_sh g to) (vertex_address g (new_copied_v g to))
            (make_header g v) (make_fields_vals g v)) (graph_rep g).
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
              Intros. forward. clear H37.
              sep_apply (field_at_data_at_cancel
                           sh' tuint (vint 0)
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
              (* gather_SEP 1 0 3. *)
              gather_SEP
                (data_at sh' tuint (vint 0) _) 
                (data_at sh' int_or_ptr_type nv _)
                (data_at sh' _ _ _).
              rewrite H30. subst l'.
              rewrite <- lmc_vertex_rep_eq.
              thaw FR1.
              gather_SEP 0 1.
              (* no matching clauses *)
              (* gather_SEP *)
              (*   (vertex_rep sh' (lgraph_mark_copied g' v (new_copied_v g to)) v) *)
              (*   (vertex_rep sh' (lgraph_mark_copied g' v (new_copied_v g to)) v -* *)
              (*                graph_rep (lgraph_mark_copied g' v (new_copied_v g to))). *)
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
                as t_info'. unfold thread_info_rep. Intros. forward.
              remember (Znth z (live_roots_indices f_info)) as lz.
              (* gather_SEP 1 2 3. *)
              gather_SEP
                (data_at sh thread_info_type _ ti)
                (heap_struct_rep sh _ _)
                (heap_rest_rep _ ).
              replace_SEP 0 (thread_info_rep
                               sh (update_thread_info_arg t_info' lz nv H16) ti). {
                unfold thread_info_rep. simpl heap_head. simpl ti_heap_p.
                simpl ti_args. simpl ti_heap. clear Heqt_info'. entailer!. }
              remember (update_thread_info_arg t_info' lz nv H16) as t. subst t_info'.
              rename t into t_info'. rewrite H30 in H32.
              assert (forward_relation from to 0 (inl (inr v)) g g') by
                  (subst g'; constructor; assumption).
              assert (forward_condition g' t_info' from to). {
                subst g' t_info' from. apply lcv_forward_condition; try assumption.
                red. intuition. }
              remember (upd_bunch z f_info roots (inr (new_copied_v g to))) as roots'.
              assert (super_compatible (g', t_info', roots') f_info outlier). {
                subst g' t_info' roots' lz. rewrite H30, H32.
                apply lcv_super_compatible; try assumption. red. intuition. }
              assert (thread_info_relation t_info t_info'). {
                subst t_info'. split; [|split]; [reflexivity| |]; intros m.
                - rewrite utiacti_gen_size. reflexivity.
                - rewrite utiacti_space_start. reflexivity. }
              apply semax_if_seq. forward_if.
              ** destruct H41 as [? [? ?]]. replace fp with (gen_start g' from) by
                     (subst fp g'; apply lcv_gen_start; assumption).
                 replace (offset_val fn (gen_start g' from)) with
                     (limit_address g' t_info' from) by
                     (subst fn gn; rewrite H43; reflexivity).
                 replace n_addr with (next_address t_info' to) by
                     (subst n_addr; rewrite H41; reflexivity).
                 forward_for_simple_bound
                   n
                   (EX i: Z, EX g3: LGraph, EX t_info3: thread_info,
                    PROP (super_compatible (g3, t_info3, roots') f_info outlier;
                          forward_loop
                            from to (Z.to_nat (depth - 1))
                            (sublist 0 i (vertex_pos_pairs g' (new_copied_v g to)))
                            g' g3;
                          forward_condition g3 t_info3 from to;
                          thread_info_relation t_info' t_info3)
                    LOCAL (temp _new nv;
                           temp _sz (vint n);
                           temp _from_start (gen_start g3 from);
                           temp _from_limit (limit_address g3 t_info3 from);
                           temp _next (next_address t_info3 to);
                           temp _depth (vint depth))
                    SEP (all_string_constants rsh gv;
                         fun_info_rep rsh f_info fi;
                         outlier_rep outlier;
                         graph_rep g3;
                         thread_info_rep sh t_info3 ti))%assert.
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
                     forward_call (rsh, sh, gv, fi, ti, g3, t_info3, f_info, roots',
                                   outlier, from, to, depth - 1,
                                   (@inr Z _ (new_copied_v g to, i))).
                     +++ simpl. apply prop_right. rewrite sub_repr.
                         do 3 split; [|easy]. f_equal. rewrite H30.
                         rewrite sem_add_pi_ptr_special.
                         *** simpl. f_equal. erewrite fl_vertex_address; eauto.
                             subst g'. apply graph_has_v_in_closure. assumption.
                         *** rewrite <- H30. assumption.
                         *** subst n. clear -H45 Hr. rep_omega.
                     +++ do 3 (split; [assumption |]). split.
                         *** simpl. split; [|split; [|split]]; auto.
                             ---- destruct H39 as [_ [_ [? _]]].
                                  apply (fl_graph_has_v _ _ _ _ _ _ H39 H47 _ H51).
                             ---- erewrite <- fl_raw_fields; eauto. subst g'.
                                  unfold lgraph_copy_v. subst n.
                                  rewrite <- lmc_raw_fields, lacv_vlabel_new.
                                  assumption.
                             ---- erewrite <- fl_raw_mark; eauto. subst g' from.
                                  rewrite lcv_vlabel_new; assumption.
                         *** split; [assumption|]. split; [omega | assumption].
                     +++ Intros vret. destruct vret as [[g4 t_info4] roots4].
                         simpl fst in *. simpl snd in *. Exists g4 t_info4.
                         simpl in H53. subst roots4.
                         assert (gen_start g3 from = gen_start g4 from). {
                           eapply fr_gen_start; eauto.
                           erewrite <- fl_graph_has_gen; eauto. } rewrite H53.
                         assert (limit_address g3 t_info3 from =
                                 limit_address g4 t_info4 from). {
                           unfold limit_address. f_equal. 2: assumption. f_equal.
                           destruct H56 as [? [? _]]. rewrite H57. reflexivity. }
                         rewrite H57.
                         assert (next_address t_info3 to = next_address t_info4 to). {
                           unfold next_address. f_equal. destruct H56. assumption. }
                         rewrite H58. clear H53 H57 H58.
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
                     rewrite sublist_all in H46. clear Heqt.
                     2: { rewrite Z.le_lteq. right. subst n g' from.
                          rewrite vpp_Zlength, lcv_vlabel_new; auto. }
                     Opaque super_compatible. forward. clear H50 H51 H52 H53.
                     remember (upd_bunch z f_info roots (inr (new_copied_v g to)))
                       as roots'. Exists g3 t_info3 roots'. simpl. entailer!.
                     rewrite <- Heqroot, H21, if_true by reflexivity.
                     replace (Z.to_nat depth) with (S (Z.to_nat (depth - 1))) by
                         (rewrite <- Z2Nat.inj_succ; [f_equal|]; omega).
                     constructor; [|constructor]; easy.
                     Transparent super_compatible.
              ** assert (depth = 0) by omega. subst depth. clear H42.
                 deadvars!. clear Heqnv. forward.
                 remember (Znth z (live_roots_indices f_info)) as lz.
                 remember (vertex_address (lgraph_copy_v g v to) (new_copied_v g to))
                          as nv.
                 remember (cut_thread_info
                             t_info (Z.of_nat to) (vertex_size g v) Hi Hh).
                 Exists (lgraph_copy_v g v to) (update_thread_info_arg t lz nv H16)
                        (upd_bunch z f_info roots (inr (new_copied_v g to))).
                 entailer!. simpl; rewrite <- Heqroot.
                 rewrite if_true by reflexivity; rewrite H21; easy. 
      * apply semax_if_seq. forward_if. 1: exfalso; apply H21'; reflexivity.
        rewrite H20 in n. forward.
        Exists g t_info roots. simpl. entailer!.
        -- rewrite <- Heqroot, if_false by assumption.
           split3; [|simpl root2forward; constructor |]; easy. 
        -- unfold thread_info_rep. entailer!.
  (* p is Vtype * Z, ie located in graph *)
  - destruct p as [v n]. destruct H0 as [? [? [? ?]]]. freeze [0; 1; 2; 4] FR.
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
    gather_SEP
      (data_at (nth_sh g (vgeneration v)) tuint (Z2val (make_header g v))
               (offset_val (- WORD_SIZE) (vertex_address g v)))
      (data_at (nth_sh g (vgeneration v))
               (tarray int_or_ptr_type (Zlength (make_fields_vals g v)))
               (make_fields_vals g v) (vertex_address g v)).
    replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v)) g v).
    1: unfold vertex_rep, vertex_at; entailer!.
    unlocalize [graph_rep g]. 1: apply graph_vertex_ramif_stable; assumption. thaw FR.
    unfold make_fields_vals.
    rewrite H12, Znth_map; [|rewrite make_fields_eq_length; assumption].
    assert_PROP (valid_int_or_ptr (field2val g (Znth n (make_fields g v)))). {
      destruct (Znth n (make_fields g v)) eqn:?; [destruct s|].
      - unfold field2val; unfold odd_Z2val.
        replace (2 * z + 1) with (z + z + 1) by omega.
        entailer!. apply valid_int_or_ptr_ii1.
      - unfold field2val, outlier_rep.
        apply in_gcptr_outlier with (gcptr:= g0) (outlier:=outlier) (n:=n) in H0;
          try assumption.
        apply (in_map single_outlier_rep outlier g0) in H0.
        replace_SEP 3 (single_outlier_rep g0). {
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
      unfold field2val, odd_Z2val. apply semax_if_seq. forward_if.
      1: exfalso; apply H20'; reflexivity.
      forward. Exists g t_info roots. entailer!. split.
      * easy.
      * unfold forward_condition, thread_info_relation.
        simpl. rewrite Heqf, H12. simpl. constructor; [constructor|easy].
    + (* GC_Pointer *)
      destruct g0. unfold field2val, GC_Pointer2val. apply semax_if_seq. forward_if.
      2: exfalso; apply Int.one_not_zero; assumption.
      forward_call (Vptr b i). 1: exact I.
      unfold thread_info_rep; Intros.
      (* gather_SEP 0 6 3. *)
      gather_SEP (graph_rep g)
                 (heap_rest_rep _) (outlier_rep _).
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
        gather_SEP (graph_rep g) (heap_rest_rep (ti_heap t_info)).
        sep_apply H18. rewrite Heqfn in v0.
        pose proof in_gcptr_outlier g (GCPtr b i) outlier n v H0 H6 H11 Heqf.
        sep_apply (outlier_rep_single_rep outlier (GCPtr b i)).
        Intros.
        gather_SEP (data_at_ fsh (tarray int_or_ptr_type gn) fp)
                   (single_outlier_rep (GCPtr b i)).
        change (Vptr b i) with (GC_Pointer2val (GCPtr b i)) in v0.
        pose proof (generation_share_writable (nth_gen g from)).
        change (generation_sh (nth_gen g from)) with (nth_sh g from) in H22.
        rewrite <- Heqfsh in H22. unfold generation_data_at_.
        sep_apply (single_outlier_rep_memory_block_FF (GCPtr b i) fp gn fsh H22 v0).
        assert_PROP False by entailer!. contradiction.
      * (* no *)
        apply semax_if_seq. forward_if.
        1: exfalso; apply H19'; reflexivity.
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
      apply semax_if_seq. forward_if.
      2: exfalso; apply Int.one_not_zero in H21; assumption.
      clear H21 H21'. forward_call (Vptr b i).
      unfold thread_info_rep; Intros.
      (* gather_SEP 0 6 3. *)
      gather_SEP (graph_rep g)
                 (heap_rest_rep _) (outlier_rep _).
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
          pose proof (proj1 (raw_fields_range (vlabel g v'))). rewrite Z.max_r; omega.
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
        rewrite H21 in v0. clear H21. apply semax_if_seq. forward_if.
        2: exfalso; inversion H21.
        deadvars!. freeze [1; 2; 3; 4; 5; 6] FR.
        clear H21 H21'. localize [vertex_rep (nth_sh g (vgeneration v')) g v'].
        unfold vertex_rep, vertex_at. Intros. rewrite v0.
        assert (readable_share (nth_sh g from)) by
            (unfold nth_sh; apply writable_readable, generation_share_writable).
        rewrite <- Heqv0.
        sep_apply (data_at_minus1_address
                     (nth_sh g from) (Z2val (make_header g v')) (vertex_address g v')).
        Intros. forward. clear H22.
        gather_SEP (data_at (nth_sh g from) tuint (Z2val (make_header g v'))
            (offset_val (- WORD_SIZE) (vertex_address g v')))
          (data_at (nth_sh g from)
            (tarray int_or_ptr_type (Zlength (make_fields_vals g v')))
            (make_fields_vals g v') (vertex_address g v')).

        replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v')) g v') by
            (unfold vertex_rep, vertex_at; entailer!).
        unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H19).
        apply semax_if_seq. forward_if; rewrite make_header_int_rep_mark_iff in H22.
        -- (* yes, already forwarded *)
          deadvars!.
          localize [vertex_rep (nth_sh g (vgeneration v')) g v'].
          change (Tpointer tvoid {| attr_volatile := false;
                                    attr_alignas := Some 2%N |}) with int_or_ptr_type.
          rewrite v0. unfold vertex_rep, vertex_at. Intros.
          unfold make_fields_vals at 2. rewrite H22.
          assert (0 <= 0 < Zlength (make_fields_vals g v')). {
             split. 1: omega. rewrite fields_eq_length.
             apply (proj1 (raw_fields_range (vlabel g v'))).
          }
          assert (is_pointer_or_integer
                    (vertex_address g (copied_vertex (vlabel g v')))). {
            apply isptr_is_pointer_or_integer. unfold vertex_address.
            rewrite isptr_offset_val.
            apply graph_has_gen_start_isptr, H9; assumption. }
          forward. rewrite Znth_0_cons.
          gather_SEP (data_at (nth_sh g from) tuint (Z2val (make_header g v'))
            (offset_val (- WORD_SIZE) (vertex_address g v')))
          (data_at (nth_sh g from)
            (tarray int_or_ptr_type (Zlength (make_fields_vals g v')))
            (vertex_address g (copied_vertex (vlabel g v'))
             :: tl (map (field2val g) (make_fields g v'))) 
            (vertex_address g v')).
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
          (* gather_SEP 1 0. *)
          gather_SEP (data_at _ tuint _ _ ) (data_at _ _ _ _).
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
          forward.
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
           apply not_true_is_false in H22. rewrite make_header_Wosize by assumption.
           assert (0 <= Z.of_nat to < 12). {
             clear -H H8. destruct H as [_ [_ ?]]. red in H8.
             pose proof (spaces_size (ti_heap t_info)).
             rewrite Zlength_correct in H0. rep_omega. } unfold heap_struct_rep.
           destruct (gt_gs_compatible _ _ H _ H8) as [? [? ?]].
           rewrite nth_space_Znth in *.
           remember (Znth (Z.of_nat to) (spaces (ti_heap t_info))) as sp_to.
           assert (isptr (space_start sp_to)) by (rewrite <- H24; apply start_isptr).
           remember (map space_tri (spaces (ti_heap t_info))).
           assert (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef))
                         (Z.of_nat to) l = space_tri sp_to). {
             subst l sp_to. rewrite Znth_map by (rewrite spaces_size; rep_omega).
             reflexivity. }
           forward; rewrite H28; unfold space_tri. 1: entailer!.
           forward. simpl sem_binary_operation'.
           rewrite sapi_ptr_val; [| assumption | rep_omega].
           Opaque Znth.  forward. Transparent Znth.
           assert (Hr: Int.min_signed <= Zlength (raw_fields (vlabel g v')) <=
                       Int.max_signed). {
             pose proof (raw_fields_range (vlabel g v')). destruct H29. split.
             - rep_omega.
             - transitivity (two_power_nat 22). 1: omega.
               compute; intro s; inversion s. }
           rewrite sapi_ptr_val; [|easy|easy].
           rewrite H28. unfold space_tri.
           rewrite <- Z.add_assoc.
           replace (1 + Zlength (raw_fields (vlabel g v'))) with (vertex_size g v') by
               (unfold vertex_size; omega). thaw FR. freeze [0; 2; 3; 4; 5; 6] FR.
           assert (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info))) by
               (rewrite spaces_size; rep_omega).
           assert (Hh: has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info)))
                                 (vertex_size g v')). {
             red. split. 1: pose proof (svs_gt_one g v'); omega.
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
           (* gather_SEP 4 5 7. *)
           gather_SEP
             (data_at sh thread_info_type _ ti)
             (data_at sh heap_type _ _) (heap_rest_rep _).
           replace_SEP 0 (thread_info_rep
                            sh (cut_thread_info t_info _ _ Hi Hh) ti). {
             entailer. unfold thread_info_rep. simpl ti_heap. simpl ti_heap_p. cancel.
             simpl spaces. rewrite <- upd_Znth_map. unfold cut_space.
             unfold space_tri at 3. simpl. unfold heap_struct_rep. cancel. }
           sep_apply (graph_vertex_ramif_stable _ _ H19). Intros.
           freeze [1; 2; 3; 4; 5] FR. deadvars!. rewrite v0.
           remember (nth_sh g from) as shv.
           assert (writable_share (space_sh sp_to)) by
               (rewrite <- H25; apply generation_share_writable).
           remember (space_sh sp_to) as sht.
           rewrite (data_at__tarray_value _ _ 1). 2: unfold vertex_size; rep_omega.
           Intros.
           remember (offset_val (WORD_SIZE * used_space sp_to) (space_start sp_to)).
           rewrite (data_at__int_or_ptr_tuint sht v1).
           assert_PROP
             (force_val (sem_add_ptr_int
                           tuint Signed
                           (offset_val (WORD_SIZE * (used_space sp_to + 1))
                                       (space_start sp_to))
                           (eval_unop Oneg tint (vint 1))) =
              field_address tuint [] v1). {
             subst v1. rewrite WORD_SIZE_eq. entailer!. unfold field_address.
             simpl. rewrite neg_repr. rewrite sem_add_pi_ptr_special'; auto.
             rewrite if_true by assumption. simpl. rewrite !offset_offset_val.
             f_equal. omega. }
           forward. sep_apply (field_at_data_at_cancel
                                 sht tuint (Z2val (make_header g v')) v1). clear H30.
           subst v1. rewrite offset_offset_val.
           replace (vertex_size g v' - 1) with (Zlength (raw_fields (vlabel g v')))
             by (unfold vertex_size; omega).
           replace (WORD_SIZE * used_space sp_to + WORD_SIZE * 1) with
               (WORD_SIZE * (used_space sp_to + 1))%Z by rep_omega.
           remember (offset_val (WORD_SIZE * (used_space sp_to + 1))
                                (space_start sp_to)) as nv.
           thaw FR. freeze [0; 1; 2; 3; 4; 5] FR. rename i into j. deadvars!.
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
                     temp _sz (vint n');
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
           ++ rewrite sublist_nil. replace (n' - 0) with n' by omega.
              replace (WORD_SIZE * 0)%Z with 0 by omega.
              rewrite isptr_offset_val_zero by assumption.
              rewrite data_at_zero_array_eq;
                [|reflexivity | assumption | reflexivity]. entailer!.
           ++ unfold vertex_rep, vertex_at. Intros.
              rewrite fields_eq_length, <- Heqn'. forward.
              ** entailer!. pose proof (mfv_all_is_ptr_or_int _ _ H9 H10 H19).
                 rewrite Forall_forall in H46. apply H46, Znth_In.
                 rewrite fields_eq_length. assumption.
              ** rewrite (data_at__tarray_value _ _ 1) by omega. Intros.
                 rewrite data_at__singleton_array_eq.
                 assert_PROP
                   (field_compatible int_or_ptr_type []
                                     (offset_val (WORD_SIZE * i) nv)) by
                     (sep_apply (data_at__local_facts
                                   sht int_or_ptr_type
                                   (offset_val (WORD_SIZE * i) nv)); entailer!).
                 assert_PROP
                   (force_val (sem_add_ptr_int int_or_ptr_type
                                               Signed nv (vint i)) =
                    field_address int_or_ptr_type []
                                  (offset_val (WORD_SIZE * i) nv)). {
                   unfold field_address. rewrite if_true by assumption.
                   clear. entailer!. }
                 gather_SEP
                 (data_at shv tuint (Z2val (make_header g v'))
                          (offset_val (- WORD_SIZE) (vertex_address g v'))) (data_at shv (tarray int_or_ptr_type n') (make_fields_vals g v')
                                                                                     (vertex_address g v')).
                 replace_SEP 0 (vertex_rep shv g v') by
                     (unfold vertex_rep, vertex_at;
                      rewrite fields_eq_length; entailer!). forward.
                 rewrite offset_offset_val.
                 replace (n' - i - 1) with (n' - (i + 1)) by omega.
                 replace (WORD_SIZE * i + WORD_SIZE * 1) with
                     (WORD_SIZE * (i + 1))%Z by rep_omega.
                 gather_SEP 1 2.
                 (* gather_SEP *)
                 (*   (data_at sht (tarray int_or_ptr_type i) (sublist 0 i (make_fields_vals g v')) *)
                 (*            nv) *)
                 (*   (field_at sht int_or_ptr_type [] (Znth i (make_fields_vals g v')) *)
                 (*             (offset_val (WORD_SIZE * i) nv)). *)
                 (* no matching... *)
                 rewrite data_at_mfs_eq;
                                   [|assumption|subst n'; assumption].
                 entailer!.
           ++ thaw FR. rewrite v0, <- Heqshv.
              gather_SEP 0 4.
              (* gather_SEP (vertex_rep shv g v') (vertex_rep shv g v' -* graph_rep g). *)
              (* no matching clauses *)
              replace_SEP 0 (graph_rep g) by (entailer!; apply wand_frame_elim).
              rewrite sublist_all by (rewrite fields_eq_length; omega).
              replace_SEP 2 emp. {
                replace (n' - n') with 0 by omega. clear. entailer.
                apply data_at__value_0_size. }
              assert (nv = vertex_address g (new_copied_v g to)). {
                subst nv. unfold vertex_address. unfold new_copied_v. simpl. f_equal.
                - unfold vertex_offset. simpl. rewrite H26. reflexivity.
                - unfold gen_start. rewrite if_true by assumption.
                  rewrite H24. reflexivity. }
              (* gather_SEP 1 2 3. *)
              gather_SEP
              (data_at sht _ _ nv)
              (emp) (data_at sht tuint _ _).
              replace_SEP
                0 (vertex_at (nth_sh g to)
                             (vertex_address g (new_copied_v g to))
                             (make_header g v') (make_fields_vals g v')). {
                normalize. rewrite <- H25.
                change (generation_sh (nth_gen g to)) with (nth_sh g to).
                rewrite <- fields_eq_length in Heqn'.
                replace (offset_val (WORD_SIZE * used_space sp_to) (space_start sp_to))
                  with (offset_val (- WORD_SIZE) nv) by
                    (rewrite Heqnv; rewrite offset_offset_val; f_equal; rep_omega).
                rewrite <- H31. unfold vertex_at; entailer!. }
              gather_SEP (vertex_at (nth_sh g to) (vertex_address g (new_copied_v g to))
            (make_header g v') (make_fields_vals g v')) (graph_rep g).
              rewrite (copied_v_derives_new_g g v' to) by assumption.
              freeze [1; 2; 3; 4] FR. remember (lgraph_add_copied_v g v' to) as g'.
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
                           sh' tuint (vint 0)
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
              (* gather_SEP 1 0 3. *)
              gather_SEP
                (data_at sh' tuint (vint 0) _)
                (data_at sh' int_or_ptr_type nv _)
                (data_at sh' (tarray int_or_ptr_type _) _ _).
              rewrite H31. subst l'.
              rewrite <- lmc_vertex_rep_eq.
              thaw FR1.
              gather_SEP 0 1.
           (*    gather_SEP *)
           (*      (vertex_rep sh' (lgraph_mark_copied g' v' (new_copied_v g to)) v') *)
           (*      ((vertex_rep sh' (lgraph_mark_copied g' v' (new_copied_v g to)) v' -* *)
              (* graph_rep (lgraph_mark_copied g' v' (new_copied_v g to)))). *)
              (* no matching... *)
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
                  (intro; subst v; clear -v0 H13; omega).
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
              (* gather_SEP 1 0. *)
              gather_SEP
                (data_at shh tuint _ _) (data_at shh _ _ _).
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
                  (rewrite arg_size; rep_omega).
              (* gather_SEP 1 2 3. *)
              gather_SEP
                (data_at sh thread_info_type _ _)
                (heap_struct_rep sh _ _) (heap_rest_rep _).
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
                assert (super_compatible (g1, t_info', roots') f_info outlier). {

                  subst g1 g' t_info' roots'.
                  apply lgd_super_compatible, lcv_super_compatible_unchanged;
                    try assumption.
                  red; intuition. }
              assert (thread_info_relation t_info t_info'). {
                subst t_info'. split; [|split]; [reflexivity| |]; intros m.
                - rewrite cti_gen_size. reflexivity.
                - rewrite cti_space_start. reflexivity. }
                apply semax_if_seq. forward_if.
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
                    PROP (super_compatible (g3, t_info3, roots') f_info outlier;
                          forward_loop
                            from to (Z.to_nat (depth - 1))
                            (sublist 0 i (vertex_pos_pairs g1 (new_copied_v g to)))
                            g1 g3;
                          forward_condition g3 t_info3 from to;
                          thread_info_relation t_info' t_info3)
                    LOCAL (temp _new nv;
                           temp _sz (vint n');
                           temp _from_start (gen_start g3 from);
                           temp _from_limit (limit_address g3 t_info3 from);
                           temp _next (next_address t_info3 to);
                           temp _depth (vint depth))
                    SEP (all_string_constants rsh gv;
                         fun_info_rep rsh f_info fi;
                         outlier_rep outlier;
                         graph_rep g3;
                         thread_info_rep sh t_info3 ti))%assert.
                 --- Exists g1 t_info'. autorewrite with sublist.
                     assert (forward_loop from to (Z.to_nat (depth - 1)) [] g1 g1) by
                         constructor. unfold thread_info_relation.
                     destruct H54 as [? [? [? ?]]].
                     entailer!. easy.
                 --- change (Tpointer tvoid {| attr_volatile := false;
                                               attr_alignas := Some 2%N |})
                       with (int_or_ptr_type). Intros.
                     assert (graph_has_gen g1 to) by
                         (rewrite Heqg1, lgd_graph_has_gen; subst g';
                          rewrite <- lcv_graph_has_gen; assumption).
                     assert (graph_has_v g1 (new_copied_v g to)) by
                       (subst g1; rewrite <- lgd_graph_has_v;
                       rewrite Heqg'; apply lcv_graph_has_v_new; assumption).
                     forward_call (rsh, sh, gv, fi, ti, g3, t_info3, f_info, roots',
                                   outlier, from, to, depth - 1,
                                   (@inr Z _ (new_copied_v g to, i))).
                     +++ simpl. apply prop_right. rewrite sub_repr.
                         do 3 split; [|easy].
                         f_equal. rewrite H31. rewrite sem_add_pi_ptr_special.
                         *** simpl. f_equal.
                             rewrite <- (lgd_vertex_address_eq g' e v1), <- Heqg1.
                             subst v1. apply (fl_vertex_address _ _ _ _ _ _ H64 H61).
                             apply graph_has_v_in_closure; assumption.
                         *** rewrite <- H31. assumption.
                         *** subst n'. clear -H59 Hr. rep_omega.
                     +++ do 3 (split; [assumption |]). split.
                         *** simpl. split; [|split].
                             ---- destruct H53 as [_ [_ [? _]]].
                                  apply (fl_graph_has_v _ _ _ _ _ _ H64 H61 _ H65).
                             ---- erewrite <- fl_raw_fields; eauto. subst g1.
                                  unfold lgraph_copy_v. subst n'.
                                  rewrite <- lgd_raw_fld_length_eq.
                                  subst g'. rewrite lcv_vlabel_new.
                                  assumption. rewrite v0. omega.
                             ---- erewrite <- fl_raw_mark; eauto. subst g1 from.
                                  rewrite <- lgd_raw_mark_eq. subst g'.
                                  rewrite lcv_vlabel_new; try assumption.
                                  split; try assumption. omega.
                         *** split; [assumption|]. split; [omega | assumption].
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
                     rewrite sublist_all in H60.
                     2: { rewrite Z.le_lteq. right. subst n' g1 from.
                          rewrite vpp_Zlength,  <- lgd_raw_fld_length_eq.
                          subst g'; rewrite lcv_vlabel_new; auto. }
                     Opaque super_compatible. forward. clear H64 H65 H66 H67.
                     simpl.
                     Exists g3 t_info3 roots. simpl. entailer!.
                     replace (Z.to_nat depth) with (S (Z.to_nat (depth - 1))) by
                         (rewrite <- Z2Nat.inj_succ; [f_equal|]; omega).
                     rewrite Heqf, H12. simpl.
                     constructor; [reflexivity | assumption..].
                     Transparent super_compatible.
              ** assert (depth = 0) by omega. subst depth. clear H56.
                 deadvars!. clear Heqnv. forward.
                 simpl.
                 remember (cut_thread_info t_info (Z.of_nat to)
                             (vertex_size g (dst g e)) Hi Hh) as t_info'.
              remember (lgraph_copy_v g (dst g e) to) as g'.

              remember (new_copied_v g to).
              remember (labeledgraph_gen_dst g' e v0) as g1.
              Exists g1 t_info' roots.
              rewrite Heqf.
              simpl field2forward. rewrite H12. simpl. entailer!.
      * apply semax_if_seq. forward_if. 1: exfalso; apply H22'; reflexivity.
        rewrite H21 in n0. forward.
        simpl.
        Exists g t_info roots. simpl. rewrite H12. entailer!.
        -- rewrite Heqf. split; [constructor; assumption |
                                 split; [hnf; intuition | apply tir_id]].
        -- unfold thread_info_rep. entailer!.
Qed.
