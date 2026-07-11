From CertiGraph.CertiGC Require Import
  env_graph_gc gc_spec forward_lemmas gc_correct.
Require Import CertiGraph.graph.graph_model.

Local Open Scope logic.

Lemma graph_rep_interior_field_address: forall g src pos,
    graph_has_v g src ->
    0 <= pos < Zlength (raw_fields (vlabel g src)) ->
    graph_rep g |--
      !! (interior_address (InteriorVertexPos src pos) g =
          field_address
            (tarray int_or_ptr_type (Zlength (make_fields_vals g src)))
            [ArraySubsc pos] (vertex_address g src)).
Proof.
  intros g src pos Hsrc Hpos.
  sep_apply (graph_rep_vertex_rep g src Hsrc). Intros sh.
  unfold vertex_rep, vertex_at. Intros.
  entailer !.
  unfold interior_address, field_address.
  rewrite if_true.
  - reflexivity.
  - match goal with
    | Hfc : field_compatible _ [] _ |- _ =>
        clear -Hfc Hpos;
        rewrite <- fields_eq_length in Hpos;
        unfold field_compatible in *; simpl in *; tauto
    end.
Qed.

Lemma heap_head_nth_space_O: forall h,
    heap_head h = nth_space h O.
Proof.
  intros h.
  destruct (heap_head_cons h) as [sp [rest [Hspaces Hhead]]].
  unfold nth_space. rewrite Hspaces, Hhead. reflexivity.
Qed.

Theorem int_mutable_update_restores_garbage_collect_model_preconditions:
  forall g src pos new g' t_info t_info' roots outlier rmst rh rh',
    mutable_location_compatible g (InteriorVertexPos src pos) ->
    exterior_compatible g outlier new ->
    mutable_graph_update g (InteriorVertexPos src pos) new g' ->
    info_recordable t_info ->
    t_info' = decr_info_nursery t_info (exterior2val g new) ->
    rh' = mtb_upd_remset_heap
            (exterior2val g new)
            (RemSetInterior (InteriorVertexPos src pos)) rh ->
    super_compatible
      g (pt_heap (ti_heap t_info))
      (frames2rootpairs (ti_frames t_info)) roots outlier ->
    garbage_collect_condition g (pt_heap (ti_heap t_info)) ->
    no_unrecorded_backward_edge g rh ->
    safe_to_copy_heap g (pt_heap (ti_heap t_info)) ->
    remset_compatible
      g outlier O rmst rh (pt_heap (ti_heap t_info)) ->
    remset_generation_compatible O rmst rh ->
    super_compatible
      g' (pt_heap (ti_heap t_info'))
      (frames2rootpairs (ti_frames t_info')) roots outlier /\
    garbage_collect_condition g' (pt_heap (ti_heap t_info')) /\
    no_unrecorded_backward_edge g' rh' /\
    safe_to_copy_heap g' (pt_heap (ti_heap t_info')) /\
    remset_compatible
      g' outlier O rmst rh' (pt_heap (ti_heap t_info')) /\
    remset_generation_compatible O rmst rh'.
Proof.
  intros g src pos new g' t_info t_info' roots outlier rmst rh rh'
         Hloc Hext Hupd Hrecordable Htinfo Hrh
         Hsuper Hgcc Hunrecorded Hsafe Hremset Hremgen.
  subst t_info' rh'.
  unfold info_recordable in Hrecordable.
  rewrite heap_head_nth_space_O in Hrecordable.
  pose proof
    (mutable_update_garbage_collect_model_preconditions
       g src pos new g' (pt_heap (ti_heap t_info))
       (frames2rootpairs (ti_frames t_info)) roots outlier rmst rh
       Hloc Hext Hupd Hrecordable Hsuper Hgcc Hunrecorded Hsafe
       Hremset Hremgen) as Hclosed.
  assert (Hheap:
    pt_heap
      (ti_heap
        (decr_info_nursery t_info (exterior2val g new))) =
    if isptr_dec (exterior2val g new)
    then incr_remset_heap (pt_heap (ti_heap t_info)) 0
    else pt_heap (ti_heap t_info)).
  { unfold decr_info_nursery.
    destruct (isptr_dec (exterior2val g new)); reflexivity. }
  assert (Hframes:
    ti_frames
      (decr_info_nursery t_info (exterior2val g new)) =
    ti_frames t_info).
  { unfold decr_info_nursery.
    destruct (isptr_dec (exterior2val g new)); reflexivity. }
  rewrite Hheap, Hframes.
  unfold mtb_upd_remset_heap.
  exact Hclosed.
Qed.

Lemma generation_data_at__test_order: forall g h gen i j,
    graph_has_gen g gen ->
    0 <= i <= available_size h gen ->
    0 <= j <= available_size h gen ->
    0 < available_size h gen ->
    generation_data_at_ g h gen |--
      denote_tc_test_order
        (offset_val (WORD_SIZE * i) (gen_start g gen))
        (offset_val (WORD_SIZE * j) (gen_start g gen)).
Proof.
  intros g h gen i j Hgen Hi Hj Hav.
  unfold generation_data_at_. rewrite data_at__memory_block. Intros.
  rewrite sizeof_tarray_int_or_ptr by
    (unfold available_size; apply available_space_range).
  rewrite isptr_denote_tc_test_order by
    (apply isptr_offset_val'; apply graph_has_gen_start_isptr; exact Hgen).
  unfold test_order_ptrs.
  rewrite sameblock_offset_val by
    (apply graph_has_gen_start_isptr; exact Hgen).
  apply andp_right.
  - eapply derives_trans with
      (Q := memory_block (nth_sh g gen)
              (WORD_SIZE * available_size h gen) (gen_start g gen));
      [cancel|].
    apply memory_block_weak_valid_pointer;
      [unfold WORD_SIZE; lia|unfold WORD_SIZE; lia|].
    unfold nth_sh. apply readable_nonidentity, writable_readable,
      generation_share_writable.
  - eapply derives_trans with
      (Q := memory_block (nth_sh g gen)
              (WORD_SIZE * available_size h gen) (gen_start g gen));
      [cancel|].
    apply memory_block_weak_valid_pointer;
      [unfold WORD_SIZE; lia|unfold WORD_SIZE; lia|].
    unfold nth_sh. apply readable_nonidentity, writable_readable,
      generation_share_writable.
Qed.

Lemma align_compatible_int_or_ptr_tptr: forall z,
    align_compatible_rec cenv_cs int_or_ptr_type z <->
    align_compatible_rec cenv_cs (tptr int_or_ptr_type) z.
Proof.
  intro z; split; intro H.
  - eapply align_compatible_rec_by_value_inv in H; [|reflexivity].
    apply align_compatible_rec_by_value with (ch := Mptr);
      [reflexivity|exact H].
  - eapply align_compatible_rec_by_value_inv in H; [|reflexivity].
    apply align_compatible_rec_by_value with (ch := Mptr);
      [reflexivity|exact H].
Qed.

Lemma data_at__int_or_ptr_tptr: forall sh p,
    data_at_ sh int_or_ptr_type p = data_at_ sh (tptr int_or_ptr_type) p.
Proof.
  intros. unfold data_at_, field_at_, data_at, field_at.
  simpl nested_field_type. simpl nested_field_offset. f_equal; f_equal.
  apply prop_ext. unfold field_compatible. destruct p; simpl; try tauto.
  rewrite align_compatible_int_or_ptr_tptr. reflexivity.
Qed.

Lemma data_at_int_or_ptr_tptr: forall sh p v,
    isptr v ->
    data_at sh int_or_ptr_type v p =
    data_at sh (tptr int_or_ptr_type) v p.
Proof.
  intros sh p v Hv. unfold data_at, field_at.
  simpl nested_field_type. simpl nested_field_offset.
  destruct v; try contradiction.
  unfold int_or_ptr_type. cbv [Archi.ptr64 log2_sizeof_pointer].
  f_equal; f_equal. apply prop_ext. unfold field_compatible.
  destruct p; simpl; try tauto.
  rewrite align_compatible_int_or_ptr_tptr. reflexivity.
Qed.

Lemma body_mutable_update:
  semax_body Vprog Gprog f_mutable_update int_mutable_update_spec.
Proof.
  start_function.
  rename H into Hrecordable.
  rename H0 into Hghc.
  rename H1 into Hrhhc.
  rename H2 into Hloc.
  rename H3 into Hext.
  destruct it as [src pos].
  destruct Hloc as [Hsrc [Hpos [Hmark Htag]]].
  assert (Hloc: mutable_location_compatible
                  g (InteriorVertexPos src pos)) by
    (exact (conj Hsrc (conj Hpos (conj Hmark Htag)))).
  destruct (mutable_graph_update_exists
              g (InteriorVertexPos src pos) v Hloc) as [g' Hupd].
  assert_PROP (valid_int_or_ptr (exterior2val g v)) as Hvalid.
  { sep_apply (extr_valid_int_or_ptr g v outlier Hext). entailer!. }
  assert_PROP
    (interior_address (InteriorVertexPos src pos) g =
     field_address
       (tarray int_or_ptr_type (Zlength (make_fields_vals g src)))
       [ArraySubsc pos] (vertex_address g src)) as Hcell.
  { sep_apply (graph_rep_interior_field_address g src pos Hsrc Hpos).
    entailer!. }
  pose proof
    (gt_gs_compatible g (pt_heap (ti_heap t_info)) Hghc O
       (graph_has_gen_O g)) as Hgsc.
  destruct Hgsc as [Hstart [Hspace_sh Hused]].
  assert (Hgenstart:
    gen_start g O =
    space_start (heap_head (pt_heap (ti_heap t_info)))).
  { unfold gen_start. rewrite if_true by apply graph_has_gen_O.
    rewrite heap_head_nth_space_O. exact Hstart. }
  unfold info_recordable in Hrecordable.
  unfold before_gc_thread_info_rep, heap_management_rep. Intros.
  assert_PROP
    (field_compatible
       (tarray int_or_ptr_type (available_size (pt_heap (ti_heap t_info)) O))
       [] (gen_start g O)) as Harray.
  { gather_SEP (graph_rep g) (heap_unused_rep (pt_heap (ti_heap t_info))).
    sep_apply
      (graph_and_heap_rest_data_at_
         g (pt_heap (ti_heap t_info)) O (graph_has_gen_O g) Hghc).
    unfold generation_data_at_. entailer!.
  }
  assert (Hused_range:
    0 <= used_space (heap_head (pt_heap (ti_heap t_info))) <=
    available_space (heap_head (pt_heap (ti_heap t_info)))).
  { apply used_leq_available. }
  assert (Halloc_address:
    field_address0
      (tarray int_or_ptr_type (available_size (pt_heap (ti_heap t_info)) O))
      [ArraySubsc (used_space (heap_head (pt_heap (ti_heap t_info))))]
      (gen_start g O) =
    offset_val
      (WORD_SIZE * used_space (heap_head (pt_heap (ti_heap t_info))))
      (space_start (heap_head (pt_heap (ti_heap t_info))))).
  { rewrite arr_field_address0.
    - rewrite Hgenstart. reflexivity.
    - exact Harray.
    - unfold available_size. rewrite <- heap_head_nth_space_O. exact Hused_range. }
  assert (Hlimit_address:
    field_address0
      (tarray int_or_ptr_type (available_size (pt_heap (ti_heap t_info)) O))
      [ArraySubsc (available_space (heap_head (pt_heap (ti_heap t_info))))]
      (gen_start g O) =
    offset_val
      (WORD_SIZE * available_space (heap_head (pt_heap (ti_heap t_info))))
      (space_start (heap_head (pt_heap (ti_heap t_info))))).
  { rewrite arr_field_address0.
    - rewrite Hgenstart. reflexivity.
    - exact Harray.
    - unfold available_size. rewrite <- heap_head_nth_space_O. lia. }
  assert (Hcmp:
    typed_true tint
      (force_val
        (sem_cmp_pp Clt
          (offset_val
            (WORD_SIZE * used_space (heap_head (pt_heap (ti_heap t_info))))
            (space_start (heap_head (pt_heap (ti_heap t_info)))))
          (offset_val
            (WORD_SIZE * available_space (heap_head (pt_heap (ti_heap t_info))))
            (space_start (heap_head (pt_heap (ti_heap t_info)))))))).
  { rewrite <- Halloc_address, <- Hlimit_address.
    rewrite ptr_comparison_lt_iff.
    - exact Hrecordable.
    - exact Harray.
    - unfold available_size. rewrite <- heap_head_nth_space_O. exact Hused_range.
    - unfold available_size. rewrite <- heap_head_nth_space_O. lia.
    - change (0 < WORD_SIZE). unfold WORD_SIZE. lia.
    - apply graph_has_gen_start_isptr, graph_has_gen_O.
  }
  assert_PROP (isptr ti) as Hti by entailer!.
  forward.
  - entailer !. apply isptr_is_pointer_or_null. apply isptr_offset_val'.
    rewrite <- Hgenstart. apply graph_has_gen_start_isptr, graph_has_gen_O.
  - forward.
    + entailer !. apply isptr_is_pointer_or_null. apply isptr_offset_val'.
      rewrite <- Hgenstart. apply graph_has_gen_start_isptr, graph_has_gen_O.
    + forward_if True.
      * sep_apply
          (graph_and_heap_rest_data_at_
             g (pt_heap (ti_heap t_info)) O (graph_has_gen_O g) Hghc).
        sep_apply
          (generation_data_at__test_order
             g (pt_heap (ti_heap t_info)) O
             (used_space (heap_head (pt_heap (ti_heap t_info))))
             (available_space (heap_head (pt_heap (ti_heap t_info))))).
        { apply graph_has_gen_O. }
        { unfold available_size. rewrite <- heap_head_nth_space_O.
          exact Hused_range. }
        { unfold available_size. rewrite <- heap_head_nth_space_O. lia. }
        { unfold available_size. rewrite <- heap_head_nth_space_O. lia. }
        { rewrite Hgenstart.
          rewrite !isptr_denote_tc_test_order by
            (apply isptr_offset_val'; rewrite <- Hgenstart;
             apply graph_has_gen_start_isptr, graph_has_gen_O).
          unfold test_order_ptrs.
          rewrite !sameblock_offset_val by
            (rewrite <- Hgenstart;
             apply graph_has_gen_start_isptr, graph_has_gen_O).
          apply andp_right.
          - apply sepcon_weak_valid_pointer1.
            apply andp_left1. apply derives_refl.
          - apply sepcon_weak_valid_pointer1.
            apply andp_left2. apply derives_refl. }
      * forward. entailer!.
      * exfalso. unfold force_val in Hcmp.
        unfold typed_true, typed_false in *. congruence.
      * assert (Hsrc_share:
          writable_share (nth_sh g (vgeneration src))).
        { unfold nth_sh. apply generation_share_writable. }
        sep_apply
          (graph_rep_mutable_update_ramif
             g src pos v g' Hloc Hupd).
        Intros.
        rewrite Hcell.
        let p := constr:(field_address
          (tarray int_or_ptr_type (Zlength (make_fields_vals g src)))
          [ArraySubsc pos] (vertex_address g src)) in
        assert_PROP (field_compatible int_or_ptr_type [] p) as Hfield.
        { entailer!. }
        assert (Hfield_address:
          field_address
            (tarray int_or_ptr_type (Zlength (make_fields_vals g src)))
            [ArraySubsc pos] (vertex_address g src) =
          field_address int_or_ptr_type []
            (field_address
              (tarray int_or_ptr_type (Zlength (make_fields_vals g src)))
              [ArraySubsc pos] (vertex_address g src))).
        { unfold field_address at 2. rewrite if_true by exact Hfield. simpl.
          symmetry. apply isptr_offset_val_zero. destruct Hfield; assumption. }
        forward.
        gather_SEP
          (field_at (nth_sh g (vgeneration src)) int_or_ptr_type []
             (exterior2val g v)
             (field_address
                (tarray int_or_ptr_type (Zlength (make_fields_vals g src)))
                [ArraySubsc pos] (vertex_address g src)))
          (data_at (nth_sh g (vgeneration src)) int_or_ptr_type
             (exterior2val g v)
             (field_address
                (tarray int_or_ptr_type (Zlength (make_fields_vals g src)))
                [ArraySubsc pos] (vertex_address g src)) -* graph_rep g').
        replace_SEP 0 (graph_rep g').
        { entailer !!. apply wand_frame_elim. }
        forward_call (exterior2val g v).
        rewrite
          (heap_remset_rep_mutable_graph_update
             g (InteriorVertexPos src pos) v g'
             (pt_heap (ti_heap t_info)) rh Hloc Hupd).
        assert (Hghc':
          graph_heap_compatible g' (pt_heap (ti_heap t_info))).
        { eapply mutable_graph_update_graph_heap_compatible; eassumption. }
        remember (exterior2val g v) as x eqn:Hx.
        destruct x; simpl in Hvalid; try contradiction.
        { forward_if.
          - contradiction.
          - forward.
            assert (Hnptr: ~ isptr (exterior2val g v)).
            { intro Hp. rewrite <- Hx in Hp. contradiction. }
            Exists g' t_info rh.
            unfold decr_info_nursery, mtb_upd_remset_heap.
            destruct (isptr_dec (exterior2val g v)); [contradiction|].
            entailer!.
            unfold before_gc_thread_info_rep, heap_management_rep.
            cancel. }
        { forward_if.
          - assert (Hnursery_ptr:
              isptr (space_start (heap_head (pt_heap (ti_heap t_info))))).
            { rewrite <- Hgenstart.
              apply graph_has_gen_start_isptr, graph_has_gen_O. }
            forward.
            forward.
            simpl force_val.
            rewrite sem_sub_pi_available_space_minus by exact Hnursery_ptr.
            forward.
            assert (Hrecordable0:
              used_space (nth_space (pt_heap (ti_heap t_info)) O) <
              available_space (nth_space (pt_heap (ti_heap t_info)) O)).
            { rewrite <- heap_head_nth_space_O. exact Hrecordable. }
            sep_apply
              (heap_unused_rep_incr
                 g' (pt_heap (ti_heap t_info)) O Hghc'
                 (graph_has_gen_O g') Hrecordable0).
            Intros.
            rewrite data_at__int_or_ptr_tptr.
            assert (Hspacew:
              writable_share
                (space_sh (nth_space (pt_heap (ti_heap t_info)) O))).
            { rewrite <- Hspace_sh. apply generation_share_writable. }
            rewrite heap_head_nth_space_O.
            forward.
            assert (Hpcell_ptr:
              isptr
                (field_address
                   (tarray int_or_ptr_type
                     (Zlength (make_fields_vals g src)))
                   [ArraySubsc pos] (vertex_address g src))).
            { destruct Hfield. assumption. }
            rewrite <- data_at_int_or_ptr_tptr by exact Hpcell_ptr.
            rewrite <- Hcell. unfold interior_address.
            assert (Haddr:
              vertex_address g' src = vertex_address g src).
            { eapply mutable_graph_update_vertex_address; eassumption. }
            rewrite <- Haddr.
            sep_apply
              (remset_rep_upd_int
                 g' (pt_heap (ti_heap t_info)) O rh src pos Hghc'
                 (graph_has_gen_O g') Hrhhc Hrecordable0).
            set (h := pt_heap (ti_heap t_info)) in *.
            set (hp := ti_heap_p t_info) in *.
            assert (Hrange0: 0 <= Z.of_nat O < Zlength (spaces h)).
            { pose proof (spaces_size h) as Hlen.
              rewrite MAX_SPACES_eq in Hlen. lia. }
            assert (Htails:
              tl (spaces (incr_remset_heap h (Z.of_nat O))) =
              tl (spaces h)).
            { rewrite spaces_incr_remset_heap_split by exact Hrange0.
              simpl. destruct (spaces h); reflexivity. }
            assert (Htoken:
              ti_token_rep h hp =
              ti_token_rep (incr_remset_heap h (Z.of_nat O)) hp).
            { apply ti_token_rep_weak_heap_relation.
              apply incr_remset_heap_whr. }
            Exists g'
              (Build_thread_info
                 hp
                 (build_compatible_heap
                    (incr_remset_heap h (Z.of_nat O)))
                 (ti_args t_info) (arg_size t_info)
                 (ti_frames t_info) (ti_nalloc t_info))
              (upd_remset_heap
                 (RemSetInterior (InteriorVertexPos src pos)) rh O).
            unfold decr_info_nursery, mtb_upd_remset_heap.
            destruct (isptr_dec (Vptr b i)) as [Hptr | Hnptr].
            2: { exfalso. apply Hnptr. exact I. }
            entailer!.
            unfold before_gc_thread_info_rep, heap_management_rep.
            simpl pt_heap. rewrite heap_head_nth_space_O.
            rewrite irh_used_space, irh_space_start, irh_total_space.
            pose proof
              (irh_available_space_same h O Hrange0 Hrecordable0)
              as Havail.
            pose proof Htails as Htails'.
            pose proof Htoken as Htoken'.
            cbn in Havail, Htails', Htoken'.
            rewrite Htoken'.
            rewrite Havail, Htails'.
            unfold ti_fp. simpl ti_frames. cancel.
            cbv [Vptrofs Archi.ptr64].
            unfold data_at, field_at.
            simpl nested_field_type. simpl nested_field_offset.
            simpl ti_heap_p. cancel. apply derives_refl.
          - match goal with
            | Hfalse : Int.repr 1 = Int.zero |- _ =>
                apply Int.one_not_zero in Hfalse; contradiction
            end. }
Qed.
