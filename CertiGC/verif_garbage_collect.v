From CertiGraph.CertiGC Require Import env_graph_gc gc_spec.
Require Import CertiGraph.msl_ext.iter_sepcon.

Local Open Scope logic.

Lemma sem_sub_pp_available_space: forall s,
    isptr (space_start s) ->
    force_val
      (sem_sub_pp int_or_ptr_type
                  (offset_val (WORD_SIZE * available_space s) (space_start s))
                  (space_start s)) =
    if Archi.ptr64 then Vlong (Int64.repr (available_space s)) else
      Vint (Int.repr (available_space s)).
Proof.
  intros. destruct (space_start s); try contradiction. simpl. destruct (eq_block b b).
  2: exfalso; apply n; reflexivity.
  unfold sem_sub_pp; destruct eq_block; [|easy].
  inv_int i. rewrite ptrofs_add_repr, ptrofs_sub_repr.
  replace (ofs + WORD_SIZE * available_space s - ofs) with
      (WORD_SIZE * available_space s)%Z by lia. simpl.
  pose proof (available_space_signed_range s). unfold Ptrofs.divs.
  rewrite !Ptrofs.signed_repr by rep_lia.
  rewrite Vptrofs_unfold_true, ptrofs_to_int64_repr by reflexivity.
  do 2 f_equal.
  unfold WORD_SIZE. rewrite Z.mul_comm, Z.quot_mul by lia. auto.
Qed.

Lemma sem_sub_pp_total_space: forall s,
    isptr (space_start s) ->
    force_val
      (sem_sub_pp int_or_ptr_type
                  (offset_val (WORD_SIZE * total_space s) (space_start s))
                  (space_start s)) =
    if Archi.ptr64 then Vlong (Int64.repr (total_space s)) else
      Vint (Int.repr (total_space s)).
Proof.
  intros. destruct (space_start s); try contradiction. simpl. destruct (eq_block b b).
  2: exfalso; apply n; reflexivity.
  unfold sem_sub_pp; destruct eq_block; [|easy].
  inv_int i. rewrite ptrofs_add_repr, ptrofs_sub_repr.
  replace (ofs + WORD_SIZE * total_space s - ofs) with
      (WORD_SIZE * total_space s)%Z by lia. simpl.
  pose proof (total_space_signed_range s). unfold Ptrofs.divs.
  rewrite !Ptrofs.signed_repr by rep_lia.
  rewrite Vptrofs_unfold_true, ptrofs_to_int64_repr by reflexivity.
  do 2 f_equal.
  unfold WORD_SIZE. rewrite Z.mul_comm, Z.quot_mul by lia. auto.
Qed.

Lemma sem_sub_pp_rest_space: forall s,
    isptr (space_start s) ->
    force_val
      (sem_sub_pp int_or_ptr_type
                  (offset_val (WORD_SIZE * available_space s) (space_start s))
                  (offset_val (WORD_SIZE * used_space s) (space_start s))) =
    if Archi.ptr64 then Vlong (Int64.repr (available_space s - used_space s)) else
      Vint (Int.repr (available_space s - used_space s)).
Proof.
  intros. destruct (space_start s); try contradiction. simpl. destruct (eq_block b b).
  2: exfalso; apply n; reflexivity.
  inv_int i. unfold sem_sub_pp; destruct eq_block; [|easy].
  rewrite !ptrofs_add_repr, ptrofs_sub_repr.
  replace (ofs + WORD_SIZE * available_space s - (ofs + WORD_SIZE * used_space s)) with
          (WORD_SIZE * (available_space s - used_space s))%Z by
      (rewrite Z.mul_sub_distr_l; lia). simpl.
  pose proof (rest_space_signed_range s). rewrite <- Z.mul_sub_distr_l in H0.
  rewrite Vptrofs_unfold_true by reflexivity.
  unfold Ptrofs.divs. rewrite !Ptrofs.signed_repr by rep_lia.
  rewrite ptrofs_to_int64_repr by reflexivity.
  do 2 f_equal.
  unfold WORD_SIZE.
  rewrite Z.mul_comm, Z.quot_mul by lia. auto.
Qed.

Lemma t_info_space_address: forall t_info i,
    0 <= i -> isptr (ti_heap_p t_info) ->
    (if Archi.ptr64 then
      force_val (sem_add_ptr_long space_type (offset_val 0 (ti_heap_p t_info))
                                  (Vlong (Int64.repr i))) else
      force_val (sem_add_ptr_int space_type Signed
                                 (offset_val 0 (ti_heap_p t_info)) (Vint (Int.repr i)))) =
    space_address (ti_heap_p t_info) (Z.to_nat i).
Proof.
  intros. rewrite isptr_offset_val_zero by assumption. simpl.
  first [rewrite sem_add_pi_ptr_special' | rewrite sem_add_pl_ptr_special']; auto.
  unfold space_address. rewrite Z2Nat.id by lia. simpl. f_equal.
Qed.

Ltac tc_val_Znth := entailer!!; rewrite Znth_map by assumption;
                    unfold space_quad; apply isptr_is_pointer_or_null;
                    try assumption.

Lemma gather_thread_info_rep:
  forall (v1 v2: val) sh t_info ti ,
   data_at sh thread_info_type (v1,(v2, (ti_heap_p t_info, (ti_args t_info, (ti_fp t_info, (Vptrofs(ti_nalloc t_info),nullval)))))) ti
   * frames_rep sh (ti_frames t_info)
   * data_at sh heap_type (@map space (val * (val * (val*val)))  space_quad (spaces (pt_heap (ti_heap t_info)))) (ti_heap_p t_info)
   * heap_unused_rep (pt_heap (ti_heap t_info))
   * ti_token_rep (pt_heap (ti_heap t_info)) (ti_heap_p t_info)
   |-- thread_info_rep sh t_info ti.
Proof.
  intros.
  unfold thread_info_rep, heap_rep, heap_struct_rep.
  do 2 unfold_data_at (data_at _ thread_info_type _ _).
  cancel.
Qed.

Lemma ti_rel_token_the_same_weak: forall (h1 h2: part_heap) p,
    weak_heap_relation h1 h2 -> ti_token_rep h1 p = ti_token_rep h2 p.
Proof.
  intros h1 h2 p [Hstart Htotal]. unfold ti_token_rep. f_equal.
  apply (iter_sepcon_pointwise_eq _ _ _ _ null_space null_space).
  - rewrite <- !ZtoNat_Zlength, !spaces_size. reflexivity.
  - intros. fold (nth_space h1 i). fold (nth_space h2 i).
    unfold total_size in Htotal.
    unfold space_token_rep.
    rewrite Hstart, Htotal. reflexivity.
Qed.

Lemma remset_item_val_add_new_gen: forall g gi from rmst item,
    remset_item_compatible g from rmst item ->
    remset_item_val (lgraph_add_new_gen g gi) item = remset_item_val g item.
Proof.
  intros. destruct item as [addr | [v pos]]; simpl; auto.
  destruct H as [Hv _]. rewrite ang_vertex_address_old by exact Hv. reflexivity.
Qed.

Lemma space_remset_rep_add_new_gen: forall g gi from rmst sp rs,
    remset_and_remset_space_compatible g from rmst rs ->
    space_remset_rep g (sp, rs) =
    space_remset_rep (lgraph_add_new_gen g gi) (sp, rs).
Proof.
  intros. unfold space_remset_rep. destruct (Val.eq (space_start sp) nullval); auto.
  f_equal. apply map_ext_in. intros item Hin.
  hnf in H. rewrite Forall_forall in H.
  symmetry. apply remset_item_val_add_new_gen with (from := from) (rmst := rmst).
  apply H. exact Hin.
Qed.

Lemma heap_remset_rep_add_new_gen: forall g h rh gi from rmst,
    remset_and_remset_heap_compatible g from rmst rh ->
    heap_remset_rep g h rh =
    heap_remset_rep (lgraph_add_new_gen g gi) h rh.
Proof.
  intros. unfold heap_remset_rep. apply iter_sepcon_func_strong.
  intros [sp rs] Hin. apply space_remset_rep_add_new_gen with (from := from) (rmst := rmst).
  hnf in H. rewrite Forall_forall in H. apply H.
  eapply in_combine_r. exact Hin.
Qed.

Lemma remset_rep_add_new_gen: forall sh g gi outlier rmst,
    remset_graph_outlier_compatible g outlier rmst ->
    remset_rep sh g rmst =
    remset_rep sh (lgraph_add_new_gen g gi) rmst.
Proof.
  intros. unfold remset_rep. apply iter_sepcon_func_strong.
  intros rext Hin. unfold remset_ext_rep.
  destruct rext as [out addr | v addr]; auto.
  f_equal. symmetry. apply ang_vertex_address_old.
  hnf in H. rewrite Forall_forall in H.
  specialize (H _ Hin). simpl in H. exact H.
Qed.

Lemma remset_ext_compatible_add_new_gen: forall g gi outlier rext,
    remset_ext_compatible g outlier rext ->
    remset_ext_compatible (lgraph_add_new_gen g gi) outlier rext.
Proof.
  intros. destruct rext as [out addr | v addr]; simpl in *; auto.
  apply ang_graph_has_v. assumption.
Qed.

Lemma remset_item_compatible_add_new_gen: forall g gi from rmst item,
    remset_item_compatible g from rmst item ->
    remset_item_compatible (lgraph_add_new_gen g gi) from rmst item.
Proof.
  intros. destruct item as [addr | [v pos]]; simpl in *; auto.
  destruct H as [Hv [Hpos Hmark]]. split.
  - apply ang_graph_has_v. assumption.
  - split; assumption.
Qed.

Lemma remset_compatible_add_new_empty: forall g h rh rmst outlier from gi sp i
    (Hs: 0 <= i < MAX_SPACES),
    remset_compatible g outlier from rmst rh h ->
    space_start (Znth i (spaces h)) = nullval ->
    available_space sp = total_space sp ->
    remset_compatible (lgraph_add_new_gen g gi) outlier from rmst rh
      (add_new_space h sp i Hs).
Proof.
  intros g h rh rmst outlier from gi sp i Hs Hremc Hnull Hfresh.
  destruct Hremc as [Hrgo [Hrgh Hrhh]].
  split.
  - hnf in Hrgo |- *. rewrite Forall_forall in *. intros rext Hin.
    apply remset_ext_compatible_add_new_gen. apply Hrgo. exact Hin.
  - split.
    + hnf in Hrgh |- *. rewrite Forall_forall in *. intros rs Hin.
      specialize (Hrgh _ Hin). hnf in Hrgh |- *. rewrite Forall_forall in *.
      intros item Hitem. apply remset_item_compatible_add_new_gen.
      apply Hrgh. exact Hitem.
    + hnf in Hrhh |- *. rewrite Forall2_forall_Znth in *.
      destruct Hrhh as [Hlen Hrhh]. split.
      * simpl. rewrite upd_Znth_Zlength by (rewrite spaces_size; exact Hs).
        exact Hlen.
      * intros j Hj. simpl in Hj.
        assert (Hj_sp: 0 <= j < Zlength (spaces h)) by
          (rewrite <- Hlen; exact Hj).
        destruct (Z.eq_dec j i).
        -- subst j.
           change (spaces (add_new_space h sp i Hs)) with
             (upd_Znth i (spaces h) sp).
           rewrite upd_Znth_same by (rewrite spaces_size; exact Hs).
           specialize (Hrhh i ltac:(rewrite Hlen, spaces_size; exact Hs)).
           unfold remset_space_size_compatible in *.
           rewrite Hnull in Hrhh. destruct (Val.eq nullval nullval); [|contradiction].
           destruct (Val.eq (space_start sp) nullval).
           ++ exact Hrhh.
           ++ rewrite Hrhh, Hfresh. lia.
        -- change (spaces (add_new_space h sp i Hs)) with
             (upd_Znth i (spaces h) sp).
           rewrite upd_Znth_diff by
             (try exact Hj_sp; try (rewrite spaces_size; exact Hs); lia).
           apply Hrhh. exact Hj.
Qed.

Lemma heap_remset_rep_add_empty_space: forall g h rh sp i (Hs: 0 <= i < MAX_SPACES),
    remset_heap_and_heap_compatible rh h ->
    space_start (Znth i (spaces h)) = nullval ->
    available_space sp = total_space sp ->
    isptr (space_start sp) ->
    heap_remset_rep g h rh |-- heap_remset_rep g (add_new_space h sp i Hs) rh.
Proof.
  intros g h rh sp i Hs Hrhh Hnull Hfresh Hptr.
  unfold heap_remset_rep. simpl.
  hnf in Hrhh. rewrite Forall2_forall_Znth in Hrhh.
  destruct Hrhh as [Hlen Hrhh].
  remember (spaces h) as l.
  assert (Hl: Zlength l = MAX_SPACES) by (subst; apply spaces_size).
  assert (Hrh_len: Zlength rh = MAX_SPACES) by (rewrite Hlen, Hl; reflexivity).
  rewrite upd_Znth_unfold by (subst; rewrite spaces_size; exact Hs).
  rewrite <- (sublist_same 0 (Zlength l) l) at 1 by lia.
  rewrite <- (sublist_same 0 (Zlength rh) rh) at 1 by lia.
  rewrite <- (sublist_rejoin 0 i (Zlength l) l) at 1 by lia.
  rewrite <- (sublist_rejoin 0 i (Zlength rh) rh) at 1 by lia.
  rewrite (sublist_next i (Zlength l) l) by lia.
  rewrite (sublist_next i (Zlength rh) rh) by lia.
  assert (Hrh_split: rh = sublist 0 i rh ++ Znth i rh :: sublist (i + 1) (Zlength rh) rh). {
    transitivity (sublist 0 (Zlength rh) rh).
    - rewrite sublist_same by lia. reflexivity.
    - rewrite <- (sublist_rejoin 0 i (Zlength rh) rh) by lia.
      f_equal. rewrite (sublist_next i (Zlength rh) rh) by lia. reflexivity.
  }
  replace (combine (sublist 0 i l ++ [sp] ++ sublist (i + 1) (Zlength l) l) rh)
    with (combine (sublist 0 i l ++ [sp] ++ sublist (i + 1) (Zlength l) l)
                  (sublist 0 i rh ++ Znth i rh :: sublist (i + 1) (Zlength rh) rh)) by
    (rewrite <- Hrh_split; reflexivity).
  rewrite !combine_app' by list_solve.
  simpl.
  rewrite !iter_sepcon_app_sepcon. Opaque space_remset_rep. simpl.
  cancel. Transparent space_remset_rep.
  unfold space_remset_rep.
  assert (Hnull_l: space_start (Znth i l) = nullval) by (subst; exact Hnull).
  rewrite Hnull_l. destruct (Val.eq nullval nullval); [|contradiction].
  specialize (Hrhh i ltac:(rewrite Hrh_len; exact Hs)).
  unfold remset_space_size_compatible in Hrhh.
  rewrite Hnull_l in Hrhh. destruct (Val.eq nullval nullval) in Hrhh; [|contradiction].
  apply Zlength_nil_inv in Hrhh. rewrite Hrhh.
  destruct (Val.eq (space_start sp) nullval).
  - destruct (space_start sp); try contradiction; simpl in e; try discriminate.
  - rewrite Hfresh. replace (total_space sp - total_space sp) with 0 by lia.
    rewrite data_at_zero_array_eq;
      [entailer! | reflexivity | apply isptr_offset_val'; exact Hptr | reflexivity].
Qed.

Lemma body_garbage_collect:
  semax_body Vprog Gprog f_garbage_collect garbage_collect_spec.
Proof.
  start_function.
  assert (Tf: forall (tif: thread_info) (j: Z),
             0 <= j -> offset_val (sizeof (Tstruct _space noattr) * j) (ti_heap_p tif)=
                       space_address (ti_heap_p tif) (Z.to_nat j)). {
          intros. unfold space_address. now rewrite Z2Nat.id. }
  unfold before_gc_thread_info_rep, heap_management_rep, heap_struct_rep. Intros.
  rename H1 into Hsafeh. rename H2 into Hremc. pose proof H0 as Hgcc_init.
  assert (Hsafe_graph: safe_to_copy g) by
      (eapply safe_to_copy_heap_implies_safe_to_copy;
       [apply (proj1 H) | destruct H0 as [_ [_ [_ Hsize]]]; exact Hsize | exact Hsafeh]).
  forward.
  pose proof H as Hsc_init.
  destruct Hsc_init as [Hghc_init _].
  pose proof (gt_gs_compatible _ _ Hghc_init _ (graph_has_gen_O _)) as Hgen0.
  destruct Hgen0 as [Hstart0 [? ?]].
  replace (heap_head (pt_heap (ti_heap t_info))) with (nth_space (pt_heap (ti_heap t_info)) 0) by
      (destruct (heap_head_cons (pt_heap (ti_heap t_info))) as [hs [hl [Hspaces_head Hhead_eq]]];
       unfold nth_space; rewrite Hspaces_head, Hhead_eq; simpl; reflexivity).
  assert (isptr (space_start (nth_space (pt_heap (ti_heap t_info)) 0))) by
    (rewrite <- Hstart0; apply start_isptr). do 2 forward. deadvars!.
  simpl fst in *. simpl snd in *. rewrite upd_Znth0_old.
  2: { pose proof (@Zlength_nonneg (val * (val * (val*val)))
                                   (map space_quad (tl (spaces (pt_heap (ti_heap t_info)))))).
       rewrite Zlength_cons. lia. }
  rewrite sublist_1_cons, Zlength_cons, sublist_same by lia.
  do 2 forward.
  simpl fst. simpl snd. rewrite upd_Znth0_old.
  2: { pose proof (@Zlength_nonneg (val * (val * (val*val)))
                                   (map space_quad (tl (spaces (pt_heap (ti_heap t_info)))))).
       rewrite Zlength_cons. lia. }
  rewrite sublist_1_cons, Zlength_cons, sublist_same by lia.
  fold (space_quad (nth_space (pt_heap (ti_heap t_info)) 0)). rewrite <- map_cons.
  replace (nth_space (pt_heap (ti_heap t_info)) 0 :: tl (spaces (pt_heap (ti_heap t_info)))) with
      (spaces (pt_heap (ti_heap t_info))) by
      (destruct (heap_head_cons (pt_heap (ti_heap t_info))) as [hs [hl [Hspaces_head Hhead_eq]]];
       unfold nth_space; rewrite Hspaces_head; simpl; reflexivity).
  sep_apply gather_thread_info_rep.
  forward_for_simple_bound
    (MAX_SPACES - 1)
    (EX i: Z, EX g': LGraph, EX roots': roots_t, EX t_info': thread_info,
     EX rh': remset_heap, EX rmst': remset,
     PROP (super_compatible g' (ti_heap t_info').(pt_heap) (frames2rootpairs (ti_frames t_info')) roots' outlier;
           garbage_collect_condition g' (ti_heap t_info').(pt_heap);
           safe_to_copy_to_except g' (Z.to_nat i);
           safe_to_copy_to_except_heap g' (ti_heap t_info').(pt_heap) (Z.to_nat i);
           firstn_gen_clear g' (Z.to_nat i);
           garbage_collect_loop (nat_inc_list (Z.to_nat i)) roots g roots' g';
           graph_has_gen g' (Z.to_nat i);
           frame_shells_eq (ti_frames t_info) (ti_frames t_info');
           ti_nalloc t_info = ti_nalloc t_info';
           remset_compatible g' outlier (Z.to_nat i) rmst' rh' (ti_heap t_info').(pt_heap))
     LOCAL (temp _h (ti_heap_p t_info'); temp _ti ti;
            gvars gv)
     SEP (thread_info_rep sh t_info' ti;
          heap_remset_rep g' (ti_heap t_info').(pt_heap) rh';
          remset_rep sh g' rmst';
          mem_mgr gv;
          all_string_constants rsh gv;
          outlier_rep outlier;
          graph_rep g')).
  - Exists g roots t_info rh rmst. destruct Hgcc_init as [? [? [? ?]]].
    pose proof (graph_has_gen_O g). entailer!!.
    repeat split.
    + apply stc_stcte_O_iff; assumption.
    + apply stch_stcteh_O_iff; assumption.
    + red. intros. lia.
    + unfold nat_inc_list. simpl. constructor.
    + apply frame_shells_eq_refl.
  - cbv beta. Intros g' roots' t_info' rh' rmst'.
    rename H5 into Hsc_loop. rename H6 into Hgcc_loop.
    rename H7 into Hstcte_loop. rename H8 into Hstcteh_loop.
    rename H9 into Hfirst_loop. rename H10 into Hgcl_loop.
    rename H11 into Hhas_i_loop. rename H12 into FSE.
    rename H13 into HN. rename H14 into Hremc_loop.
    unfold thread_info_rep, heap_rep. Intros.
    unfold heap_struct_rep.
    assert (Hi1_range: 0 <= i + 1 < Zlength (spaces (ti_heap t_info').(pt_heap))) by
        (rewrite spaces_size; rep_lia).
    pose proof (space_start_is_pointer_or_null _ _ _ (proj1 Hsc_loop) Hi1_range).
    forward.
    1: entailer!!.
     1: entailer!!; rewrite Znth_map by assumption; unfold space_quad; assumption.
    rewrite Znth_map by assumption. unfold space_quad at 1.
    forward_if
      (EX g1: LGraph, EX t_info1: thread_info,
       EX rh1: remset_heap, EX rmst1: remset,
       PROP (super_compatible g1 (pt_heap (ti_heap t_info1)) (frames2rootpairs (ti_frames t_info1)) roots' outlier;
             garbage_collect_condition g1 (pt_heap (ti_heap t_info1));
             safe_to_copy_to_except g1 (Z.to_nat i);
             safe_to_copy_to_except_heap g1 (pt_heap (ti_heap t_info1)) (Z.to_nat i);
             firstn_gen_clear g1 (Z.to_nat i);
             new_gen_relation (Z.to_nat (i + 1)) g' g1;
             graph_has_gen g1 (Z.to_nat (i + 1));
             frame_shells_eq (ti_frames t_info) (ti_frames t_info1);
             ti_nalloc t_info = ti_nalloc t_info1;
             remset_compatible g1 outlier (Z.to_nat i) rmst1 rh1 (pt_heap (ti_heap t_info1)))
       LOCAL (temp _h (ti_heap_p t_info1); temp _ti ti;
              gvars gv; temp _i (Vint (Int.repr i)))
       SEP (thread_info_rep sh t_info1 ti;
            heap_remset_rep g1 (pt_heap (ti_heap t_info1)) rh1;
            remset_rep sh g1 rmst1;
            mem_mgr gv;
            all_string_constants rsh gv;
            outlier_rep outlier;
            graph_rep g1)).
    + remember (space_start (Znth (i + 1) (spaces (pt_heap (ti_heap t_info'))))).
      Transparent denote_tc_test_eq. destruct v0; try contradiction; simpl; entailer!!.
        assert (isptr (Vptr b i0)) by exact I. rewrite Heqv0 in *.
        pull_left (heap_unused_rep (pt_heap (ti_heap t_info'))).
        pull_left (heap_remset_rep g' (pt_heap (ti_heap t_info')) rh').
        pull_left (graph_rep g').
        pose proof (proj1 Hsc_loop) as Hghc'.
        rewrite <- (space_start_isptr_iff g') in H14 by assumption.
        pose proof Hremc_loop as Hremc'.
        destruct Hremc' as [_ [_ Hrhhc']].
        pose proof (Forall2_length Hrhhc') as Hrh_len'.
        destruct Hgcc_loop as [_ [_ [_ Hsize']]].
        sep_apply (graph_and_heap_remset_valid_ptr
                     g' (pt_heap (ti_heap t_info')) rh' _ H14 Hghc' Hrh_len' Hsize').
        rewrite nth_space_Znth, Z2Nat.id by lia.
        sep_apply (valid_pointer_weak
                     (space_start (Znth (i + 1) (spaces (pt_heap (ti_heap t_info')))))).
        apply extend_weak_valid_pointer. Opaque denote_tc_test_eq.
    + assert (0 <= i < Zlength (spaces (pt_heap (ti_heap t_info')))) by lia.
      pose proof (space_start_isptr _ _ _ (proj1 Hsc_loop) Hhas_i_loop) as Hstart_i.
      rewrite nth_space_Znth, Z2Nat.id in Hstart_i by lia. forward.
      entailer!!.
      1: entailer!!; rewrite Znth_map by assumption; unfold space_quad;
        apply isptr_is_pointer_or_null, isptr_offset_val'; exact Hstart_i.
      rewrite Znth_map by assumption. unfold space_quad at 1. forward.
      entailer!!.
      1: entailer!!; rewrite Znth_map by assumption; unfold space_quad;
        apply isptr_is_pointer_or_null; exact Hstart_i.
      rewrite Znth_map by assumption. unfold space_quad at 1. forward.
      1: entailer!!; destruct (space_start (Znth i (spaces (pt_heap (ti_heap t_info')))));
        try contradiction; simpl; unfold denote_tc_samebase;
          apply prop_right; simpl; destruct (peq b b); simpl; [|apply n]; auto.
      simpl sem_binary_operation'.
      change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some _ |})
        with int_or_ptr_type. remember (Znth i (spaces (pt_heap (ti_heap t_info')))).
      subst s.
      rewrite sem_sub_pp_total_space by exact Hstart_i.
      pose proof Hgcc_loop as Hgcc'.
      destruct Hgcc' as [_ [_ [_ Hsize_spec']]].
      pose proof (ti_size_gen _ _ _ (proj1 Hsc_loop) Hhas_i_loop Hsize_spec') as Htotal_i.
      unfold total_size in Htotal_i.
      rewrite nth_space_Znth, Z2Nat.id in Htotal_i by lia.
      simpl in Htotal_i. rewrite Htotal_i. clear Hsize_spec' Htotal_i.
      assert_PROP (isptr (ti_heap_p t_info')) as Hheap_ptr by entailer!.
      sep_apply gather_thread_info_rep.
      assert (Hi1_max: 0 <= i + 1 < MAX_SPACES) by lia.
      unfold thread_info_rep, heap_rep. Intros.
      rewrite hsr_single_explicit with (i := i + 1). 2: exact Hi1_max.
      2: rewrite Zlength_map, spaces_size; reflexivity. Intros.
      sep_apply (data_at_data_at_
                   sh space_type
                   (Znth (i + 1) (map space_quad (spaces (pt_heap (ti_heap t_info')))))
                   (space_address (ti_heap_p t_info') (Z.to_nat (i + 1)))).
      pose proof (t_info_space_address _ _ (proj1 Hi1_range) Hheap_ptr) as Hspace_addr_i1.
      simpl in Hspace_addr_i1.
      assert (0 <= 2 * nth_gen_size (Z.to_nat i) <= MAX_SPACE_SIZE) by
          (rewrite ngs_S by lia; apply ngs_range; rep_lia).
      forward_call (sh, (space_address (ti_heap_p t_info') (Z.to_nat (i + 1))),
                    (2 * nth_gen_size (Z.to_nat i))%Z, gv, rsh).
      * first [rewrite Int64.signed_repr by (apply ngs_int_signed_range; rep_lia) |
               rewrite Int.signed_repr by (apply ngs_int_singed_range; rep_lia)].
        rewrite ngs_S by lia. apply ngs_int_signed_range. rep_lia.
      * simpl. entailer!!. f_equal. now rewrite Tf.
      * Intros p.
        pose proof (ngs_S i (proj1 H4)) as Hngs_i.
        rewrite Hngs_i in *.
        assert (Hso: 0 <= 0 <= (nth_gen_size (Z.to_nat (i + 1)))) by lia.
        rewrite data_at__isptr. Intros.
        remember (Build_space p 0
                              (nth_gen_size (Z.to_nat (i + 1)))
                              (nth_gen_size (Z.to_nat (i + 1)))
                              Ews Hso (Z.le_refl _) (proj2 H8))
          as sp. remember (Build_generation_info p O Ews Pp writable_Ews) as gi.
        assert (forall (gr: LGraph) (gen: nat),
                   generation_space_compatible gr (gen, gi, sp)) by
            (intros; red; rewrite Heqsp, Heqgi; simpl; intuition).
        remember (lgraph_add_new_gen g' gi) as g1.
        assert (Hfresh_sp: available_space sp = total_space sp) by
          (subst sp; simpl; reflexivity).
        remember (ti_add_new_space t_info' sp _ Hi1_max Hfresh_sp) as t_info1.
        pose proof H6 as Hnext_null.
        rewrite <- (space_start_isnull_iff g') in Hnext_null; auto.
        2: apply (proj1 Hsc_loop).
        assert (Hgi_empty: number_of_vertices gi = O) by (subst gi; simpl; reflexivity).
        assert (super_compatible g1 (pt_heap (ti_heap t_info1)) (frames2rootpairs (ti_frames t_info1)) roots' outlier). {
          subst g1 t_info1. simpl ti_heap. simpl pt_heap. simpl ti_frames. apply super_compatible_add; auto.
          replace (i + 1 - 1) with i by lia. assumption. }
        assert (firstn_gen_clear g1 (Z.to_nat i)) by
            (subst g1; apply firstn_gen_clear_add; assumption).
        assert (new_gen_relation (Z.to_nat (i + 1)) g' g1). {
          subst g1. red. rewrite if_false by assumption. exists gi. split; auto. }
        gather_SEP (malloc_token Ews (tarray int_or_ptr_type (nth_gen_size (Z.to_nat (i + 1)))) p) (ti_token_rep (pt_heap (ti_heap t_info')) (ti_heap_p t_info')).
        assert (Hav_sp: available_space sp = nth_gen_size (Z.to_nat (i + 1))) by
            (subst sp; simpl; reflexivity).
        assert (Htot_sp: total_space sp = nth_gen_size (Z.to_nat (i + 1))) by
            (subst sp; simpl; reflexivity).
        rewrite <- Htot_sp.
        assert (Hstart_sp: space_start sp = p) by (subst sp; simpl; reflexivity).
        rewrite <- Hstart_sp.
        assert (Hstart_sp_nonnull: space_start sp <> nullval) by
            (rewrite Hstart_sp; destruct p; try contradiction; intro Hcontra; inversion Hcontra).
        sep_apply (ti_token_rep_add (pt_heap (ti_heap t_info')) (ti_heap_p t_info') sp (i + 1) Hi1_max); auto.
        replace (space_start sp,
                 (space_start sp,
                  (offset_val (WORD_SIZE * total_space sp) (space_start sp),
                   offset_val (WORD_SIZE * total_space sp) (space_start sp)))) with
            (space_quad sp) by
            (unfold space_quad; do 2 f_equal; subst sp; simpl;
             try rewrite isptr_offset_val_zero by assumption; reflexivity).

        gather_SEP
          (data_at sh space_type _ _)
          (data_at sh (tarray space_type
                              (Zlength
                                 (sublist (i + 1 + 1) MAX_SPACES
                                    (map space_quad (spaces (pt_heap (ti_heap t_info'))))))) _
                   (offset_val (sizeof space_type)
                               (offset_val (SPACE_STRUCT_SIZE * (i + 1)) (ti_heap_p t_info'))))
          (data_at sh (tarray space_type (i + 1)) _
                   (ti_heap_p t_info')).
  (* the above "match goal with" replaces the following, which was absurdly slow:
        gather_SEP
          (data_at sh space_type _ _)
          (data_at sh (tarray space_type
                              (Zlength
                                 (sublist (i + 1 + 1) 12 (map space_quad (spaces (ti_heap t_info')))))) _
                   (offset_val (sizeof space_type)
                               (offset_val (SPACE_STRUCT_SIZE * (i + 1)) (ti_heap_p t_info'))))
          (data_at sh (tarray space_type (i + 1)) _
                   (ti_heap_p t_info')).
    *)
        pose proof (heap_struct_rep_add (ti_heap_p t_info')
                      (pt_heap (ti_heap t_info')) sh sp
                      (Z.succ i) Hi1_max) as Hheap_struct_add.
        change (Z.succ i) with (i + 1) in Hheap_struct_add.
        replace_SEP 0
          (heap_struct_rep sh
             (map space_quad (spaces (add_new_space (pt_heap (ti_heap t_info')) sp (i + 1) Hi1_max)))
             (ti_heap_p t_info')) by
          (rewrite <- Hheap_struct_add; entailer!).
        replace (ti_heap_p t_info') with (ti_heap_p t_info1) by (clear - Heqt_info1; subst; reflexivity).
        replace (ti_args t_info') with (ti_args t_info1) by (clear - Heqt_info1; subst; reflexivity).
        replace (ti_heap_p t_info') with (ti_heap_p t_info1) by
            (subst t_info1; simpl; reflexivity).
        replace (ti_args t_info') with (ti_args t_info1) by
            (subst t_info1; simpl; reflexivity).
        replace_SEP 4 (space_unused_rep sp) by
        (
          unfold space_unused_rep;
          rewrite if_false by assumption;
          replace (space_sh sp) with Ews by (subst sp; simpl; reflexivity);
          replace (used_space sp) with 0 by (subst sp; simpl; reflexivity);
          rewrite Z.sub_0_r, Z.mul_0_r, isptr_offset_val_zero by
              (subst; simpl; assumption);
          rewrite Hfresh_sp;
          entailer!!
        ).
        gather_SEP (heap_unused_rep (pt_heap (ti_heap t_info'))) (space_unused_rep sp).
        rewrite (heap_unused_rep_add _ _ (i + 1) Hi1_max) by assumption.
        gather_SEP
          (data_at sh thread_info_type _ _)
          (frames_rep _ _)
          (heap_struct_rep _ _ _)
          (heap_unused_rep _)
          (ti_token_rep _ _).
        replace_SEP 0 (thread_info_rep sh t_info1 ti) by
            (unfold thread_info_rep, heap_rep; entailer!!).
        rewrite (graph_rep_add g' gi).
        2: exact Hgi_empty.
        2: { destruct Hgcc_loop as [Hunmarked _].
             apply graph_unmarked_copy_compatible; assumption. }
        2: { destruct Hgcc_loop as [_ [_ [Hndd _]]]. exact Hndd. }
        rewrite <- Heqg1.
        assert (Hi1_nat: Z.to_nat (i + 1) = S (Z.to_nat i)) by
            (rewrite Z2Nat.inj_add by lia; simpl; lia).
        assert (graph_has_gen g1 (Z.to_nat (i + 1))). {
          subst g1. rewrite ang_graph_has_gen. right.
          rewrite Hi1_nat in Hnext_null |- *.
          unfold graph_has_gen in Hhas_i_loop, Hnext_null. lia. }
        assert (safe_to_copy_to_except g1 (Z.to_nat i)) by
            (subst g1; apply stcte_add; auto; subst gi; simpl; reflexivity).
        assert (safe_to_copy_to_except_heap g1 (pt_heap (ti_heap t_info1)) (Z.to_nat i)). {
          subst g1 t_info1.
          eapply stcteh_add with (new := i + 1) (Hs := Hi1_max).
          - exact Hi1_nat.
          - apply (proj1 Hsc_loop).
          - exact Hhas_i_loop.
          - intro Hnext. apply Hnext_null. rewrite Hi1_nat. exact Hnext.
          - destruct Hgcc_loop as [_ [_ [_ Hsize']]]. exact Hsize'.
          - subst sp; simpl. rewrite Hi1_nat. reflexivity.
          - exact Hfresh_sp.
          - subst sp; simpl; reflexivity.
          - exact Hstcteh_loop.
        }
        assert (garbage_collect_condition g1 (pt_heap (ti_heap t_info1))) by
            (subst g1 t_info1; apply gcc_add; assumption).
        pose proof Hremc_loop as Hremc_parts.
        destruct Hremc_parts as [Hrgo [Hrgh Hrhh]].
        assert (remset_compatible g1 outlier (Z.to_nat i) rmst' rh'
                  (pt_heap (ti_heap t_info1))). {
          subst g1 t_info1.
          apply remset_compatible_add_new_empty; assumption.
        }
        assert (Hsp_ptr: isptr (space_start sp)) by (subst sp; simpl; exact Pp).
        sep_apply (heap_remset_rep_add_empty_space
                     g' (pt_heap (ti_heap t_info')) rh' sp (i + 1)
                     Hi1_max Hrhh H6 Hfresh_sp Hsp_ptr).
        rewrite (heap_remset_rep_add_new_gen
                   g' (add_new_space (pt_heap (ti_heap t_info')) sp (i + 1) Hi1_max)
                   rh' gi (Z.to_nat i) rmst' Hrgh).
        rewrite (remset_rep_add_new_gen sh g' gi outlier rmst' Hrgo).
        Local Opaque super_compatible. Exists g1 t_info1 rh' rmst'. entailer!!.
    + forward. remember (space_start (Znth (i + 1) (spaces (pt_heap (ti_heap t_info'))))).
      assert (Hisptr_next: isptr v). {
        destruct v; try contradiction.
        hnf in H5; subst i0. contradiction H6; reflexivity.
        apply I.
      } subst v. rewrite <- (space_start_isptr_iff g') in Hisptr_next; auto.
      2: apply (proj1 Hsc_loop). assert (new_gen_relation (Z.to_nat (i + 1)) g' g') by
          (unfold new_gen_relation; rewrite if_true; auto).
      Exists g' t_info' rh' rmst'. entailer!!. unfold thread_info_rep, heap_rep, heap_struct_rep.
      entailer!!.
    + Intros g1 t_info1 rh1 rmst1.
      clear FSE HN.
      rename H6 into Hsc1. rename H7 into Hgcc1.
      rename H8 into Hstcte1. rename H9 into Hstcteh1.
      rename H10 into Hfirst1. rename H11 into Hnewgen1.
      rename H12 into Hgen1_next. rename H13 into FSE.
      rename H14 into HN. rename H15 into Hremc1.
      assert_PROP (isptr (ti_heap_p t_info1)) as Hheap_p1
        by (unfold thread_info_rep, heap_rep, heap_struct_rep; entailer!).
      assert (Hi1_nat2: Z.to_nat (i + 1) = S (Z.to_nat i)) by
          (rewrite Z2Nat.inj_add by lia; simpl; lia).
      assert (do_generation_condition
                g1 (pt_heap (ti_heap t_info1)) (Z.to_nat i) (Z.to_nat (i + 1))) by
          (rewrite Hi1_nat2 in *; eapply gc_cond_implies_do_gen_cons; eauto;
           apply (proj1 Hsc1)). pose proof (t_info_space_address _ _ (proj1 H4) Hheap_p1).
      pose proof (t_info_space_address _ _ (proj1 Hi1_range) Hheap_p1).
      unfold thread_info_rep. Intros.
      forward.
      freeze FR1 := (data_at _ _ _ _) (mem_mgr gv) (ti_token_rep _ _).
      forward_call (rsh, sh, gv, g1, (pt_heap (ti_heap t_info1)), (ti_heap_p t_info1),
                    (ti_frames t_info1), roots', outlier, rh1, rmst1,
                    (Z.to_nat i), (Z.to_nat (i + 1))).
      1: simpl; entailer!!; now rewrite !Tf.
      Intros vret. destruct vret as [[gpack h2] roots2].
      destruct gpack as [[[[g_rem h_rem] rh2] rmst2] g2].
      simpl fst in *. simpl snd in *.
      set (fr2 := update_frames _ _) in *.
      thaw FR1.
      pose (t_info2 := {| ti_heap_p := ti_heap_p t_info1;
                          ti_heap := build_compatible_heap h2; ti_args := ti_args t_info1;
                          arg_size := arg_size t_info1;
                          ti_frames := fr2; ti_nalloc := ti_nalloc t_info1|}).
      change (ti_heap_p t_info1) with (ti_heap_p t_info2).
      change h2 with (pt_heap (ti_heap t_info2)).
      change (ti_args t_info1) with (ti_args t_info2).
      replace (ti_fp t_info1) with (ti_fp t_info2).
      2:{ unfold ti_fp; simpl. unfold fr2. rewrite frames_p_update_frames. auto. }
      change (ti_nalloc t_info1) with (ti_nalloc t_info2).
      change fr2 with (ti_frames t_info2).
      unfold heap_rep. Intros. unfold heap_struct_rep.
      replace_SEP 10 (ti_token_rep (pt_heap (ti_heap t_info2)) (ti_heap_p t_info2))
        by (erewrite ti_rel_token_the_same_weak; eauto; entailer!!; apply derives_refl).
      sep_apply gather_thread_info_rep.
      unfold thread_info_rep, heap_rep, heap_struct_rep.
      Intros. assert (Hhas_i1_g2: graph_has_gen g2 (Z.to_nat (i + 1))) by
          (erewrite <- do_generation_relation_graph_has_gen; eauto).
      assert (Hhas_i_g2: graph_has_gen g2 (Z.to_nat i)) by
          (red in Hhas_i1_g2 |-*; lia).
      assert (isptr (space_start (Znth i (spaces (pt_heap (ti_heap t_info2)))))). {
          rewrite <- (Z2Nat.id i), <- nth_space_Znth by lia.
          pose proof (proj1 (gt_gs_compatible _ _ (proj1 H9) _ Hhas_i_g2))
            as Hstart_i_g2.
          change (pt_heap (ti_heap t_info2)) with h2. rewrite <- Hstart_i_g2.
        apply start_isptr. }
      assert (0 <= i < Zlength (spaces (pt_heap (ti_heap t_info2)))) by
          (rewrite spaces_size; rep_lia). forward.
      1:{ apply prop_right. clear - H4. rewrite MAX_SPACES_eq in H4. lia. }
      1: tc_val_Znth; rewrite isptr_offset_val; assumption. forward.
      1:{ apply prop_right. clear - H4. rewrite MAX_SPACES_eq in H4. lia. }
      1: tc_val_Znth.
      rewrite Znth_map by assumption. unfold space_quad at 1 2.
      assert (0 <= i + 1 < Zlength (spaces (pt_heap (ti_heap t_info2)))) by
          (rewrite spaces_size; rep_lia).
      assert (isptr (space_start (Znth (i + 1) (spaces (pt_heap (ti_heap t_info2)))))). {
        rewrite <- (Z2Nat.id (i + 1)), <- nth_space_Znth by lia.
        pose proof (proj1 (gt_gs_compatible _ _ (proj1 H9) _ Hhas_i1_g2))
          as Hstart_i1_g2.
        simpl in Hstart_i1_g2.
        change (pt_heap (ti_heap t_info2)) with h2. rewrite <- Hstart_i1_g2.
        apply start_isptr. }
      forward.
        1:{ apply prop_right. clear - H4. rewrite MAX_SPACES_eq in H4. lia. }
      1: tc_val_Znth; rewrite isptr_offset_val; assumption.
      forward.
      1:{ apply prop_right. clear - H4. rewrite MAX_SPACES_eq in H4. lia. }
      1: tc_val_Znth; rewrite isptr_offset_val; assumption.
      rewrite Znth_map by assumption. unfold space_quad at 1 2. rewrite Hi1_nat2 in *.

      assert (Hgcc2: garbage_collect_condition g2 (pt_heap (ti_heap t_info2))). {
         pose proof H11 as Hdgr.
         destruct H6 as [? [? [? ?]]], Hdgr;
            eapply (do_gen_gcc g1 (pt_heap (ti_heap t_info1)) roots'); try eassumption.
            split; auto.
      }
      assert (Hfirst2: firstn_gen_clear g2 (Z.to_nat (i + 1))) by
          (rewrite Hi1_nat2; eapply do_gen_firstn_gen_clear; eauto).
      assert (Hstcte2: safe_to_copy_to_except g2 (Z.to_nat (i + 1))) by
          (rewrite Hi1_nat2; eapply do_gen_stcte; eauto).
     sep_apply gather_thread_info_rep.
      assert (Hgcl2: garbage_collect_loop (nat_inc_list (Z.to_nat (i + 1))) roots g roots2 g2) by
          (rewrite Hi1_nat2, nat_inc_list_S; eapply gcl_add_tail; eauto).
      replace_SEP 5 (ti_token_rep (pt_heap (ti_heap t_info2)) (ti_heap_p t_info2))
         by (erewrite ti_rel_token_the_same; eauto; entailer!!; apply derives_refl).
      simpl spaces in *.
      assert (FSE': frame_shells_eq (ti_frames t_info)
               (update_frames (ti_frames t_info1) (map (exterior2val g2) roots2))). {
            eapply frame_shells_eq_trans. eassumption.
            pose proof (sc_Zlength Hsc1) as Hroots1_len.
            pose proof (sc_Zlength H9) as Hroots2_len.
            pose proof H11 as Hrel_for_len.
            destruct Hrel_for_len as [? [? [? [FRR _]]]].
            apply frr_Zlength_roots in FRR.
            clear - FRR Hroots1_len Hroots2_len.
            forget (Zlength roots') as n; subst n.
            rewrite Hroots2_len in FRR; clear Hroots2_len.
            set (frs := ti_frames t_info1) in *; clearbody frs.
            rewrite <- (Zlength_map _ _ (exterior2val g2) roots2) in FRR.
            set (al := map _ roots2) in *. clearbody al.
            revert al FRR; induction frs as [ | [?? r]]; simpl; intros.
            constructor.
            rewrite frames2rootpairs_cons in *.
            rewrite Zlength_app, Zlength_frame2rootpairs in FRR.
            simpl in FRR.
            constructor; auto. simpl. list_solve.
            apply IHfrs. list_solve.
      }

      forward_if.
      * destruct (space_start (Znth i (spaces h2))); try contradiction.
        destruct (space_start (Znth (i + 1) (spaces h2)));
          try contradiction. Transparent denote_tc_samebase.
        unfold denote_tc_samebase. simpl. Opaque denote_tc_samebase. entailer!!.
      * change (Tpointer tvoid
                         {| attr_volatile := false; attr_alignas := Some 2%N |})
          with int_or_ptr_type in H39.
        rewrite sem_sub_pp_available_space, sem_sub_pp_rest_space in H40; auto.
        simpl in H40. apply typed_true_of_bool in H40. rewrite negb_true_iff in H40.
        match goal with
        | H : Int64.lt _ _ = false |- _ => apply lt64_repr_false in H
        | H : Int.lt _ _ = false |- _ => apply lt_repr_false in H
        end.
        2: apply rest_space_repable_signed. 2: apply available_space_repable_signed.
        assert (safe_to_copy_gen g2 (Z.to_nat i) (S (Z.to_nat i))). {
          red. destruct H9 as [? _]. destruct Hgcc2 as [_ [_ [_ ?]]].
          do 2 (erewrite <- ti_size_gen; eauto). rewrite <- Hi1_nat2 in *.
          unfold available_size, graph_gen_size.
          destruct (gt_gs_compatible _ _ H9 _ Hhas_i1_g2) as [_ [_ Hused_i1]].
          simpl in Hused_i1 |- *; rewrite Hused_i1, !nth_space_Znth, !Z2Nat.id; lia. }
        assert (graph_heap_compatible g2 (ti_heap t_info2)) by (apply (proj1 H9)).
        assert (graph_gen_clear g2 O) by (apply Hfirst2; rewrite Hi1_nat2; lia).
        forward_call (rsh, sh, gv, ti, g2, t_info2, roots2). forward.
        Exists g2 t_info2 roots2. entailer!!. split3.
        -- exists (Z.to_nat i). rewrite <- Hi1_nat2 at 1. split; assumption.
        -- rewrite Hi1_nat2 in Hstcte2. eapply safe_to_copy_complete; eauto.
        -- rewrite HN. auto.
      * forward. Intros. Exists g2 roots2 t_info2. rewrite <- Hi1_nat2 in *. entailer!!.
  - Intros g2 roots2 t_info2. unfold all_string_constants. Intros.
     forward_call; contradiction.
Qed.
