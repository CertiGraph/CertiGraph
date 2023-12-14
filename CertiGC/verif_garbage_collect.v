Require Import CertiGraph.CertiGC.gc_spec.

Local Open Scope logic.

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
  rewrite !Ptrofs.signed_repr by rep_lia. unfold vptrofs, Archi.ptr64.
  unfold WORD_SIZE. rewrite Z.mul_comm, Z.quot_mul by lia.
  first [rewrite ptrofs_to_int64_repr by easy | rewrite ptrofs_to_int_repr].
  reflexivity.
Qed.

Lemma sem_sub_pp_rest_space: forall s,
    isptr (space_start s) ->
    force_val
      (sem_sub_pp int_or_ptr_type
                  (offset_val (WORD_SIZE * total_space s) (space_start s))
                  (offset_val (WORD_SIZE * used_space s) (space_start s))) =
    if Archi.ptr64 then Vlong (Int64.repr (total_space s - used_space s)) else
      Vint (Int.repr (total_space s - used_space s)).
Proof.
  intros. destruct (space_start s); try contradiction. simpl. destruct (eq_block b b).
  2: exfalso; apply n; reflexivity.
  inv_int i. unfold sem_sub_pp; destruct eq_block; [|easy].
  rewrite !ptrofs_add_repr, ptrofs_sub_repr.
  replace (ofs + WORD_SIZE * total_space s - (ofs + WORD_SIZE * used_space s)) with
          (WORD_SIZE * (total_space s - used_space s))%Z by
      (rewrite Z.mul_sub_distr_l; lia). simpl.
  pose proof (rest_space_signed_range s). rewrite <- Z.mul_sub_distr_l in H0.
  unfold Ptrofs.divs. rewrite !Ptrofs.signed_repr by rep_lia.
  unfold vptrofs, Archi.ptr64. unfold WORD_SIZE.
  rewrite Z.mul_comm, Z.quot_mul by lia.
  first [rewrite ptrofs_to_int64_repr by easy | rewrite ptrofs_to_int_repr]. easy.
Qed.

Lemma t_info_space_address: forall t_info i,
    0 <= i -> isptr (ti_heap_p t_info) ->
    (if Archi.ptr64 then
      force_val (sem_add_ptr_long space_type (offset_val 0 (ti_heap_p t_info))
                                  (Vlong (Int64.repr i))) else
      force_val (sem_add_ptr_int space_type Signed
                                 (offset_val 0 (ti_heap_p t_info)) (vint i))) =
    space_address (ti_heap_p t_info) (Z.to_nat i).
Proof.
  intros. rewrite isptr_offset_val_zero by assumption. simpl.
  first [rewrite sem_add_pi_ptr_special' | rewrite sem_add_pl_ptr_special']; auto.
  unfold space_address. rewrite Z2Nat.id by lia. simpl. f_equal.
Qed.

Ltac tc_val_Znth := entailer!; rewrite Znth_map by assumption;
                    unfold space_tri; apply isptr_is_pointer_or_null;
                    try assumption.

Lemma gather_thread_info_rep:
  forall (v1 v2: val) sh t_info ti , 
   data_at sh thread_info_type (v1,(v2, (ti_heap_p t_info, (ti_args t_info,(ti_fp t_info, (Vptrofs(ti_nalloc t_info),nullval)))))) ti
   * frames_rep sh (ti_frames t_info)
   * data_at sh heap_type (@map space (val * (val * (val*val)))  space_tri (spaces (ti_heap t_info))) (ti_heap_p t_info) 
   * heap_rest_rep (ti_heap t_info)
   |-- thread_info_rep sh t_info ti.
Proof.
intros.
unfold thread_info_rep, heap_rep, heap_struct_rep.
do 2 unfold_data_at (data_at _ thread_info_type _ _).
cancel.
Qed.

Lemma body_garbage_collect:
  semax_body Vprog Gprog f_garbage_collect garbage_collect_spec.
Proof.
  start_function.
  assert (Tf: forall (tif: thread_info) (j: Z),
             0 <= j -> offset_val (sizeof (Tstruct _space noattr) * j) (ti_heap_p tif)=
                       space_address (ti_heap_p tif) (Z.to_nat j)). {
          intros. unfold space_address. now rewrite Z2Nat.id. }
  unfold before_gc_thread_info_rep, heap_rep, heap_struct_rep. Intros. forward. pose proof H.
  destruct H as [? _]. pose proof (gt_gs_compatible _ _ H _ (graph_has_gen_O _)).
  destruct H3 as [? [? ?]].
  replace (heap_head (ti_heap t_info)) with (nth_space (ti_heap t_info) 0) by
      (destruct (heap_head_cons (ti_heap t_info)) as [hs [hl [? ?]]];
       unfold nth_space; rewrite H6, H7; simpl; reflexivity).
  simpl fst in *. simpl snd in *.
  assert (isptr (space_start (nth_space (ti_heap t_info) 0))) by
      (rewrite <- H3; apply start_isptr). do 2 forward. deadvars!.
  rewrite upd_Znth0_old.
  2: { pose proof (@Zlength_nonneg (val * (val * (val*val)))
                                   (map space_tri (tl (spaces (ti_heap t_info))))).
       rewrite Zlength_cons. lia. }
  rewrite sublist_1_cons, Zlength_cons, sublist_same, Znth_0_cons by lia.
  simpl fst. simpl snd.
  do 2 forward.
  rewrite upd_Znth0_old.
  2: { pose proof (@Zlength_nonneg (val * (val * (val*val)))
                                   (map space_tri (tl (spaces (ti_heap t_info))))).
       rewrite Zlength_cons. lia. }
  rewrite sublist_1_cons, Zlength_cons, sublist_same, Znth_0_cons by lia.
  simpl fst. simpl snd.
  fold (space_tri (nth_space (ti_heap t_info) 0)). rewrite <- map_cons.
  replace (nth_space (ti_heap t_info) 0 :: tl (spaces (ti_heap t_info))) with
      (spaces (ti_heap t_info)) by
      (destruct (heap_head_cons (ti_heap t_info)) as [hs [hl [? ?]]];
       unfold nth_space; rewrite H7; simpl; reflexivity).
  sep_apply gather_thread_info_rep.
  forward_for_simple_bound
    (MAX_SPACES-1)
    (EX i: Z, EX g': LGraph, EX roots': roots_t, EX t_info': thread_info,
     PROP (super_compatible g' (ti_heap t_info') (frames2rootpairs (ti_frames t_info')) roots' outlier;
           garbage_collect_condition g' (ti_heap t_info') roots';
           safe_to_copy_to_except g' (Z.to_nat i);
           firstn_gen_clear g' (Z.to_nat i);
           garbage_collect_loop (nat_inc_list (Z.to_nat i)) roots g roots' g';
           graph_has_gen g' (Z.to_nat i);
           frame_shells_eq (ti_frames t_info) (ti_frames t_info');
           ti_nalloc t_info = ti_nalloc t_info')
     LOCAL (temp _h (ti_heap_p t_info'); temp _ti ti;
            gvars gv)
     SEP (thread_info_rep sh t_info' ti;
          mem_mgr gv;
          all_string_constants rsh gv;
          outlier_rep outlier;
          graph_rep g';
          ti_token_rep (ti_heap t_info') (ti_heap_p t_info'))).
  - Exists g roots t_info. destruct H2 as [? [? [? ?]]].
    pose proof (graph_has_gen_O g). entailer!. split; [|split; [|split3]].
    + split3; auto.
    + apply stc_stcte_O_iff; assumption.
    + red. intros. simpl in H12. lia.
    + unfold nat_inc_list. simpl. constructor.
    + apply frame_shells_eq_refl.
  - cbv beta. Intros g' roots' t_info'. rename H14 into FSE. rename H15 into HN.
    unfold thread_info_rep, heap_rep. Intros.
    unfold heap_struct_rep. assert (0 <= i + 1 < Zlength (spaces (ti_heap t_info'))) by
        (rewrite spaces_size; rep_lia).
    pose proof (space_start_is_pointer_or_null _ _ _ (proj1 H8) H14). 
    forward.
      entailer!.
      1: entailer!; rewrite Znth_map by assumption; unfold space_tri; assumption.
    rewrite Znth_map by assumption. unfold space_tri at 1.
    forward_if
      (EX g1: LGraph, EX t_info1: thread_info,
       PROP (super_compatible g1 (ti_heap t_info1) (frames2rootpairs (ti_frames t_info1)) roots' outlier;
             garbage_collect_condition g1 (ti_heap t_info1) roots';
             safe_to_copy_to_except g1 (Z.to_nat i);
             firstn_gen_clear g1 (Z.to_nat i);
             new_gen_relation (Z.to_nat (i + 1)) g' g1;
             graph_has_gen g1 (Z.to_nat (i + 1));
             frame_shells_eq (ti_frames t_info) (ti_frames t_info1);
             ti_nalloc t_info = ti_nalloc t_info1)
       LOCAL (temp _h (ti_heap_p t_info1); temp _ti ti;
              gvars gv; temp _i (Vint (Int.repr i)))
       SEP (thread_info_rep sh t_info1 ti;
            ti_token_rep (ti_heap t_info1) (ti_heap_p t_info1);
            mem_mgr gv;
            all_string_constants rsh gv;
            outlier_rep outlier;
            graph_rep g1)).
    + remember (space_start (Znth (i + 1) (spaces (ti_heap t_info')))).
      Transparent denote_tc_test_eq. destruct v0; try contradiction; simpl; entailer!.
        assert (isptr (Vptr b i0)) by exact I. rewrite Heqv0 in *.
        pull_left (heap_rest_rep (ti_heap t_info')). pull_left (graph_rep g').
        destruct H8. rewrite <- (space_start_isptr_iff g') in H24 by assumption.
        sep_apply (graph_and_heap_rest_valid_ptr g' (ti_heap t_info') _ H24); auto.
        hnf in H9; apply H9.
        rewrite nth_space_Znth, Z2Nat.id by lia.
        sep_apply (valid_pointer_weak
                     (space_start (Znth (i + 1) (spaces (ti_heap t_info'))))).
        apply extend_weak_valid_pointer. Opaque denote_tc_test_eq.
    + assert (0 <= i < Zlength (spaces (ti_heap t_info'))) by lia.
      pose proof (space_start_isptr _ _ _ (proj1 H8) H17 H13). forward.
      entailer!.
      1: entailer!; rewrite Znth_map by assumption; unfold space_tri;
        apply isptr_is_pointer_or_null, isptr_offset_val'; assumption.
      rewrite Znth_map by assumption. unfold space_tri at 1. forward.
      entailer!.
      1: entailer!; rewrite Znth_map by assumption; unfold space_tri;
        apply isptr_is_pointer_or_null; assumption.
      rewrite Znth_map by assumption. unfold space_tri at 1. forward.
      1: entailer!; destruct (space_start (Znth i (spaces (ti_heap t_info'))));
        try contradiction; simpl; unfold denote_tc_samebase;
          apply prop_right; simpl; destruct (peq b b); simpl; [|apply n]; auto.
      simpl sem_binary_operation'.
      change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some _ |})
        with int_or_ptr_type. remember (Znth i (spaces (ti_heap t_info'))).
      simpl in H18. subst s.
      rewrite sem_sub_pp_total_space by assumption.
      pose proof H9. destruct H19 as [_ [_ [_ ?]]].
      pose proof (ti_size_gen _ _ _ (proj1 H8) H13 H19). unfold gen_size in H20.
      rewrite nth_space_Znth, Z2Nat.id in H20 by lia. simpl in H20. rewrite H20. clear H19 H20.
      assert_PROP (isptr (ti_heap_p t_info')) by entailer!.
      sep_apply gather_thread_info_rep.
      pose proof H14.
      rewrite spaces_size in H20. unfold thread_info_rep, heap_rep. Intros.
      rewrite hsr_single_explicit with (i := i + 1). 2: assumption.
      2: rewrite Zlength_map, spaces_size; reflexivity. Intros.
      freeze [0;1;3;4;5;8;9] FR.
      sep_apply (data_at_data_at_
                   sh space_type
                   (Znth (i + 1) (map space_tri (spaces (ti_heap t_info'))))
                   (space_address (ti_heap_p t_info') (Z.to_nat (i + 1)))).
      pose proof (t_info_space_address _ _ (proj1 H14) H19). simpl in H21.
      assert (0 <= 2 * nth_gen_size (Z.to_nat i) <= MAX_SPACE_SIZE) by
          (rewrite ngs_S by lia; apply ngs_range; rep_lia).
      forward_call (sh, (space_address (ti_heap_p t_info') (Z.to_nat (i + 1))),
                    (2 * nth_gen_size (Z.to_nat i))%Z, gv, rsh).
      * first [rewrite Int64.signed_repr by (apply ngs_int_signed_range; rep_lia) |
               rewrite Int.signed_repr by (apply ngs_int_singed_range; rep_lia)].
        rewrite ngs_S by lia. apply ngs_int_signed_range. rep_lia.
      * simpl. entailer!. f_equal. now rewrite Tf.
      * rewrite ngs_S by lia. Intros p. rewrite ngs_S in H22 by lia.
        assert (Hso: 0 <= 0 <= (nth_gen_size (Z.to_nat (i + 1)))) by lia.
        rewrite data_at__isptr. Intros.
        remember (Build_space p 0
                              (nth_gen_size (Z.to_nat (i + 1))) Ews Hso (proj2 H22))
          as sp. remember (Build_generation_info p O Ews Pp writable_Ews) as gi.
        assert (forall (gr: LGraph) (gen: nat),
                   generation_space_compatible gr (gen, gi, sp)) by
            (intros; red; rewrite Heqsp, Heqgi; simpl; intuition).
        remember (lgraph_add_new_gen g' gi) as g1.
        remember (ti_add_new_space t_info' sp _ H20) as t_info1. pose proof H16.
        rewrite <- (space_start_isnull_iff g') in H16; auto. 2: apply (proj1 H8).
        assert (number_of_vertices gi = O) by (subst gi; simpl; reflexivity).
        assert (super_compatible g1 (ti_heap t_info1) (frames2rootpairs (ti_frames t_info1)) roots' outlier). {
          subst g1 t_info1. simpl ti_heap. simpl ti_frames. apply super_compatible_add; auto.
          replace (i + 1 - 1) with i by lia. assumption. }
        assert (firstn_gen_clear g1 (Z.to_nat i)) by
            (subst g1; apply firstn_gen_clear_add; assumption).
        assert (new_gen_relation (Z.to_nat (i + 1)) g' g1). {
          subst g1. red. rewrite if_false by assumption. exists gi. split; auto. }
        gather_SEP (malloc_token Ews (tarray int_or_ptr_type (nth_gen_size (Z.to_nat (i + 1)))) p) (ti_token_rep (ti_heap t_info') (ti_heap_p t_info')).
        assert (total_space sp = nth_gen_size (Z.to_nat (i + 1))) by
            (subst sp; simpl; reflexivity). rewrite <- H29.
        assert (space_start sp = p) by (subst sp; simpl; reflexivity). rewrite <- H30.
        assert (space_start sp <> nullval) by
            (rewrite H30; destruct p; try contradiction; intro; inversion H31).
        sep_apply (ti_token_rep_add (ti_heap t_info') (ti_heap_p t_info') sp (i + 1) H20); auto.
        replace (space_start sp,
                 (space_start sp,
                  (offset_val (WORD_SIZE * total_space sp) (space_start sp),
                   offset_val (WORD_SIZE * total_space sp) (space_start sp)))) with
            (space_tri sp) by          
            (unfold space_tri; do 2 f_equal; subst sp; simpl;
             rewrite isptr_offset_val_zero by assumption; reflexivity).
        thaw FR.

  match goal with |- context [SEPx  [_; _; _; _; ?a; _; _; ?b; ?c; _; _; _]] =>
     gather_SEP a b c
   end.
  (* the above "match goal with" replaces the following, which was absurdly slow:
        gather_SEP
          (data_at sh space_type _ _)
          (data_at sh (tarray space_type
                              (Zlength
                                 (sublist (i + 1 + 1) 12 (map space_tri (spaces (ti_heap t_info')))))) _
                   (offset_val (sizeof space_type)
                               (offset_val (SPACE_STRUCT_SIZE * (i + 1)) (ti_heap_p t_info'))))
          (data_at sh (tarray space_type (i + 1)) _
                   (ti_heap_p t_info')).
    *)
        rewrite sepcon_assoc, (heap_struct_rep_add (ti_heap_p t_info') (ti_heap t_info') sh sp (i + 1) H20).
        replace (ti_heap_p t_info') with (ti_heap_p t_info1) by (clear - Heqt_info1; subst; reflexivity).
        replace (ti_args t_info') with (ti_args t_info1) by (clear - Heqt_info1; subst; reflexivity).
        replace (ti_heap_p t_info') with (ti_heap_p t_info1) by
            (subst t_info1; simpl; reflexivity).
        replace (ti_args t_info') with (ti_args t_info1) by
            (subst t_info1; simpl; reflexivity).
        replace_SEP 4 (space_rest_rep sp). {
          unfold space_rest_rep. rewrite if_false by assumption.
          replace (space_sh sp) with Ews by (subst sp; simpl; reflexivity).
          replace (used_space sp) with 0 by (subst sp; simpl; reflexivity).
          rewrite Z.sub_0_r, Z.mul_0_r, isptr_offset_val_zero by
              (subst; simpl; assumption). entailer!. }
        gather_SEP (heap_rest_rep (ti_heap t_info')) (space_rest_rep sp).
        rewrite (heap_rest_rep_add _ _ (i + 1) H20) (*, <- Heqt_info1*) by assumption.
        gather_SEP
          (data_at sh thread_info_type _ _)
          (frames_rep _ _)
          (heap_struct_rep _ _ _)
          (heap_rest_rep _).
        replace_SEP 0 (thread_info_rep sh t_info1 ti) by
            (unfold thread_info_rep, heap_rep; entailer!). rewrite (graph_rep_add g' gi); auto.
        3: apply H9.
        2: apply graph_unmarked_copy_compatible, H9. 
        rewrite <- Heqg1.
        assert (graph_has_gen g1 (Z.to_nat (i + 1))). {
          subst g1. rewrite ang_graph_has_gen. right. clear -H13 H16 H7.
          unfold graph_has_gen in *.
          replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat in *. 1: lia.
          change (S O) with (Z.to_nat 1). rewrite <- Z2Nat.inj_add by lia. auto. }
        assert (safe_to_copy_to_except g1 (Z.to_nat i)) by
            (subst g1; apply stcte_add; auto; subst gi; simpl; reflexivity).
        assert (garbage_collect_condition g1 (ti_heap t_info1) roots') by
            (subst g1 t_info1; apply gcc_add; assumption).
        Local Opaque super_compatible. Exists g1 t_info1. entailer!.
    + forward. remember (space_start (Znth (i + 1) (spaces (ti_heap t_info')))).
      assert (isptr v). { 
        destruct v; try contradiction. simpl in H15. subst i0. contradiction.
        simpl. exact I. } subst v. rewrite <- (space_start_isptr_iff g') in H17; auto.
      2: destruct H8; auto. assert (new_gen_relation (Z.to_nat (i + 1)) g' g') by
          (unfold new_gen_relation; rewrite if_true; auto).
      Exists g' t_info'. entailer!. unfold thread_info_rep, heap_rep, heap_struct_rep.
      entailer!.
    + Intros g1 t_info1. clear FSE. rename H22 into FSE. clear HN; rename H23 into HN.
      assert_PROP (isptr (ti_heap_p t_info1))
        by (unfold thread_info_rep, heap_rep, heap_struct_rep; entailer!).
      assert (Z.to_nat (i + 1) = S (Z.to_nat i)) by
          (rewrite Z2Nat.inj_add by lia; simpl; lia).
      assert (do_generation_condition
                g1 (ti_heap t_info1) (Z.to_nat i) (Z.to_nat (i + 1))) by
          (rewrite H23 in *; eapply gc_cond_implies_do_gen_cons; eauto;
           apply (proj1 H16)). pose proof (t_info_space_address _ _ (proj1 H7) H22).
      pose proof (t_info_space_address _ _ (proj1 H14) H22).
      unfold thread_info_rep. Intros.
      forward.
      freeze FR1 := (data_at _ _ _ _) (mem_mgr gv) (ti_token_rep _ _).
      forward_call (rsh, sh, gv, g1, (ti_heap t_info1), (ti_heap_p t_info1),
                    (ti_frames t_info1), roots', outlier,
                    (Z.to_nat i), (Z.to_nat (i + 1))).
      1: simpl; entailer!; now rewrite !Tf.
      Intros vret. destruct vret as [[g2 h2] roots2].
      simpl fst in *. simpl snd in *.
      set (fr2 := update_frames _ _) in *.
      thaw FR1.      
      pose (t_info2 := {| ti_heap_p := ti_heap_p t_info1;
                          ti_heap := h2; ti_args := ti_args t_info1;
                          arg_size := arg_size t_info1;
                          ti_frames := fr2; ti_nalloc := ti_nalloc t_info1|}).
      change (ti_heap_p t_info1) with (ti_heap_p t_info2).
      change h2 with (ti_heap t_info2).
      change (ti_args t_info1) with (ti_args t_info2).
      replace (ti_fp t_info1) with (ti_fp t_info2).
      2:{ unfold ti_fp; simpl. unfold fr2. rewrite frames_p_update_frames. auto. }
      change (ti_nalloc t_info1) with (ti_nalloc t_info2).
      change fr2 with (ti_frames t_info2).
      unfold heap_rep. Intros. unfold heap_struct_rep.
      sep_apply gather_thread_info_rep.
      unfold thread_info_rep, heap_rep, heap_struct_rep.
      Intros. assert (graph_has_gen g2 (Z.to_nat (i + 1))) by
          (rewrite <- do_gen_graph_has_gen; eauto).
      assert (graph_has_gen g2 (Z.to_nat i)) by (red in H30 |-* ; lia).
      assert (isptr (space_start (Znth i (spaces (ti_heap t_info2))))). {
          rewrite <- (Z2Nat.id i), <- nth_space_Znth by lia.
          pose proof (proj1 (gt_gs_compatible _ _ (proj1 H27) _ H31)).
          change (ti_heap _) with h2. rewrite <- H32.
        apply start_isptr. }
      assert (0 <= i < Zlength (spaces (ti_heap t_info2))) by
          (rewrite spaces_size; rep_lia). forward.
      1:{ apply prop_right. clear - H7. rewrite MAX_SPACES_eq in H7. lia. }
      1: tc_val_Znth; rewrite isptr_offset_val; assumption. forward.
      1:{ apply prop_right. clear - H7. rewrite MAX_SPACES_eq in H7. lia. }
      1: tc_val_Znth.
      rewrite Znth_map by assumption. unfold space_tri at 1 2.
      assert (0 <= i + 1 < Zlength (spaces (ti_heap t_info2))) by
          (rewrite spaces_size; rep_lia).
      assert (isptr (space_start (Znth (i + 1) (spaces (ti_heap t_info2))))). {
        rewrite <- (Z2Nat.id (i + 1)), <- nth_space_Znth by lia.
        pose proof (proj1 (gt_gs_compatible _ _ (proj1 H27) _ H30)).
        simpl in H35. change (ti_heap _) with h2. rewrite <- H35.
        apply start_isptr. }
      forward.
        1:{ apply prop_right. clear - H7. rewrite MAX_SPACES_eq in H7. lia. }
      1: tc_val_Znth; rewrite isptr_offset_val; assumption.
      forward.
      1:{ apply prop_right. clear - H7. rewrite MAX_SPACES_eq in H7. lia. }
      1: tc_val_Znth; rewrite isptr_offset_val; assumption.
      rewrite Znth_map by assumption. unfold space_tri at 1 2. rewrite H23 in *.

      assert (garbage_collect_condition g2 (ti_heap t_info2) roots2). {
         destruct H16 as [? [? [? ?]]], H28;
            eapply (do_gen_gcc g1 (ti_heap t_info1) roots'); try eassumption.
            split; auto.
      } 
      assert (firstn_gen_clear g2 (Z.to_nat (i + 1))) by
          (rewrite H23; eapply do_gen_firstn_gen_clear; eauto).
      assert (safe_to_copy_to_except g2 (Z.to_nat (i + 1))) by
          (rewrite H23; eapply do_gen_stcte; eauto).
     sep_apply gather_thread_info_rep.
      assert (garbage_collect_loop (nat_inc_list (Z.to_nat (i + 1))) roots g roots2 g2) by
          (rewrite H23, nat_inc_list_S; eapply gcl_add_tail; eauto).
      replace_SEP 5 (ti_token_rep (ti_heap t_info2) (ti_heap_p t_info2))
         by (erewrite ti_rel_token_the_same; eauto; entailer!; apply derives_refl).
      simpl spaces in *.
      assert (FSE': frame_shells_eq (ti_frames t_info)
               (update_frames (ti_frames t_info1) (map (root2val g2) roots2))). {
            eapply frame_shells_eq_trans. eassumption.
            apply sc_Zlength in H8, H16.
            destruct H29 as [? [? [FRR _]]]. 
            apply frr_Zlength_roots in FRR.
            clear - FRR H8 H16.
            forget (Zlength roots') as n; subst n.
            rewrite H16 in FRR; clear H16.
            set (frs := ti_frames t_info1) in *; clearbody frs.
            rewrite <- (Zlength_map _ _ (root2val g2) roots2) in FRR.
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
        unfold denote_tc_samebase. simpl. Opaque denote_tc_samebase. entailer!.
      * change (Tpointer tvoid
                         {| attr_volatile := false; attr_alignas := Some 2%N |})
          with int_or_ptr_type in H39.
        rewrite sem_sub_pp_total_space, sem_sub_pp_rest_space in H40; auto.
        simpl in H40. apply typed_true_of_bool in H40. rewrite negb_true_iff in H40.
        match goal with
        | H : Int64.lt _ _ = false |- _ => apply lt64_repr_false in H
        | H : Int.lt _ _ = false |- _ => apply lt_repr_false in H
        end.
        2: apply rest_space_repable_signed. 2: apply total_space_repable_signed.
        assert (safe_to_copy_gen g2 (Z.to_nat i) (S (Z.to_nat i))). {
          red. destruct H27 as [? _]. destruct H36 as [_ [_ [_ ?]]].
          do 2 (erewrite <- ti_size_gen; eauto). rewrite <- H23 in *.
          unfold gen_size, graph_gen_size. destruct (gt_gs_compatible _ _ H27 _ H30)
            as [_ [_ ?]]. simpl in H41|-*; rewrite H41, !nth_space_Znth, !Z2Nat.id; lia. }
        assert (graph_heap_compatible g2 (ti_heap t_info2)) by (apply (proj1 H27)).
        assert (graph_gen_clear g2 O) by (apply H37; rewrite H23; lia).
        forward_call (rsh, sh, gv, ti, g2, t_info2, roots2). forward.
        Exists g2 t_info2 roots2. entailer!. split3.
        -- exists (Z.to_nat i). rewrite <- H23 at 1. split; assumption.
        -- rewrite H23 in H38. eapply safe_to_copy_complete; eauto.
        -- rewrite HN. auto.
      * forward. Intros. Exists g2 roots2 t_info2. rewrite <- H23 in *. entailer!.
  - Intros g2 roots2 t_info2. unfold all_string_constants. Intros.
     forward_call; contradiction.
Qed.
