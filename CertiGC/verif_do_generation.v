Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_do_scan: semax_body Vprog Gprog f_do_generation do_generation_spec.
Proof.
  start_function.
  pose proof H. pose proof H0. destruct H3 as [? _]. destruct H4 as [? [? [? _]]].
  assert (generation_space_compatible
            g (from, nth_gen g from, nth_space t_info from)) by
      (apply gt_gs_compatible; assumption). destruct H7 as [? [? ?]].
  assert (generation_space_compatible g (to, nth_gen g to, nth_space t_info to)) by
      (apply gt_gs_compatible; assumption). destruct H10 as [? [? ?]].
  assert (isptr (space_start (nth_space t_info from))) by
      (rewrite <- H7; apply start_isptr).
  assert (isptr (space_start (nth_space t_info to))) by
      (rewrite <- H10; apply start_isptr).
  assert (HS: forall gen, graph_has_gen g gen -> Z.of_nat gen < MAX_SPACES). {
    intros. unfold graph_has_gen in H12. destruct H as [[_ [_ ?]] _].
    rewrite <- (spaces_size (ti_heap t_info)). rewrite Zlength_correct.
    apply inj_lt. apply Nat.lt_le_trans with
                      (Datatypes.length (g_gen (glabel g))); assumption. }
  assert (Z.of_nat from < MAX_SPACES) by (apply HS; assumption).
  assert (Z.of_nat to < MAX_SPACES) by (apply HS; assumption). clear HS.
  freeze [0;1;2;3] FR.
  localize [space_struct_rep sh t_info from; space_struct_rep sh t_info to].
  unfold space_struct_rep. unfold space_tri. do 5 forward.
  gather_SEP 0 1.
  replace_SEP 0 (space_struct_rep sh t_info from * space_struct_rep sh t_info to) by
    (unfold space_struct_rep; entailer!).
  unlocalize [do_generation_ti_rep from sh t_info ti].
  1: apply do_generation_ti_rep_ramif_stable; assumption.
  remember (space_start (nth_space t_info from)) as from_p.
  remember (space_start (nth_space t_info to)) as to_p.
  remember (WORD_SIZE * used_space (nth_space t_info to))%Z as to_used.
  remember (WORD_SIZE * total_space (nth_space t_info to))%Z as to_total.
  remember (WORD_SIZE * used_space (nth_space t_info from))%Z as from_used.
  assert (is_true (sameblock (offset_val from_used from_p) from_p)). {
    destruct from_p; try contradiction. simpl.
    destruct peq. 2: contradiction. exact I. }
  assert (is_true (sameblock (offset_val to_total to_p) (offset_val to_used to_p))). {
    destruct to_p; try contradiction. simpl.
    destruct peq. 2: contradiction. exact I. }
  forward_if True. 1: entailer!; unfold denote_tc_samebase; entailer!.
  - forward. entailer!.
  - destruct from_p; try contradiction. inv_int i. destruct to_p; try contradiction.
    inv_int i0. simpl in H19. exfalso.
    rewrite !ptrofs_add_repr, !ptrofs_sub_repr, !if_true in H19 by reflexivity.
    simpl in H19. replace (ofs0 + to_total - (ofs0 + to_used)) with
                      (to_total - to_used) in H19 by omega.
    replace (ofs + from_used - ofs) with from_used in H19 by omega.
    assert (Ptrofs.min_signed <= from_used <= Ptrofs.max_signed) by
        (subst; apply used_space_signed_range).
    assert (Ptrofs.min_signed <= to_total - to_used <= Ptrofs.max_signed) by
        (subst; apply rest_space_signed_range). unfold Ptrofs.divs in H19.
    rewrite !Ptrofs.signed_repr in H19 by rep_omega. subst.
    rewrite <- Z.mul_sub_distr_l, WORD_SIZE_eq, Z.mul_comm, Z.quot_mul,
    Z.mul_comm, Z.quot_mul, !ptrofs_to_int_repr in H19 by omega. red in H19.
    destruct (Int.lt
                (Int.repr
                   (total_space (nth_space t_info to) -
                    used_space (nth_space t_info to)))
                (Int.repr (used_space (nth_space t_info from)))) eqn: ?; simpl in H19.
    2: inversion H19. apply lt_repr in Heqb1. 2: apply rest_space_repable_signed.
    2: apply used_space_repable_signed. clear -H9 H4 Heqb1. red in H4.
    unfold graph_gen_size, rest_gen_size in H4. rewrite H9 in H4. omega.
  - Intros. deadvars!. sep_apply (do_generation_derives_thread from sh t_info ti).
    localize [space_struct_rep_gen sh t_info from].
    unfold space_struct_rep_gen, space_tri_gen. do 2 forward.
    replace_SEP 0 (space_struct_rep_gen sh t_info from) by
        (unfold space_struct_rep_gen, space_tri_gen; entailer!).
    unlocalize [thread_info_rep sh t_info ti].
    1: apply thread_info_rep_ramif_stable_1; assumption.
    apply dgc_imply_fc in H0. rewrite <- Heqfrom_p.
    replace from_p with (gen_start g from) by
        (subst; unfold gen_start; rewrite if_true; assumption).
    replace (offset_val (WORD_SIZE * total_space (nth_space t_info from))
                        (gen_start g from)) with (limit_address g t_info from) by
        (unfold limit_address, gen_size; reflexivity).
    assert_PROP (isptr (space_address t_info to)). {
      unfold space_address. rewrite isptr_offset_val. unfold thread_info_rep.
      Intros. unfold heap_struct_rep. entailer!. }
    assert_PROP (offset_val 4 (space_address t_info to) = next_address t_info to). {
      unfold thread_info_rep. unfold heap_struct_rep. Intros. entailer!.
      unfold space_address, next_address, field_address. rewrite if_true.
      - simpl. rewrite offset_offset_val. f_equal.
      - destruct H as [[_ [_ ?]] _]. clear -H H6 H27. unfold field_compatible in *.
        simpl in *. unfold in_members. simpl. intuition. red in H6.
        pose proof (spaces_size (ti_heap t_info)). rewrite Zlength_correct in H4.
        rep_omega. } thaw FR.
    forward_call (rsh, sh, gv, fi, ti, g, t_info, f_info, roots, outlier, from, to).
    1: intuition. Intros vret. destruct vret as [[g1 t_info1] roots1]. simpl fst in *.
    simpl snd in *. freeze [0;1;2;3] FR. deadvars!.
    replace (space_address t_info from) with (space_address t_info1 from) by
        (unfold space_address; rewrite (proj1 H24); reflexivity).
    assert (space_start (nth_space t_info1 from) = gen_start g1 from). {
      destruct H21 as [? _]. destruct H23 as [_ [? _]].
      destruct (gt_gs_compatible _ _ H21 _ H23) as [? _]. rewrite <- H25.
      unfold gen_start. rewrite if_true by assumption. reflexivity. }
    assert (isptr (space_start (nth_space t_info1 from))). {
      rewrite H25. unfold gen_start. destruct H23 as [_ [? _]].
      rewrite if_true by assumption. apply start_isptr. }
    localize [space_struct_rep_gen sh t_info1 from].
    unfold space_struct_rep_gen, space_tri_gen. do 2 forward.
    replace_SEP 0 (space_struct_rep_gen sh t_info1 from) by
        (unfold space_struct_rep_gen, space_tri_gen; entailer!).
    unlocalize [thread_info_rep sh t_info1 ti].
    1: apply thread_info_rep_ramif_stable_1; assumption.
    thaw FR. rewrite H25.
    replace (offset_val (WORD_SIZE * total_space (nth_space t_info1 from))
                        (gen_start g1 from)) with (limit_address g1 t_info1 from) by
        (unfold limit_address, gen_size; reflexivity).
    assert_PROP (offset_val 4 (space_address t_info to) = next_address t_info1 to). {
      unfold thread_info_rep. unfold heap_struct_rep. entailer!.
      unfold space_address, next_address, field_address. rewrite (proj1 H24), if_true.
      - simpl. rewrite offset_offset_val. f_equal.
      - clear -H34 H16. unfold field_compatible in *. simpl.
        unfold in_members. simpl. intuition. }
    assert (closure_has_v g (to, number_of_vertices (nth_gen g to))) by
        (red; simpl; unfold closure_has_index; split; [assumption | omega]).
    replace (offset_val to_used to_p) with
        (offset_val (- WORD_SIZE)
                    (vertex_address g1 (to, number_of_vertices (nth_gen g to)))) by
        (rewrite <- (frr_vertex_address _ _ _ _ _ _ _ H6 H22 _ H28); subst;
         unfold vertex_address, vertex_offset, gen_start; simpl;
         rewrite offset_offset_val, H12, H10, if_true by assumption;
         f_equal; rep_omega). 
    forward_call (rsh, sh, gv, fi, ti, g1, t_info1, f_info, roots1, outlier,
                  from, to, number_of_vertices (nth_gen g to)).
    1: { intuition.
Abort.
