Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_do_scan: semax_body Vprog Gprog f_do_scan do_scan_spec.
Proof.
  start_function.
  forward.
  forward_loop (EX index: nat, EX g': LGraph, EX t_info': thread_info,
                PROP (super_compatible (g', t_info', roots) f_info outlier;
                      forward_condition g' t_info' from to;
                      thread_info_relation t_info t_info' from)
                LOCAL
                (temp _s (offset_val (- WORD_SIZE) (vertex_address g' (to, index)));
                 temp _from_start (gen_start g' from);
                 temp _from_limit (limit_address g' t_info' from);
                 temp _next (next_address t_info' to))
                SEP (all_string_constants rsh gv; outlier_rep outlier; 
                     graph_rep g'; thread_info_rep sh t_info' ti))
  break: (EX g' : LGraph, EX t_info' : thread_info,
          PROP (super_compatible (g', t_info', roots) f_info outlier;
                forward_condition g' t_info' from to;
                do_scan_relation from to to_index g g';
                thread_info_relation t_info t_info' from)
          LOCAL ()
          SEP (all_string_constants rsh gv; outlier_rep outlier; 
               graph_rep g'; thread_info_rep sh t_info' ti)).
  - Exists to_index g t_info. destruct H as [? [? [? ?]]]. entailer!.
    apply tir_id.
  - Intros index g' t_info'. unfold next_address, thread_info_rep. Intros.
    freeze [0; 1; 2; 3; 5] FR. unfold heap_struct_rep. destruct H3 as [? [? [? ?]]].
    destruct H4 as [? [? [? [? ?]]]].
    assert (0 <= Z.of_nat to < 12). {
      clear -H3 H10. destruct H3 as [_ [_ ?]]. red in H10.
      pose proof (spaces_size (ti_heap t_info')).
      rewrite Zlength_correct in H0. rep_omega. } assert (0 < Z.of_nat to) by omega.
    destruct (gt_gs_compatible _ _ H3 _ H10) as [? [? ?]]. rewrite nth_space_Znth in *.
    remember (Znth (Z.of_nat to) (spaces (ti_heap t_info'))) as sp_to.
    assert (isptr (space_start sp_to)) by (rewrite <- H15; apply start_isptr).
    remember ((space_start (heap_head (ti_heap t_info')),
               (Vundef,
                offset_val (WORD_SIZE * total_space (heap_head (ti_heap t_info')))
                           (space_start (heap_head (ti_heap t_info')))))
                :: map space_tri (tl (spaces (ti_heap t_info')))).
    assert (Znth (Z.of_nat to) l = space_tri sp_to). {
      subst l sp_to. rewrite Znth_pos_cons by assumption.
      rewrite map_tl, Znth_tl by omega.
      replace (Z.of_nat to - 1 + 1) with (Z.of_nat to) by omega.
      rewrite Znth_map by (rewrite spaces_size; rep_omega). reflexivity. }
    unfold Inhabitant_pair, Inhabitant_val, Inhabitant in H19.
    forward; rewrite H19; unfold space_tri. 1: entailer!.
    unfold vertex_address, vertex_offset. rewrite offset_offset_val. simpl vgeneration.
    simpl vindex.
    replace (WORD_SIZE * (previous_vertices_size g' to index + 1) + - WORD_SIZE) with
        (WORD_SIZE * (previous_vertices_size g' to index))%Z by rep_omega.
    unfold gen_start at 1. rewrite if_true by assumption. rewrite H15.
    forward_if (gen_has_index g' to index).
    + remember (space_start (Znth (Z.of_nat to) (spaces (ti_heap t_info')))) as sp_to.
      destruct sp_to; try contradiction. admit.
    + admit.
    + admit.
    + admit.
  - Intros g' t_info'. forward. Exists g' t_info'. entailer!.
Abort.
