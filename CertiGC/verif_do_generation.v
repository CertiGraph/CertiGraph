Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_do_scan: semax_body Vprog Gprog f_do_generation do_generation_spec.
Proof.
  start_function.
  assert (generation_space_compatible
            g (from, nth_gen g from, nth_space t_info from)) by
      (destruct H; destruct H0 as [_ [? [? _]]]; apply gt_gs_compatible; assumption).
  destruct H3 as [? [? ?]]. assert (generation_space_compatible
                                      g (to, nth_gen g to, nth_space t_info to)) by
      (destruct H; destruct H0 as [_ [? [? _]]]; apply gt_gs_compatible; assumption).
  destruct H6 as [? [? ?]]. assert (isptr (space_start (nth_space t_info from))) by
      (rewrite <- H3; apply start_isptr).
  assert (isptr (space_start (nth_space t_info to))) by
      (rewrite <- H6; apply start_isptr).
  assert (HS: forall gen, graph_has_gen g gen -> Z.of_nat gen < MAX_SPACES). {
    intros. unfold graph_has_gen in H11. destruct H as [[_ [_ ?]] _].
    rewrite <- (spaces_size (ti_heap t_info)). rewrite Zlength_correct.
    apply inj_lt. apply Nat.lt_le_trans with
                      (Datatypes.length (g_gen (glabel g))); assumption. }
  assert (Z.of_nat from < MAX_SPACES) by
      (destruct H0 as [_ [? [? _]]]; apply HS; assumption).
  assert (Z.of_nat to < MAX_SPACES) by
      (destruct H0 as [_ [? [? _]]]; apply HS; assumption). clear HS.
  freeze [0;1;2;3] FR.
  localize [space_struct_rep sh t_info from; space_struct_rep sh t_info to].
  unfold space_struct_rep. unfold space_tri. do 5 forward.
  gather_SEP 0 1.
  replace_SEP 0 (space_struct_rep sh t_info from * space_struct_rep sh t_info to) by
    (unfold space_struct_rep; entailer!).
  unlocalize [do_generation_ti_rep from sh t_info ti].
  1: apply do_generation_ti_rep_ramif_stable; assumption.
Abort.
