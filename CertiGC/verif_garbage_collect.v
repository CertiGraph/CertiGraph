Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_garbage_collect:
  semax_body Vprog Gprog f_garbage_collect garbage_collect_spec.
Proof.
  start_function.
  unfold thread_info_rep, heap_struct_rep. Intros. forward.
  remember (ti_heap t_info) as th. remember (ti_heap_p t_info) as h.
  destruct (heap_head_cons th) as [hs [hl [? ?]]]. rewrite H0, H1 in *. simpl tl.
  destruct H as [[? ?] ?]. destruct (g_gen (glabel g)) eqn: ?.
  1: exfalso; apply (g_gen_not_nil (glabel g)); assumption. rewrite <- Heqth, H0 in H.
  simpl in H. rewrite Forall_forall in H.
  assert (generation_space_compatible g (O, g0, hs)) by (apply H; left; reflexivity).
  destruct H4 as [? [? ?]]. rewrite <- H4 in *. pose proof (start_isptr g0). forward.
  forward. rewrite upd_Znth0, sublist_1_cons, Zlength_cons, sublist_same by omega.
  forward_for_simple_bound
    11
    (EX i: Z, EX g_tinfo_roots: LGraph * thread_info * roots_t,
     PROP (super_compatible g_tinfo_roots f_info outlier)
     LOCAL (temp _h h; gvars gv)
     SEP (all_string_constants rsh gv;
          fun_info_rep rsh f_info fi;
          outlier_rep outlier;
          graph_rep (fst (fst g_tinfo_roots));
          thread_info_rep sh (snd (fst g_tinfo_roots)) ti)).
Abort.
