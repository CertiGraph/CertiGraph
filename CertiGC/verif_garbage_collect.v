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
  forward. rewrite upd_Znth0. rewrite sublist_1_cons.
  rewrite Zlength_cons, sublist_same by omega.
  
Abort.
