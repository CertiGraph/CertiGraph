Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_resume: semax_body Vprog Gprog f_resume resume_spec.
Proof.
  start_function.
  unfold thread_info_rep. destruct (Val.eq (ti_heap_p t_info) nullval).
  1: hnf in e; exfalso; tauto. clear n. Intros. unfold heap_struct_rep. forward. 
  unfold fun_info_rep. forward. 1: entailer!. rewrite Znth_0_cons.
  forward_if True; [forward; entailer!|exfalso; destruct t_info; simpl in *; tauto|].
  Intros. remember (ti_heap_p t_info) as h. remember (ti_heap t_info) as theap.
  pose proof (sound_gg g). simpl in H1.
  forward; rewrite Znth_0_cons.
  - entailer!.
Abort.
