Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_resume: semax_body Vprog Gprog f_resume resume_spec.
Proof.
  start_function.
  remember (glabel g) as tinfo. unfold thread_info_rep.
  destruct (EquivDec.equiv_dec (ti_heap_p tinfo) nullval).
  1: hnf in e; exfalso; tauto. clear c. Intros. unfold heap_struct_rep. forward.
  unfold fun_info_rep. forward. 1: entailer!. rewrite Znth_0_cons.
  forward_if True; [forward; entailer!|exfalso; destruct tinfo; simpl in *; tauto|].
  Intros. remember (ti_heap_p tinfo) as h. remember (ti_heap tinfo) as theap.
  
Abort.
