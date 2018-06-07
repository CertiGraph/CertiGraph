Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_garbage_collect:
  semax_body Vprog Gprog f_garbage_collect garbage_collect_spec.
Proof.
  start_function.
  unfold thread_info_rep. if_tac.
  - forward. forward_if. 2: discriminate.
    forward_call (rsh, gv). Intros hp. destruct hp as [h p].
    simpl fst. simpl snd. forward.
    admit.
  - Intros. forward. entailer!.
Abort.
