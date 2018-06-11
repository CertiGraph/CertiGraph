Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_garbage_collect:
  semax_body Vprog Gprog f_garbage_collect garbage_collect_spec.
Proof.
  start_function.
Abort.
