Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_do_scan: semax_body Vprog Gprog f_do_generation do_generation_spec.
Proof.
  start_function.
Abort.
