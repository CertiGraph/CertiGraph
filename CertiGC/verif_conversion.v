Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_int_to_int_or_ptr:
  semax_body Vprog Gprog f_int_to_int_or_ptr int_to_int_or_ptr_spec.
Proof.
  start_function.
  forward.
Qed.

Lemma body_int_or_ptr_to_int:
  semax_body Vprog Gprog f_int_or_ptr_to_int int_or_ptr_to_int_spec.
Proof.
  start_function.
  red in H. destruct x; try easy.
  forward.
Qed.

Lemma body_ptr_to_int_or_ptr:
  semax_body Vprog Gprog f_ptr_to_int_or_ptr ptr_to_int_or_ptr_spec.
Proof.
  start_function.
  forward.
Qed.

Lemma body_int_or_ptr_to_ptr:
  semax_body Vprog Gprog f_int_or_ptr_to_ptr int_or_ptr_to_ptr_spec.
Proof.
  start_function.
  forward.
Qed.
