Require Import RamifyCoq.CertiGC.gc_spec.

Ltac hif_tac H :=
  match type of H with context [if ?a then _ else _] => destruct a eqn: ?H end.

Lemma body_Is_block: semax_body Vprog Gprog f_Is_block Is_block_spec.
Proof.
  start_function.
  assert (eqb_type
            (Tpointer Tvoid {| attr_volatile := false; attr_alignas := Some 2%N |})
            int_or_ptr_type = true) by
      (rewrite eqb_type_spec; unfold int_or_ptr_type; f_equal). forward_call x.
  forward. hif_tac H1. 2: inversion H0. destruct x; simpl in *; entailer!.
Qed.
