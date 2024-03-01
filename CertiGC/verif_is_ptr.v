From CertiGraph.CertiGC Require Import env_graph_gc gc_spec.

Ltac hif_tac H :=
  match type of H with context [if ?a then _ else _] => destruct a eqn: ?H end.

Lemma body_is_ptr: semax_body Vprog Gprog f_is_ptr is_ptr_spec.
Proof.
  start_function. forward_call x.
  forward. red in H0. hif_tac H0. 2: inversion H1. destruct x; simpl in *; entailer!!.
Qed.
