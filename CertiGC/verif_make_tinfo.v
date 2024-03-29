From CertiGraph.CertiGC Require Import env_graph_gc gc_spec.

Lemma body_make_tinfo: semax_body Vprog Gprog f_make_tinfo make_tinfo_spec.
Proof.
  start_function.
  forward_call (sh, gv).
  Intros vret. destruct vret as [h p]. simpl fst. simpl snd.
  forward_call (thread_info_type, gv).
  Intros t. if_tac.
  - subst t. forward_if False; [ | congruence].
    unfold all_string_constants; Intros; forward_call; contradiction.
  - Intros. forward_if True; [contradiction | forward; entailer!! |]. Intros.
    forward. forward. rewrite Znth_0_cons. forward. forward. rewrite Znth_0_cons.
    forward. forward. forward. forward. forward. Exists t h p. entailer!!.
Qed.
