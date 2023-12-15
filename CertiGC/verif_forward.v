From CertiGraph.CertiGC Require Import env_graph_gc gc_spec.
Require Import CertiGraph.msl_ext.ramification_lemmas.
Require Import CertiGraph.CertiGC.verif_forward1.
Require Import CertiGraph.CertiGC.verif_forward2.

Local Open Scope logic.

Lemma body_forward: semax_body Vprog Gprog f_forward forward_spec.
Proof.
  start_function.
  match goal with |- semax _ _ ?c _ => change c with (fn_body f_forward) end.
  change Delta with (func_tycontext f_forward Vprog Gprog nil).
  destruct forward_p.
  eapply body_forward_inL; eassumption.
  eapply body_forward_inR; eassumption.
Qed.





