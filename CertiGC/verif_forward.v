From CertiGraph.CertiGC Require Import env_graph_gc gc_spec.
Require Import CertiGraph.msl_ext.ramification_lemmas.
Require Import CertiGraph.CertiGC.verif_forward1.
Require Import CertiGraph.CertiGC.verif_forward2.

#[local] Open Scope logic.

Lemma body_forward: semax_body Vprog Gprog f_forward forward_spec.
Proof.
  start_function.
  match goal with |- semax _ _ ?c _ => change c with (fn_body f_forward) end.
  change Delta with (func_tycontext f_forward Vprog Gprog nil).
  destruct forward_p, fwd_addr; simpl forward_p_address; simpl forward_p_rep.
  - eapply body_forward_extr; eassumption.
  - simpl in H2. contradiction.
  - simpl in H2. contradiction.
  - gather_SEP (all_string_constants _ _) emp. rewrite sepcon_emp.
    eapply body_forward_intr; eassumption.
Qed.
