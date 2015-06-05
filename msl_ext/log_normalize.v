Require Import RamifyCoq.msl_ext.seplog.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.

Local Open Scope logic.

Lemma ocon_sep_true: forall {A} `{OverlapSL A} (P Q: A), ocon P Q |-- P * TT.
Proof.
  intros.
  eapply derives_trans.
  + apply ocon_derives; [apply derives_refl | apply TT_right].
  + rewrite ocon_TT.
    apply derives_refl.
Qed.

Lemma exp_allp: forall {A: Type} {ND: NatDed A} (S T: Type) (P: S -> T -> A),
    exp (fun s => allp (P s)) |-- allp (fun t => exp (fun s => P s t)).
Proof.
  intros.
  apply exp_left; intro s.
  apply allp_right; intro t.
  apply (exp_right s).
  eapply allp_left.
  apply derives_refl.
Qed.
