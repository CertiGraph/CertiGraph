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

Lemma precise_wand_sepcon: forall {A: Type} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} P Q, precise P -> P -* (P * Q) = Q.
Proof.
  intros.
  apply pred_ext.
  + apply precise_sepcon_cancel with P; auto.
    apply modus_ponens_wand.
  + apply wand_sepcon_adjoint.
    rewrite sepcon_comm.
    apply derives_refl.
Qed.

Lemma precise_andp_left: forall {A: Type} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} P Q, precise P -> precise (P && Q).
Proof.
  intros.
  apply derives_precise with P; auto.
  apply andp_left1; auto.
Qed.
  
Lemma precise_andp_right: forall {A: Type} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} P Q, precise Q -> precise (P && Q).
Proof.
  intros.
  apply derives_precise with Q; auto.
  apply andp_left2; auto.
Qed.

Lemma exp_sepcon: forall {A: Type} {ND: NatDed A} {SL: SepLog A} {B} (P Q: B -> A), exp (P * Q) |-- exp P * exp Q.
Proof.
  intros.
  apply exp_left; intro.
  simpl.
  apply sepcon_derives; apply (exp_right x); apply derives_refl.
Qed.

Lemma precise_exp_sepcon: forall {A: Type} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {B} (P Q: B -> A), precise (exp P) -> precise (exp Q) -> precise (exp (P * Q)).
Proof.
  intros.
  eapply derives_precise.
  + apply exp_sepcon.
  + apply precise_sepcon; auto.
Qed.

