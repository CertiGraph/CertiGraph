Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import VST.msl.Extensionality.
Require Import VST.msl.simple_CCC.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.

Local Open Scope logic.

Lemma sepcon_left1_corable_right: forall {A} `{CorableSepLog A} P Q R, corable R -> P |-- R -> P * Q |-- R.
Proof.
  intros.
  rewrite (add_andp _ _ H1).
  rewrite corable_andp_sepcon2 by auto.
  apply andp_left1; auto.
Qed.

Lemma sepcon_left2_corable_right: forall {A} `{CorableSepLog A} P Q R, corable R -> Q |-- R -> P * Q |-- R.
Proof.
  intros.
  rewrite sepcon_comm.
  apply sepcon_left1_corable_right; auto.
Qed.

Lemma ocon_sep_true: forall {A} `{OverlapSepLog A} (P Q: A), ocon P Q |-- P * TT.
Proof.
  intros.
  eapply derives_trans.
  + apply ocon_derives; [apply derives_refl | apply TT_right].
  + rewrite ocon_TT.
    apply derives_refl.
Qed.

Lemma exp_allp: forall {A} `{NatDed A} (S T: Type) (P: S -> T -> A),
    exp (fun s => allp (P s)) |-- allp (fun t => exp (fun s => P s t)).
Proof.
  intros.
  apply exp_left; intro s.
  apply allp_right; intro t.
  apply (exp_right s).
  eapply allp_left.
  apply derives_refl.
Qed.

Lemma precise_andp_left: forall {A} `{PreciseSepLog A} P Q, precise P -> precise (P && Q).
Proof.
  intros.
  apply derives_precise with P; auto.
  apply andp_left1; auto.
Qed.

Lemma precise_andp_right: forall {A} `{PreciseSepLog A} P Q, precise Q -> precise (P && Q).
Proof.
  intros.
  apply derives_precise with Q; auto.
  apply andp_left2; auto.
Qed.

Lemma exp_sepcon: forall {A} `{SepLog A} {B} (P Q: B -> A), exp (P * Q) |-- exp P * exp Q.
Proof.
  intros.
  apply exp_left; intro.
  simpl.
  apply sepcon_derives; apply (exp_right x); apply derives_refl.
Qed.

Lemma precise_exp_sepcon: forall {A} `{PreciseSepLog A} {B} (P Q: B -> A), precise (exp P) -> precise (exp Q) -> precise (exp (P * Q)).
Proof.
  intros.
  eapply derives_precise.
  + apply exp_sepcon.
  + apply precise_sepcon; auto.
Qed.

Lemma ocon_self: forall {A} {ND: NatDed A} {SL: SepLog A} {CLS: ClassicalSep A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} P, P |-- ocon P P.
Proof.
  intros.
  apply ocon_contain.
  apply sepcon_TT.
Qed.

Lemma precise_ocon_self: forall {A} {ND: NatDed A} {SL: SepLog A} {CLS: ClassicalSep A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} P, precise P -> P = ocon P P.
Proof.
  intros.
  apply precise_ocon_contain; auto.
Qed.

Lemma ocon_sepcon_cancel: forall {A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} P Q, P * Q |-- ocon P (P * Q).
Proof.
  intros.
  apply ocon_contain.
  apply sepcon_derives; auto.
  apply TT_right.
Qed.

Lemma precise_ocon_sepcon_cancel: forall {A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} P Q, precise P -> P * Q = ocon P (P * Q).
Proof.
  intros.
  apply precise_ocon_contain; auto.
  apply sepcon_derives; auto.
  apply TT_right.
Qed.

Lemma disj_sepcon_right: forall {A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} P Q R, precise P -> disjointed P Q -> disjointed P R -> disjointed P (Q * R).
Proof.
  intros.
  pose proof disj_ocon_right _ _ _ H H0 H1.
  eapply disj_derives; [apply derives_refl | | exact H2].
  apply sepcon_ocon.
Qed.

Lemma mapsto_precise: forall {AV} {A} `{PreciseSepLog A} {MSL: MapstoSepLog AV A} p v , precise (mapsto p v).
Proof.
  intros.
  eapply derives_precise; [| apply mapsto__precise].
  apply (exp_right v).
  apply derives_refl.
Qed.

Lemma disj_mapsto: forall {AV A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {MSL: MapstoSepLog AV A} {DSL: DisjointedSepLog A} {SMSL: StaticMapstoSepLog AV A} p1 p2 v1 v2, addr_conflict p1 p2 = false -> disjointed (mapsto p1 v1) (mapsto p2 v2).
Proof.
  intros.
  eapply disj_derives; [| | apply disj_mapsto_]; eauto.
  + apply (exp_right v1). apply derives_refl.
  + apply (exp_right v2). apply derives_refl.
Qed.
