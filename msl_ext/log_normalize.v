Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import VST.msl.Extensionality.
Require Import VST.msl.simple_CCC.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.

Local Open Scope logic.

Lemma allp_uncurry: forall {A} `{NatDed A} (S T: Type) (P: S -> T -> A),
  allp (fun s => allp (P s)) = allp (fun st => P (fst st) (snd st)).
Proof.
  intros.
  apply pred_ext.
  + apply allp_right; intros [s t].
    apply (allp_left _ s).
    apply (allp_left _ t).
    apply derives_refl.
  + apply allp_right; intro s.
    apply allp_right; intro t.
    apply (allp_left _ (s, t)).
    apply derives_refl.
Qed.

Lemma allp_curry: forall {A} `{NatDed A} (S T: Type) (P: S * T -> A),
  allp P = allp (fun s => allp (fun t => P (s, t))).
Proof.
  intros.
  apply pred_ext.
  + apply allp_right; intro s.
    apply allp_right; intro t.
    apply (allp_left _ (s, t)).
    apply derives_refl.
  + apply allp_right; intros [s t].
    apply (allp_left _ s).
    apply (allp_left _ t).
    apply derives_refl.
Qed.

Lemma exp_uncurry: forall {A} `{NatDed A} (S T: Type) (P: S -> T -> A),
  exp (fun s => exp (P s)) = exp (fun st => P (fst st) (snd st)).
Proof.
  intros.
  apply pred_ext.
  + apply exp_left; intro s.
    apply exp_left; intro t.
    apply (exp_right (s, t)).
    apply derives_refl.
  + apply exp_left; intros [s t].
    apply (exp_right s).
    apply (exp_right t).
    apply derives_refl.
Qed.

Lemma exp_curry: forall {A} `{NatDed A} (S T: Type) (P: S * T -> A),
  exp P = exp (fun s => exp (fun t => P (s, t))).
Proof.
  intros.
  apply pred_ext.
  + apply exp_left; intros [s t].
    apply (exp_right s).
    apply (exp_right t).
    apply derives_refl.
  + apply exp_left; intro s.
    apply exp_left; intro t.
    apply (exp_right (s, t)).
    apply derives_refl.
Qed.

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

Lemma precise_left_sepcon_andp_sepcon: forall {A} `{PreciseSepLog A} P Q R, precise P -> (P * Q) && (P * R) |-- P * (Q && R).
Proof.
  intros.
  eapply derives_trans.
  + apply precise_left_sepcon_andp_distr with P; auto.
  + apply sepcon_derives; auto.
    apply andp_left1; auto.
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

Lemma emp_disj: forall {A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} P, disjointed emp P.
Proof.
  intros.
  apply disj_comm, disj_emp.
Qed.

Lemma disj_FF: forall {A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} P, disjointed P FF.
Proof.
  intros.
  eapply disj_derives; [| | apply disj_emp].
  apply derives_refl.
  apply FF_left.
Qed.

Lemma FF_disj: forall {A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} P, disjointed FF P.
Proof.
  intros.
  apply disj_comm, disj_FF.
Qed.

Lemma disj_ocon_left: forall {A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} P Q R, disjointed Q P -> disjointed R P -> disjointed (ocon Q R) P.
Proof.
  intros.
  apply disj_comm.
  apply disj_comm in H.
  apply disj_comm in H0.
  apply disj_ocon_right; auto.
Qed.

Lemma disj_sepcon_right: forall {A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} P Q R, disjointed P Q -> disjointed P R -> disjointed P (Q * R).
Proof.
  intros.
  pose proof disj_ocon_right _ _ _ H H0.
  eapply disj_derives; [apply derives_refl | | exact H1].
  apply sepcon_ocon.
Qed.

Lemma disj_sepcon_left: forall {A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} P Q R, disjointed Q P -> disjointed R P -> disjointed (Q * R) P.
Proof.
  intros.
  apply disj_comm.
  apply disj_comm in H.
  apply disj_comm in H0.
  apply disj_sepcon_right; auto.
Qed.

Lemma disj_prop_andp_left: forall {A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} (P: Prop) Q R, ({P} + {~ P}) -> (P -> disjointed Q R) -> disjointed ((!! P) && Q) R.
Proof.
  intros.
  destruct H.
  + apply H0 in p.
    eapply disj_derives; [ | | exact p].
    - apply andp_left2, derives_refl.
    - apply derives_refl.
  + eapply disj_derives; [ | | apply FF_disj].
    - apply andp_left1. normalize.
    - apply derives_refl.
Qed.

Lemma disj_prop_andp_right: forall {A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {DSL: DisjointedSepLog A} (P: Prop) Q R, ({P} + {~ P}) -> (P -> disjointed R Q) -> disjointed R ((!! P) && Q).
Proof.
  intros.
  apply disj_comm.
  apply disj_prop_andp_left; auto.
  intros; apply disj_comm; auto.
Qed.

Lemma mapsto_precise: forall {AV: AbsAddr} {A} {mapsto: Addr -> Val -> A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {MSL: MapstoSepLog AV mapsto} p v , precise (mapsto p v).
Proof.
  intros.
  eapply derives_precise; [| apply mapsto__precise].
  apply (exp_right v).
  apply derives_refl.
Qed.

Lemma disj_mapsto: forall {AV: AbsAddr} {A} {mapsto: Addr -> Val -> A} {ND: NatDed A} {SL: SepLog A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} {MSL: MapstoSepLog AV mapsto} {DSL: DisjointedSepLog A} {SMSL: StaticMapstoSepLog AV mapsto} p1 p2 v1 v2, addr_conflict p1 p2 = false -> disjointed (mapsto p1 v1) (mapsto p2 v2).
Proof.
  intros.
  eapply disj_derives; [| | apply disj_mapsto_]; eauto.
  + apply (exp_right v1). apply derives_refl.
  + apply (exp_right v2). apply derives_refl.
Qed.

Lemma corable_andp_ocon2 {A} `{CorableOverlapSepLog A}:
  forall P Q R : A, corable P -> ocon (Q && P) R = P && (ocon Q R).
Proof.
intros. rewrite andp_comm. apply corable_andp_ocon1. auto.
Qed.

Lemma corable_ocon_andp1 {A} `{CorableOverlapSepLog A}:
  forall P Q R : A, corable P -> ocon Q (P && R) = P && (ocon Q R).
Proof.
intros. rewrite ocon_comm. rewrite corable_andp_ocon1; auto. rewrite ocon_comm; auto.
Qed.

Lemma corable_ocon_andp2 {A} `{CorableOverlapSepLog A}:
  forall P Q R : A, corable P -> ocon Q (R && P) = P && (ocon Q R).
Proof.
intros. rewrite ocon_comm. rewrite andp_comm. rewrite corable_andp_ocon1; auto. rewrite ocon_comm; auto.
Qed.

Lemma tri_sepcon_ocon {A} `{OverlapSepLog A}:
  forall P Q R, P * Q * R |-- ocon (P * Q) (Q * R).
Proof.
  intros.
  eapply derives_trans; [| apply ocon_wand].
  instantiate (1 := Q).
  rewrite sepcon_assoc.
  rewrite (sepcon_comm Q R).
  rewrite <- sepcon_assoc.
  repeat apply sepcon_derives; auto.
  + apply wand_sepcon_adjoint; auto.
  + apply wand_sepcon_adjoint; auto.
Qed.
  
Instance ocon_owand_CCC: forall A `{OverlapSepLog A}, CCCviaNatDed A ocon owand.
Proof.
  intros.
  constructor.
  apply ocon_comm.
  apply ocon_assoc.
  apply owand_ocon_adjoint.
  intros; apply ocon_derives; auto.
Defined.

Lemma exp_ocon1 {A} `{OverlapSepLog A}: forall B (p: B -> A) q, ocon (exp p) q = (exp (fun x => ocon (p x) q)).
Proof.
  eapply CCC_exp_prod1.
  apply ocon_owand_CCC.
Qed.

Lemma exp_ocon2 {A} `{OverlapSepLog A}: forall B (p: A) (q: B -> A) , ocon p (exp q) = exp (fun x => ocon p (q x)).
Proof.
  eapply CCC_exp_prod2.
  apply ocon_owand_CCC.
Qed.

Ltac normalize_overlap :=
  repeat
  match goal with
     | |- context [ocon (?P && ?Q) ?R] => rewrite (corable_andp_ocon1 P Q R) by (auto with norm)
     | |- context [ocon ?Q (?P && ?R)] => rewrite (corable_ocon_andp1 P Q R) by (auto with norm)
     | |- context [ocon (?Q && ?P) ?R] => rewrite (corable_andp_ocon2 P Q R) by (auto with norm)
     | |- context [ocon ?Q (?R && ?P)] => rewrite (corable_ocon_andp2 P Q R) by (auto with norm)
     | |- context [ocon (exp ?P) ?Q] => rewrite (exp_ocon1 _ P Q)
     | |- context [ocon ?P (exp ?Q)] => rewrite (exp_ocon2 _ P Q)
     | |- _ => eauto with typeclass
  end;
  repeat rewrite <- andp_assoc;
  try normalize.

Goal forall {A} `{CorableOverlapSepLog A} P (Q R: A), ocon (!! P && !! P  && Q) R = ocon (!! P && Q && !! P) (!! P && R && !! P).
intros.
normalize_overlap.
Abort.

Goal forall {A} `{CorableOverlapSepLog A} P R (Q: A), Q |-- ocon (ocon (EX x: nat, P x) Q) (EX x: nat, R x).
intros.
normalize_overlap.
apply (exp_right 0).
normalize_overlap.
Abort.