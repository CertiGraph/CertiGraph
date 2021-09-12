Require Import VST.msl.seplog.
Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.sepalg.
Require Import VST.msl.age_sepalg.
Require Import VST.msl.predicates_hered.
Require Import VST.msl.alg_seplog.
Require Import CertiGraph.msl_ext.seplog.
Require Import CertiGraph.msl_ext.precise.
Require Import CertiGraph.msl_ext.overlapping.
Require Import VST.msl.predicates_sl.
Require Import VST.msl.corable.
Local Open Scope logic.

Instance algPreciseSepLog (A : Type) {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG : ageable A} {AA: Age_alg A}: PreciseSepLog (pred A).
  apply (mkPreciseSepLog precise); simpl; intros.
  (* + eapply precise_left_sepcon_andp_distr_i; eauto. *)
  + apply derivesI in H. eapply (derives_precise _ _ H); eauto.
  + apply precise_emp.
  + apply precise_sepcon_i; auto.
  (* + apply precise_wand_ewand_i; auto. *)
Defined.

Instance algOverlapSepLog (A: Type) {JA: Join A} {SA: Sep_alg A} {PA : Perm_alg A} {DA: Disj_alg A} {CrA: Cross_alg A} {AG : ageable A} {AA : Age_alg A} : OverlapSepLog (pred A).
  apply (mkOverlapSepLog ocon owand); unfold algNatDed, algSepLog, algPreciseSepLog; simpl.
  + apply ocon_emp_i.
  + apply ocon_TT_i.
  + intros. apply Build_nd_derives. apply andp_ocon_i.
  + apply ocon_andp_prop_i.
  + intros. apply Build_nd_derives. apply sepcon_ocon_i.
  + intros. rewrite ocon_wand_i. apply Build_nd_derives.
    apply (exp_right R).
    apply derives_refl.
  + apply ocon_comm_i.
  + apply ocon_assoc_i.
  + intros. apply Build_nd_derives.
    apply derivesI in H, H0. apply ocon_derives_i; auto.
  + split; intros; apply Build_nd_derives; apply derivesI in H; apply owand_ocon_adjoint_i; auto.
  + intros.
    apply Build_nd_derives. apply derivesI in H.
    apply ocon_contain_i. auto.
  (* + apply precise_ocon_contain_i. *)
  + apply precise_ocon_self.
  + apply precise_ocon_i.
Defined.

Instance algDisjointedSepLog (A: Type) {JA: Join A} {PA : Perm_alg A} {SA: Sep_alg A} {DA: Disj_alg A} {TA: Trip_alg A} {CrA: Cross_alg A} {AG : ageable A} {AA : Age_alg A} : DisjointedSepLog (pred A).
  apply (mkDisjointedSepLog disjointed); unfold algNatDed, algSepLog, algPreciseSepLog; simpl.
  + intros. apply Build_nd_derives, ocon_sepcon_i. auto.
  + apply disj_emp_i.
  + apply disj_comm_i.
  + intros. apply derivesI in H, H0.
    apply (disj_derives_i _ _ _ _ H H0 H1).
  + apply disj_ocon_right_i.
Defined.

Instance algCorableOverlapSepLog (A: Type) {JA: Join A} {PA : Perm_alg A} {SA: Sep_alg A} {DA: Disj_alg A} {TA: Trip_alg A} {CrA: Cross_alg A} {AG : ageable A} {AA : Age_alg A} : CorableOverlapSepLog (pred A).
  apply mkCorableOverlapSepLog; unfold algNatDed, algSepLog, algPreciseSepLog; simpl; intros.
  + apply corable_ocon_i; auto.
  + apply corable_andp_ocon1_i; auto.
Defined.
