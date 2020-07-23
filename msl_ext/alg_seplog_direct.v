Require Import VST.msl.seplog.
Require Import VST.msl.base.
Require Import VST.msl.sepalg.
Require Import VST.msl.alg_seplog_direct.
Require Import CertiGraph.msl_ext.seplog.
Require Import CertiGraph.msl_ext.precise_direct.
Require Import CertiGraph.msl_ext.overlapping_direct.
Require Import VST.msl.predicates_sa.
Local Open Scope logic.

Instance algPreciseSepLog (A : Type) {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A}: PreciseSepLog (pred A).
  apply (mkPreciseSepLog precise); simpl; intros.
  (* + eapply precise_left_sepcon_andp_distr_d; eauto. *)
  + eapply derives_precise; eauto.
  + apply precise_emp.
  + apply precise_sepcon_d; auto.
  (* + apply precise_wand_ewand_d; auto. *)
Defined.

Instance algOverlapSepLog (A: Type) {JA: Join A} {SA: Sep_alg A} {PA : Perm_alg A} {CA: Canc_alg A} {DA: Disj_alg A} {CrA: Cross_alg A} : OverlapSepLog (pred A).
  apply (mkOverlapSepLog ocon owand); unfold algNatDed, algSepLog, algPreciseSepLog; simpl.
  + apply ocon_emp_d.
  + apply ocon_TT_d.
  + apply andp_ocon_d.
  + apply ocon_andp_prop_d.
  + apply sepcon_ocon_d.
  + intros. rewrite ocon_wand_d.
    apply (exp_right R).
    apply derives_refl.
  + apply ocon_comm_d.
  + apply ocon_assoc_d.
  + apply ocon_derives_d.
  + apply owand_ocon_adjoint_d.
  + apply ocon_contain_d.
  (* + apply precise_ocon_contain_d. *)
  + apply precise_ocon_self_d.
  + apply precise_ocon_d.
Defined.

Instance algDisjointedSepLog (A: Type) {JA: Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A} {DA: Disj_alg A} {TA: Trip_alg A} {CrA: Cross_alg A}: DisjointedSepLog (pred A).
  apply (mkDisjointedSepLog disjointed); unfold algNatDed, algSepLog, algPreciseSepLog; simpl.
  + apply ocon_sepcon_d.
  + apply disj_emp_d.
  + apply disj_comm_d.
  + apply disj_derives_d.
  + apply disj_ocon_right_d.
Defined.

Instance algCorableOverlapSepLog (A: Type) {JA: Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A} {DA: Disj_alg A} {TA: Trip_alg A} {CrA: Cross_alg A} : CorableOverlapSepLog (pred A).
  apply mkCorableOverlapSepLog; unfold algNatDed, algSepLog, algPreciseSepLog; simpl; intros.
  + apply corable_ocon_d; auto.
  + apply corable_andp_ocon1_d; auto.
Defined.
