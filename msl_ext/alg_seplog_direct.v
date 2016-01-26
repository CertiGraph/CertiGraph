Require Import VST.msl.seplog.
Require Import VST.msl.base.
Require Import VST.msl.sepalg.
Require Import VST.msl.alg_seplog_direct.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.precise_direct.
Require Import RamifyCoq.msl_ext.overlapping_direct.
Require Import VST.msl.predicates_sa.
Local Open Scope logic.

Instance algPreciseSepLog (A : Type) {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A}: PreciseSepLog (pred A).
  apply (mkPreciseSepLog precise); simpl; intros.
  + eapply precise_left_sepcon_andp_distr; eauto.
  + eapply derives_precise; eauto.
  + apply precise_emp.
  + apply precise_sepcon; auto.
  + apply precise_wand_ewand; auto.
Defined.

Instance algOverlapSepLog (A: Type) {JA: Join A} {SA: Sep_alg A} {PA : Perm_alg A} {CA: Canc_alg A} {DA: Disj_alg A} {CrA: Cross_alg A} : OverlapSepLog (pred A).
  apply (mkOverlapSepLog ocon owand); unfold algNatDed, algSepLog, algPreciseSepLog; simpl.
  + apply ocon_emp.
  + apply ocon_TT.
  + apply andp_ocon.
  + apply ocon_andp_prop.
  + apply sepcon_ocon.
  + intros. rewrite ocon_wand.
    apply (exp_right R).
    apply derives_refl.
  + apply ocon_comm.
  + apply ocon_assoc.
  + apply ocon_derives.
  + apply owand_ocon_adjoint.
  + apply ocon_contain.
  + apply precise_ocon_contain.
  + apply precise_ocon.
Defined.

Instance algDisjointedSepLog (A: Type) {JA: Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A} {DA: Disj_alg A} {TA: Trip_alg A} {CrA: Cross_alg A}: DisjointedSepLog (pred A).
  apply (mkDisjointedSepLog disjointed); unfold algNatDed, algSepLog, algPreciseSepLog; simpl.
  + apply ocon_sepcon.
  + apply disj_emp.
  + apply disj_comm.
  + apply disj_derives.
  + apply disj_ocon_right.
Defined.

Instance algCorableOverlapSepLog (A: Type) {JA: Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A} {DA: Disj_alg A} {TA: Trip_alg A} {CrA: Cross_alg A} : CorableOverlapSepLog (pred A).
  apply mkCorableOverlapSepLog; unfold algNatDed, algSepLog, algPreciseSepLog; simpl; intros.
  + apply corable_ocon; auto.
  + apply corable_andp_ocon1; auto.
Defined.
