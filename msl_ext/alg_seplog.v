Require Import VST.msl.seplog.
Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.sepalg.
Require Import VST.msl.age_sepalg.
Require Import VST.msl.predicates_hered.
Require Import VST.msl.alg_seplog.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.precise.
Require Import RamifyCoq.msl_ext.overlapping.
Require Import VST.msl.predicates_sl.
Local Open Scope logic.

Instance algPreciseSepLog (A : Type) {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A} {AG : ageable A} {AA: Age_alg A}: PreciseSepLog (pred A).
  apply (mkPreciseSepLog precise); simpl; intros.
  + apply precise_sepcon_andp_sepcon; auto.
  + eapply derives_precise; eauto.
  + apply precise_emp.
  + apply precise_sepcon; auto.
Defined.

Instance algOverlapSepLog (A: Type) {JA: Join A} {SA: Sep_alg A} {PA : Perm_alg A} {CA: Canc_alg A} {DA: Disj_alg A} {CrA: Cross_alg A} {AG : ageable A} {AA : Age_alg A} : OverlapSepLog (pred A).
  apply (mkOverlapSepLog ocon owand); unfold algNatDed, algSepLog, algPreciseSepLog; simpl.
  + apply ocon_emp.
  + apply ocon_TT.
  + apply andp_ocon.
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
Defined.

Instance algDisjointedSepLog (A: Type) {JA: Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A} {DA: Disj_alg A} {TA: Trip_alg A} {CrA: Cross_alg A} {AG : ageable A} {AA : Age_alg A} : DisjointedSepLog (pred A).
  apply (mkDisjointedSepLog disjointed); unfold algNatDed, algSepLog, algPreciseSepLog; simpl.
  + apply ocon_sepcon.
  + apply disj_emp.
  + apply disj_comm.
  + apply disj_derives.
  + apply disj_ocon_right.
Defined.
