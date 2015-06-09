Require Import VST.msl.seplog.
Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.sepalg.
Require Import VST.msl.age_sepalg.
Require Import VST.msl.predicates_hered.
Require Import VST.msl.predicates_sl.
Require Import VST.msl.alg_seplog.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.overlapping.
Local Open Scope logic.

(*
Instance algOverlapSepLog {A: Type} {JA: Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A} {CA: Cross_alg A} {AG : ageable A} {AA : Age_alg A} : OverlapSepLog (pred A).
  apply (mkOverlapSL (pred A) _ _ ocon); unfold algNatDed, algSepLog.
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
Defined.
*)