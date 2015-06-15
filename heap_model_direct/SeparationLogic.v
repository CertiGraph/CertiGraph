Require Import VST.msl.seplog.
Require Import VST.msl.sepalg.
Require Import VST.msl.psepalg.
Require Import VST.msl.alg_seplog_direct.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.overlapping_direct.
Require Import RamifyCoq.msl_ext.alg_seplog_direct.
Require Import RamifyCoq.msl_ext.ramify_tactics.
Require Import RamifyCoq.heap_model_direct.SeparationAlgebra.
Require Import RamifyCoq.heap_model_direct.mapsto.
Require Import VST.msl.msl_direct.
Require Import VST.msl.predicates_sa.

Instance Ndirect : NatDed (pred world) := algNatDed world.
Instance Sdirect : SepLog (pred world) := algSepLog world.
Instance Cldirect : ClassicalSep (pred world) := algClassicalSep world.
Instance CSLdirect : CorableSepLog (pred world) := algCorableSepLog world.
Instance PSLdirect : PreciseSepLog (pred world) := algPreciseSepLog world.
Instance OSLdirect : OverlapSepLog (pred world) := algOverlapSepLog world.
Instance DSLdirect : DisjointedSepLog (pred world) := algDisjointedSepLog world.

Instance MSLdirect : MapstoSepLog AbsAddr_world mapsto.
Proof.
  apply mkMapstoSepLog.
  apply mapsto__precise.
Defined.

Instance sMSLdirect : StaticMapstoSepLog AbsAddr_world mapsto.
Proof.
  apply mkStaticMapstoSepLog; simpl; intros.
  + hnf in H. simpl in H. unfold adr_conflict in H. destruct (eq_nat_dec p p).
    - inversion H.
    - exfalso; tauto.
  + apply mapsto_conflict.
    unfold adr_conflict in H.
    destruct (eq_nat_dec p1 p2); congruence.
  + apply disj_mapsto_.
    unfold adr_conflict in H.
    destruct (eq_nat_dec p1 p2); congruence.
Defined.

Instance nMSLdirect : NormalMapstoSepLog AbsAddr_world mapsto.
Proof.
  apply mkNormalMapstoSepLog.
  apply mapsto_inj.
Defined.
