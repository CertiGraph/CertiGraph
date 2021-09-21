Require Import VST.msl.seplog.
Require Import VST.msl.sepalg.
Require Import VST.msl.psepalg.
Require Import VST.msl.alg_seplog_direct.
Require Import CertiGraph.msl_ext.abs_addr.
Require Import CertiGraph.msl_ext.seplog.
Require Import CertiGraph.msl_ext.overlapping_direct.
Require Import CertiGraph.msl_ext.alg_seplog_direct.
Require Import CertiGraph.msl_ext.ramify_tactics.
Require Import CertiGraph.heap_model_direct.SeparationAlgebra.
Require Import CertiGraph.heap_model_direct.mapsto.
Require Import VST.msl.msl_direct.
Require Import VST.msl.predicates_sa.
Require Import Peano_dec.

Instance Ndirect : NatDed (pred world). exact (algNatDed world). Defined.
Instance Sdirect : SepLog (pred world). exact (algSepLog world). Defined.
Instance Cldirect : ClassicalSep (pred world). exact (algClassicalSep world). Defined.
Instance CSLdirect : CorableSepLog (pred world). exact (algCorableSepLog world). Defined.
Instance PSLdirect : PreciseSepLog (pred world). exact (algPreciseSepLog world). Defined.
Instance OSLdirect : OverlapSepLog (pred world). exact (algOverlapSepLog world). Defined.
Instance DSLdirect : DisjointedSepLog (pred world). exact (algDisjointedSepLog world). Defined.

Instance MSLdirect : MapstoSepLog AbsAddr_world mapsto.
Proof.
  apply mkMapstoSepLog.
  apply mapsto__precise.
Defined.

Instance sMSLdirect : StaticMapstoSepLog AbsAddr_world mapsto.
Proof.
  apply mkStaticMapstoSepLog; simpl; intros.
  + hnf in H. simpl in H. unfold adr_conflict in H. destruct (NPeano.Nat.eq_dec p p).
    - inversion H.
    - exfalso; tauto.
  + apply mapsto_conflict.
    unfold adr_conflict in H.
    destruct (NPeano.Nat.eq_dec p1 p2); congruence.
  + apply disj_mapsto_.
    unfold adr_conflict in H.
    destruct (NPeano.Nat.eq_dec p1 p2); congruence.
Defined.

Instance nMSLdirect : NormalMapstoSepLog AbsAddr_world mapsto.
Proof.
  apply mkNormalMapstoSepLog.
  apply mapsto_inj.
Defined.
