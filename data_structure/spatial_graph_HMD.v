Require Import RamifyCoq.data_structure.spatial_graph.
Require Import VST.msl.alg_seplog_direct.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.alg_seplog_direct.
Require Import RamifyCoq.msl_ext.ramify_tactics.
Require Import RamifyCoq.heap_model_direct.SeparationAlgebra.
Require Import RamifyCoq.heap_model_direct.mapsto.
Require Import RamifyCoq.heap_model_direct.SeparationLogic.
Require Import VST.msl.msl_direct.
Require Import VST.msl.predicates_sa.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Local Open Scope pred.

Definition trinode x d l r := !! (3 | x) && ((mapsto x d) * (mapsto (x+1) l) * (mapsto (x+2) r)).

Instance MSLdirect : MapstoSepLog AbsAddr_world trinode.
Proof.
  apply mkMapstoSepLog.
Abort.
(*
 repeat intro.
  destruct H1 as [w3 ?], H2 as [w4 ?]; destruct H as [? [? [? ?]]], H0 as [? [? [? ?]]].
  destruct w1 as [v1 f1]; destruct w2 as [v2 f2]; destruct w3 as [v3 f3]; destruct w4 as [v4 f4]; destruct w as [v f].
  hnf in H1, H2; simpl in *. apply exist_ext. extensionality mm. destruct (eq_dec mm p).
  + subst. specialize (H1 p). specialize (H2 p). rewrite H4 in *. rewrite H6 in *. inversion H1.
    - subst. inversion H2.
      * rewrite H10, H12. auto.
      * subst. rewrite <- H8 in H2. rewrite <- H11 in H2. hnf in H2. inversion H2. subst. inversion H15.
    - subst. rewrite <- H8 in H1. rewrite <- H9 in H1. hnf in H1. inversion H1. subst. inversion H13.
  + specialize (H3 mm n). specialize (H5 mm n). rewrite H3, H5. auto.
Defined.


*)