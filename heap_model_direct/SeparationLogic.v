Require Import VST.msl.seplog.
Require Import VST.msl.sepalg.
Require Import VST.msl.alg_seplog_direct.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.alg_seplog_direct.
Require Import RamifyCoq.heap_model_direct.SeparationAlgebra.
Require Import RamifyCoq.heap_model_direct.mapsto.
Require Import VST.msl.predicates_sa.

Instance Ndirect : NatDed (pred world) := algNatDed world.
Instance Sdirect : SepLog (pred world) := algSepLog world.
Instance Cldirect : ClassicalSep (pred world) := algClassicalSep world.
(* Instance CSLdirect : CorableSepLog (pred world) := algCorableSepLog world. *)
Instance PSLdirect : PreciseSepLog (pred world) := algPreciseSepLog world.
Instance OSLdirect : OverlapSepLog (pred world) := algOverlapSepLog world.
Instance DSLdirect : DisjointedSepLog (pred world) := algDisjointedSepLog world.
