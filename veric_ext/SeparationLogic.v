Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.alg_seplog.

Instance PSLveric: PreciseSepLog mpred := algPreciseSepLog compcert_rmaps.RML.R.rmap.
Instance OSLveric: OverlapSepLog mpred := algOverlapSepLog compcert_rmaps.RML.R.rmap.
Instance DSLveric: DisjointedSepLog mpred := algDisjointedSepLog compcert_rmaps.RML.R.rmap.

