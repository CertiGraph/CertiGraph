Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_application.ArrayGraph.
Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.veric_ext.SeparationLogic.
Require Import RamifyCoq.msl_ext.alg_seplog.
Require Import RamifyCoq.sample_mark.env_unionfind_arr.
Require Import RamifyCoq.veric_ext.SeparationLogic.
Require Import RamifyCoq.floyd_ext.DataatSL.
Require Import RamifyCoq.floyd_ext.share.

Local Open Scope logic.

Instance SAGA_VST: SpatialArrayGraphAssum mpred. Proof. refine (Build_SpatialArrayGraphAssum _ _ _ _ _). Defined.

Definition vgamma2cdata (rpa : nat * Z) : reptype vertex_type :=
  match rpa with
  | (r, pa) => (Vint (Int.repr (Z.of_nat r)), Vint (Int.repr pa))
  end.

Instance SAG_VST (sh: share): SpatialArrayGraph pointer_val mpred := fun pt lst => data_at sh (tarray vertex_type (Z.of_nat (length lst))) (map vgamma2cdata lst) (pointer_val_val pt).
