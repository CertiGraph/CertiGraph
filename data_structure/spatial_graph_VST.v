Require Import RamifyCoq.data_structure.spatial_graph.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.msl_ext.alg_seplog.
Require Import RamifyCoq.veric_ext.SeparationLogic.
Require Import RamifyCoq.sample_mark.env_mark.

(* Move into VST *)
Lemma block_eq_dec: forall b1 b2: block, {b1 = b2} + {b1 <> b2}.
Proof. exact (Coqlib.peq). Qed.

Lemma PV_eq_dec: forall x y: pointer_val, {x = y} + {x <> y}.
Proof.
  intros; destruct x, y; [| right | right | left]; try congruence.
  destruct (block_eq_dec b b0), (Int.eq_dec i i0); [left | right | right | right]; congruence.
Qed.

(* Move into env_mark. *)
Definition node_type := (talignas 4%N (Tstruct _Node noattr)).

Instance SGS_VST: SpatialGraphSetting.
  apply (Build_SpatialGraphSetting int pointer_val NullPointer PV_eq_dec).
Defined.

Definition trinode (sh: share) (p: Addr) (dlr: Val): mpred :=
  match dlr with
  | (d, l, r) => data_at sh node_type (repinj node_type (d, (l, r))) (pointer_val_val p)
  end.

