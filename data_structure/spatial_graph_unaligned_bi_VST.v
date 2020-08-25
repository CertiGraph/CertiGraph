Require Import CertiGraph.msl_application.Graph.
Require Import CertiGraph.msl_application.GraphBi.
Require Import VST.veric.SeparationLogic.
Require Import CertiGraph.dispose.env_dispose_bi.
Require Import CertiGraph.floyd_ext.share.

Local Open Scope logic.

Instance PointerVal_EqDec: EquivDec.EqDec pointer_val eq.
  hnf; intros.
  apply PV_eq_dec.
Defined.

Instance PointerValLR_EqDec: EquivDec.EqDec (pointer_val * LR) eq.
  hnf; intros.
  destruct x, y.
  destruct l, l0; [| right | right |]; simpl; try congruence.
  + destruct (PV_eq_dec p p0); [left | right]; congruence.
  + destruct (PV_eq_dec p p0); [left | right]; congruence.
Defined.

Instance SGBA_VST: PointwiseGraphBasicAssum pointer_val (pointer_val * LR).
  refine (Build_PointwiseGraphBasicAssum pointer_val (pointer_val * LR) _ _).
Defined.

Instance pSGG_VST: pPointwiseGraph_Graph_Bi.
refine (Build_pPointwiseGraph_Graph_Bi pointer_val NullPointer
                                       _).
Defined.

Definition vgamma2cdata (dlr : bool * addr * addr) : reptype node_type :=
  match dlr with
  | (d, l, r) => (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r))
  end.

Definition trinode (sh: share) (p: addr) (dlr: bool * addr * addr): mpred :=
  data_at sh node_type (vgamma2cdata dlr) (pointer_val_val p).

Instance SGP_VST (sh: share) : PointwiseGraphPred addr (addr * LR) (bool * addr * addr) unit mpred.
  refine (Build_PointwiseGraphPred _ _ _ _ _ (trinode sh) (fun _ _ => emp)).
Defined.

(*
Instance MSLstandard sh : MapstoSepLog (AAV (SGP_VST sh)) (trinode sh).
Proof.
  intros.
  apply mkMapstoSepLog.
  intros.
  apply derives_precise with (memory_block sh (sizeof node_type) (pointer_val_val p));
   [| apply memory_block_precise].
  apply exp_left; intros [[? ?] ?].
  unfold trinode.
  apply data_at_memory_block.
Defined.
*)
Lemma sepcon_unique_vertex_at sh: writable_share sh -> iter_sepcon.sepcon_unique2 (@vertex_at _ _ _ _ _ (SGP_VST sh)).
Proof.
  intros.
  hnf; intros.
  simpl.
  destruct y1 as [[? ?] ?], y2 as [[? ?] ?].
  unfold trinode.
  rewrite data_at_isptr.
  normalize.
  apply data_at_conflict.
  + apply readable_nonidentity, writable_readable. auto.
  + change (sizeof node_type) with 12. lia.
Qed.

Instance SGA_VST (sh: share) : PointwiseGraphAssum (SGP_VST sh).
  refine (Build_PointwiseGraphAssum _ _ _ _ _ _ _ _ _ _ _).
Defined.

Instance SGAvs_VST (sh: wshare): PointwiseGraphAssum_vs (SGP_VST sh).
  apply sepcon_unique_vertex_at; auto.
Defined.

Instance SGAvn_VST (sh: wshare): PointwiseGraphAssum_vn (SGP_VST sh) NullPointer.
  intros [[? ?] ?].
  simpl.
  unfold trinode.
  rewrite data_at_isptr.
  normalize.
Defined.

Instance sSGG_VST (sh: wshare): @sPointwiseGraph_Graph_Bi pSGG_VST bool unit.
  refine (Build_sPointwiseGraph_Graph_Bi pSGG_VST _ _ _ (SGP_VST sh) (SGA_VST sh) (SGAvs_VST sh) (SGAvn_VST sh)).
Defined.
