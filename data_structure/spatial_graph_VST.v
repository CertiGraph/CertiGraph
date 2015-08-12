Require Import RamifyCoq.data_structure.general_spatial_graph.
Require Import RamifyCoq.data_structure.spatial_graph_bi.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.veric_ext.SeparationLogic.
Require Import RamifyCoq.msl_ext.alg_seplog.
Require Import RamifyCoq.sample_mark.env_mark_bi.
Require Import RamifyCoq.veric_ext.SeparationLogic.
Require Import RamifyCoq.floyd_ext.DataatSL.
Require Import RamifyCoq.Coqlib.

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

Instance SGBA_VST: SpatialGraphBasicAssum pointer_val (pointer_val * LR).
  refine (Build_SpatialGraphBasicAssum pointer_val (pointer_val * LR) _ _).
Defined.

Instance SGGS_VST: SpatialGraph_Graph_Setting_Bi.
  refine (Build_SpatialGraph_Graph_Setting_Bi pointer_val NullPointer mpred _).
Defined.

Definition trinode (sh: share) (p: addr) (dlr: bool * addr * addr): mpred :=
  match dlr with
  | (d, l, r) => data_at sh node_type
                  (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r))
                    (pointer_val_val p)
  end.

Instance SGP_VST (sh: share) : SpatialGraphPred addr (addr * LR) (bool * addr * addr) unit pred.
  refine (Build_SpatialGraphPred _ _ _ _ _ (trinode sh) (fun _ _ => emp)).
Defined.

Instance MSLstandard sh : MapstoSepLog (AAV (SGP_VST sh)) (trinode sh).
Proof.
  intros.
  apply mkMapstoSepLog.
  intros.
  apply derives_precise with (memory_block sh (sizeof cenv_cs node_type) (pointer_val_val p));
   [| apply memory_block_precise].
  apply exp_left; intros [[? ?] ?].
  unfold trinode.
  apply data_at_memory_block.
Defined.

Instance sMSLstandard sh : StaticMapstoSepLog (AAV (SGP_VST sh)) (trinode sh).
Proof.
  apply mkStaticMapstoSepLog; simpl; intros.
  + hnf in H. simpl in H.
    destruct_eq_dec p p; congruence.
  + unfold trinode.
    destruct v1 as [[d1 l1] r1].
    destruct v2 as [[d2 l2] r2].
    rewrite (add_andp _ _ (@data_at_compatible CompSpecs CS_legal _ node_type _ (pointer_val_val p1))).
    rewrite (add_andp _ _ (@data_at_compatible CompSpecs CS_legal _ node_type _ (pointer_val_val p2))).
    normalize.
    apply data_at_conflict.
    change (sizeof cenv_cs node_type) with 16.
    destruct_eq_dec p1 p2; [| congruence].
    subst.
    apply pointer_range_overlap_refl; try omega.
    destruct H0; auto.
  + unfold msl_ext.seplog.mapsto_, trinode.
    eapply disj_derives with
     (!! field_compatible node_type [] (pointer_val_val p1) &&
        EX v: reptype node_type, data_at sh node_type v (pointer_val_val p1))
     (!! field_compatible node_type [] (pointer_val_val p2) &&
        EX v: reptype node_type, data_at sh node_type v (pointer_val_val p2)).
    - apply exp_left; intros [[d l] r]; normalize.
      apply (exp_right (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r))).
      rewrite andp_comm, <- (add_andp _ _ (data_at_compatible _ _ _ _)).
      apply derives_refl.
    - apply exp_left; intros [[d l] r]; normalize.
      apply (exp_right (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r))).
      rewrite andp_comm, <- (add_andp _ _ (data_at_compatible _ _ _ _)).
      apply derives_refl.
    - apply disj_prop_andp_left; [apply field_compatible_dec | intro].
      apply disj_prop_andp_right; [apply field_compatible_dec | intro].
      apply disj_data_at.
      change (sizeof cenv_cs node_type) with 16.
      destruct_eq_dec p1 p2; [congruence |].
      destruct H0 as [? [_ [_ [_ [_ [_ [? _]]]]]]].
      destruct H1 as [? [_ [_ [_ [_ [_ [? _]]]]]]].
      unfold align_compatible in *.
      change (alignof cenv_cs node_type) with 16 in *.
      destruct p1, p2;
        try solve [simpl in H0; tauto | simpl in  H1; tauto].
      cbv beta iota zeta delta [pointer_val_val] in *; clear H0 H1.
      intros [[? ?] [[? ?] [? [? ?]]]].
      inv H0; inv H1.
      apply res_predicates.range_overlap_spec in H5; [| omega | omega].
      assert (Int.unsigned i = Int.unsigned i0) by (destruct H5 as [[? ?] | [? ?]], H4, H3; omega).
      assert (b = b0) by (destruct H5 as [[? ?] | [? ?]]; subst; auto).
      apply H2.
      rewrite H1, <- (Int.repr_unsigned i), H0, Int.repr_unsigned; auto.
Defined.

Instance SGA_VST (sh: share) : SpatialGraphAssum (SGP_VST sh).
  refine (Build_SpatialGraphAssum _ _ _ _ _ _ _ _ _ _ _ _ _).
  + simpl; left.
    intros; apply (@msl_ext.seplog.mapsto_conflict _ _ _ _ _ _ _ _ _ _ _ (sMSLstandard sh)).
    simpl.
    destruct_eq_dec x x; congruence.
  + simpl; right.
    intros; auto.
Defined.

Instance SGG_VST (sh: share): SpatialGraph_Graph_Bi.
  refine (Build_SpatialGraph_Graph_Bi SGGS_VST (SGP_VST sh) (SGA_VST sh)).
Defined.

