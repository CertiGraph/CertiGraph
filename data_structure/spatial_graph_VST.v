Require Import RamifyCoq.data_structure.spatial_graph2.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.veric_ext.SeparationLogic.
Require Import RamifyCoq.msl_ext.alg_seplog.
Require Import RamifyCoq.sample_mark.env_mark.
Require Import RamifyCoq.veric_ext.SeparationLogic.
Require Import RamifyCoq.floyd_ext.DataatSL.

Local Open Scope logic.

Instance SGS_VST: SpatialGraphSetting.
  apply (Build_SpatialGraphSetting pointer_val NullPointer PV_eq_dec).
Defined.

Definition trinode (sh: share) (p: Addr) (dlr: Val): mpred :=
  match dlr with
  | (d, l, r) => data_at sh node_type
                  (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r))
                    (pointer_val_val p)
  end.

Instance MSLstandard sh : MapstoSepLog AV_SGraph (trinode sh).
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

Instance sMSLstandard sh : StaticMapstoSepLog AV_SGraph (trinode sh).
Proof.
  apply mkStaticMapstoSepLog; simpl; intros.
  + hnf in H. simpl in H. unfold addr_eqb in H. simpl in H.
    destruct PV_eq_dec; congruence.
  + unfold trinode.
    destruct v1 as [[d1 l1] r1].
    destruct v2 as [[d2 l2] r2].
    rewrite (add_andp _ _ (@data_at_compatible CompSpecs CS_legal _ node_type _ (pointer_val_val p1))).
    rewrite (add_andp _ _ (@data_at_compatible CompSpecs CS_legal _ node_type _ (pointer_val_val p2))).
    normalize.
    apply data_at_conflict.
    change (sizeof cenv_cs node_type) with 16.
    unfold addr_eqb in H; simpl in H.
    destruct (PV_eq_dec p1 p2); [| congruence].
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
      unfold addr_eqb in H; simpl in H.
      destruct (PV_eq_dec p1 p2); [congruence |].
      destruct H0 as [? [_ [_ [_ [_ [_ [? _]]]]]]].
      destruct H1 as [? [_ [_ [_ [_ [_ [? _]]]]]]].
      unfold align_compatible in *.
      change (alignof cenv_cs node_type) with 16 in *.
      destruct p1, p2;
        try solve [simpl in H0; tauto | simpl in  H1; tauto].
      cbv beta iota zeta delta [pointer_val_val] in *; clear H0 H1.
      intros [[? ?] [[? ?] [? [? ?]]]].
      inv H0; inv H1.
      apply res_predicates.range_overlap_spec in H4; [| omega | omega].
      assert (Int.unsigned i = Int.unsigned i0) by (destruct H4 as [[? ?] | [? ?]], H3, H2; omega).
      assert (b = b0) by (destruct H4 as [[? ?] | [? ?]]; subst; auto).
      apply n.
      rewrite H1, <- (Int.repr_unsigned i), H0, Int.repr_unsigned; auto.
Defined.

Instance SGA_VST (sh: Share.t) : SpatialGraphAssum.
  apply (Build_SpatialGraphAssum mpred _ _ _ _ _ _ _ _ SGS_VST (trinode sh) _ (sMSLstandard sh)).
Defined.


