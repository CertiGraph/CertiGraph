Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GraphBi.
Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.sample_mark.env_mark_bi.
Require Import RamifyCoq.floyd_ext.share.

Local Open Scope logic.

Section pSGG_VST.

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

End pSGG_VST.

Instance pSGG_VST: pPointwiseGraph_Graph_Bi.
  refine (Build_pPointwiseGraph_Graph_Bi pointer_val NullPointer SGBA_VST).
Defined.

Section sSGG_VST.

Definition trinode (sh: share) (p: addr) (dlr: bool * addr * addr): mpred :=
  match dlr with
  | (d, l, r) => data_at sh node_type
                  (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r))
                    (pointer_val_val p)
  end.

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

Lemma sepcon_unique_vertex_at sh: writable_share sh -> sepcon_unique2 (@vertex_at _ _ _ _ _ (SGP_VST sh)).
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
  + change (sizeof node_type) with 16. omega.
Qed.

(*
Instance sMSLstandard sh : StaticMapstoSepLog (AAV (SGP_VST sh)) (trinode sh).
Proof.
  apply mkStaticMapstoSepLog; simpl; intros.
  + hnf in H. simpl in H.
    destruct_eq_dec p p; congruence.
  + unfold trinode.
    destruct v1 as [[d1 l1] r1].
    destruct v2 as [[d2 l2] r2].
    rewrite (add_andp _ _ (@data_at_local_facts CompSpecs _ node_type _ (pointer_val_val p1))).
    rewrite (add_andp _ _ (@data_at_local_facts CompSpecs _ node_type _ (pointer_val_val p2))).
    normalize.
    apply data_at_conflict; auto.
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
      rewrite (add_andp _ _ (@data_at_local_facts CompSpecs sh node_type _ (pointer_val_val p1))) at 1.
      entailer!.
      tauto.
    - apply exp_left; intros [[d l] r]; normalize.
      apply (exp_right (Vint (Int.repr (if d then 1 else 0)), (pointer_val_val l, pointer_val_val r))).
      rewrite (add_andp _ _ (@data_at_local_facts CompSpecs sh node_type _ (pointer_val_val p2))) at 1.
      entailer!.
      tauto.
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
*)
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

End sSGG_VST.

Hint Extern 10 (@sepcon_unique2 _ _ _ _ _ (@vertex_at _ _ _ _ _ _)) => apply sepcon_unique_vertex_at; auto.

Instance sSGG_VST (sh: wshare): @sPointwiseGraph_Graph_Bi pSGG_VST bool unit.
  refine (Build_sPointwiseGraph_Graph_Bi pSGG_VST _ _ _ (SGP_VST sh) (SGA_VST sh) (SGAvs_VST sh) (SGAvn_VST sh)).
Defined.

(* Global Opaque pSGG_VST sSGG_VST. *)
