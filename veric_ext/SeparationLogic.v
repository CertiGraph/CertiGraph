Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.alg_seplog.
Require Import RamifyCoq.veric_ext.seplog.

Instance PSLveric: PreciseSepLog mpred := algPreciseSepLog compcert_rmaps.RML.R.rmap.
Instance OSLveric: OverlapSepLog mpred := algOverlapSepLog compcert_rmaps.RML.R.rmap.
Instance DSLveric: DisjointedSepLog mpred := algDisjointedSepLog compcert_rmaps.RML.R.rmap.

Module Mapsto.
Section Mapsto.

Definition adr_conflict (a1 a2 : val * type) : bool :=
  match a1, a2 with
  | (p1, t1), (p2, t2) => 
    if (pointer_range_overlap_dec p1 (BV_sizeof t1) p2 (BV_sizeof t2)) then true else false
  end.

Instance AbsAddr_veric : AbsAddr.
  apply (mkAbsAddr (val * type) val adr_conflict); intros; unfold adr_conflict in *; destruct p1, p2.
  + destruct (pointer_range_overlap_dec v (BV_sizeof t) v0 (BV_sizeof t0)); subst;
    destruct (pointer_range_overlap_dec v0 (BV_sizeof t0) v (BV_sizeof t)); subst; auto;
    pose proof pointer_range_overlap_comm v (BV_sizeof t) v0 (BV_sizeof t0);
    tauto.
  + destruct (pointer_range_overlap_dec v (BV_sizeof t) v0 (BV_sizeof t0)); auto.
    destruct (pointer_range_overlap_isptr _ _ _ _ p).
    destruct (zlt 0 (BV_sizeof t)).
    - assert (pointer_range_overlap v (BV_sizeof t) v (BV_sizeof t))
        by (apply pointer_range_overlap_refl; auto; omega).
      destruct (pointer_range_overlap_dec v (BV_sizeof t) v (BV_sizeof t)); [congruence | tauto].
    - apply pointer_range_overlap_non_zero in p.
      omega.
Defined.

Instance MSLveric sh: MapstoSepLog AbsAddr_veric (fun pt v => let (p, t) := pt in mapsto sh t p v).
Proof.
  apply mkMapstoSepLog.
  intros [p t].
  apply exp_mapsto_precise.
Defined.

Instance sMSLveric sh: StaticMapstoSepLog AbsAddr_veric (fun pt v => let (p, t) := pt in mapsto sh t p v).
Proof.
  apply mkStaticMapstoSepLog.
  + intros [p t] v ?.
    unfold addr_empty in H; simpl in H.
    destruct (pointer_range_overlap_dec p (BV_sizeof t) p (BV_sizeof t)); [congruence |].
    unfold mapsto.
    destruct (access_mode t) eqn:?H; try apply FF_left.
    destruct (type_is_volatile t), p; try apply FF_left.
    assert (pointer_range_overlap (Vptr b i) (BV_sizeof t) (Vptr b i) (BV_sizeof t)); [| tauto].
    apply pointer_range_overlap_refl.
    - simpl; tauto.
    - eapply BV_sizeof_pos; eauto.
    - eapply BV_sizeof_pos; eauto.
  + intros [p1 t1] [p2 t2] v1 v2 ?.
    apply mapsto_conflict with (PTree.empty _).
    apply pointer_range_overlap_BV_sizeof.
    simpl in H.
    destruct (pointer_range_overlap_dec p1 (BV_sizeof t1) p2 (BV_sizeof t2)); [auto | congruence].
  + intros [p1 t1] [p2 t2] ?.
    simpl in H.
    destruct (pointer_range_overlap_dec p1 (BV_sizeof t1) p2 (BV_sizeof t2)); [congruence |].
    destruct (pointer_range_overlap_dec p1 (sizeof (PTree.empty _) t1) p2 (sizeof (PTree.empty _) t2)).
    - apply pointer_range_overlap_sizeof with (sh := sh) in p.
      destruct p as [? | [? | ?]].
      * tauto.
      * eapply disj_derives; [exact H0 | apply derives_refl |].
        pose proof log_normalize.FF_disj.
        simpl in H1; apply H1.
      * eapply disj_derives; [apply derives_refl | exact H0 |].
        pose proof log_normalize.disj_FF.
        simpl in H1; apply H1.
    - apply disj_mapsto_ with (PTree.empty _); auto.
Defined.

End Mapsto.
End Mapsto.
