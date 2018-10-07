Require Import VST.floyd.base.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.mapsto_memory_block.

Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.veric_ext.SeparationLogic.

Local Open Scope logic.

Module Mapsto.
Section Mapsto.

Definition empty_compspecs : compspecs.
Proof.
  refine (mkcompspecs (PTree.empty _) _ _ _).
  + constructor.
    - rewrite PTree.gempty in H; inv H.
    - rewrite PTree.gempty in H; inv H.
    - rewrite PTree.gempty in H; inv H.
    - rewrite PTree.gempty in H; inv H.
  + hnf; intros.
    rewrite PTree.gempty in H; inv H.
  + hnf; intros.
    rewrite PTree.gempty in H; inv H.
Defined.

Definition adr_conflict (sh: share) : val * type -> val * type -> bool :=
  fun a1 a2 =>
  if (dec_share_nonunit sh)
  then match a1, a2 with
       | (p1, t1), (p2, t2) => 
         if (pointer_range_overlap_dec p1 (BV_sizeof t1) p2 (BV_sizeof t2)) then true else false
       end
  else false.

Instance AA (sh: share) : AbsAddr (val * type) val.
  apply (mkAbsAddr (val * type) val (adr_conflict sh)); intros; unfold adr_conflict in *; destruct p1, p2.
  + destruct (pointer_range_overlap_dec v (BV_sizeof t) v0 (BV_sizeof t0)); subst;
    destruct (pointer_range_overlap_dec v0 (BV_sizeof t0) v (BV_sizeof t)); subst; auto;
    pose proof pointer_range_overlap_comm v (BV_sizeof t) v0 (BV_sizeof t0);
    tauto.
  + destruct (pointer_range_overlap_dec v (BV_sizeof t) v0 (BV_sizeof t0)); [| if_tac; auto].
    destruct (pointer_range_overlap_isptr _ _ _ _ p).
    destruct (zlt 0 (BV_sizeof t)).
    - assert (pointer_range_overlap v (BV_sizeof t) v (BV_sizeof t))
        by (apply pointer_range_overlap_refl; auto; omega).
      destruct (pointer_range_overlap_dec v (BV_sizeof t) v (BV_sizeof t)); [congruence | tauto].
    - apply pointer_range_overlap_non_zero in p.
      omega.
Defined.

Instance MSL sh: MapstoSepLog (AA sh) (fun pt v => let (p, t) := pt in mapsto sh t p v).
Proof.
  apply mkMapstoSepLog.
  intros [p t].
  apply exp_mapsto_precise.
Defined.

Instance sMSL (sh: share): StaticMapstoSepLog (AA sh) (fun pt v => let (p, t) := pt in mapsto sh t p v).
Proof.
  apply mkStaticMapstoSepLog.
  + intros [p t] v ?.
    unfold addr_empty in H. simpl in H. unfold adr_conflict in H.
    if_tac in H.
    - destruct (pointer_range_overlap_dec p (BV_sizeof t) p (BV_sizeof t)); [congruence |].
      unfold mapsto.
      destruct (access_mode t) eqn:?H; try apply FF_left.
      destruct (type_is_volatile t), p; try apply FF_left.
      assert (pointer_range_overlap (Vptr b i) (BV_sizeof t) (Vptr b i) (BV_sizeof t)); [| tauto].
      apply pointer_range_overlap_refl.
      * simpl; tauto.
      * eapply BV_sizeof_pos; eauto.
      * eapply BV_sizeof_pos; eauto.
    - apply mapsto_memory_block.mapsto_not_nonunit; auto.
  + intros [p1 t1] [p2 t2] v1 v2 ?.
    simpl in H; unfold adr_conflict in H.
    if_tac in H; [| congruence].
    apply mapsto_memory_block.mapsto_overlap with empty_compspecs; auto.
    apply pointer_range_overlap_BV_sizeof.
    destruct (pointer_range_overlap_dec p1 (BV_sizeof t1) p2 (BV_sizeof t2)); [auto | congruence].
  + intros [p1 t1] [p2 t2] ?.
    simpl in H; unfold adr_conflict in H.
    if_tac in H.
    1: {
     destruct (pointer_range_overlap_dec p1 (BV_sizeof t1) p2 (BV_sizeof t2)); [congruence |].
     destruct (pointer_range_overlap_dec p1 (@sizeof (PTree.empty _) t1) p2 (@sizeof (PTree.empty _) t2)).
      - apply pointer_range_overlap_sizeof with (sh0 := sh) in p.
        destruct p as [? | [? | ?]].
        * tauto.
        * eapply disj_derives; [exact H1 | apply derives_refl |].
          pose proof log_normalize.FF_disj.
          simpl in H2; apply H2.
        * eapply disj_derives; [apply derives_refl | exact H1 |].
          pose proof log_normalize.disj_FF.
          simpl in H2; apply H2.
      - apply @disj_mapsto_ with (PTree.empty _); auto.
    }
    1: {
      unfold mapsto_.
      simpl.
      eapply disj_derives.
      + apply exp_left; intro; apply mapsto_memory_block.mapsto_not_nonunit; auto.
      + apply exp_left; intro; apply mapsto_memory_block.mapsto_not_nonunit; auto.
      + apply (@emp_disj _ Nveric).
    }
Defined.

End Mapsto.
End Mapsto.

Module MemoryBlock.
Section MemoryBlock.

Definition adr_conflict (a1 a2 : val * Z) : bool :=
  match a1, a2 with
  | (p1, n1), (p2, n2) => 
    if (pointer_range_overlap_dec p1 n1 p2 n2) then true else false
  end.

Instance AA : AbsAddr (val * Z) unit.
  apply (mkAbsAddr (val * Z) unit adr_conflict); intros; unfold adr_conflict in *; destruct p1, p2.
  + destruct (pointer_range_overlap_dec v z v0 z0); subst;
    destruct (pointer_range_overlap_dec v0 z0 v z); subst; auto;
    pose proof pointer_range_overlap_comm v z v0 z0;
    tauto.
  + destruct (pointer_range_overlap_dec v z v0 z0); auto.
    destruct (pointer_range_overlap_isptr _ _ _ _ p).
    destruct (zlt 0 z).
    - assert (pointer_range_overlap v z v z)
        by (apply pointer_range_overlap_refl; auto; omega).
      destruct (pointer_range_overlap_dec v z v z); [congruence | tauto].
    - apply pointer_range_overlap_non_zero in p.
      omega.
Defined.

Instance MSL sh: MapstoSepLog AA (fun pn v => let (p, n) := pn in memory_block sh n p).
Proof.
  apply mkMapstoSepLog.
  intros [p n].
  rewrite exp_unit.
  apply memory_block_precise.
Defined.

Instance sMSL (sh: share) (H_non_unit: sepalg.nonunit sh): StaticMapstoSepLog AA (fun pn v => let (p, n) := pn in memory_block sh n p).
Proof.
  apply mkStaticMapstoSepLog.
  + intros [p n] v ?.
    unfold addr_empty in H; simpl in H.
    destruct (pointer_range_overlap_dec p n p n); [congruence |].
    rewrite memory_block_isptr.
    normalize.
    destruct p; try inversion Pp.
    destruct (zlt 0 n).
    - assert (pointer_range_overlap (Vptr b i) n (Vptr b i) n); [| tauto].
      apply pointer_range_overlap_refl; simpl; try tauto; omega.
    - change memory_block with mapsto_memory_block.memory_block.
      unfold mapsto_memory_block.memory_block.
      rewrite nat_of_Z_neg by omega.
      simpl.
      change (predicates_hered.andp
        (predicates_hered.prop (Int.unsigned i + n <= Int.modulus))
        predicates_sl.emp) with (!! (Int.unsigned i + n <= Int.modulus) && emp)%logic.
      apply andp_left2; auto.
  + intros [p1 n1] [p2 n2] _ _ ?.
    apply mapsto_memory_block.memory_block_overlap; auto.
    simpl in H.
    destruct (pointer_range_overlap_dec p1 n1 p2 n2); [auto | congruence].
  + intros [p1 n1] [p2 n2] ?.
    simpl in H.
    unfold mapsto_.
    rewrite !exp_unit.
    destruct (pointer_range_overlap_dec p1 n1 p2 n2); [congruence |].
    destruct (pointer_range_overlap_dec p1 n1 p2 n2); [tauto |].
    apply disj_memory_block; auto.
Defined.

End MemoryBlock.
End MemoryBlock.


