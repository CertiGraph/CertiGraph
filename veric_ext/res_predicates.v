Require Import VST.veric.base.
Require Import VST.msl.rmaps.
Require Import VST.msl.rmaps_lemmas.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.slice.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr.
Require Import VST.veric.res_predicates.

Require Import RamifyCoq.msl_ext.precise.
Require Import RamifyCoq.msl_ext.overlapping.

Lemma disj_VALspec_range: forall rsh sh l1 n1 l2 n2, ~ range_overlap l1 n1 l2 n2 ->
  disjointed (VALspec_range n1 rsh sh l1) (VALspec_range n2 rsh sh l2).
Proof.
  intros.
  unfold VALspec_range, disjointed.
  intros.
  simpl in H2, H3.
  assert (identity h2).
  Focus 1. {
    apply all_resource_at_identity.
    intros l; specialize (H2 l); specialize (H3 l).
    assert (identity (h12 @ l) \/ identity (h23 @ l)).
    Focus 1. {
      destruct (adr_range_dec l1 n1 l), (adr_range_dec l2 n2 l); try tauto.
      specialize (H (ex_intro _ _ (conj a a0))).
      tauto.
    } Unfocus.
    destruct H4; [clear - H0 H4 | clear - H1 H4].
    + pose proof (resource_at_join _ _ _ l H0).
      apply join_comm in H.
      apply split_identity in H; auto.
    + pose proof (resource_at_join _ _ _ l H1).
      apply split_identity in H; auto.
  } Unfocus.
  split; auto.
  pose proof H4 _ _ H1.
  pose proof H4 _ _ (join_comm H0).
  subst h23 h12.
  apply resource_at_joins2.
  + apply join_level in H0.
    apply join_level in H1.
    omega.
  + intros l; specialize (H2 l); specialize (H3 l).
    pose proof resource_at_join _ _ _ l H0.
    pose proof resource_at_join _ _ _ l H1.
    clear - H H2 H3 H5 H6.
    apply join_comm in H6.
    destruct (adr_range_dec l1 n1 l); [| exists (h3 @ l); apply H2 in H5; rewrite <- H5; auto].
    destruct (adr_range_dec l2 n2 l); [| exists (h1 @ l); apply H3 in H6; rewrite <- H6; auto].
    specialize (H (ex_intro _ _ (conj a a0))).
    tauto.
Qed.

Lemma address_mapsto__precise: forall ch rsh sh l, precise (EX v: val, address_mapsto ch v rsh sh l).
Proof.
  intros.
  eapply derives_precise.
  + apply exp_left; intro v.
    apply address_mapsto_VALspec_range.
  + apply VALspec_range_precise.
Qed.

Lemma disj_address_mapsto_: forall rsh sh l1 ch1 l2 ch2,
  ~ range_overlap l1 (size_chunk ch1) l2 (size_chunk ch2) ->
  disjointed (EX v1: val, address_mapsto ch1 v1 rsh sh l1) (EX v2: val, address_mapsto ch2 v2 rsh sh l2).
Proof.
  intros.
  eapply disj_derives; [| | apply disj_VALspec_range; eauto];
  apply exp_left; intro; apply address_mapsto_VALspec_range.
Qed.

Lemma range_overlap_spec: forall l1 n1 l2 n2,
  n1 > 0 ->
  n2 > 0 ->
  (range_overlap l1 n1 l2 n2 <-> adr_range l1 n1 l2 \/ adr_range l2 n2 l1).
Proof.
  intros.
  unfold range_overlap, adr_range.
  destruct l1, l2.
  split; intros.
  + destruct H1 as [[? ?] [[? ?] [? ?]]].
    subst.
    destruct (zle z z0); [left | right].
    - split; auto.
      omega.
    - split; auto.
      omega.
  + destruct H1 as [[? ?] | [? ?]].
    - exists (b0, z0). repeat split; auto; omega.
    - exists (b, z). repeat split; auto; omega.
Qed.

Lemma range_overlap_comm: forall l1 n1 l2 n2, range_overlap l1 n1 l2 n2 -> range_overlap l2 n2 l1 n1.
Proof.
  unfold range_overlap.
  intros.
  destruct H as [l ?].
  exists l.
  tauto.
Qed.

Lemma range_overlap_non_zero: forall l1 n1 l2 n2, range_overlap l1 n1 l2 n2 -> n1 > 0 /\ n2 > 0.
Proof.
  unfold range_overlap.
  intros.
  destruct H as [l [? ?]].
  apply adr_range_non_zero in H.
  apply adr_range_non_zero in H0.
  auto.
Qed.

Lemma VALspec_range_conflict: forall rsh sh l1 n1 l2 n2,
  range_overlap l1 n1 l2 n2 ->
  VALspec_range n1 rsh sh l1 * VALspec_range n2 rsh sh l2 |-- FF.
Proof.
  intros.
  pose proof range_overlap_non_zero _ _ _ _ H.
  apply range_overlap_spec in H; try tauto.
  destruct H.
  + apply VALspec_range_overlap; tauto.
  + rewrite sepcon_comm.
    apply VALspec_range_overlap; tauto.
Qed.

Lemma address_mapsto_conflict: forall rsh sh l1 ch1 v1 l2 ch2 v2,
  range_overlap l1 (size_chunk ch1) l2 (size_chunk ch2) ->
  address_mapsto ch1 v1 rsh sh l1 * address_mapsto ch2 v2 rsh sh l2 |-- FF.
Proof.
  intros.
  apply range_overlap_spec in H; try apply size_chunk_pos.
  destruct H.
  + apply address_mapsto_overlap; auto.
  + rewrite sepcon_comm.
    apply address_mapsto_overlap; auto.
Qed.
