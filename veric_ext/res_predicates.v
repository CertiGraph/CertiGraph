Require Import VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.rmaps_lemmas.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.slice.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr.
Require Import VST.veric.res_predicates.

Require Import RamifyCoq.msl_ext.precise.
Require Import RamifyCoq.msl_ext.overlapping.

Lemma disj_VALspec_range: forall rsh l1 n1 l2 n2, ~ range_overlap l1 n1 l2 n2 ->
  disjointed (VALspec_range n1 rsh l1) (VALspec_range n2 rsh l2).
Proof.
  intros.
  unfold VALspec_range, disjointed.
  intros.
  simpl in H2, H3. destruct H2, H3.
  assert (identity h2).
  1: {
    apply all_resource_at_identity.
    intros l; specialize (H2 l); specialize (H3 l).
    assert (identity (h12 @ l) \/ identity (h23 @ l)).
    1: {
      destruct (adr_range_dec l1 n1 l), (adr_range_dec l2 n2 l); try tauto.
      specialize (H (ex_intro _ _ (conj a a0))).
      tauto.
    }
    destruct H6; [clear - H0 H6 | clear - H1 H6].
    + pose proof (resource_at_join _ _ _ l H0).
      apply join_comm in H.
      apply split_identity in H; auto.
    + pose proof (resource_at_join _ _ _ l H1).
      apply split_identity in H; auto.
    + clear H2 H3. apply ghost_of_join in H1.
      apply split_identity in H1; auto.
  }
  split; auto.
  pose proof H6 _ _ H1.
  pose proof H6 _ _ (join_comm H0).
  subst h23 h12.
  apply resource_at_joins2.
  + apply join_level in H0.
    apply join_level in H1.
    omega.
  + intros l; specialize (H2 l); specialize (H3 l).
    pose proof resource_at_join _ _ _ l H0.
    pose proof resource_at_join _ _ _ l H1.
    clear - H H2 H3 H7 H8.
    apply join_comm in H8.
    destruct (adr_range_dec l1 n1 l); [| exists (h3 @ l); apply H2 in H7; rewrite <- H7; auto].
    destruct (adr_range_dec l2 n2 l); [| exists (h1 @ l); apply H3 in H8; rewrite <- H8; auto].
    specialize (H (ex_intro _ _ (conj a a0))).
    tauto.
  + exists (compcert_rmaps.R.ghost_of h3).
    assert (ghost_of h1 = ghost_of h3). {
      pose proof (ghost_core (ghost_of h1)).
      rewrite <- (ghost_core (ghost_of h3)),
      <- (identity_core H4), <- (identity_core H5) in H7. assumption.
    } rewrite H7. apply core_self_join. apply identity_core; auto.
Qed.

Lemma disj_nonlock_permission_bytes: forall sh l1 n1 l2 n2, ~ range_overlap l1 n1 l2 n2 ->
  disjointed (nonlock_permission_bytes sh l1 n1) (nonlock_permission_bytes sh l2 n2).
Proof.
  intros.
  unfold nonlock_permission_bytes, disjointed; intros.
  simpl in H2, H3. destruct H2, H3.
  assert (identity h2).
  1: {
    apply all_resource_at_identity.
    intros l; specialize (H2 l); specialize (H3 l).
    assert (identity (h12 @ l) \/ identity (h23 @ l)).
    1: {
      destruct (adr_range_dec l1 n1 l), (adr_range_dec l2 n2 l); try tauto.
      specialize (H (ex_intro _ _ (conj a a0))).
      tauto.
    }
    destruct H6; [clear - H0 H6 | clear - H1 H6].
    + pose proof (resource_at_join _ _ _ l H0).
      apply join_comm in H.
      apply split_identity in H; auto.
    + pose proof (resource_at_join _ _ _ l H1).
      apply split_identity in H; auto.
    + clear H2 H3. apply ghost_of_join in H1.
      apply split_identity in H1; auto.
  }
  split; auto.
  pose proof H6 _ _ H1.
  pose proof H6 _ _ (join_comm H0).
  subst h23 h12.
  apply resource_at_joins2.
  + apply join_level in H0.
    apply join_level in H1.
    omega.
  + intros l; specialize (H2 l); specialize (H3 l).
    pose proof resource_at_join _ _ _ l H0.
    pose proof resource_at_join _ _ _ l H1.
    clear - H H2 H3 H7 H8.
    apply join_comm in H8.
    destruct (adr_range_dec l1 n1 l); [| exists (h3 @ l); apply H2 in H7; rewrite <- H7; auto].
    destruct (adr_range_dec l2 n2 l); [| exists (h1 @ l); apply H3 in H8; rewrite <- H8; auto].
    specialize (H (ex_intro _ _ (conj a a0))).
    tauto.
  + exists (compcert_rmaps.R.ghost_of h3).
    assert (ghost_of h1 = ghost_of h3). {
      pose proof (ghost_core (ghost_of h1)).
      rewrite <- (ghost_core (ghost_of h3)),
      <- (identity_core H4), <- (identity_core H5) in H7. assumption.
    } rewrite H7. apply core_self_join. apply identity_core; auto.
Qed.

Lemma address_mapsto__precise: forall ch sh l, precise (EX v: val, address_mapsto ch v sh l).
Proof.
  intros.
  eapply derives_precise.
  + apply exp_left; intro v.
    apply address_mapsto_VALspec_range.
  + apply VALspec_range_precise.
Qed.

Lemma disj_address_mapsto_: forall sh l1 ch1 l2 ch2,
  ~ range_overlap l1 (size_chunk ch1) l2 (size_chunk ch2) ->
  disjointed (EX v1: val, address_mapsto ch1 v1 sh l1) (EX v2: val, address_mapsto ch2 v2 sh l2).
Proof.
  intros.
  eapply disj_derives; [| | apply disj_VALspec_range; eauto];
  apply exp_left; intro; apply address_mapsto_VALspec_range.
Qed.
