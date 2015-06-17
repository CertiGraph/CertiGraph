Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.

Require Export veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.slice.
Require Import veric.res_predicates.
Require Import veric.tycontext.
Require Import veric.expr.
Require Import VST.veric.seplog.

Require Import VST.msl.msl_standard.
Require Import VST.msl.alg_seplog.
Require Import RamifyCoq.msl_ext.alg_seplog.
Require Import RamifyCoq.veric_ext.res_predicates.

Local Open Scope pred.

Lemma exp_maspto_precise: forall sh t p, precise (EX v: val, mapsto sh t p v).
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); try apply @exp_FF_precise with (H := algPreciseSepLog _).
  destruct (type_is_volatile t); try apply @exp_FF_precise with (H := algPreciseSepLog _).
  destruct p; try apply @exp_FF_precise with (H := algPreciseSepLog _).
  apply derives_precise with (exp (fun v0 =>
          address_mapsto m v0 (Share.unrel Share.Lsh sh)
            (Share.unrel Share.Rsh sh) (b, Int.unsigned i))); [| apply address_mapsto__precise].
  apply exp_left; intro v.
  apply orp_left.
  + apply andp_left2, (exp_right v).
    auto.
  + apply andp_left2; auto.
Qed.

Definition pointer_range_overlap p n p' n' :=
  exists l l', val2adr p l /\ val2adr p' l' /\ range_overlap l n l' n'.

Lemma disj_mapsto_: forall sh env t1 t2 p1 p2,
  ~ pointer_range_overlap p1 (sizeof env t1) p2 (sizeof env t2) ->
  disjointed (EX v1: val, mapsto sh t1 p1 v1) (EX v2: val, mapsto sh t2 p2 v2).
Proof.
  pose proof (@exp_FF mpred val _) as EXP_FF.
  change (@seplog.exp _ _ val) with (@exp _ _ val) in EXP_FF.
  change seplog.FF with FF in EXP_FF.

  intros.
  unfold mapsto.
  destruct (access_mode t1) eqn:AM1; try (rewrite EXP_FF; apply (@FF_disj _ _ _ _ _ (algDisjointedSepLog _))).
  destruct (access_mode t2) eqn:AM2; try (rewrite EXP_FF; apply (@disj_FF _ _ _ _ _ (algDisjointedSepLog _))).
  destruct (type_is_volatile t1); try (rewrite EXP_FF; apply (@FF_disj _ _ _ _ _ (algDisjointedSepLog _))).
  destruct (type_is_volatile t2); try (rewrite EXP_FF; apply (@disj_FF _ _ _ _ _ (algDisjointedSepLog _))).
  destruct p1; try (rewrite EXP_FF; apply (@FF_disj _ _ _ _ _ (algDisjointedSepLog _))).
  destruct p2; try (rewrite EXP_FF; apply (@disj_FF _ _ _ _ _ (algDisjointedSepLog _))).
  eapply disj_derives; [| | apply disj_address_mapsto_]; simpl.
  + apply exp_left; intro v.
    apply orp_left.
    - apply andp_left2, (exp_right v).
      auto.
    - apply andp_left2; auto.
  + apply exp_left; intro v.
    apply orp_left.
    - apply andp_left2, (exp_right v).
      auto.
    - apply andp_left2; auto.
  + erewrite !Clight_lemmas.size_chunk_sizeof in H by eauto.
    intro.
    apply H.
    exists (b, Int.unsigned i), (b0, Int.unsigned i0).
    repeat split; auto.
Qed.

Lemma mapsto_conflict: forall sh env t1 t2 p1 p2 v1 v2,
  pointer_range_overlap p1 (sizeof env t1) p2 (sizeof env t2) ->
  mapsto sh t1 p1 v1 * mapsto sh t2 p2 v2 |-- FF.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t1) eqn:AM1; try (rewrite FF_sepcon; auto).
  destruct (access_mode t2) eqn:AM2; try (rewrite normalize.sepcon_FF; auto).
  destruct (type_is_volatile t1); try (rewrite FF_sepcon; auto).
  destruct (type_is_volatile t2); try (rewrite normalize.sepcon_FF; auto).
  destruct p1; try (rewrite FF_sepcon; auto).
  destruct p2; try (rewrite normalize.sepcon_FF; auto).
  apply derives_trans with ((EX  v : val,
        address_mapsto m v (Share.unrel Share.Lsh sh)
          (Share.unrel Share.Rsh sh) (b, Int.unsigned i)) *
    (EX  v : val,
        address_mapsto m0 v (Share.unrel Share.Lsh sh)
          (Share.unrel Share.Rsh sh) (b0, Int.unsigned i0))).
  + apply sepcon_derives.
    - apply orp_left.
      * apply andp_left2, (exp_right v1).
        auto.
      * apply andp_left2; auto.
    - apply orp_left.
      * apply andp_left2, (exp_right v2).
        auto.
      * apply andp_left2; auto.
  + clear v1 v2.
    rewrite exp_sepcon1.
    apply exp_left; intro v1.
    rewrite exp_sepcon2.
    apply exp_left; intro v2.
    destruct H as [? [? [? [? ?]]]].
    inversion H; subst.
    inversion H0; subst.
    erewrite !Clight_lemmas.size_chunk_sizeof in H1 by eauto.
    apply address_mapsto_conflict; auto.
Qed.
