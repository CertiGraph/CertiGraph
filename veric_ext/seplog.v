Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.

Require Export VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.rmaps_lemmas.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.slice.
Require Import VST.veric.res_predicates.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr.
Require Import VST.veric.address_conflict.
Require Import VST.veric.seplog.

Require Import VST.msl.msl_standard.
Require Import VST.msl.alg_seplog.
Require Import RamifyCoq.msl_ext.alg_seplog.
Require Import RamifyCoq.veric_ext.res_predicates.

Local Open Scope pred.

(*

Lemma exp_mapsto_precise: forall sh t p, precise (EX v: val, mapsto sh t p v).
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); try apply @exp_FF_precise with (H := algPreciseSepLog _).
  destruct (type_is_volatile t); try apply @exp_FF_precise with (H := algPreciseSepLog _).
  destruct p; try apply @exp_FF_precise with (H := algPreciseSepLog _).
  if_tac.
  + apply derives_precise with (exp (fun v0 =>
            address_mapsto m v0 sh (b, Ptrofs.unsigned i))); [| apply address_mapsto__precise].
    apply exp_left; intro v.
    apply orp_left.
    - apply andp_left2, (exp_right v). auto.
    - apply andp_left2; auto.
  + apply derives_precise with (nonlock_permission_bytes sh (b, Ptrofs.unsigned i) (size_chunk m)).
    - apply exp_left; intro. apply andp_left2. auto.
    - apply nonlock_permission_bytes_precise.
Qed.

 *)

Definition BV_sizeof t :=
  match access_mode t with
  | By_value m => size_chunk m
  | _ => 0
  end.

Lemma BV_sizeof_size_chunk: forall t m,
  access_mode t = By_value m -> BV_sizeof t = size_chunk m.
Proof.
  intros.
  unfold BV_sizeof.
  rewrite H.
  reflexivity.
Qed.

Lemma BV_sizeof_sizeof: forall {cs: composite_env} t m,
  access_mode t = By_value m -> BV_sizeof t = sizeof t.
Proof.
  intros.
  erewrite BV_sizeof_size_chunk by eauto.
  apply eq_sym, size_chunk_sizeof; auto.
Qed.

(*
Lemma disj_mapsto_: forall {cs: composite_env} sh t1 t2 p1 p2,
  ~ pointer_range_overlap p1 (sizeof t1) p2 (sizeof t2) ->
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
  if_tac.
  + eapply disj_derives; [| | apply disj_address_mapsto_]; simpl.
    - apply exp_left; intro v.
      apply orp_left.
      * apply andp_left2, (exp_right v).
        auto.
      * apply andp_left2; auto.
    - apply exp_left; intro v.
      apply orp_left.
      * apply andp_left2, (exp_right v).
        auto.
      * apply andp_left2; auto.
    - erewrite !size_chunk_sizeof in H by eauto.
      intro.
      apply H.
      exists (b, Int.unsigned i), (b0, Int.unsigned i0).
      repeat split; auto.
  + eapply disj_derives; [| | apply disj_nonlock_permission_bytes]; simpl.
    - apply exp_left; intro; apply andp_left2; apply derives_refl.
    - apply exp_left; intro; apply andp_left2; apply derives_refl.
    - erewrite !size_chunk_sizeof in H by eauto.
      intro.
      apply H.
      exists (b, Int.unsigned i), (b0, Int.unsigned i0).
      repeat split; auto.
Qed.

 *)

Lemma BV_sizeof_pos: forall t m, access_mode t = By_value m -> BV_sizeof t > 0.
Proof.
  intros.
  erewrite BV_sizeof_size_chunk by eauto.
  apply size_chunk_pos.
Qed.

Lemma pointer_range_overlap_BV_sizeof: forall {cs: composite_env} p1 p2 t1 t2,
  pointer_range_overlap p1 (BV_sizeof t1) p2 (BV_sizeof t2) ->
  pointer_range_overlap p1 (sizeof t1) p2 (sizeof t2).
Proof.
  intros.
  pose proof pointer_range_overlap_non_zero _ _ _ _ H.
  unfold BV_sizeof in H0.
  destruct (access_mode t1) eqn:?H, (access_mode t2) eqn:?H; try omega.
  erewrite !BV_sizeof_sizeof in H by eauto.
  eauto.
Qed.

Lemma pointer_range_overlap_sizeof: forall {cs: composite_env} sh p1 p2 t1 t2,
  pointer_range_overlap p1 (sizeof t1) p2 (sizeof t2) ->
  pointer_range_overlap p1 (BV_sizeof t1) p2 (BV_sizeof t2) \/
  (EX v: val, mapsto sh t1 p1 v |-- FF) \/
  (EX v: val, mapsto sh t2 p2 v |-- FF).
Proof.
  pose proof (@exp_FF mpred val _) as EXP_FF.
  change (@seplog.exp _ _ val) with (@exp _ _ val) in EXP_FF.
  change seplog.FF with FF in EXP_FF.

  intros.
  unfold BV_sizeof.
  unfold mapsto.
  destruct (access_mode t1) eqn:?H; try solve [right; left; rewrite EXP_FF; auto].
  destruct (access_mode t2) eqn:?H; try solve [right; right; rewrite EXP_FF; auto].
  left.
  erewrite !size_chunk_sizeof in H by eauto.
  auto.
Qed.

(*
Lemma memory_block_precise: forall sh p n, precise (memory_block sh n p).
Proof.
  intros.
  unfold memory_block.
  destruct p; try apply (@FF_precise _ _ _ (algPreciseSepLog _)).
Opaque Z.le.
  apply (@precise_prop_andp _ _ _ (algPreciseSepLog _)).
Transparent Z.le. (* A bug of Coq here ? *)
  1: destruct (zle (Int.unsigned i + n) (Int.modulus)); [left | right]; auto.
  intros.
  rewrite memory_block'_eq; [| pose proof Int.unsigned_range i; omega | apply Clight_lemmas.Nat2Z_add_le; auto].
  simpl.
  unfold memory_block'_alt.
  if_tac.
  + apply VALspec_range_precise.
  + apply nonlock_permission_bytes_precise.
Qed.

 *)

(*

Lemma disj_memory_block: forall sh p1 n1 p2 n2, ~ pointer_range_overlap p1 n1 p2 n2 -> disjointed (memory_block sh n1 p1) (memory_block sh n2 p2).
Proof.
  intros.
  unfold memory_block.
  destruct p1; try apply (@FF_disj _ _ _ _ _ (algDisjointedSepLog _)).
  destruct p2; try apply (@disj_FF _ _ _ _ _ (algDisjointedSepLog _)).
Opaque Z.le.
  apply (@disj_prop_andp_left _ _ _ _ _ (algDisjointedSepLog _)); [| intros].
Transparent Z.le. (* A bug of Coq here ? *)
  1: destruct (zle (Int.unsigned i + n1) (Int.modulus)); [left | right]; auto.
Opaque Z.le.
  apply (@disj_prop_andp_right _ _ _ _ _ (algDisjointedSepLog _)); [| intros].
Transparent Z.le. (* A bug of Coq here ? *)
  1: destruct (zle (Int.unsigned i0 + n2) (Int.modulus)); [left | right]; auto.
  rewrite memory_block'_eq; [| pose proof Int.unsigned_range i; omega | apply Clight_lemmas.Nat2Z_add_le; auto].
  rewrite memory_block'_eq; [| pose proof Int.unsigned_range i0; omega | apply Clight_lemmas.Nat2Z_add_le; auto].
  unfold memory_block'_alt.
  if_tac.
  + clear H2.
    apply disj_VALspec_range.
    intro; apply H.
    exists (b, Int.unsigned i), (b0, Int.unsigned i0); auto.
    repeat split; auto.
    pose proof range_overlap_non_zero _ _ _ _ H2.
    destruct (zlt 0 n1); [| rewrite (nat_of_Z_neg n1) in H3 by omega; simpl in H3; omega].
    destruct (zlt 0 n2); [| rewrite (nat_of_Z_neg n2) in H3 by omega; simpl in H3; omega].
    rewrite !Coqlib.nat_of_Z_eq in H2 by omega.
    auto.
  + clear H2.
    apply disj_nonlock_permission_bytes.
    intro; apply H.
    exists (b, Int.unsigned i), (b0, Int.unsigned i0); auto.
    repeat split; auto.
    pose proof range_overlap_non_zero _ _ _ _ H2.
    destruct (zlt 0 n1); [| rewrite (nat_of_Z_neg n1) in H3 by omega; simpl in H3; omega].
    destruct (zlt 0 n2); [| rewrite (nat_of_Z_neg n2) in H3 by omega; simpl in H3; omega].
    rewrite !Coqlib.nat_of_Z_eq in H2 by omega.
    auto.
Qed.

*)