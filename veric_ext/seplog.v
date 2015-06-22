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

Lemma exp_mapsto_precise: forall sh t p, precise (EX v: val, mapsto sh t p v).
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

Lemma BV_sizeof_sizeof: forall env t m,
  access_mode t = By_value m -> BV_sizeof t = sizeof env t.
Proof.
  intros.
  erewrite BV_sizeof_size_chunk by eauto.
  apply eq_sym, size_chunk_sizeof; auto.
Qed.

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
  + erewrite !size_chunk_sizeof in H by eauto.
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
    erewrite !size_chunk_sizeof in H1 by eauto.
    apply address_mapsto_conflict; auto.
Qed.

Lemma pointer_range_overlap_dec: forall p1 n1 p2 n2, {pointer_range_overlap p1 n1 p2 n2} + {~ pointer_range_overlap p1 n1 p2 n2}.
Proof.
  unfold pointer_range_overlap.
  intros.
  destruct p1;
  try solve
   [right;
    intros [[? ?] [[? ?] [HH [_ _]]]];
    inversion HH].
  destruct p2;
  try solve
   [right;
    intros [[? ?] [[? ?] [_ [HH _]]]];
    inversion HH].
  destruct (zlt 0 n1); [| right; intros [[? ?] [[? ?] [_ [_ HH]]]]; apply range_overlap_non_zero in HH; omega].
  destruct (zlt 0 n2); [| right; intros [[? ?] [[? ?] [_ [_ HH]]]]; apply range_overlap_non_zero in HH; omega].
  destruct (Clight_lemmas.block_eq_dec b b0).
  + subst b0.
    unfold val2adr.
    forget (Int.unsigned i) as i1; 
    forget (Int.unsigned i0) as i2;
    clear i i0.
    destruct (range_dec i1 i2 (i1 + n1)); [| destruct (range_dec i2 i1 (i2 + n2))].
    - left.
      exists (b, i1), (b, i2); repeat split; auto.
      apply range_overlap_spec; try omega.
      left; simpl; auto.
    - left.
      exists (b, i1), (b, i2); repeat split; auto.
      apply range_overlap_spec; try omega.
      right; simpl; auto.
    - right.
      intros [[? ?] [[? ?] [? [? HH]]]].
      inversion H; inversion H0; subst.
      apply range_overlap_spec in HH; [| omega | omega].
      simpl in HH; omega.
  + right.
    intros [[? ?] [[? ?] [? [? HH]]]].
    simpl in H, H0.
    inversion H; inversion H0; subst.
    apply range_overlap_spec in HH; [| omega | omega].
    simpl in HH.
    pose proof @eq_sym _ b0 b.
    tauto.
Qed.    

Lemma pointer_range_overlap_refl: forall p n1 n2,
  isptr p ->
  n1 > 0 -> 
  n2 > 0 ->
  pointer_range_overlap p n1 p n2.
Proof.
  intros.
  destruct p; try inversion H.
  exists (b, Int.unsigned i), (b, Int.unsigned i).
  repeat split; auto.
  apply range_overlap_spec; auto.
  left.
  simpl.
  split; auto; omega.
Qed.

Lemma pointer_range_overlap_comm: forall p1 n1 p2 n2,
  pointer_range_overlap p1 n1 p2 n2 <->
  pointer_range_overlap p2 n2 p1 n1.
Proof.
  cut (forall p1 n1 p2 n2,
         pointer_range_overlap p1 n1 p2 n2 ->
         pointer_range_overlap p2 n2 p1 n1).
  Focus 1. {
    intros.
    pose proof H p1 n1 p2 n2.
    pose proof H p2 n2 p1 n1.
    tauto.
  } Unfocus.
  unfold pointer_range_overlap.
  intros.
  destruct H as [l [l' [? [? ?]]]].
  exists l', l.
  repeat split; auto.
  apply range_overlap_comm.
  auto.
Qed.

Lemma pointer_range_overlap_non_zero: forall p1 n1 p2 n2,
  pointer_range_overlap p1 n1 p2 n2 -> n1 > 0 /\ n2 > 0.
Proof.
  intros.
  destruct H as [? [? [? [? ?]]]].
  eapply range_overlap_non_zero; eauto.
Qed.

Lemma pointer_range_overlap_isptr: forall p1 n1 p2 n2,
  pointer_range_overlap p1 n1 p2 n2 -> isptr p1 /\ isptr p2.
Proof.
  intros.
  destruct H as [? [? [? [? ?]]]].
  destruct p1, p2; try solve [inversion H | inversion H0].
  simpl; auto.
Qed.

Lemma BV_sizeof_pos: forall t m, access_mode t = By_value m -> BV_sizeof t > 0.
Proof.
  intros.
  erewrite BV_sizeof_size_chunk by eauto.
  apply size_chunk_pos.
Qed.

Lemma pointer_range_overlap_BV_sizeof: forall env p1 p2 t1 t2,
  pointer_range_overlap p1 (BV_sizeof t1) p2 (BV_sizeof t2) ->
  pointer_range_overlap p1 (sizeof env t1) p2 (sizeof env t2).
Proof.
  intros.
  pose proof pointer_range_overlap_non_zero _ _ _ _ H.
  unfold BV_sizeof in H0.
  destruct (access_mode t1) eqn:?H, (access_mode t2) eqn:?H; try omega.
  erewrite !BV_sizeof_sizeof in H by eauto.
  eauto.
Qed.

Lemma pointer_range_overlap_sizeof: forall sh env p1 p2 t1 t2,
  pointer_range_overlap p1 (sizeof env t1) p2 (sizeof env t2) ->
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
  apply VALspec_range_precise.
Qed.

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
  apply disj_VALspec_range.
  intro; apply H.
  exists (b, Int.unsigned i), (b0, Int.unsigned i0); auto.
  repeat split; auto.
  pose proof range_overlap_non_zero _ _ _ _ H2.
  destruct (zlt 0 n1); [| rewrite (nat_of_Z_neg n1) in H3 by omega; simpl in H3; omega].
  destruct (zlt 0 n2); [| rewrite (nat_of_Z_neg n2) in H3 by omega; simpl in H3; omega].
  rewrite !Coqlib.nat_of_Z_eq in H2 by omega.
  auto.
Qed.

Lemma memory_block_conflict: forall sh p1 n1 p2 n2, pointer_range_overlap p1 n1 p2 n2 -> memory_block sh n1 p1 * memory_block sh n2 p2 |-- FF.
Proof.
  intros.
  unfold memory_block.
  destruct p1; try solve [rewrite FF_sepcon; auto].
  destruct p2; try solve [rewrite normalize.sepcon_FF; auto].
  rewrite sepcon_andp_prop1.
  rewrite sepcon_andp_prop2.
  apply normalize.derives_extract_prop; intros.
  apply normalize.derives_extract_prop; intros.
  rewrite memory_block'_eq; [| pose proof Int.unsigned_range i; omega | apply Clight_lemmas.Nat2Z_add_le; auto].
  rewrite memory_block'_eq; [| pose proof Int.unsigned_range i0; omega | apply Clight_lemmas.Nat2Z_add_le; auto].
  unfold memory_block'_alt.
  apply VALspec_range_conflict.
  pose proof pointer_range_overlap_non_zero _ _ _ _ H.
  rewrite !Coqlib.nat_of_Z_eq by omega.
  destruct H as [[? ?] [[? ?] [? [? ?]]]].
  inversion H; inversion H3.
  subst.
  auto.
Qed.
