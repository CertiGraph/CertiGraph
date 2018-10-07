Require Import RamifyCoq.msl_ext.ramify_tactics.
Require Import RamifyCoq.msl_ext.msl_ext.
Require Import VST.msl.msl_direct.
Require Import RamifyCoq.msl_ext.sepalg.

Local Open Scope pred.

Definition ocon {A: Type}{JA: Join A} (p q:pred A) : pred A :=
  fun h:A => exists h1 h2 h3 h12 h23, join h1 h2 h12 /\ join h2 h3 h23 /\ join h12 h3 h /\ p h12 /\ q h23.

Notation "P ⊗ Q" := (ocon P Q) (at level 40, left associativity) : pred.

Program Definition owand {A: Type}{JA: Join A} (p q:pred A) : pred A :=
  fun h23:A => forall h1 h2 h3 h12 h123, join h1 h2 h12 -> join h2 h3 h23 -> join h12 h3 h123 -> p h12 -> q h123.

Lemma ocon_emp {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}: forall P: pred A, P ⊗ emp = P.
Proof.
  intros; apply pred_ext; hnf; intros; simpl in *; intros.
  destruct_ocon H h; try_join h2 h3 h23'; equate_join h23 h23'.
  rewrite (H3 _ _ (join_comm H5)) in H.
  generalize (join_positivity H H1); intro; rewrite H4; trivial.
  exists a, (core a), (core a), a, (core a).
  generalize (core_unit a); intro.
  unfold unit_for in H0.
  repeat split; auto.
  apply core_duplicable.
  apply core_identity.
Qed.

Lemma ocon_TT {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}: forall P: pred A, P ⊗ TT = P * TT.
Proof.
  intros; apply pred_ext; hnf; intros; simpl in *; intros.
  + destruct_ocon H h.
    exists h12, h3; auto.
  + destruct H as [? [? [? [? ?]]]].
    exists x, (core x), x0, x, x0.
    repeat split; auto.
    - apply join_comm, core_unit.
    - apply join_core2 in H.
      rewrite H.
      apply core_unit.
Qed.

Lemma andp_ocon {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}: forall P Q, P && Q |-- P ⊗ Q.
Proof.
  intros.
  hnf; intros; simpl in *; intros.
  destruct H.
  remember (core a) as u.
  exists u, a, u, a, a.
  repeat split; try rewrite Hequ; auto;
  try apply core_unit;
  apply join_comm; apply core_unit.
Qed.

Lemma ocon_andp_prop {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}: forall P Q R, P ⊗ (!!Q && R) = !!Q && (P ⊗ R).
Proof.
  intros; apply pred_ext; hnf; intros; simpl in *.
  + destruct H as [h1 [h2 [h3 [h12 [h23 [? [? [? [? [? ?]]]]]]]]]].
    split; auto. exists h1, h2, h3, h12, h23. intuition.
  + destruct H as [? [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]]].
    exists h1, h2, h3, h12, h23. unfold andp. intuition.
Qed.

Lemma sepcon_ocon {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}: forall P Q, P * Q |-- P ⊗ Q.
Proof.
  intros; hnf; intros; simpl in *; intros.
  destruct H as [y [z [? [? ?]]]].
  remember (core z) as u.
  exists y, u, z, y, z.
  repeat split; auto.
  generalize (join_core H); intro.
  generalize (join_core (join_comm H)); intro.
  rewrite Hequ.
  replace (core z) with (core y).
  apply join_comm, core_unit.
  rewrite H2, H3; trivial.
  rewrite Hequ. apply core_unit.
Qed.

Lemma ocon_sep_true {A}{JA: Join A}{PA: Perm_alg A}: forall P Q, P ⊗ Q |-- P * TT.
Proof.
  intros; hnf; intros; simpl in *; intros.
  destruct_ocon H h.
  exists h12, h3.
  repeat split; auto.
Qed.

Lemma ocon_wand {A}{JA: Join A}{PA: Perm_alg A}: forall P Q, P ⊗ Q = EX R : pred A, (R -* P) * (R -* Q) * R.
Proof.
  intros; apply pred_ext; hnf; intros; simpl in *.
  destruct_ocon H h; try_join h2 h3 h23'; equate_join h23 h23'; try_join h1 h3 h13.
  exists (exactly h2), h13, h2; repeat split; simpl; auto; exists h1, h3; repeat split; auto.
  intros h2' h12'; intros; rewrite H8 in *; equate_join h12 h12'; trivial.
  intros h2' h23'; intros; rewrite H8 in *; equate_join h23 h23'; trivial.
  (* another direction *)
  destruct H as [R [w13 [w2 [? [[w1 [w3 [? [HP HQ]]]] HR]]]]].
  try_join w2 w3 w23; try_join w1 w2 w12.
  exists w1, w2, w3, w12, w23; repeat split; auto.
  apply (HP w2 w12). auto. trivial. apply (HQ w2 w23); auto.
Qed.

Lemma ocon_comm {A}{JA: Join A}{PA: Perm_alg A}: forall P Q, P ⊗ Q = Q ⊗ P.
Proof.
  intros; apply pred_ext; hnf; intros; simpl in *; intros;
  destruct_ocon H h; exists h3, h2, h1, h23, h12;
  repeat split; auto; try_join h2 h3 h23'; equate_join h23 h23'; auto.
Qed.

Lemma cross_rev {A}{JA: Join A}{PA: Perm_alg A}: forall h1 h2 h3 h4
  h12 h34 h13 h24 h1234, join h1 h2 h12 -> join h1 h3 h13 -> join h3 h4
  h34 -> join h2 h4 h24 -> join h12 h34 h1234 -> join h13 h24 h1234.
Proof.
  intros; try_join h2 h34 h234;
  try_join h2 h4 h24'; equate_join h24 h24';
  try_join h1 h3 h13'; equate_join h13 h13'; auto.
Qed.

Lemma ocon_assoc {A}{JA: Join A}{PA: Perm_alg A}{CA: Cross_alg A}:
  forall P Q R: pred A, P ⊗ Q ⊗ R = P ⊗ (Q ⊗ R).
Proof.
  intros; apply pred_ext; hnf; intros; simpl in *; intros.
  destruct H as [w124 [w567 [w3 [w124567 [w3567 [? [? [? [[w15 [w47 [w26 [w1457 [w2467 [? [? [? [? ?]]]]]]]]] ?]]]]]]]]].
  destruct (cross_split _ _ _ _ _ H H4) as [[[[w14 w2] w57] w6] [? [? [? ?]]]].
  destruct (cross_split _ _ _ _ _ H2 H10) as [[[[w1 w5] w4] w7] [? [? [? ?]]]].
  try_join w5 w47 w457; try_join w3 w26 w236; try_join w236 w457 w234567.
  exists w1, w457, w236, w1457, w234567; repeat split; auto.
  try_join w2 w4 w24; try_join w6 w7 w67; try_join w3 w5 w35.
  exists w24, w67, w35, w2467, w3567; repeat split; auto.
  apply (cross_rev w2 w6 w4 w7 w26 w47); auto. apply (cross_rev w47 w5 w26 w3 w457 w236); auto.
  (* another direction *)
  destruct H as [w1 [w457 [w236 [w1457 [w234567 [? [? [? [? [w24 [w67 [w35 [w2467 [w3567 [? [? [? [? ?]]]]]]]]]]]]]]]]]].
  destruct (cross_split _ _ _ _ _ H0 H5) as [[[[w47 w5] w26] w3] [? [? [? ?]]]].
  destruct (cross_split _ _ _ _ _ H3 H10) as [[[[w4 w2] w7] w6] [? [? [? ?]]]].
  try_join w26 w1457 w124567; try_join w5 w67 w567; try_join w5 w7 w57; try_join w1 w4 w14;
  try_join w14 w26 w1246; try_join w2 w14 w124.
  exists w124, w567, w3, w124567, w3567; repeat split; auto.
  apply join_comm; apply (cross_rev w6 w2 w57 w14 w26 w1457); auto.
  try_join_through w67 w5 w7 w57'; equate_join w57 w57'; auto.
  try_join w1 w5 w15; exists w15, w47, w26, w1457, w2467;
  repeat split; auto.
Qed.

Lemma ocon_derives {A} {JA: Join A}{PA: Perm_alg A}: forall p q p' q', (p |-- p') -> (q |-- q') -> (p ⊗ q |-- p' ⊗ q').
Proof.
  repeat (intros; hnf).
  simpl in H1.
  destruct_ocon H1 w.
  exists w1,w2,w3,w12,w23.
  repeat split; auto.
Qed.

Lemma owand_ocon_adjoint {A} {JA: Join A}{PA: Perm_alg A}: forall P Q R, ocon P Q |-- R <-> P |-- owand Q R.
Proof.
  intros.
  rewrite ocon_comm.
  unfold ocon, owand, derives.
  simpl.
  split; intros.
  + apply H.
    exists h1, h2, h3, h12, a.
    repeat split; auto.
  + destruct H0 as [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]].
    specialize (H h23 H4).
    specialize (H h1 h2 h3 h12 a).
    apply H; auto.
Qed.

Lemma ocon_contain {A} {JA: Join A} {PA: Perm_alg A} {SA: Sep_alg A}: forall P Q, Q |-- P * TT -> Q |-- ocon P Q.
Proof.
  unfold ocon, owand, derives; simpl; intros.
  destruct (H a H0) as [y [z [? [? ?]]]].
  exists (core y), y, z, y, a.
  repeat split; auto.
  apply core_unit.
Qed.

Lemma precise_ocon_contain {A} {JA: Join A} {PA: Perm_alg A} {SA: Sep_alg A} {CA: Canc_alg A} {DA: Disj_alg A} : forall P Q, precise P -> Q |-- P * TT -> Q = ocon P Q.
Proof.
  intros; apply pred_ext; [apply ocon_contain; auto |].
  unfold ocon, owand, derives in *; simpl in *.
  intros.
  destruct H1 as [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]].
  destruct (H0 _ H5) as [y [z [? [? ?]]]].
  try_join h2 h3 h23'. equate_join h23 h23'. assertSub y a HS1.
  equate_precise_direct y h12.
  try_join z h1 h3'. equate_canc h3 h3'.
  assert (identity h1).
  1: {
    try_join h1 h3 h_temp.
    assertSub h1 h3 H12.
    eapply join_sub_joins_identity; eauto.
  }
  apply join_comm in H4.
  apply H9 in H10; apply H9 in H4.
  subst.
  auto.
Qed.

Definition disjointed {A: Type} {JA: Join A} (P Q: pred A):=
  forall h1 h2 h3 h12 h23,
  join h1 h2 h12 -> join h2 h3 h23 -> P h12 -> Q h23 -> identity h2 /\ joins h1 h3.

Lemma ocon_sepcon {A: Type} {JA: Join A} {SA: Sep_alg A} {PA : Perm_alg A}:
  forall P Q, disjointed P Q -> ocon P Q |-- P * Q.
Proof.
  unfold ocon, sepcon, disjointed, derives; simpl.
  intros.
  destruct H0 as [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]].
  destruct (H h1 h2 h3 h12 h23 H0 H1 H3 H4) as [? ?].
  apply join_comm in H0.
  apply H5 in H0.
  apply H5 in H1.
  subst.
  exists h12, h23.
  auto.
Qed.

Lemma disj_emp {A: Type} {JA: Join A} {SA: Sep_alg A} {PA : Perm_alg A} {CA: Canc_alg A}: forall P, disjointed P emp.
Proof.
  intros.
  unfold disjointed. simpl; intros.
  pose proof split_identity _ _ H0 H2.
  pose proof split_identity _ _ (join_comm H0) H2.
  pose proof identities_unique H3 H4 (ex_intro _ h23 H0).
  subst.
  split; eauto.
Qed.

Lemma disj_comm {A: Type} {JA: Join A} {PA: Perm_alg A}: forall P Q, disjointed P Q -> disjointed Q P.
Proof.
  unfold disjointed; intros.
  specialize (H h3 h2 h1 h23 h12).
  do 2 (spec H; [apply join_comm; auto |]).
  do 2 (spec H; [auto |]).
  destruct H; split; auto.
  apply joins_comm; auto.
Qed.

Lemma disj_derives {A: Type} {JA: Join A} {PA: Perm_alg A}:
  forall P P' Q Q', P |-- P' -> Q |-- Q' -> disjointed P' Q' -> disjointed P Q.
Proof.
  unfold derives, disjointed.
  intros.
  apply H1 with h12 h23; auto.
Qed.

(**************************************************************************



          |------------------------------------------|
          |                                          | 
          |                                          | 
          |                                          | 
          |                     P                    | 
          |                                          | 
          |                                          | 
|---------|----------|-----------------------|-------|------------|
|         |          |                       |       |            |
|         |    p1    |         p2            |   p3  |            |
|         |          |                       |       |            |
|         |------------------------------------------|            |
|                    |                       |                    |
|                    |                       |                    |
|        r1          |          r2           |         r3         |
|                    |                       |                    |
|                    |                       |                    |
|                    |                       |                    |
|--------------------|-----------------------|--------------------|




**************************************************************************)

Lemma disj_ocon_right {A: Type} {JA: Join A} {SA: Sep_alg A} {PA : Perm_alg A} {CA: Canc_alg A} {CrA: Cross_alg A} {TA: Trip_alg A}:
  forall P Q R, disjointed P Q -> disjointed P R -> disjointed P (ocon Q R).
Proof.
  unfold ocon, disjointed, precise; simpl.
  intros P Q R ? ? hP hp1p2p3 hr1r2r3 hPp h123.
  intros.
  destruct H4 as [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]].
  destruct (join_assoc H4 H6) as [h23' [? ?]]; equate_join h23 h23'.
  destruct (cross_split _ _ _ _ _ H10 H2) as [[[[hp1 hr1] hp2p3] hr2r3] [? [? [? ?]]]].
  destruct (cross_split _ _ _ _ _ H5 H11) as [[[[hp2 hr2] hp3] hr3] [? [? [? ?]]]].
  try_join hp1 hp2 hp1p2.
  try_join hr1 hr2 hr1r2.
  assert (join hp1p2 hr1r2 h12).
  1: {
    try_join hp1 h2 hp1p2r2.
    destruct (join_assoc (join_comm H14) (join_comm H22)) as [hp1p2' [? ?]].
    equate_join hp1p2 hp1p2'.
    destruct (join_assoc (join_comm H25) (join_comm H23)) as [hr1r2' [? ?]].
    equate_join hr1r2 hr1r2'.
    auto.
  }

  try_join hP hp3 hPp3.
  assert (identity hp1p2 /\ joins hPp3 hr1r2) as [? ?] by (apply H with hPp h12; auto).
  try_join hP hp1 hPp1.
  assert (identity hp2p3 /\ joins hPp1 hr2r3) as [? ?] by (apply H0 with hPp h23; auto).

  assert (identity hp1) by (apply split_identity with hp2 hp1p2; auto).
  assert (identity hp3) by (apply split_identity with hp2 hp2p3; auto).
  split.
  + apply join_identity with hp1 hp2p3; auto.
  + apply H31 in H27.
    apply H32 in H23.
    subst hPp1 hPp3.
    destruct H26 as [hPr1r2 ?].
    destruct H30 as [hPr1r3 ?].
    destruct (join_assoc H20 (join_comm H23)) as [hPr1 [? ?]].
    destruct (triple_join_exists _ _ _ _ _ _ H13 (join_comm H26) H27) as [hPr1r2r3 ?H].
    apply joins_comm; eauto.
Qed.

Lemma covariant_ocon {B}{A} {JA: Join A}{PA: Perm_alg A}:
   forall F1 F2 : (B -> pred A) -> (B -> pred A),
    covariant F1 -> covariant F2 ->
    covariant (fun (x : B -> pred A) b => F1 x b ⊗ F2 x b).
Proof.
  intros; hnf.
  intros P Q ? ?.
  eapply ocon_derives.
  apply H, H1.
  apply H0, H1.
Qed.

Definition contravariant {B A : Type} (F: (B -> pred A) -> (B -> pred A)) : Prop :=
forall (P Q: B -> pred A), (forall x, P x |-- Q x) -> (forall x, F Q x |-- F P x).

Lemma contravariant_ocon {B}{A} {JA: Join A}{PA: Perm_alg A}:
   forall F1 F2 : (B -> pred A) -> (B -> pred A),
    contravariant F1 -> contravariant F2 ->
    contravariant (fun (x : B -> pred A) b => F1 x b ⊗ F2 x b).
Proof.
  intros; hnf.
  intros P Q ? ?.
  eapply ocon_derives.
  apply H, H1.
  apply H0, H1.
Qed.

Lemma precise_ocon {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A}{CaA : Canc_alg A}{CrA : Cross_alg A}{DA : Disj_alg A} :
  forall P Q, precise P -> precise Q -> precise (P ⊗ Q).
Proof.
  intros; intro; intros.
  destruct_ocon H1 h; destruct_ocon H2 i.
  generalize (join_join_sub H6); intro; generalize (join_sub_trans H13 H3); intro.
  generalize (join_join_sub H10); intro; generalize (join_sub_trans H15 H4); intro.
  generalize (H w h12 i12 H7 H11 H14 H16); intro.
  try_join h2 h3 h23'; equate_join h23 h23'; try_join i2 i3 i23'; equate_join i23 i23'.
  generalize (join_join_sub' H19); intro; generalize (join_sub_trans H18 H3); intro.
  generalize (join_join_sub' H20); intro; generalize (join_sub_trans H22 H4); intro.
  generalize (H0 w h23 i23 H8 H12 H21 H23); intro.
  rewrite H17 in *; rewrite H24 in *. clear h12 h23 H7 H8 H11 H12 H13 H14 H15 H16 H17 H18 H21 H22 H23 H24.
  apply (overlapping_eq h1 h2 h3 i1 i2 i3 i12 i23); trivial.
Qed.

Lemma precise_tri_exp_ocon {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CaA : Canc_alg A}
      {CrA : Cross_alg A} {DA : Disj_alg A} B:
  forall (P : B -> B -> B -> pred A) (Q R: B -> pred A),
    precise (EX x : B, EX y : B, EX z : B, P x y z) -> precise (exp Q) -> precise (exp R) ->
    precise (EX x : B, EX y : B, EX z : B, P x y z ⊗ Q y ⊗ R z).
Proof.
  repeat intro.
  destruct H2 as [x1 [y1 [z1 ?]]]; destruct_ocon H2 h; destruct_ocon H8 j;
  destruct H3 as [x2 [y2 [z2 ?]]]; destruct_ocon H3 i; destruct_ocon H16 k.
  assert (j12 = k12) by (hnf in H; apply H with (w := w);
                         [exists x1, y1, z1 | exists x2, y2, z2 | assertSub j12 w Hsub | assertSub k12 w Hsub]; auto).
  assert (j23 = k23) by (hnf in H0; apply H0 with (w := w);
                         [exists y1 | exists y2 | try_join j2 j3 j23'; equate_join j23 j23'; assertSub j23 w Hsub |
                                 try_join k2 k3 k23'; equate_join k23 k23'; assertSub k23 w Hsub]; auto).
  rewrite H22 in *; rewrite H23 in *; assert (h12 = i12) by (apply (overlapping_eq j1 j2 j3 k1 k2 k3 k12 k23); trivial).
  assert (h23 = i23) by (hnf in H1; apply H1 with (w := w);
                         [exists z1 | exists z2 | try_join h2 h3 h23'; equate_join h23 h23'; assertSub h23 w Hsub |
                                 try_join i2 i3 i23'; equate_join i23 i23'; assertSub i23 w Hsub]; auto).
  rewrite H24 in *; rewrite H25 in *; apply (overlapping_eq h1 h2 h3 i1 i2 i3 i12 i23); trivial.
Qed.

Lemma extract_andp_ocon_ocon_left {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A}:
  forall (w : A) P Q R S, (P && Q ⊗ R ⊗ S) w -> exists w', P w'.
Proof. repeat intro; destruct_ocon H h; destruct_ocon H2 i; destruct H6; exists i12; trivial. Qed.

Lemma ocon_precise_elim  {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}{DA : Disj_alg A}:
  forall P : pred A, precise P -> P ⊗ P = P.
Proof.
  intros; apply pred_ext; intro w; intro. destruct_ocon H0 h. try_join h2 h3 h23'; equate_join h23 h23'.
  equate_precise_direct h12 h23. assert (emp h1). assertSub h1 h12 HS. assert (joins h1 h12). exists w; auto.
  apply (join_sub_joins_identity HS H4). equate_canc h1 h3. apply (join_unit1_e _ _ H4) in H6. subst. auto. hnf.
  exists (core w), w, (core w), w, w. split. apply core_unit. split. apply join_comm, core_unit. split.
  apply join_comm, core_unit. split; auto.
Qed.

Lemma corable_ocon: forall {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A} P Q, corable P -> corable Q -> corable (ocon P Q).
Proof.
  intros.
  rewrite corable_spec in H, H0 |- *.
  unfold ocon.
  intros.
  simpl in H2 |- *.
  destruct H2 as [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]].
  exists (core y), (core y), y, (core y), y.
  pose proof join_core H2.
  pose proof join_core (join_comm H2).
  pose proof join_core H3.
  pose proof join_core (join_comm H3).
  pose proof join_core H4.
  pose proof join_core (join_comm H4).
  repeat split.
  + rewrite <- core_idem at 1.
    apply core_unit.
  + apply core_unit.
  + apply core_unit.
  + apply H with h12; auto.
    rewrite core_idem.
    congruence.
  + apply H0 with h23; auto.
    congruence.
Qed.

Lemma corable_andp_ocon1{A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
   forall P Q R, corable P ->  ocon (P && Q) R = P && (ocon Q R).
Proof.
  intros.
  apply pred_ext.
  + intros h [h1 [h2 [h3 [h12 [h23 [? [? [? [[? ?] ?]]]]]]]]].
    split.
    - apply join_core in H2.
      rewrite corable_spec in H.
      apply H with h12; [congruence | auto].
    - exists h1, h2, h3, h12, h23.
      tauto.
  + intros h [? [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]]].
    exists h1, h2, h3, h12, h23.
    rewrite corable_spec in H.
    repeat split; auto.
    apply join_core in H3.
    apply H with h; [congruence | auto].
Qed.

