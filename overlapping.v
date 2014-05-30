Require Import msl.msl_classical.

Program Definition ovrlapcon {A: Type}{JA: Join A}{PA: Perm_alg A}{AG: ageable A}{XA: Age_alg A} (p q:pred A) : pred A :=
  fun h:A => exists h1 h2 h3 h12 h23, join h1 h2 h12 /\ join h2 h3 h23 /\ join h12 h3 h /\ p h12 /\ q h23.
Next Obligation.
  Ltac getEq h1 h2 := unfold age in h1, h2; rewrite h1 in h2; injection h2; intro.
  destruct H0 as [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]].
  destruct (join_assoc H0 H2) as [h23' [? ?]].
  generalize (join_eq H1 H5); intro.
  rewrite <- H7 in H6.
  clear h23' H5 H7.
  destruct (age1_join2 _ H2 H) as [w12 [w3 [? [? ?]]]].
  destruct (age1_join2 _ H0 H7) as [w1 [w2 [? [? ?]]]].
  destruct (join_assoc H9 H5) as [w23 [? ?]].
  exists w1, w2, w3, w12, w23.
  repeat split; auto.
  apply pred_hereditary with h12; auto.
  apply pred_hereditary with h23; auto.
  destruct (age1_join2 _ H6 H) as [w1' [w23' [? [? ?]]]].
  destruct (age1_join2 _ H1 H16) as [w2' [w3' [? [? ?]]]].
  getEq H11 H18; getEq H8 H19.
  rewrite H20, H21 in H12.
  generalize (join_eq H12 H17); intro.
  rewrite H22; trivial.
Qed.

Notation "P ⊗ Q" := (ovrlapcon P Q) (at level 40, left associativity) : pred.

Lemma overlapping_emp {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall P: pred A, (P ⊗ emp = P)%pred.
Proof.
  intros; apply pred_ext; hnf; intros; simpl in *; intros.
  destruct H as [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]].
  unfold identity in H3.
  destruct (join_assoc H H1) as [h23' [? ?]].
  generalize (join_eq H0 H4); intro.
  rewrite <- H6 in H5.
  apply join_comm in H5.
  apply H3 in H5.
  rewrite H5 in H.
  generalize (join_positivity H H1); intro.
  rewrite H7; trivial.
  exists a, (core a), (core a), a, (core a).
  generalize (core_unit a); intro.
  unfold unit_for in H0.
  repeat split; auto.
  apply core_duplicable.
  apply core_identity.
Qed.

Lemma andp_overlapping {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall P Q, P && Q |-- P ⊗ Q.
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

Lemma sepcon_overlapping {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall P Q, P * Q |-- P ⊗ Q.
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

Lemma overlapping_sep_true {A}{JA: Join A}{PA: Perm_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall P Q, P ⊗ Q |-- P * TT.
Proof.
  intros; hnf; intros; simpl in *; intros.
  destruct H as [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]].
  exists h12, h3.
  repeat split; auto.
Qed.

Lemma overlapping_wand {A}{JA: Join A}{PA: Perm_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall P Q, (P ⊗ Q = EX R : pred A, (R -* P) * (R -* Q) * R)%pred.
Proof.
  intros; apply pred_ext; hnf; intros; simpl in *.
  destruct H as [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]].
  destruct (join_assoc H H1) as [h23' [H5 H4]].
  generalize (join_eq H0 H5); intro.
  rewrite <- H6 in H4; clear h23' H5 H6.
  destruct (join_assoc H0 (join_comm H4)) as [h13 [? ?]].
  apply join_comm in H5. apply join_comm in H6.
  exists (exactly h2), h13, h2.
  repeat split; simpl; auto.
  exists h1, h3.
  repeat split; auto.

  intros h1' h2' h12'; intros;
  apply (pred_nec_hereditary P h12); auto;
  destruct (nec_join H H7) as [w2 [w12 [? [? ?]]]];
  destruct (join_level h1' h2' h12' H8); rewrite <- H14 in H13; clear H14;
  destruct (join_level h1' w2 w12 H10); rewrite <- H15 in H14; clear H15;
  rewrite H14 in H13; clear H14;
  generalize (necR_linear' H11 H9 H13); intro;
  rewrite H14 in H10;
  generalize (join_eq H10 H8); intro;
  rewrite H15 in H12; auto.

  intros h3' h2' h23'; intros;
  apply (pred_nec_hereditary Q h23); auto;
  apply join_comm in H0;
  destruct (nec_join H0 H7) as [w2 [w23 [? [? ?]]]];
  destruct (join_level h3' h2' h23' H8); rewrite <- H14 in H13; clear H14;
  destruct (join_level h3' w2 w23 H10); rewrite <- H15 in H14; clear H15;
  rewrite H14 in H13; clear H14;
  generalize (necR_linear' H11 H9 H13); intro;
  rewrite H14 in H10;
  generalize (join_eq H10 H8); intro;
  rewrite H15 in H12; auto.

  (* another direction *)
  destruct H as [R [w13 [w2 [H132a [[w1 [w3 [H13 [HP HQ]]]] HR]]]]].
  destruct (join_assoc H13 H132a) as [w23 [H23 H123a]].
  destruct (join_assoc H23 (join_comm H123a)) as [w12 [H2112 H312a]].
  exists w1, w2, w3, w12, w23.
  repeat split; auto.
  apply (HP w1 w2); auto.
  apply (HQ w3 w2); auto.
Qed.

Lemma overlapping_comm {A}{JA: Join A}{PA: Perm_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall P Q, (P ⊗ Q = Q ⊗ P)%pred.
Proof.
  intros; apply pred_ext; hnf; intros; simpl in *; intros;
  destruct H as [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]];
  exists h3, h2, h1, h23, h12;
  repeat split; auto; destruct (join_assoc H H1) as [h23' [? ?]];
  generalize (join_eq H0 H4); intro;
  rewrite <- H6 in H5; apply join_comm in H5; trivial.
Qed.

Lemma cross_rev {A}{JA: Join A}{PA: Perm_alg A}: forall h1 h2 h3 h4
  h12 h34 h13 h24 h1234, join h1 h2 h12 -> join h1 h3 h13 -> join h3 h4
  h34 -> join h2 h4 h24 -> join h12 h34 h1234 -> join h13 h24 h1234.
Proof.
  intros.
  destruct (join_assoc H H3) as [h234 [? ?]].
  destruct (join_assoc H1 (join_comm H4)) as [h24' [? ?]];
  generalize (join_eq H2 (join_comm H6)); intro;
  rewrite <- H8 in H7; clear h24' H6 H8.
  destruct (join_assoc (join_comm H7) (join_comm H5)) as [h13' [? ?]].
  generalize (join_eq H0 (join_comm H6)); intro.
  rewrite <- H9 in H8.
  apply join_comm; trivial.
Qed.

Lemma overlapping_assoc {A}{JA: Join A}{PA: Perm_alg A}{CA: Cross_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall P Q R: pred A, (P ⊗ Q ⊗ R = P ⊗ (Q ⊗ R))%pred.
Proof.
  intros; apply pred_ext; hnf; intros; simpl in *; intros.
  destruct H as [w124 [w567 [w3 [w124567 [w3567 [H124_567 [H567_3 [H124567_3 [[w15 [w47 [w26 [w1457 [w2467 [H15_47 [H47_26 [H1457_26 [Pw1457 Qw2467]]]]]]]]] Rw3567]]]]]]]]].
  destruct (cross_split w124 w567 w1457 w26 w124567 H124_567 H1457_26) as [[[[w14 w2] w57] w6] [H14_2 [H57_6 [H14_57 H2_6]]]].
  destruct (cross_split w15 w47 w14 w57 w1457 H15_47 H14_57) as [[[[w1 w5] w4] w7] [H1_5 [H4_7 [H1_4 H5_7]]]].
  destruct (join_assoc H1_5 H15_47) as [w457 [H5_47 H1_457]].
  destruct (join_assoc H1457_26 H124567_3) as [w236 [H26_3 H1457_236]].
  destruct (join_assoc H1_457 H1457_236) as [w234567 [H457_236 H1_234567]].
  exists w1, w457, w236, w1457, w234567.
  repeat split; auto.
  destruct (join_assoc H1_4 H14_2) as [w24 [H4_2 H1_24]].
  destruct (join_assoc H5_7 H57_6) as [w67 [H7_6 H5_67]].
  destruct (join_assoc (join_comm H5_67) H567_3) as [w35 [H5_3 H67_35]].
  exists w24, w67, w35, w2467, w3567.
  repeat split; auto.
  apply (cross_rev w2 w6 w4 w7 w26 w47); auto.
  apply (cross_rev w47 w5 w26 w3 w457 w236); auto.

  (* another direction *)
  destruct H as [w1 [w457 [w236 [w1457 [w234567 [H1_457 [H457_236 [H1457_236 [Pw1457 [w24 [w67 [w35 [w2467 [w3567 [H24_67 [H67_35 [H2467_35 [Qw2467 Rw3567]]]]]]]]]]]]]]]]]].
  destruct (cross_split w457 w236 w2467 w35 w234567 H457_236 H2467_35) as [[[[w47 w5] w26] w3] [H47_5 [H26_3 [H47_26 H5_3]]]].
  destruct (cross_split w24 w67 w47 w26 w2467 H24_67 H47_26) as [[[[w4 w2] w7] w6] [H4_2 [H7_6 [H4_7 H2_6]]]].
  destruct (join_assoc (join_comm H26_3) (join_comm H1457_236)) as [w124567 [H26_1457 H3_124567]].
  destruct (join_assoc (join_comm H5_3) (join_comm H67_35)) as [w567 [H5_67 H3_567]].

  destruct (join_assoc H4_7 H47_5) as [w57 [H7_5 H4_57]].
  destruct (join_assoc (join_comm H4_57) (join_comm H1_457)) as [w14 [H4_1 H57_14]].
  destruct (join_assoc H57_14 (join_comm H26_1457)) as [w1246 [H14_26 H57_1246]].
  destruct (join_assoc (join_comm H2_6) (join_comm H14_26)) as [w124 [H2_14 H6_124]].

  exists w124, w567, w3, w124567, w3567.
  repeat split; auto.
  apply join_comm.
  apply (cross_rev w6 w2 w57 w14 w26 w1457); auto.
  destruct (join_assoc (join_comm H7_6) (join_comm H5_67)) as [w57' [Ht H6_57]];
  generalize (join_eq Ht H7_5); intro Ht2; rewrite Ht2 in H6_57; clear w57' Ht Ht2; trivial.
  destruct (join_assoc H47_5 (join_comm H1_457)) as [w15 [H5_1 H47_15]].
  exists w15, w47, w26, w1457, w2467.
  repeat split; auto.
Qed.

Definition covariant {B A : Type} {AG: ageable A} (F: (B -> pred A) -> (B -> pred A)) : Prop :=
forall (P Q: B -> pred A), (forall x, P x |-- Q x) -> (forall x, F P x |-- F Q x).

Lemma overlapping_derives {A} {JA: Join A}{PA: Perm_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall p q p' q', (p |-- p') -> (q |-- q') -> (p ⊗ q |-- p' ⊗ q').
Proof.
  repeat (intros; hnf).
  simpl in H1.
  destruct H1 as [w1 [w2 [w3 [w12 [w23 [? [? [? [? ?]]]]]]]]].
  exists w1,w2,w3,w12,w23.
  repeat split; auto.
Qed.

Lemma covariant_overlapping {B}{A} {JA: Join A}{PA: Perm_alg A}{AG: ageable A}{XA: Age_alg A}:
   forall F1 F2 : (B -> pred A) -> (B -> pred A),
    covariant F1 -> covariant F2 ->
    covariant (fun (x : B -> pred A) b => F1 x b ⊗ F2 x b)%pred.
Proof.
  intros; hnf.
  intros P Q ? ?.
  eapply overlapping_derives.
  apply H, H1.
  apply H0, H1.
Qed.

Definition contravariant {B A : Type} {AG: ageable A} (F: (B -> pred A) -> (B -> pred A)) : Prop :=
forall (P Q: B -> pred A), (forall x, P x |-- Q x) -> (forall x, F Q x |-- F P x).

Lemma contravariant_overlapping {B}{A} {JA: Join A}{PA: Perm_alg A}{AG: ageable A}{XA: Age_alg A}:
   forall F1 F2 : (B -> pred A) -> (B -> pred A),
    contravariant F1 -> contravariant F2 ->
    contravariant (fun (x : B -> pred A) b => F1 x b ⊗ F2 x b)%pred.
Proof.
  intros; hnf.
  intros P Q ? ?.
  eapply overlapping_derives.
  apply H, H1.
  apply H0, H1.
Qed.

Ltac try_join h1 h2 h1h2 :=
  let helper m1 m2 m1m2 :=
      match goal with
        | [H1: join _ m1 ?X, H2: join ?X m2 _ |- _] => destruct (join_assoc H1 H2) as [m1m2 [? ?]]
        | [H1: join m1 _ ?X, H2: join ?X m2 _ |- _] => destruct (join_assoc (join_comm H1) H2) as [m1m2 [? ?]]
        | [H1: join _ m1 ?X, H2: join m2 ?X _ |- _] => destruct (join_assoc H1 (join_comm H2)) as [m1m2 [? ?]]
        | [H1: join m1 _ ?X, H2: join m2 ?X _ |- _] => destruct (join_assoc (join_comm H1) (join_comm H2)) as [m1m2 [? ?]]
      end
  in helper h1 h2 h1h2 || helper h2 h1 h1h2.

Ltac try_join_through X h1 h2 h1h2 :=
  let helper m1 m2 m1m2 :=
      match goal with
        | [H1: join _ m1 X, H2: join X m2 _ |- _] => destruct (join_assoc H1 H2) as [m1m2 [? ?]]
        | [H1: join m1 _ X, H2: join X m2 _ |- _] => destruct (join_assoc (join_comm H1) H2) as [m1m2 [? ?]]
        | [H1: join _ m1 X, H2: join m2 X _ |- _] => destruct (join_assoc H1 (join_comm H2)) as [m1m2 [? ?]]
        | [H1: join m1 _ X, H2: join m2 X _ |- _] => destruct (join_assoc (join_comm H1) (join_comm H2)) as [m1m2 [? ?]]
      end
  in helper h1 h2 h1h2 || helper h2 h1 h1h2.

Ltac equate_join x1 x2 :=
  let Heq := fresh "Heq" in
  match goal with
    |[H1: join ?a ?b x1, H2: join ?b ?a x2 |- _] => apply join_comm in H2
    | _ => idtac
  end;
  match goal with
    |[H1: join ?a ?b x1, H2: join ?a ?b x2 |- _] =>
     generalize (join_eq H2 H1); intro Heq;
     rewrite Heq in *; clear H2 Heq x2
  end.

Lemma later_sepcon1 {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A} : forall P Q,
  (|>(P * Q) = |>P * |>Q)%pred.
Proof.
  pose (H:=True).
  intros.
  repeat rewrite later_age.
  apply pred_ext; hnf; intros.
  simpl in H0.
  case_eq (age1 a); intros.
  destruct (H0 a0) as [w [v [? [? ?]]]]; auto.
  destruct (unage_join2 _ H2 H1) as [w' [v' [? [? ?]]]].
  exists w'; exists v'; intuition.
  simpl; intros.
  replace a' with w; auto.
  unfold age in *; congruence.
  simpl; intros.
  replace a' with v; auto.
  unfold age in *; congruence.
  destruct (join_ex_units a).
  exists x; exists a.
  intuition.
  hnf; intros.
  red in u.
  simpl in H2.
  destruct (age1_join _ u H2) as [s [t [? [? ?]]]].
  unfold age in H5.
  rewrite H1 in H5; discriminate.
  hnf; intros.
  simpl in H2.
  unfold age in H2.
  rewrite H1 in H2; discriminate.

  destruct H0 as [w [v [? [? ?]]]].
  hnf; intros.
  simpl in H3.
  destruct (age1_join2 _ H0 H3) as [w' [v' [? [? ?]]]].
  exists w'; exists v'; intuition.
Qed.


Lemma later_overlapping {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall P Q, ((|> (P ⊗ Q)) = |> Q ⊗ |> P)%pred.
Proof.
  intros; apply pred_ext. hnf; intros; simpl in *.
  case_eq (age1 a); intros.
  destruct (H a0) as [h1' [h2' [h3' [h12' [h23' [? [? [? [? ?]]]]]]]]].
  apply t_step; apply H0.
  destruct (unage_join2 _ H3 H0) as [x12 [x3 [? [? ?]]]].
  destruct (unage_join2 _ H1 H7) as [x1 [x2 [? [? ?]]]].
  try_join x2 x3 x23.
  exists x3, x2, x1, x23, x12; repeat (split; auto).
  intro h23; intros.
  assert (age x23 h23'); destruct (age1_join2 _ H13 H0) as [w1 [w23 [? [? ?]]]].
  destruct (age1_join2 _ H12 H17) as [w2 [w3 [? [? ?]]]]; getEq H19 H11; getEq H20 H8;
  rewrite H21, H22 in H18; equate_join h23' w23; auto.
  generalize (age_later_nec x23 h23' h23 H15 H14); intro; apply pred_nec_hereditary with h23'; auto.
  intro h12; intros.
  assert (age x12 h12'); try_join x1 x2 x12'; equate_join x12 x12'.
  destruct (age1_join2 _ H16 H0) as [w3 [w12 [? [? ?]]]].
  destruct (age1_join2 _ H9 H18) as [w1 [w2 [? [? ?]]]]; getEq H20 H10; getEq H21 H11; rewrite H22, H23 in H19;
  equate_join h12' w12; auto.
  generalize (age_later_nec x12 h12' h12 H15 H14); intro; apply pred_nec_hereditary with h12'; auto.
  exists (core a), a, (core a), a, a. repeat split.
  apply core_unit. apply join_comm, core_unit. apply join_comm, core_unit.
  intros; rewrite age1_level0 in H0; apply laterR_level in H1; exfalso; intuition.
  intros; rewrite age1_level0 in H0; apply laterR_level in H1; exfalso; intuition.
  (* * *)
  repeat rewrite later_age; hnf; intros.
  destruct H as [x1 [x2 [x3 [x12 [x23 [? [? [? [? ?]]]]]]]]]; intros.
  hnf; intros. simpl in H2, H3, H4.
  destruct (age1_join2 _ H1 H4) as [h12 [h3 [? [? ?]]]].
  destruct (age1_join2 _ H H6) as [h1 [h2 [? [? ?]]]].
  try_join h2 h3 h23; exists h3, h2, h1, h23, h12; repeat (split; auto).
  assert (age x23 h23). try_join x2 x3 x23'; equate_join x23 x23'.
  destruct (age1_join2 _ H14 H4) as [w1 [w23 [? [? ?]]]].
  destruct (age1_join2 _ H0 H16) as [w2 [w3 [? [? ?]]]].
  getEq H18 H10; getEq H19 H7; rewrite H21, H20 in H17; equate_join h23 w23; auto. auto.
Qed.

(* Require Import msl.cjoins. *)
(* Require Import msl.cross_split. *)

(* Lemma assoc_overlapping_cross {A}{JA: Join A}{PA: Perm_alg A}{AG: ageable A}{XA: Age_alg A}: *)
(*   (forall P Q R: pred A, (P ⊗ Q ⊗ R = P ⊗ (Q ⊗ R))%pred) -> sa_distributive A. *)
(* Proof. *)
(*   intros; hnf; intros. *)
