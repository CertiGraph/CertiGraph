Require Import msl.msl_classical.
Require Import ramify_tactics.

Lemma overlapping_eq {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG: ageable A} {XA: Age_alg A}
      {CaA : Canc_alg A} {CrA : Cross_alg A} {DA : Disj_alg A}:
  forall h1 h2 h3 i1 i2 i3 i12 i23 w1 w2,
    join h1 h2 i12 -> join h2 h3 i23 -> join i12 h3 w1 -> join i1 i2 i12 -> join i2 i3 i23 -> join i12 i3 w2 -> w1 = w2.
Proof.
  intros; try_join h2 h3 h23'; equate_join i23 h23'; try_join i2 i3 i23'; equate_join i23 i23'.
  destruct (cross_split h1 h2 i1 i2 i12 H H2) as [[[[h1i1 h1i2] h2i1] h2i2] [? [? [? ?]]]].
  try_join h1i2 i3 i3'; try_join i3 h2i2 i23'; try_join h1i2 h1 h1'; try_join h1i2 h1i2 x.
  generalize (join_self H17); intro Heq; rewrite <- Heq in *; clear Heq x;
  assert (Hid1: unit_for h1i2 h1i2) by apply H17; rewrite <- identity_unit_equiv in Hid1.

  try_join h2i1 h3 h3'; try_join h3 h2i2 h23; try_join h2i1 i1 i1'; try_join h2i1 h2i1 x;
  generalize (join_self H25); intro Heq; rewrite <- Heq in *; clear Heq x;
  assert (Hid2: unit_for h2i1 h2i1) by apply H25; rewrite <- identity_unit_equiv in Hid2.
  repeat match goal with
           | [H1: identity ?X, H2: join ?X _ _ |- _] => apply H1 in H2; rewrite H2 in *; clear H2
           | [H1: identity ?X, H2: join _ ?X _ |- _] => apply join_comm in H2; apply H1 in H2; rewrite H2 in *; clear H2
         end.
  equate_join w1 w2; apply eq_refl.
Qed.

Lemma precise_andp_left {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG: ageable A} {XA: Age_alg A}:
  forall P Q, precise P -> precise (P && Q).
Proof. intros; intro; intros; destruct H0; destruct H1; generalize (H w w1 w2 H0 H1 H2 H3); tauto. Qed.

Lemma precise_andp_right {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG: ageable A} {XA: Age_alg A}:
  forall P Q, precise Q -> precise (P && Q).
Proof. intros; intro; intros; destruct H0; destruct H1; generalize (H w w1 w2 H4 H5 H2 H3); tauto. Qed.

Lemma precise_orp {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG: ageable A} {XA: Age_alg A}:
  forall P Q, (forall w1 w2: A, ~ (app_pred P w1 /\ app_pred Q w2)) -> precise P -> precise Q -> precise (P || Q).
Proof.
  intros P Q Hfalse H H0; intro; intros.
  destruct H1; destruct H2. generalize (H w w1 w2 H1 H2 H3 H4); tauto.
  specialize (Hfalse w1 w2); destruct Hfalse; intuition.
  specialize (Hfalse w2 w1); destruct Hfalse; intuition.
  generalize (H0 w w1 w2 H1 H2 H3 H4); tauto.
Qed.

Lemma precise_sepcon {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG: ageable A} {XA: Age_alg A}:
  forall P Q, precise Q -> precise P -> precise (P * Q).
Proof.
  repeat intro; destruct H1 as [w11 [w12 [? [? ?]]]], H2 as [w21 [w22 [? [? ?]]]].
  assert (w11 = w21) by (apply join_join_sub in H1; generalize (join_sub_trans H1 H3); intro;
                         apply join_join_sub in H2; generalize (join_sub_trans H2 H4); intro;
                         hnf in H0; apply H0 with (w := w); trivial).
  assert (w12 = w22) by (apply join_join_sub' in H1; generalize (join_sub_trans H1 H3); intro;
                         apply join_join_sub' in H2; generalize (join_sub_trans H2 H4); intro;
                         hnf in H; apply H with (w := w); trivial).
  rewrite H9 in *; rewrite H10 in *; equate_join w1 w2; auto.
Qed.

Lemma precise_exp_sepcon {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG: ageable A} {XA: Age_alg A} B:
  forall P Q: B -> pred A, precise (exp P) -> precise (exp Q) -> precise (EX x : B, P x * Q x).
Proof.
  repeat intro.
  destruct H1 as [x [w11 [w12 [? [? ?]]]]]; destruct H2 as [y [w21 [w22 [? [? ?]]]]].
  specialize (H w w11 w21); specialize (H0 w w12 w22).
  assert (w11 = w21) by (apply H; [exists x; auto | exists y; auto |
                                   apply join_sub_trans with (b := w1); apply join_join_sub in H1; auto |
                                   apply join_sub_trans with (b := w2); apply join_join_sub in H2; auto]).
  assert (w12 = w22) by (apply H0; [exists x; auto | exists y; auto |
                                    apply join_sub_trans with (b := w1); apply join_join_sub' in H1; auto |
                                    apply join_sub_trans with (b := w2); apply join_join_sub' in H2; auto]).
  rewrite H9 in *; rewrite H10 in *; equate_join w1 w2; auto.
Qed.

Lemma precise_tri_exp_andp_right {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG: ageable A} {XA: Age_alg A} B:
  forall (P Q: B -> B -> B -> pred A),
    precise (EX x : B, EX y : B, EX z : B, Q x y z) ->
    precise (EX x : B, EX y : B, EX z : B, P x y z && Q x y z).
Proof.
  repeat intro; destruct H0 as [x1 [y1 [z1 [? ?]]]], H1 as [x2 [y2 [z2 [? ?]]]];
  hnf in H; apply H with (w := w); [exists x1, y1, z1 | exists x2, y2, z2 | | ]; auto.
Qed.

Lemma precise_tri_exp_andp_left {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG: ageable A} {XA: Age_alg A} B:
  forall (P Q: B -> B -> B -> pred A),
    precise (EX x : B, EX y : B, EX z : B, P x y z) ->
    precise (EX x : B, EX y : B, EX z : B, P x y z && Q x y z).
Proof.
  repeat intro; destruct H0 as [x1 [y1 [z1 [? ?]]]], H1 as [x2 [y2 [z2 [? ?]]]];
  hnf in H; apply H with (w := w); [exists x1, y1, z1 | exists x2, y2, z2 | | ]; auto.
Qed.

Lemma precise_tri_exp_sepcon {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG: ageable A} {XA: Age_alg A} B:
  forall (P Q R: B -> pred A),
    precise (exp P) -> precise (exp Q) -> precise (exp R) -> precise (EX x : B, EX y : B, EX z : B, P x * Q y * R z).
Proof.
  repeat intro; destruct H2 as [x1 [y1 [z1 [h1 [h2 [? [[i1 [i2 [? [? ?]]]] ?]]]]]]];
  destruct H3 as [x2 [y2 [z2 [j1 [j2 [? [[k1 [k2 [? [? ?]]]] ?]]]]]]].
  assert (i1 = k1) by (hnf in H; apply H with (w := w);
                       [exists x1 | exists x2; auto | assertSub i1 w Hsub | assertSub k1 w Hsub]; auto).
  assert (i2 = k2) by (hnf in H0; apply H0 with (w := w);
                       [exists y1 | exists y2; auto | assertSub i2 w Hsub | assertSub k2 w Hsub]; auto).
  rewrite H14 in *; rewrite H15 in *; equate_join h1 j1.
  assert (h2 = j2) by (hnf in H1; apply H1 with (w := w);
                       [exists z1 | exists z2; auto | assertSub h2 w Hsub | assertSub j2 w Hsub]; auto).
  rewrite H10 in *; equate_join w1 w2; auto.
Qed.
