Require Import msl.msl_classical.
Require Import ramify_tactics.

Lemma precise_andp_left {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG: ageable A} {XA: Age_alg A}:
  forall P Q, precise P -> precise (P && Q).
Proof. intros; intro; intros; destruct H0; destruct H1; generalize (H w w1 w2 H0 H1 H2 H3); tauto. Qed.

Lemma precise_andp_right {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG: ageable A} {XA: Age_alg A}:
  forall P Q, precise Q -> precise (P && Q).
Proof. intros; intro; intros; destruct H0; destruct H1; generalize (H w w1 w2 H4 H5 H2 H3); tauto. Qed.

Lemma precise_orp {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG: ageable A} {XA: Age_alg A}:
  forall P Q, (forall w1 w2: A, ~ (app_pred P w1 /\ app_pred Q w2)) -> precise Q -> precise P -> precise (P || Q).
Proof.
  intros P Q Hfalse H H0; intro; intros.
  destruct H1; destruct H2. generalize (H0 w w1 w2 H1 H2 H3 H4); tauto.
  specialize (Hfalse w1 w2); destruct Hfalse; intuition.
  specialize (Hfalse w2 w1); destruct Hfalse; intuition.
  generalize (H w w1 w2 H1 H2 H3 H4); tauto.
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

Lemma precise_exp {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG: ageable A} {XA: Age_alg A} B:
  forall P : B -> pred A, (forall x w1 w2, app_pred (P x) w1 -> app_pred (P x) w2) ->
                          (forall x, precise (P x)) -> precise (exp P).
Proof.
  repeat intro; destruct H1, H2; specialize (H x w1 w2 H1); specialize (H0 x); generalize (H0 w w1 w2 H1 H H3 H4); tauto.
Qed.
