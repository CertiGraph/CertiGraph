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
