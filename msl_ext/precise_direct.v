Require Import VST.msl.msl_direct.
Require Import RamifyCoq.msl_ext.ramify_tactics.
Require Import RamifyCoq.msl_ext.overlapping_direct.
Require Import VST.msl.predicates_sa.

Lemma precise_left_sepcon_andp_distr {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA : Canc_alg A}:
  forall P P1 P2 Q R, precise P -> P1 |-- P -> P2 |-- P -> (P1 * Q) && (P2 * R) |-- (P1 && P2) * (Q && R).
Proof.
  intros.
  unfold sepcon, andp, derives; simpl.
  intros.
  destruct H2 as [[?y [?z [? [? ?]]]] [?y [?z [? [? ?]]]]].
  exists y, z.
  assert (P y) by auto.
  assert (P y0) by auto.
  equate_precise_direct y y0.
  equate_canc z z0.
  repeat split; auto.
Qed.

(* derives_precise, precise_emp is in predicates_sa.v. *)

Lemma precise_sepcon {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A}:
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

Lemma precise_wand_ewand {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA : Canc_alg A}:
  forall R P Q R', precise P -> R |-- P * (Q -* R') -> Q * (ewand P R) |-- R'.
Proof.
  intros. intro w. intros. destruct_sepcon H1 h. destruct H3 as [h3 [h4 [? [? ?]]]].
  specialize (H0 h4 H5). destruct_sepcon H0 h. equate_precise_direct h3 h0.
  equate_canc h2 h5. apply (H7 h1); auto.
Qed.

(*
Lemma overlapping_precise_emp {A} {JA : Join A} {PA : Perm_alg A} {SA : Sep_alg A} {CA : Canc_alg A} {DA : Disj_alg A} {AG : ageable A} {AA: Age_alg A}:
  forall w1 w2 w3 w12 w23 w (P Q : pred A),
    join w1 w2 w12 -> join w2 w3 w23 -> join w12 w3 w -> P w12 -> Q w23 -> precise P -> precise Q -> (P * Q)%pred w -> emp w2.
Proof.
  intros. destruct_sepcon H6 k. try_join w2 w3 w23'; equate_join w23 w23'. equate_precise w12 k1. equate_precise w23 k2.
  apply join_sub_joins_identity with w23. exists w3; auto. try_join w2 w23 w223; exists w223; auto.
Qed.

Lemma precise_andp_left {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG : ageable A} {AA: Age_alg A} :
  forall P Q, precise P -> precise (P && Q).
Proof. intros; intro; intros; destruct H0; destruct H1; generalize (H w w1 w2 H0 H1 H2 H3); tauto. Qed.

Lemma precise_andp_right {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG : ageable A} {AA: Age_alg A} :
  forall P Q, precise Q -> precise (P && Q).
Proof. intros; intro; intros; destruct H0; destruct H1; generalize (H w w1 w2 H4 H5 H2 H3); tauto. Qed.
*)

(*
Lemma precise_exp_sepcon {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG : ageable A} {AA: Age_alg A} B:
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

Lemma precise_tri_exp_andp_right {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG : ageable A} {AA: Age_alg A} B:
  forall (P Q: B -> B -> B -> pred A),
    precise (EX x : B, EX y : B, EX z : B, Q x y z) ->
    precise (EX x : B, EX y : B, EX z : B, P x y z && Q x y z).
Proof.
  repeat intro; destruct H0 as [x1 [y1 [z1 [? ?]]]], H1 as [x2 [y2 [z2 [? ?]]]];
  hnf in H; apply H with (w := w); [exists x1, y1, z1 | exists x2, y2, z2 | | ]; auto.
Qed.

Lemma precise_tri_exp_andp_left {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG : ageable A} {AA: Age_alg A} B:
  forall (P Q: B -> B -> B -> pred A),
    precise (EX x : B, EX y : B, EX z : B, P x y z) ->
    precise (EX x : B, EX y : B, EX z : B, P x y z && Q x y z).
Proof.
  repeat intro; destruct H0 as [x1 [y1 [z1 [? ?]]]], H1 as [x2 [y2 [z2 [? ?]]]];
  hnf in H; apply H with (w := w); [exists x1, y1, z1 | exists x2, y2, z2 | | ]; auto.
Qed.

Lemma precise_tri_exp_sepcon {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {AG : ageable A} {AA: Age_alg A} B:
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
*)