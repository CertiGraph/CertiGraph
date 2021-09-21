Require Import VST.msl.msl_direct.
Require Import CertiGraph.msl_ext.ramify_tactics.
Require Import CertiGraph.msl_ext.overlapping_direct.
Require Import VST.msl.predicates_sa.

Lemma precise_left_sepcon_andp_distr_d {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA : Canc_alg A}:
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

Lemma precise_sepcon_d {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A}:
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

Lemma precise_wand_ewand_d {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA : Canc_alg A}:
  forall R P Q R', precise P -> R |-- P * (Q -* R') -> Q * (ewand P R) |-- R'.
Proof.
  intros. intro w. intros. destruct_sepcon H1 h. destruct H3 as [h3 [h4 [? [? ?]]]].
  specialize (H0 h4 H5). destruct_sepcon H0 h. equate_precise_direct h3 h0.
  equate_canc h2 h5. apply (H7 h1); auto.
Qed.
