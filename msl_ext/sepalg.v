Require Import VST.msl.Extensionality.
Require Import VST.msl.sepalg.
Require Import CertiGraph.msl_ext.abs_addr.
Require Import CertiGraph.msl_ext.ramify_tactics.

Set Implicit Arguments.

Lemma join_identity {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall a b c, join a b c -> identity a -> identity b -> identity c.
Proof.
  intros.
  hnf; intros x y ?.
  try_join b x bx.
  apply H1 in H3.
  apply H0 in H4.
  subst; auto.
Qed.
