Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.Equivalence_ext.

Definition app_sig {A B: Type} (P: A -> Prop) (f: A -> B): sig P -> B := fun a => f (proj1_sig a).

Definition guarded_pointwise_relation {A B : Type} (P: A -> Prop) (R : relation B) : relation (A -> B) :=
  respectful_relation (app_sig P) (pointwise_relation (sig P) R).

Instance guarded_pointwise_equivalence {A B : Type} (P: A -> Prop) {R : relation B} {EqR: Equivalence R}: Equivalence (guarded_pointwise_relation P R).
Proof.
  apply resp_Equivalence.
  apply pointwise_equivalence.
  auto.
Defined.

Definition guarded_pointwise_relation_spec: forall {A B : Type} (P: A -> Prop) (R : relation B) f g, guarded_pointwise_relation P R f g <-> (forall x: A, P x -> R (f x) (g x)).
Proof.
  intros.
  unfold guarded_pointwise_relation, respectful_relation, app_sig, pointwise_relation.
  split; intros.
  + specialize (H (exist P x H0)).
    exact H.
  + destruct a.
    specialize (H x p).
    exact H.
Qed.

Lemma guarded_pointwise_relation_weaken: forall {A B : Type} (P1 P2: A -> Prop) (R : relation B), Included P2 P1 -> inclusion _ (guarded_pointwise_relation P1 R) (guarded_pointwise_relation P2 R).
Proof.
  intros.
  hnf; intros.
  rewrite guarded_pointwise_relation_spec in H0 |- *.
  unfold Included, In in H.
  firstorder.
Qed.

Lemma guarded_pointwise_relation_pointwise_relation: forall {A B : Type} (P: A -> Prop) (R : relation B), inclusion _ (pointwise_relation A R) (guarded_pointwise_relation P R).
Proof.
  intros.
  hnf; intros.
  rewrite guarded_pointwise_relation_spec.
  intros.
  apply H.
Qed.

(* surjection properties are not used now. *)
Lemma guarded_surj_Included: forall {X Y} (f: X -> Y) (PX: X -> Prop) (PY PY0: Y -> Prop),
  (forall y, PY y -> exists x, PX x /\ f x = y) ->
  (forall x, PX x -> PY0 (f x)) ->
  Included PY PY0.
Proof.
  intros.
  unfold Included, Ensembles.In.
  intros y ?.
  destruct (H _ H1) as [x [? ?]].
  subst y.
  apply (H0 x); auto.
Qed.

Lemma guarded_surj_Disjoint: forall {X Y} (f: X -> Y) (PX: X -> Prop) (PY PY0: Y -> Prop),
  (forall y, PY y -> exists x, PX x /\ f x = y) ->
  (forall x, PX x -> ~ PY0 (f x)) ->
  Disjoint Y PY PY0.
Proof.
  intros.
  rewrite Disjoint_spec.
  intros y ? ?.
  destruct (H _ H1) as [x [? ?]].
  subst y.
  apply (H0 x); auto.
Qed.

Lemma image_set_proper_strong {A B: Type}: forall (f1 f2: A -> B) X,
  guarded_pointwise_relation X eq f1 f2 ->
  Same_set (image_set f1 X) (image_set f2 X).
Proof.
  intros.
  rewrite Same_set_spec.
  rewrite guarded_pointwise_relation_spec in H.
  intro x.
  rewrite !image_set_spec.
  firstorder; subst; firstorder.
Qed.
