Require Export Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Morphisms.
Require Export Coq.Classes.Equivalence.
Require Coq.Setoids.Setoid.

(*
Inductive relation_list {A B: Type} {Req: relation A} {Req_Equiv: Equivalence Req} (R: B -> relation A): list B -> relation A :=
  | relation_list_nil: forall x y, Req x y -> relation_list R nil x y
  | relation_list_cons: forall x y z bs b, relation_list R bs x y -> R b y z -> relation_list R (bs ++ b :: nil) x z.

Lemma relation_list_Intersection: forall {A B: Type} {Req: relation A} {Req_Equiv: Equivalence Req} (R1 R2 R3: B -> relation A) bs,
  (forall b, same_relation _ (relation_conjunction (R1 b) (R2 b)) (R3 b)) ->
  inclusion _ (relation_list R3 bs) (relation_conjunction (relation_list R1 bs) (relation_list R2 bs)).
Proof.
  intros.
  hnf; intros.
  induction H0.
  - split; constructor; auto.
  - apply (proj2 (H b)) in H1.
    destruct H1, IHrelation_list.
    split; econstructor; eauto.
Qed.
*)

Lemma same_relation_spec: forall {A} a1 a2, same_relation A a1 a2 <-> pointwise_relation A (pointwise_relation A iff) a1 a2.
Proof.
  intros.
  unfold same_relation, inclusion, pointwise_relation.
  firstorder.
Qed.

Lemma same_relation_Reflexive {A}: Reflexive (same_relation A).
Proof.
  hnf; intros.
  rewrite same_relation_spec.
  unfold pointwise_relation.
  firstorder.
Qed.

Lemma same_relation_Symmetric {A}: Symmetric (same_relation A).
Proof.
  hnf; intros.
  rewrite same_relation_spec in *.
  unfold pointwise_relation in *.
  firstorder.
Qed.

Lemma same_relation_Transitive {A}: Transitive (same_relation A).
Proof.
  hnf; intros.
  rewrite same_relation_spec in *.
  unfold pointwise_relation in *.
  firstorder.
Qed.

Instance same_relation_Equivalence {A}: Equivalence (same_relation A).
Proof.
  split.
  + apply same_relation_Reflexive.
  + apply same_relation_Symmetric.
  + apply same_relation_Transitive.
Qed.

Instance inclusion_proper {A}: Proper (same_relation A ==> same_relation A ==> iff) (inclusion A).
Proof.
  intros.
  do 2 (hnf; intros ?F ?G ?H).
  unfold inclusion.
  rewrite same_relation_spec in H, H0.
  split; intros HH x y; specialize (HH x y).
  + rewrite (H x y), (H0 x y) in HH.
    auto.
  + rewrite (H x y), (H0 x y).
    auto.
Qed.

Inductive compond_relation {A: Type} (R1 R2: relation A) : relation A :=
  | compond_intro: forall x y z, R1 x y -> R2 y z -> compond_relation R1 R2 x z.

Instance compond_relation_proper {A: Type}: Proper (same_relation A ==> same_relation A ==> same_relation A) compond_relation.
Proof.
  do 2 (hnf; intros).
  rewrite same_relation_spec in H, H0 |- *.
  unfold pointwise_relation in *.
  intros; split; intro HH; inversion HH; subst.
  + apply compond_intro with y1; firstorder.
  + apply compond_intro with y1; firstorder.
Defined.

Lemma compond_assoc: forall {A: Type} (R1 R2 R3: relation A),
  same_relation _ (compond_relation (compond_relation R1 R2) R3) (compond_relation R1 (compond_relation R2 R3)).
Proof.
  intros.
  split; hnf; intros;
  do 2
  match goal with
  | H : compond_relation _ _ _ _ |- _ => inversion H; subst; clear H
  end;
  do 2 (econstructor; eauto).
Qed.

Lemma compond_eq_right: forall {A: Type} (R: relation A), same_relation _(compond_relation R eq) R.
Proof.
  intros.
  split; hnf; intros.
  + inversion H; subst.
    auto.
  + econstructor; eauto.
Qed.

Lemma compond_eq_left: forall {A: Type} (R: relation A), same_relation _(compond_relation eq R) R.
Proof.
  intros.
  split; hnf; intros.
  + inversion H; subst.
    auto.
  + econstructor; eauto.
Qed.

Definition respectful_relation {A B} (f: A -> B) (R: relation B): relation A := fun x y => R (f x) (f y).
