Require Import Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.Equivalence_ext.
Require Export Coq.Lists.List.

Local Open Scope equiv_scope.

Section ListFun2.

Context {A B: Type}.
Context {RA: relation A}.
Context {RB: relation B}.
Context {EqRA: Equivalence RA}.
Context {EqRB: Equivalence RB}.

Instance proper_fold_left: forall (f: A -> B -> A) {Proper_f: Proper (equiv ==> equiv ==> equiv) f}, Proper (Forall2 equiv ==> equiv ==> equiv) (fold_left f).
Proof.
  intros.
  hnf; intros.
  induction H; hnf; intros; simpl.
  + auto.
  + apply IHForall2.
    apply Proper_f; auto.
Qed.

Lemma monoid_fold_left_tail: forall {f: A -> B -> A} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (e: A) a l,
  fold_left f (l ++ a :: nil) e === f (fold_left f l e) a.
Proof.
  intros.
  simpl.
  pose proof (proper_fold_left f).
  revert e; induction l; intros; simpl.
  + reflexivity.
  + apply IHl.
Qed.

End ListFun2.

Section ListFun1.

Context {A: Type}.
Context {RA: relation A}.
Context {EqRA: Equivalence RA}.

Lemma monoid_fold_left_head: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (e: A) a l,
  (forall x, f e x === x) ->
  (forall x, f x e === x) ->
  (forall x y z, f (f x y) z === f x (f y z)) ->
  fold_left f (a :: l) e === f a (fold_left f l e).
Proof.
  intros.
  simpl.
  pose proof (proper_fold_left f).
  rewrite H.
  revert a; induction l; intros; simpl.
  + symmetry; auto.
  + rewrite (IHl (f a0 a)), H, (IHl a).
    rewrite H1.
    reflexivity.
Qed.

Lemma monoid_fold_symm: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (e: A) l,
  (forall x, f e x === x) ->
  (forall x, f x e === x) ->
  (forall x y z, f (f x y) z === f x (f y z)) ->
  fold_left f l e === fold_right f e l.
Proof.
  intros.
  pose proof (proper_fold_left f).
  destruct l.
  + simpl.
    reflexivity.
  + simpl.
    rewrite H.
    revert a; induction l; intros; simpl.
    - symmetry; auto.
    - rewrite <- H1.
      apply IHl.
Qed.

Lemma monoid_fold_left_app: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (e: A) l l',
  (forall x, f e x === x) ->
  (forall x, f x e === x) ->
  (forall x y z, f (f x y) z === f x (f y z)) ->
  fold_left f (l ++ l') e === f (fold_left f l e) (fold_left f l' e).
Proof.
  intros.
  rewrite fold_left_app.
  generalize (fold_left f l e) as a; clear l; intros.
  pose proof @monoid_fold_left_head f _ e a l'.
  simpl in H2.
  pose proof (proper_fold_left f).
  rewrite H in H2.
  auto.
Qed.
  
End ListFun1.
