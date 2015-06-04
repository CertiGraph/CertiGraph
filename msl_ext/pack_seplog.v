Require Import VST.msl.base.
Require Import VST.msl.sepalg.
Require Import VST.msl.sepalg_generators.

Section SepAlgPack.

  Variable A : Type.
  Variable JA : Join A.

  Inductive Tree : Type :=
  | Leaf: A -> Tree
  | Node: list (prod Tree nat) -> Tree.

  Definition Forest : Type := list (prod Tree nat).

  Inductive flattenR : Tree -> list A -> Prop :=
  | leafR : forall a, flattenR (Leaf a) (a :: nil)
  | nodeR : forall f l, flattenRForest f l -> flattenR (Node f) l
  with flattenRForest : list (prod Tree nat) -> list A -> Prop :=
  | forestR_nil: flattenRForest nil nil
  | forestR_cons: forall t n l0 f l, flattenR t l0 -> flattenRForest f l -> flattenRForest ((t, n) :: f) (l0 ++ l).

  Inductive decreaseLH : list (prod Tree nat) -> nat -> Prop :=
  | decreaseL_nil: forall n, decreaseLH nil n
  | decreaseL_cons: forall t n0 n l, n > n0 -> decreaseLH l n0 -> decreaseLH ((t, n0) :: l) n.

  Inductive decreaseL : list (prod Tree nat) -> Prop := decrease_intro: forall n f, decreaseLH f n -> decreaseL f.

  Inductive decreaseTree : Tree -> Prop :=
  | leafD : forall a, decreaseTree (Leaf a)
  | nodeD : forall f, decreaseL f -> Forall decreaseTree (fst (split f)) -> decreaseTree (Node f).

  Definition decreaseForest : Forest -> Prop := fun f => Forall decreaseTree (fst (split f)).

  Fixpoint iter_joinable (l : list A) (u : A) (j : A) : Prop :=
    match l with
      | nil => u = j
      | x :: l' => exists j', iter_joinable l' u j' /\ join x j' j
    end.

  Definition legal (f : Forest) (u : A) : Prop := decreaseForest f /\ exists l j, flattenRForest f l /\ iter_joinable l u j.

  Record NodeOfSA := mkNodeOfSA {
                         f : Forest;
                         u : A;
                         H : legal f u
                       }.

End SepAlgPack.



