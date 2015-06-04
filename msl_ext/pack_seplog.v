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

  Definition Legal (f : Forest) (u : A) : Prop := decreaseForest f /\ exists l j, flattenRForest f l /\ iter_joinable l u j.

  Lemma Legal_nil: forall u, Legal nil u.
  Proof.
    intros.
    split.
    + constructor.
    + exists nil, u.
      split.
      - constructor.
      - simpl; auto.
  Defined.

  Record PackNode := mkNodeOfSA {
                         f : Forest;
                         u : A;
                         legal : Legal f u
                       }.

  Definition mergeR (F1 F2 F: Forest) := forall T, In T F <-> (In T F1 \/ In T F2).

  Inductive join_Pack: PackNode -> PackNode -> PackNode -> Prop :=
  | join_Pack_constr: forall fx fy fz u lx ly lz,
     mergeR fx fy fz ->
     join_Pack (mkNodeOfSA fx u lx) (mkNodeOfSA fy u ly) (mkNodeOfSA fz u lz).

  Definition core_Pack (x: PackNode) : PackNode :=
    match x with
    | mkNodeOfSA f u legal => mkNodeOfSA nil u (Legal_nil u)
    end.

  Instance Join_Pack: Join PackNode := join_Pack.

  Instance Perm_Pack: Perm_alg PackNode.
  Proof.
    constructor.

    (* join_eq *)
    intros.
    unfold join, Join_Pack in *.
    destruct x, y, z, z'.
    inversion H; clear H;
    inversion H0; clear H0.
    subst; subst u3.
    f_equal.
  Abort.
End SepAlgPack.



