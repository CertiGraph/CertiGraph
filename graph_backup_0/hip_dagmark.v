Require Import ZArith.

Module Type Mdagmark.
  Parameter formula : Type.
  Parameter valid : formula -> Prop.
  Parameter node : Type.
  Parameter null_node : node.
  Parameter ptto_node : node -> Z -> node -> node -> formula.
  Parameter A : Type.
  Parameter dag : node -> A -> formula.
  Parameter star : formula -> formula -> formula.
  Parameter and : formula -> formula -> formula.
  Parameter imp : formula -> formula -> formula.
  Parameter not : formula -> formula.
  Parameter eq : node -> node -> formula.
  Parameter mwand : formula -> formula -> formula.
  Parameter union : formula -> formula -> formula.
  Parameter neq : Z -> Z -> formula.
  Parameter mark : A -> node -> A -> formula.
  Parameter eq_notreach : A -> node -> A -> formula.
  Parameter subset_reach : A -> node -> A -> formula.
  Parameter lookup : A -> node -> Z -> node -> node -> formula.
  Parameter update : A -> node -> Z -> node -> node -> A -> formula.
  Axiom axiom_1 : forall v D1 D2 D D3 x l r, valid (imp (and (lookup D x v l r) (and (mark D r D1) (and (neq v 1) (and (mark D2 l D3) (update D1 x 1 l r D2))))) (and (mark D x D3) (lookup D3 x 1 l r))).
  Axiom axiom_2 : forall v D1 D2 D D3 x l r, valid (imp (and (lookup D x v l r) (and (mark D l D1) (and (neq v 1) (and (mark D2 r D3) (update D1 x 1 l r D2))))) (and (mark D x D3) (lookup D3 x 1 l r))).
  Axiom axiom_3 : forall v D1 D2 D D3 x l r, valid (imp (and (lookup D x v l r) (and (mark D r D1) (and (neq v 1) (and (mark D1 l D2) (update D2 x 1 l r D3))))) (and (mark D x D3) (lookup D3 x 1 l r))).
  Axiom axiom_4 : forall v D1 D2 D D3 x l r, valid (imp (and (lookup D x v l r) (and (mark D l D1) (and (neq v 1) (and (mark D1 r D2) (update D2 x 1 l r D3))))) (and (mark D x D3) (lookup D3 x 1 l r))).
  Axiom axiom_5 : forall v D1 D2 D D3 x l r, valid (imp (and (lookup D x v l r) (and (update D x 1 l r D1) (and (neq v 1) (and (mark D1 r D2) (mark D2 l D3))))) (and (mark D x D3) (lookup D3 x 1 l r))).
  Axiom axiom_6 : forall v D1 D2 D D3 x l r, valid (imp (and (lookup D x v l r) (and (update D x 1 l r D1) (and (neq v 1) (and (mark D1 l D2) (mark D2 r D3))))) (and (mark D x D3) (lookup D3 x 1 l r))).
  Axiom axiom_7 : forall D x D1, valid (imp (mark D x D1) (and (subset_reach D x D1) (eq_notreach D x D1))).
  Axiom axiom_8 : forall l r x D, valid (imp (lookup D x 1 l r) (mark D x D)).
  Axiom axiom_9 : forall D, valid (mark D null_node D).
  Axiom lem_subdagupdate : forall r D l D1, valid (imp (and (star (dag l D1) (mwand (dag l D) (union (dag l D) (dag r D)))) (and (subset_reach D l D1) (eq_notreach D l D1))) (union (dag l D1) (dag r D1))).
End Mdagmark.
