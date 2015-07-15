Module Type Mgraphmark.
  Parameter formula : Type.
  Parameter valid : formula -> Prop.
  Parameter node : Type.
  Parameter null_node : node.
  Parameter ptto_node : node -> nat -> node -> node -> formula.
  Parameter A : Type.
  Parameter graph : node -> A -> formula.
  Parameter star : formula -> formula -> formula.
  Parameter and : formula -> formula -> formula.
  Parameter imp : formula -> formula -> formula.
  Parameter ext : (nat -> formula) -> formula.
  Parameter not : formula -> formula.
  Parameter eq : node -> node -> formula.
  Parameter mwand : formula -> formula -> formula.
  Parameter union : formula -> formula -> formula.
  Parameter neq : nat -> nat -> formula.
  Parameter mark : A -> node -> A -> formula.
  Parameter eq_notreach : A -> node -> A -> formula.
  Parameter subset_reach : A -> node -> A -> formula.
  Parameter lookup : A -> node -> nat -> node -> node -> formula.
  Parameter update : A -> node -> nat -> node -> node -> A -> formula.
  Axiom axiom_1 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G r G1) (and (neq v 1) (and (mark G2 l G3) (update G1 x 1 l r G2))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_2 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G l G1) (and (neq v 1) (and (mark G2 r G3) (update G1 x 1 l r G2))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_3 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G r G1) (and (neq v 1) (and (mark G1 l G2) (update G2 x 1 l r G3))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_4 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G l G1) (and (neq v 1) (and (mark G1 r G2) (update G2 x 1 l r G3))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_5 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (update G x 1 l r G1) (and (neq v 1) (and (mark G1 r G2) (mark G2 l G3))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_6 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (update G x 1 l r G1) (and (neq v 1) (and (mark G1 l G2) (mark G2 r G3))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_7 : forall v G x G1 y l r, valid (imp (and (mark G x G1) (lookup G y v l r)) (and (subset_reach G x G1) (and (eq_notreach G x G1) (ext (fun Anon_15 => (lookup G1 y Anon_15 l r)))))).
  Axiom axiom_8 : forall l r x G, valid (imp (lookup G x 1 l r) (mark G x G)).
  Axiom axiom_9 : forall G, valid (mark G null_node G).
  Axiom lem_subgraphupdate_l : forall G v G1 x v1 l r, valid (imp (and (star (graph l G1) (mwand (graph l G) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (subset_reach G l G1) (and (eq_notreach G l G1) (and (lookup G x v l r) (lookup G1 x v1 l r))))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Axiom lem_subgraphupdate_r : forall G v G1 x v1 l r, valid (imp (and (star (graph r G1) (mwand (graph r G) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (subset_reach G r G1) (and (eq_notreach G r G1) (and (lookup G x v l r) (lookup G1 x v1 l r))))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Axiom lem_pttoupdate : forall v G x v1 l r G1, valid (imp (and (star (ptto_node x v1 l r) (mwand (ptto_node x v l r) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (lookup G x v l r) (update G x v1 l r G1))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
End Mgraphmark.
