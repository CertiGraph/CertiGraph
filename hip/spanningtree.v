Module Type Mspanningtree.
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
  Parameter extN: (nat -> formula) -> formula.
  Parameter ext: (node -> formula) -> formula.
  Parameter not : formula -> formula.
  Parameter eq : node -> node -> formula.
  Parameter mwand : formula -> formula -> formula.
  Parameter union : formula -> formula -> formula.
  Parameter neqN : nat -> nat -> formula.
  Parameter neq : node -> node -> formula.
  Parameter eq_notreach : A -> node -> A -> formula.
  Parameter subset_reach : A -> node -> A -> formula.
  Parameter span : A -> node -> A -> formula.
  Parameter lookup : A -> node -> nat -> node -> node -> formula.
  Parameter update : A -> node -> nat -> A -> formula.
  Axiom axiom_1 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (update G x 1 G1) (and (neqN v 1) (and (span G1 l G2) (span G2 r G3))))) (and (span G x G3) (lookup G3 x 1 l r))).
  Axiom axiom_2 : forall v G x G1 y l r, valid (imp (and (span G x G1) (lookup G y v l r)) (and (subset_reach G x G1) (and (eq_notreach G x G1) (extN (fun Anon_20 => (lookup G1 y Anon_20 l r)))))).
  Axiom axiom_3 : forall x G, valid (imp (ext (fun Anon_17 =>  (ext (fun Anon_18 => (lookup G x 1 Anon_17 Anon_18))))) (span G x G)).
  Axiom axiom_4 : forall G, valid (span G null_node G).
  Axiom axiom_5 : forall G x, valid (imp (ext (fun Anon_13 =>  (ext (fun Anon_14 => (lookup G x 0 Anon_13 Anon_14))))) (neq x null_node)).
  Axiom lem_graph_gen_left_null : forall v l r G x v1 G1 l1, valid (imp (and (star (ptto_node x v1 l1 r) (mwand (ptto_node x v l r) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (lookup G x v l r) (update G x v1 G1))) (union (ptto_node x v1 l1 r) (union (graph l1 G1) (graph r G1)))).
  Axiom lem_graph_gen_right_null : forall l1 v l r G x v1 G1 r1, valid (imp (and (star (ptto_node x v1 l r1) (mwand (ptto_node x v l r) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (lookup G x v l r) (update G x v1 G1))) (union (ptto_node x v1 l r1) (union (graph l1 G1) (graph r1 G1)))).
  Axiom lem_pttoupdate : forall v l r G x v1 G1, valid (imp (and (star (ptto_node x v1 l r) (mwand (ptto_node x v l r) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (lookup G x v l r) (update G x v1 G1))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Axiom lem_subgraphupdate_l : forall G v G1 x v1 l r, valid (imp (and (star (graph l G1) (mwand (graph l G) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (subset_reach G l G1) (and (eq_notreach G l G1) (and (lookup G x v l r) (lookup G1 x v1 l r))))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Axiom lem_subgraphupdate_r : forall G v G1 x v1 l r, valid (imp (and (star (graph r G1) (mwand (graph r G) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (subset_reach G r G1) (and (eq_notreach G r G1) (and (lookup G x v l r) (lookup G1 x v1 l r))))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
End Mspanningtree.

