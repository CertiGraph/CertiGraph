Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.lib.Ensembles_ext.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.Relation_ext.
Require Import CertiGraph.hip.spanningtree.
Require Import CertiGraph.msl_ext.seplog.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.weak_mark_lemmas.
Require Import CertiGraph.graph.path_lemmas.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.graph_relation.
Require Import CertiGraph.graph.subgraph2.
Require Import CertiGraph.graph.reachable_computable.
Require Import CertiGraph.graph.spanning_tree.
Require Import CertiGraph.msl_application.Graph.
Require Import CertiGraph.msl_application.GraphBi.
Require Import CertiGraph.msl_application.Graph_Mark.
Require Import CertiGraph.msl_application.GraphBi_Mark.
Require Import CertiGraph.data_structure.spatial_graph_dispose_bi.
Import CertiGraph.msl_ext.seplog.OconNotation.

Context {pSGG_Bi: pPointwiseGraph_Graph_Bi}.
Context {sSGG_Bi: sPointwiseGraph_Graph_Bi bool unit}.
Context {SGSA: PointwiseGraphStrongAssum SGP}.

Tactic Notation "LEM" constr(v) := (destruct (classic v); auto).

Module SpanningTree <: Mspanningtree.
  Definition formula : Type := pred.
  Definition valid : formula -> Prop := fun f => TT |-- f.
  Definition node : Type := addr.
  Definition null_node : node := null.
  Definition ptto_node : node -> bool -> node -> node -> formula := fun v d l r => vertex_at v (d, l, r).
  Definition A : Type := (@Graph _ bool unit).
  Definition graph : node -> A -> formula := fun x g => (@reachable_vertices_at _ _ _ _ _ _ _ _ _ SGP _ x (Graph_LGraph g)).
  Definition star : formula -> formula -> formula := sepcon.
  Definition and : formula -> formula -> formula := andp.
  Definition imp : formula -> formula -> formula := imp.
  Definition extN: (bool -> formula) -> formula := exp.
  Definition ext : (node -> formula) -> formula := exp.
  Definition not : formula -> formula := fun f => prop (f |-- FF).
  Definition eq : node -> node -> formula := fun a b => prop (a = b).
  Definition mwand : formula -> formula -> formula := ewand.
  Definition union : formula -> formula -> formula := ocon.
  Definition neqN : bool -> bool -> formula := fun a b => prop (~ a = b).
  Definition neq : node -> node -> formula := fun a b => prop (~ a = b).
  Definition eq_notreach : A -> node -> A -> formula :=
    fun g1 n g2 => prop ((predicate_partial_labeledgraph (Graph_LGraph g1) (Complement _ (reachable (pg_lg (Graph_LGraph g1)) n))) ~=~ (predicate_partial_labeledgraph (Graph_LGraph g2) (Complement _ (reachable (pg_lg (Graph_LGraph g2)) n)))%LabeledGraph).
  Definition subset_reach : A -> node -> A -> formula := fun g1 n g2 => prop (Included (reachable (pg_lg (Graph_LGraph g1)) n) (reachable (pg_lg (Graph_LGraph g2)) n)).
  Definition span : A -> node -> A -> formula := fun g1 n g2 => prop (spanning_tree g1 n g2).
  Definition lookup : A -> node -> bool -> node -> node -> formula :=
    fun g x d l r => prop (vlabel (Graph_LGraph g) x = d /\ vvalid (pg_lg (Graph_LGraph g)) x /\
                           vvalid (pg_lg (Graph_LGraph g)) l /\ vvalid (pg_lg (Graph_LGraph g)) r /\
                           dst (pg_lg (Graph_LGraph g)) (x, L) = l /\ dst (pg_lg (Graph_LGraph g)) (x, R) = r).
  Definition update : A -> node -> bool -> A -> formula := fun g1 x d g2 => prop (Graph_vgen g1 x d = g2).
    
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
  
  
End SpanningTree.
