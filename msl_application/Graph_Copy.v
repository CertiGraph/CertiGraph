Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.msl_ext.ramification_lemmas.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.dag.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.graph_morphism.
Require Import RamifyCoq.graph.local_graph_copy.
Require Import RamifyCoq.msl_application.Graph.
Require Import Coq.Logic.Classical.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Local Open Scope logic.

Section SpatialGraph_Copy.

Context {V E: Type}.
Context {SGBA: SpatialGraphBasicAssum V E}.
Context {DV DE: Type}.
Context {GV GE Pred: Type}.
Context {SGP: SpatialGraphPred V E GV GE Pred}.
Context {SGA: SpatialGraphAssum SGP}.
Context {MGS: WeakMarkGraph.MarkGraphSetting DV}.
Context {GMS: GraphMorphism.GraphMorphismSetting DV DE V E}.

Notation Graph := (LabeledGraph V E DV DE).
Notation SGraph := (SpatialGraph V E GV GE).

Variable compute_vgamma: Graph -> V -> GV.
Variable compute_egamma: Graph -> E -> GE.

Hypothesis compute_vgamma_local: forall (G1 G2: Graph) (x: V),
  ((predicate_partial_labeledgraph G1 (eq x)) ~=~ (predicate_partial_labeledgraph G1 (eq x)))%LabeledGraph ->
  compute_vgamma G1 x = compute_vgamma G2 x.

Hypothesis compute_egamma_local: forall (G1 G2: Graph) (e: E),
  evalid G1 e ->
  evalid G2 e ->
  elabel G1 e = elabel G2 e ->
  src G1 e = src G2 e ->
  dst G1 e = dst G2 e ->
  compute_egamma G1 e = compute_egamma G2 e.

Definition Graph_SpatialGraph (G: Graph) : SGraph :=
  Build_SpatialGraph _ _ _ _ _ _ G (compute_vgamma G) (compute_egamma G).

Lemma GSG_VGenPreserve: forall (G: Graph) x lx gx,
  gx = vgamma (Graph_SpatialGraph (labeledgraph_vgen G x lx)) x ->
  (Graph_SpatialGraph (labeledgraph_vgen G x lx)) -=- (spatialgraph_vgen (Graph_SpatialGraph G) x gx).
Proof.
  intros. subst.
  split; [| split].
  + reflexivity.
  + intros; simpl.
    destruct_eq_dec x v.
    - subst; auto.
    - apply compute_vgamma_local; auto.
      eapply si_stronger_partial_labeledgraph_simple; [| apply lg_vgen_stable].
      hnf; unfold Ensembles.In; intros.
      congruence.
  + intros; simpl.
    apply compute_egamma_local; auto.
Qed.

Lemma GSG_PartialGraphPreserve: forall (G: Graph) (p: V -> Prop),
  (predicate_partial_spatialgraph (Graph_SpatialGraph G) p) -=-
  (Graph_SpatialGraph (predicate_partial_labeledgraph G p)).
Proof.
  intros.
  split; [| split].
  + reflexivity.
  + simpl; intros.
    apply compute_vgamma_local; auto.
    reflexivity.
  + simpl; intros.
    apply compute_egamma_local; auto.
    destruct H; auto.
Qed.

Definition vcopy1 x (g1 g2: Graph) :=
  g1 ~=~ g2 /\
  WeakMarkGraph.mark1 x g1 g2 /\
  LocalGraphCopy.vcopy1 x g1 g2.

Definition ecopy1 e (p1 p2: Graph * Graph) :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  WeakMarkGraph.nothing (src g1 e) g1 g2 /\
  LocalGraphCopy.ecopy1 e (g1, pg_lg g1') (g2, pg_lg g2').

Definition copy x (g1 g2: Graph) (g2': Graph) :=
  g1 ~=~ g2 /\
  WeakMarkGraph.mark x g1 g2 /\
  LocalGraphCopy.copy (WeakMarkGraph.unmarked g1) x g1 g2 g2'.

Definition extended_copy x (p1 p2: Graph * Graph) :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  WeakMarkGraph.mark x g1 g2 /\
  LocalGraphCopy.extended_copy (WeakMarkGraph.unmarked g1) x (g1, pg_lg g1') (g2, pg_lg g2').

Definition side_condition (root: V) (l: list E * E) (p1 p2: Graph * Graph) :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  let (es_done, e0) := l in
  let PV1 := WeakMarkGraph.marked g1 in
  let PE1 := Intersection _ (weak_edge_prop (WeakMarkGraph.marked g1) g1) (evalid g1) in
  let PE1_root e := In e es_done in
  let P_rec := WeakMarkGraph.unmarked g1 in
  let PV0 := reachable_by g1 (dst g1 e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g1) (evalid g1) in
  GraphMorphism.disjointed_guard
     (Union _ (image_set (LocalGraphCopy.vmap g2) PV1) (image_set (LocalGraphCopy.vmap g2) (eq root))) (image_set (LocalGraphCopy.vmap g2) PV0)
     (Union _ (image_set (LocalGraphCopy.emap g2) PE1) (image_set (LocalGraphCopy.emap g2) PE1_root)) (image_set (LocalGraphCopy.emap g2) PE0).

Definition edge_copy g e := compond_relation (copy (dst g e)) (ecopy1 e).
  
Definition edge_copy_list g es := relation_list (map (edge_copy g) es).

Lemma vcopy1_edge_copy_list_copy: forall root es (p1 p2: Graph * Graph),
  let (g1, _) := p1 in
  vvalid g1 root ->
  WeakMarkGraph.unmarked g1 root ->
  (forall e, In e es <-> out_edges g1 root e) ->
  relation_list (vcopy1 root :: edge_copy_list g1 es :: nil) p1 p2 ->
  copy root p1 p2.
Admitted.
*)
End SpatialGraph_Copy.