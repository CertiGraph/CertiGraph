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

End SpatialGraph_Copy.