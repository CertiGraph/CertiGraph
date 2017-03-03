Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GList.

Local Open Scope logic.

Section GList_UnionFind.

  Context {pSGG: pSpatialGraph_GList}.
  Context {sSGG: sSpatialGraph_GList nat unit}.

  Local Coercion Graph_LGraph: Graph >-> LGraph.
  Local Coercion LGraph_SGraph: LGraph >-> SGraph.
  Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
  Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
  Local Identity Coercion SGraph_SpatialGraph: SGraph >-> SpatialGraph.
  Local Coercion pg_lg: LabeledGraph >-> PreGraph.

  Notation Graph := (@Graph pSGG nat unit unit).

  Lemma uf_root_vgamma: forall (g: Graph) v n, vvalid g v -> vgamma g v = (n, v) -> uf_root g v v.
  Proof.
    intros. split.
    - apply reachable_refl; auto.
    - intros. apply (parent_loop g _ n); auto.
  Qed.

  Lemma graph_ramify_aux_parent: forall {RamUnit: Type} (g: Graph) x r pa,
      vvalid g x -> vgamma g x = (r, pa) ->
      (reachable_vertices_at x g: pred) |-- reachable_vertices_at pa g *
      (ALL a : RamUnit * addr * Graph, !! (uf_equiv g (snd a) /\ uf_root (snd a) pa (snd (fst a)) /\ rank_unchanged g (snd a)) -->
                                          (vertices_at (reachable g pa) (snd a) -* vertices_at (reachable g x) (snd a))).
  Proof.
    intros. eapply vertices_at_ramif_xQ; auto. eexists; split; [|split].
    - eapply Prop_join_reachable_parent; auto. apply H0.
    - intros. eapply Prop_join_reachable_parent; auto. apply H0.
    - intros. destruct a as [[? rt] g']. rewrite vertices_identical_spec. intros y ?.
      rewrite Intersection_spec in H2. unfold Complement, Ensembles.In in H2.
      destruct H2. simpl in *. destruct H1 as [? [? ?]].
      hnf in H1. 

  Abort.

End GList_UnionFind.
