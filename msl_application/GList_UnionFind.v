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
Require Import RamifyCoq.graph.weak_mark_lemmas.
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

  Lemma valid_parent: forall (g: Graph) v n p, vvalid g v -> vgamma g v = (n, p) -> vvalid g p.
  Proof. intros. unfold vgamma in H0. simpl in H0. inversion H0. apply (@all_valid _ _ _ _ g _ (liGraph g)) in H. auto. Qed.

  Lemma parent_loop: forall (g: Graph) v n y, vgamma g v = (n, v) -> reachable g v y -> v = y.
  Proof. intros. apply (lst_self_loop _ (liGraph g)) in H0; auto. unfold vgamma in H. simpl in H. inversion H. rewrite H3. auto. Qed.

  Lemma uf_root_vgamma: forall (g: Graph) v n, vvalid g v -> vgamma g v = (n, v) -> uf_root g v v.
  Proof.
    intros. split.
    - apply reachable_refl; auto.
    - intros. apply (parent_loop g _ n); auto.
  Qed.

End GList_UnionFind.
