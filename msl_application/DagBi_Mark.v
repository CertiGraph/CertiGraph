Require Import RamifyCoq.lib.Ensembles_ext.
Require Import Coq.Lists.List.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.dag.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.Graph_Mark.
Require Import RamifyCoq.msl_application.GraphBi.
Require Export RamifyCoq.msl_application.GraphBi_Mark.
Require Import Coq.Logic.Classical.

Open Scope logic.

Section PointwiseGraph_Mark_Bi.

Context {pSGG_Bi: pPointwiseGraph_Graph_Bi}.
Context {sSGG_Bi: sPointwiseGraph_Graph_Bi bool unit}.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Notation Graph := (@Graph pSGG_Bi bool unit unit).

Lemma root_unfold: forall (g: Graph) x d l r,
  vvalid g x ->
  vgamma g x = (d, l, r) ->
  reachable_dag_vertices_at x g = vertex_at x (d, l, r) * reachable_through_dag_vertices_at (l :: r :: nil) g.
Proof. apply va_reachable_dag_unfold. Qed.

Lemma root_update_unfold: forall (g: Graph) x d l r v,
  vvalid g x ->
  vgamma g x = (d, l, r) ->
  reachable_dag_vertices_at x (Graph_vgen g x v) = vertex_at x (v, l, r) * reachable_through_dag_vertices_at (l :: r :: nil) g.
Proof. intros. eapply va_reachable_dag_update_unfold; eauto. Qed.

(* TODO: More modularized way to prove these two RamificationPremise? 
 For example, handling pure facts? *)
Lemma dag_ramify_left: forall (g g1: Graph) x l r,
  vvalid g x ->
  vgamma g x = (false, l, r) ->
  mark1 x g g1 ->
  @derives pred _
    (reachable_dag_vertices_at x g1)
    (reachable_dag_vertices_at l g1 *
     (ALL g': Graph,
       !! (mark l g1 g') -->
       (reachable_dag_vertices_at l g' -* reachable_dag_vertices_at x g'))).
Proof.
  intros.
  unfold reachable_dag_vertices_at.
  normalize.
  pose proof proj1 H1.
  rewrite <- H3 in H2.
  assert (localDag g1 l).
  1: {
    rewrite <- H3.
    eapply local_dag_step; eauto.
    eapply gamma_step; eauto.
  }
  rewrite prop_true_andp by auto.
  match goal with
  | |- _ |-- _ * ?A =>
    replace A with
   (ALL g' : Graph ,
      (!!mark l g1 g':pred) -->
      (vertices_at (reachable g' l) g' -*
       vertices_at (reachable g' x) g'))
  end.
  2: {
    apply allp_congr; intros g2.
    apply imp_prop_ext; [reflexivity |].
    intros [_ ?].
    rewrite prop_true_andp by (rewrite <- H5; auto).
    rewrite prop_true_andp by (rewrite <- H5, <- H3; auto).
    reflexivity.
  }
  eapply graph_ramify_left; eauto.
Qed.

Lemma dag_ramify_right: forall (g g1 g2: Graph) x l r,
  vvalid g x ->
  vgamma g x = (false, l, r) ->
  mark1 x g g1 ->
  mark l g1 g2 ->
  (reachable_dag_vertices_at x g2: pred) |-- reachable_dag_vertices_at r g2 *
   (ALL g':Graph,
     !! (mark r g2 g') -->
     (reachable_dag_vertices_at r g' -* reachable_dag_vertices_at x g')).
Proof.
  intros.
  pose proof @graph_ramify_right _ _ g g1 g2 x l r H H0 H1 H2.
  unfold reachable_dag_vertices_at.
  normalize.
  destruct H1 as [? _].
  destruct H2 as [_ ?].
  rewrite <- H2, <- H1 in H4.
  assert (localDag g2 r).
  1: {
    rewrite <- H2, <- H1.
    eapply local_dag_step; eauto.
    eapply gamma_step; eauto.
  }
  rewrite prop_true_andp by auto.

  match goal with
  | |- _ |-- _ * ?A =>
    replace A with
   (ALL  g' : Graph ,
      (!!mark r g2 g':pred) -->
      (vertices_at (reachable g' r) g' -*
       vertices_at (reachable g' x) g'))
  end.
  2: {
    apply allp_congr; intros g3.
    apply imp_prop_ext; [reflexivity |].
    intros [_ ?].
    rewrite prop_true_andp by (rewrite <- H6; auto).
    rewrite prop_true_andp by (rewrite <- H6, <- H2, <- H1; auto).
    reflexivity.
  }
  auto.
Qed.

End PointwiseGraph_Mark_Bi.
