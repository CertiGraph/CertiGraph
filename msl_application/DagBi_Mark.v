Require Import RamifyCoq.lib.Ensembles_ext.
Require Import Coq.Lists.List.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
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
Require Import RamifyCoq.msl_application.GraphBi.
Require Import RamifyCoq.msl_application.Graph_Mark.
Require Export RamifyCoq.msl_application.GraphBi_Mark.
Require Import Coq.Logic.Classical.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Open Scope logic.

Instance MGS: WeakMarkGraph.MarkGraphSetting bool.
  apply (WeakMarkGraph.Build_MarkGraphSetting bool
          (eq true)).
  intros.
  destruct x; [left | right]; congruence.
Defined.

Section SpatialGraph_Mark_Bi.

Context {pSGG_Bi: pSpatialGraph_Graph_Bi}.
Context {sSGG_Bi: sSpatialGraph_Graph_Bi bool unit}.

Notation Graph := (@Graph pSGG_Bi bool unit).

Lemma dag_unfold: forall (g: Graph) x d l r,
  sepcon_unique2 (@vertex_at _ _ _ _ _ SGP) ->
  vvalid g x ->
  vgamma g x = (d, l, r) ->
  dag x g = vertex_at x (vgamma g x) * dags' (l :: r :: nil) g.
Proof.
  intros.
  apply dag_unfold; auto.
  eapply gamma_step_list; eauto.
Qed.

Lemma dag_vgen: forall (g: Graph) x d l r v,
  sepcon_unique2 (@vertex_at _ _ _ _ _ SGP) ->
  vvalid g x ->
  vgamma g x = (d, l, r) ->
  dag x (spatialgraph_vgen g x v) = vertex_at x v * dags' (l :: r :: nil) g.
Proof.
  intros.
  apply dag_vgen; auto.
  eapply gamma_step_list; eauto.
Qed.

Lemma dag_ramify_left: forall {RamUnit: Type} (g g1: Graph) x l r,
  vvalid g x ->
  vgamma g x = (false, l, r) ->
  mark1 x g g1 ->
  (dag x g1: pred) |-- dag l g1 *
   (ALL a: RamUnit * Graph,
     !! (mark l g1 (snd a)) -->
     (dag l (snd a) -* dag x (snd a))).
Proof.
  intros.
  unfold dag.
  normalize.
  pose proof proj1 H1.
  rewrite <- H3 in H2.
  assert (localDag g1 l).
  Focus 1. {
    rewrite <- H3.
    eapply local_dag_step; eauto.
    eapply gamma_step; eauto.
  } Unfocus.
  rewrite prop_true_andp by auto.
  match goal with
  | |- _ |-- _ * ?A =>
    replace A with
   (ALL  a : RamUnit * Graph ,
      (!!mark l g1 (snd a):pred) -->
      (vertices_at (reachable (snd a) l) (snd a) -*
       vertices_at (reachable (snd a) x) (snd a)))
  end.
  Focus 2. {
    apply allp_congr; unfold snd; intros [_ g2].
    apply imp_prop_ext; [reflexivity |].
    intros [_ ?].
    rewrite prop_true_andp by (rewrite <- H5; auto).
    rewrite prop_true_andp by (rewrite <- H5, <- H3; auto).
    reflexivity.
  } Unfocus.
  eapply graph_ramify_left; eauto.
Qed.

Lemma dag_ramify_right: forall {RamUnit: Type} (g g1 g2: Graph) x l r,
  vvalid g x ->
  vgamma g x = (false, l, r) ->
  mark1 x g g1 ->
  mark l g1 g2 ->
  (dag x g2: pred) |-- dag r g2 *
   (ALL a: RamUnit * Graph,
     !! (mark r g2 (snd a)) -->
     (dag r (snd a) -* dag x (snd a))).
Proof.
  intros.
  pose proof @graph_ramify_right _ _ RamUnit g g1 g2 x l r H H0 H1 H2.
  unfold dag.
  normalize.
  destruct H1 as [? _].
  destruct H2 as [_ ?].
  rewrite <- H2, <- H1 in H4.
  assert (localDag g2 r).
  Focus 1. {
    rewrite <- H2, <- H1.
    eapply local_dag_step; eauto.
    eapply gamma_step; eauto.
  } Unfocus.
  rewrite prop_true_andp by auto.

  match goal with
  | |- _ |-- _ * ?A =>
    replace A with
   (ALL  a : RamUnit * Graph ,
      (!!mark r g2 (snd a):pred) -->
      (vertices_at (reachable (snd a) r) (snd a) -*
       vertices_at (reachable (snd a) x) (snd a)))
  end.
  Focus 2. {
    apply allp_congr; unfold snd; intros [_ g3].
    apply imp_prop_ext; [reflexivity |].
    intros [_ ?].
    rewrite prop_true_andp by (rewrite <- H6; auto).
    rewrite prop_true_andp by (rewrite <- H6, <- H2, <- H1; auto).
    reflexivity.
  } Unfocus.
  auto.
Qed.

End SpatialGraph_Mark_Bi.


