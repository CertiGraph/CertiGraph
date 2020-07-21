Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.dijkstra.env_dijkstra_arr.
Require Import RamifyCoq.dijkstra.MathDijkGraph.
Require Import RamifyCoq.graph.AdjMatGraph.

Local Open Scope logic.

Lemma elabel_Znth_graph_to_mat:
  forall (g: DijkstraGeneralGraph) src dst,
    sound_dijk_graph g ->
    evalid g (src, dst) ->
    elabel g (src, dst) =
    Znth dst (Znth src (@graph_to_mat SIZE g id)).
Proof.
  intros.
  destruct H as [? [? _]].
  red in H, H1. rewrite H1, H, H in H0. destruct H0.
  unfold graph_to_mat. replace (src, dst) with (id (src, dst)) by trivial.
  apply elabel_Znth_graph_to_mat; trivial. lia.
Qed.

Definition DijkGraph sh g gaddr : mpred := @SpaceAdjMatGraph SIZE sh _ id g gaddr.

