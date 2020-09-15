Require Import VST.veric.SeparationLogic.
Require Import CertiGraph.floyd_ext.share.
Require Import CertiGraph.dijkstra.env_dijkstra_arr.
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Import CertiGraph.graph.AdjMatGraph.

Local Open Scope logic.

Lemma elabel_Znth_graph_to_mat:
  forall inf size (g: (DijkGG inf size)) src dst,
    vvalid g src ->
    vvalid g dst ->
    elabel g (src, dst) =
    Znth dst (Znth src (@graph_to_mat size g id)).
Proof.
  intros.
  rewrite (vvalid_meaning g) in H, H0.
  unfold graph_to_mat.
  apply elabel_Znth_graph_to_mat with (f:=id); trivial.
  lia.
Qed.

Definition DijkGraph sh cs g gaddr size : mpred := @SpaceAdjMatGraph size sh cs id g gaddr.
