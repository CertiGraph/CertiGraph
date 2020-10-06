Require Import CertiGraph.dijkstra.dijkstra_env.
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Import CertiGraph.dijkstra.dijkstra_constants.
Require Export CertiGraph.graph.SpaceAdjMatGraph3.

Local Open Scope logic.

Section SpaceDijkGraph.

  Context {V_EqDec : EquivDec.EqDec V eq}. 
  Context {E_EqDec : EquivDec.EqDec E eq}. 

  Lemma elabel_Znth_graph_to_mat:
    forall (g: @DijkGG size inf) src dst,
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

  Definition DijkGraph sh cs g g_ptr size (addresses: list val) : mpred := @SpaceAdjMatGraph size cs sh id g g_ptr.
  (* "addresses" is accepted but not used *)
  (* the user should just give a nil list *)

End SpaceDijkGraph.
