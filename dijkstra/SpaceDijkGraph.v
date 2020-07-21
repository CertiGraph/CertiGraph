Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.dijkstra.env_dijkstra_arr.
Require Import RamifyCoq.dijkstra.MathDijkGraph.
Require Import RamifyCoq.graph.AdjMatGraph.

Local Open Scope logic.

(* sugared version so as not to break Dijk *)
(* massage away. even if needed, this is a LEMMA and not a definition *)
Definition inrange_graph g :=
  let grph_contents := (@graph_to_mat SIZE g id) in
  forall i j,
    vvalid g i ->
    vvalid g j ->
    0 <= elabel g (j, i) <= Int.max_signed / SIZE \/
    elabel g (j, i) = inf.

(*
(* sugared version so as not to break Dijk *)
Lemma graph_to_mat_Zlength:
  forall g,
    Zlength (@graph_to_mat SIZE g id) = SIZE.
Proof.
  intros. unfold graph_to_mat.
  apply graph_to_mat_Zlength_gen. unfold SIZE. lia.
Qed. 
 *)

(* sugared version so as not to break Dijk *)
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

 Lemma inrange_graph_cost_pos: forall g e,
     sound_dijk_graph g ->
     inrange_graph g ->
     evalid g e ->
     0 <= elabel g e.
Proof.
  intros. rewrite (surjective_pairing e) in *.
  destruct H as [? [? _]].
  red in H2, H. rewrite H2 in H1. destruct H1.
  red in H0.
  specialize (H0 _ _ H3 H1).
  destruct H0.
  destruct H0; trivial.
  unfold V, E in *. rewrite H0. compute; inversion 1. 
Qed.

Definition DijkGraph sh g gaddr : mpred := @SpaceAdjMatGraph SIZE sh _ id g gaddr.

