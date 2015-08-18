Require Import Coq.Sets.Ensembles.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require RamifyCoq.graph.marked_graph. Import RamifyCoq.graph.marked_graph.MarkGraph.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.spanning_tree.
Require Import RamifyCoq.data_structure.general_spatial_graph.
Require Import RamifyCoq.data_structure.spatial_graph_bi.

Instance MGS: MarkGraphSetting bool.
  apply (Build_MarkGraphSetting bool
          (eq true)
          (fun _ => true)
          (fun _ => false));
  intros.
  + destruct x; [left | right]; congruence.
  + auto.
  + congruence.
Defined.

Section SPATIAL_GRAPH_DISPOSE_BI.
  
  Context {pSGG_Bi: pSpatialGraph_Graph_Bi}.
  Context {sSGG_Bi: sSpatialGraph_Graph_Bi}.

  Local Open Scope logic.

  (* Existing Instances SGP SGA. *)

  Lemma graph_ramify_aux1': forall (g: Graph) (x l: addr) (P : addr -> Prop) {V_DEC: Decidable (vvalid g l)},
      vvalid g x -> marked g x -> unmarked g l ->
      step g x l -> Included (reachable g l) P -> Included P (vvalid g) ->
      (vertices_at g P : pred) |-- graph l g *
      ((EX g': Graph, !! spanning_tree g l g' && vertices_at g' (reachable g l)) -*
       (EX g': Graph, !! spanning_tree g l g' && vertices_at g' P)).
  Proof.
    intros. apply existential_partialgraph_update_prime; auto.
    + intro. apply RFG_reachable_decicable'. apply RGF. auto.
    + intros; apply H3. auto.
    + intros g' y ? ?. apply H4 in H6. unfold In in H6.
      admit.
    + intros g' ?.
  Abort.

  Lemma graph_ramify_aux1_left: forall (g: Graph) x d l r,
      vvalid g x ->
      vgamma g x = (d, l, r) ->
      (graph x g: pred) |-- graph l g *
      ((EX g': Graph, !! spanning_tree g l g' && graph l g') -* (EX g': Graph, !! spanning_tree g l g' && graph x g')).
  Proof.
  Abort.
  (* graph_ramify_aux1 *)
  
  (* graph sh x g1 *)
  (*  |-- graph sh l g1 * *)
  (*      ((EX  x0 : Graph, !!spanning_tree g1 l x0 && graph sh l x0) -* *)
  (*       (EX  x0 : Graph, !!spanning_tree g1 l x0 && graph sh x x0)) *)

End SPATIAL_GRAPH_DISPOSE_BI.
