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

  Lemma graph_ramify_aux1': forall (g: Graph) (x l: addr) {V_DEC: Decidable (vvalid g l)},
      vvalid g x -> marked g x -> unmarked g l ->
      step g x l ->
      (graph x g: pred) |-- graph l g *
      ((EX g': Graph, !! spanning_tree g l g' && graph l g') -* (EX g': Graph, !! spanning_tree g l g' && graph x g')).
  Proof.
    intros. apply graph_ramify_aux1; auto.
    + apply RGF.
    + intros. apply RGF.
    + intro y. unfold In. intro. apply edge_reachable with l; auto.
      split; [| split]; auto. apply reachable_head_valid in H3; auto.
    + intros g' ?.
      assert (vvalid g' x). {
        destruct H3 as [_ [[? _] _]].
        specialize (H3 x). simpl in H3. unfold predicate_vvalid in H3.
        assert (vvalid g x /\ ~ g |= l ~o~> x satisfying (unmarked g)). {
          split; auto.
          intro. apply reachable_by_foot_prop in H4.
          unfold unmarked in H4. rewrite negateP_spec in H4.
          tauto.
        }
        rewrite H3 in H4. tauto.
      } split; [split|]; auto.
      - intro y. unfold In. intro. apply edge_reachable with l; auto.
        split; [|split]; auto.
        * apply reachable_head_valid in H5; auto.
        * rewrite step_spec in H2 |- *. destruct H2 as [e [? [? ?]]].
          exists e. destruct H3 as [_ [[? [? [? ?]]] _]].
          specialize (H10 e); specialize (H8 e); specialize (H9 e).
          unfold Graph_SpatialGraph. simpl.
          simpl in H8, H9, H10.
          rewrite <- H9, <- H10.
          split; [| split]; auto.
          unfold predicate_weak_evalid in H8.
          assert (evalid g e /\ ~ g |= l ~o~> src g e satisfying (unmarked g)). {
            split; auto.
            rewrite H6.
            intro. apply reachable_by_foot_prop in H11.
            unfold unmarked in H11. rewrite negateP_spec in H11. tauto.
          }
          rewrite H8 in H11. tauto.
      - destruct H3 as [[? ?] [? ?]].
        specialize (H7 H1). destruct H7.
        split; [|split].
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
