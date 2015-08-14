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
  
  Context {SGG_Bi: SpatialGraph_Graph_Bi}.

  Local Open Scope logic.

  Existing Instances SGGS_Bi SGP SGA.

  Lemma graph_ramify_aux1': forall (g: Graph) (x l: addr) {V_DEC: Decidable (vvalid g l)},
      vvalid g x -> marked g x ->
      step g x l ->
      (graph x g: pred) |-- graph l g *
      ((EX g': Graph, !! spanning_tree g l g' && graph l g') -* (EX g': Graph, !! spanning_tree g l g' && graph x g')).
  Proof.
    intros. apply graph_ramify_aux1; auto.
    + apply RGF.
    + intros. apply RGF.
    + intro y. unfold In. intro. apply edge_reachable with l; auto.
      split; [| split]; auto. apply reachable_head_valid in H2; auto.
    + intros g' ?.
      assert (vvalid g' x). {
        destruct H2 as [_ [[? _] _]].
        specialize (H2 x). simpl in H2. unfold predicate_vvalid in H2.
        assert (vvalid g x /\ ~ g |= l ~o~> x satisfying (unmarked g)). {
          split; auto.
          intro. apply reachable_by_foot_prop in H3.
          unfold unmarked in H3. rewrite negateP_spec in H3.
          tauto.
        }
        rewrite H2 in H3. tauto.
      } split; [split|]; auto.
      - intro y. unfold In. intro. apply edge_reachable with l; auto.
        split; [|split]; auto.
        * apply reachable_head_valid in H4; auto.
        * rewrite step_spec in H1 |- *. destruct H1 as [e [? [? ?]]].
          exists e. destruct H2 as [_ [[? [? [? ?]]] _]].
          specialize (H7 e); specialize (H8 e); specialize (H9 e).
          (* Set Printing All. *)
          unfold Graph_SpatialGraph. simpl.
          simpl in H7, H8, H9.
          rewrite <- H8, <- H9.
          split; [| split]; auto.
          unfold predicate_weak_evalid in H7.
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
