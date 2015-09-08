Require Import Coq.Sets.Ensembles.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require RamifyCoq.graph.marked_graph. Import RamifyCoq.graph.marked_graph.MarkGraph.
Require Import RamifyCoq.Coqlib.
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

  Existing Instances maGraph biGraph finGraph.

  Local Open Scope logic.

  (* Existing Instances SGP SGA SGBA. *)

  Lemma edge_spanning_tree_left_null:
    forall (g: Graph) x d l r, vgamma g x = (d, l, r) -> (marked g) l -> edge_spanning_tree g (x, L) (Graph_gen_left_null g x).
  Proof.
    intros. assert (l = dst g (x, L)) by (simpl in H; unfold gamma in H; inversion H; auto).
    hnf. destruct (node_pred_dec (marked g) (dst g (x, L))). 2: subst l; exfalso; auto.
    split.
    + hnf. simpl. split; [| split; [|split; [| split]]]; [tauto | tauto | tauto | | ].
      - intros. unfold graph_gen.update_dst.
        destruct (equiv_dec (x, L) e); intuition.
      - unfold strong_evalid. simpl. intro. destruct H2 as [? [? ?]].
        unfold graph_gen.update_dst in H4.
        destruct (equiv_dec (x, L) (x, L)); intuition.
        apply (valid_not_null g) in H4; auto. rewrite is_null_def. auto.
    + simpl. tauto.
  Qed.

  Lemma graph_gen_left_null_ramify:
    forall (g: Graph) (x : addr) d (l r : addr),
      vvalid g x -> vgamma g x = (d, l, r) ->
      (graph x g : pred) |-- vertex_at x (d, l, r) * (vertex_at x (d, null, r) -* vertices_at (reachable g x) (Graph_gen_left_null g x)).
  Proof.
    intros.
    replace (@vertex_at _ _ _ _ _ SGP x (d, l, r)) with (graph_cell g x).
    Focus 2. {
      unfold graph_cell; simpl.
      simpl in H0; rewrite H0; auto.
    } Unfocus.
    replace (@vertex_at _ _ _ _ _ SGP x (d, null, r)) with (graph_cell (Graph_gen_left_null g x) x).
    Focus 2. {
      unfold graph_cell; simpl.
      unfold gamma. simpl.
      unfold graph_gen.update_dst.
      destruct_eq_dec (x, L) (x, L). 2: exfalso; auto.
      destruct_eq_dec (x, L) (x, R). inversion H2.
      simpl in H0; unfold gamma in H0. inversion H0; auto.
    } Unfocus.
    apply iter_sepcon.pred_sepcon_ramify1; auto.
    + apply reachable_by_reflexive; auto.
    + intuition.
    + intros. unfold graph_cell; simpl.
      unfold gamma; simpl. unfold graph_gen.update_dst.
      destruct_eq_dec (x, L) (y, L). inversion H2. exfalso; auto.
      destruct_eq_dec (x, L) (y, R). inversion H3. auto.
  Qed.

   (*   general_spatial_graph.graph x g1 *)
   (* |-- general_spatial_graph.graph l g1 * *)
   (*     ((EX  x0 : Graph, *)
   (*       !!spanning_tree g1 l x0 && *)
   (*       general_spatial_graph.vertices_at (reachable g1 l) x0) -* *)
   (*      (EX  x0 : Graph, *)
   (*       !!edge_spanning_tree g1 (x, L) x0 && *)
   (*       general_spatial_graph.vertices_at (reachable g1 x) x0)) *)


  Lemma graph_ramify_aux1': forall (g: Graph) (l: addr) (e: addr * LR) (P : addr -> Prop) {V_DEC: Decidable (vvalid g l)},
      unmarked g l -> l = dst g e ->
      Included (reachable g l) P -> Included P (vvalid g) ->
      (forall gg, spanning_tree g l gg -> edge_spanning_tree g e gg) ->
      (vertices_at P g: pred) |-- graph l g *
      ((EX g': Graph, !! spanning_tree g l g' && vertices_at (reachable g l) g') -*
       (EX g': Graph, !! edge_spanning_tree g e g' && vertices_at P g')).
  Proof.
    intros. apply existential_partialgraph_update_prime'; auto.
    + intros. apply RFG_reachable_decicable'. apply RGF. auto.
    + intros. apply H1. auto.
    + intros g' y ? ?. apply H2 in H5. unfold In in H5.
      rewrite <- (spanning_tree_vvalid g l g'); auto.
      apply Graph_reachable_by_dec; auto.
    + intros g' ?. destruct H4 as [[? ?] [? ?]]. specialize (H7 H).
      destruct H7. apply Graph_partialgraph_vi_spec.
      - apply si_stronger_partialgraph_simple with (fun n : addr => ~ g |= l ~o~> n satisfying (unmarked g)); auto.
        intro v. unfold In. intro. destruct H9.
        intro. apply H10. apply reachable_by_is_reachable in H11. auto.
      - intros. specialize (H5 v).
        assert (~ g |= l ~o~> v satisfying (unmarked g)). {
          intro. destruct H12. apply H14.
          apply reachable_by_is_reachable in H13. auto.
        } specialize (H5 H13). simpl in H5.
        destruct (vlabel g v), (vlabel g' v); try tauto.
        symmetry. tauto.
  Qed.

  Lemma graph_ramify_aux1_left: forall (g: Graph) x d l r,
      vvalid g x -> unmarked g l ->
      vgamma g x = (d, l, r) ->
      (forall gg, spanning_tree g l gg -> edge_spanning_tree g (x, L) gg) ->
      (graph x g: pred) |-- graph l g *
      ((EX g': Graph, !! spanning_tree g l g' && vertices_at (reachable g l) g') -*
       (EX g': Graph, !! edge_spanning_tree g (x, L) g' && vertices_at (reachable g x) g')).
  Proof.
    intros. apply graph_ramify_aux1'; auto.
    + apply weak_valid_vvalid_dec. apply (gamma_left_weak_valid g x d l r); auto.
    + simpl in H1. unfold gamma in H1. inversion H1; auto.
    + intros v. unfold In. intro. apply edge_reachable with l; auto. split; [| split]; auto.
      - apply reachable_head_valid in H3; auto.
      - rewrite (gamma_step g x d l r); auto.
    + intro v. unfold In. intro. apply reachable_foot_valid in H3. auto.
  Qed.

  Lemma edge_spanning_tree_left_vvalid: forall (g1 g2: Graph) x d l r n,
      vvalid g1 x -> vgamma g1 x = (d, l, r) -> edge_spanning_tree g1 (x, L) g2 -> (vvalid g1 n <-> vvalid g2 n).
  Proof.
    intros. apply (edge_spanning_tree_vvalid g1 g2 (x, L) n); auto.
    apply Graph_reachable_by_dec. apply weak_valid_vvalid_dec.
    apply (gamma_left_weak_valid g1 x d _ r); auto.
    assert (l = dst g1 (x, L)) by (simpl in H0; unfold gamma in H0; inversion H0; auto).
    rewrite <- H2. auto.
  Qed.

  Lemma edge_spanning_tree_left_reachable_vvalid: forall (g1 g2: Graph) x d l r,
      vvalid g1 x -> vgamma g1 x = (d, l, r) -> edge_spanning_tree g1 (x, L) g2 -> Included (reachable g1 x) (vvalid g2).
  Proof.
    intros. assert (x = src g1 (x, L)) by (symmetry; apply (@left_sound _ _ _ _ _ _ g1 (biGraph g1) x)).
    rewrite H2. apply edge_spanning_tree_reachable_vvalid; auto.
    apply Graph_reachable_by_dec. apply weak_valid_vvalid_dec.
    apply (gamma_left_weak_valid g1 x d _ r); auto.
    assert (l = dst g1 (x, L)) by (simpl in H0; unfold gamma in H0; inversion H0; auto).
    rewrite <- H3. auto.
  Qed.

  (* Lemma graph_ramify_aux1_right: forall (g: Graph) x d l r, *)
  (*     vvalid g x -> unmarked g r -> *)
  (*     vgamma g x = (d, l, r) -> *)
  (*     (graph x g: pred) |-- graph l g * *)
  (*     ((EX g': Graph, !! spanning_tree g l g' && vertices_at g' (reachable g l)) -* *)
  (*      (EX g': Graph, !! spanning_tree g l g' && vertices_at g' (reachable g x))). *)
  
End SPATIAL_GRAPH_DISPOSE_BI.
