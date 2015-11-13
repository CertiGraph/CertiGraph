Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require RamifyCoq.graph.marked_graph. Import RamifyCoq.graph.marked_graph.WeakMarkGraph.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import Coq.Lists.List.
Require Import RamifyCoq.msl_ext.ramification_lemmas.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.spanning_tree.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GraphBi.

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
    forall (g: Graph) x d l r, vvalid g x -> vgamma g x = (d, l, r) -> (marked g) l ->
                               edge_spanning_tree g (x, L) (Graph_gen_left_null g x).
  Proof.
    intros. assert (l = dst g (x, L)) by (simpl in H0; unfold gamma in H0; inversion H0; auto).
    hnf. destruct (node_pred_dec (marked g) (dst g (x, L))). 2: subst l; exfalso; auto.
    split.
    + hnf. simpl. split; [| split; [|split; [| split]]]; [tauto | tauto | tauto | | ].
      - intros. unfold graph_gen.update_dst.
        destruct (equiv_dec (x, L) e); intuition.
      - right. unfold graph_gen.update_dst.
        destruct (equiv_dec (x, L) (x, L)); intuition.
        * apply (valid_not_null g) in H3; auto. rewrite is_null_def. auto.
        * apply (@left_valid _ _ _ _ g _ _ (biGraph g)) in H; auto.
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
    apply pred_sepcon_ramify1; auto.
    + apply reachable_by_refl; auto.
    + intuition.
    + intros. unfold graph_cell; simpl.
      unfold gamma; simpl. unfold graph_gen.update_dst.
      destruct_eq_dec (x, L) (y, L). inversion H2. exfalso; auto.
      destruct_eq_dec (x, L) (y, R). inversion H3. auto.
  Qed.

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
    + intros g' ?. destruct H4 as [[? ?] [? [? ?]]]. specialize (H7 H).
      destruct H7. apply Graph_partialgraph_vi_spec.
      - apply si_stronger_partialgraph_simple with (fun n : addr => ~ g |= l ~o~> n satisfying (unmarked g)); auto.
        intro v. unfold In. intro. destruct H10.
        intro. apply H11. apply reachable_by_is_reachable in H12. auto.
      - intros. specialize (H5 v).
        assert (~ g |= l ~o~> v satisfying (unmarked g)). {
          intro. destruct H13. apply H15.
          apply reachable_by_is_reachable in H14. auto.
        } specialize (H5 H14). simpl in H5.
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

  Lemma edge_spanning_tree_right_vvalid: forall (g1 g2: Graph) x d l r n,
      vvalid g1 x -> vgamma g1 x = (d, l, r) -> edge_spanning_tree g1 (x, R) g2 -> (vvalid g1 n <-> vvalid g2 n).
  Proof.
    intros. apply (edge_spanning_tree_vvalid g1 g2 (x, R) n); auto.
    apply Graph_reachable_by_dec. apply weak_valid_vvalid_dec.
    apply (gamma_right_weak_valid g1 x d l _); auto.
    assert (r = dst g1 (x, R)) by (simpl in H0; unfold gamma in H0; inversion H0; auto).
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

  Lemma edge_spanning_tree_left_vgamma: forall (g1 g2: Graph) x l r,
      vvalid g1 x -> vgamma g1 x = (true, l, r) -> edge_spanning_tree g1 (x, L) g2 -> exists l', vgamma g2 x = (true, l', r).
  Proof.
    intros. simpl. unfold gamma. exists (dst g2 (x, L)).
    assert (Hvg2: vvalid g2 x) by (rewrite <- edge_spanning_tree_left_vvalid; eauto).
    unfold edge_spanning_tree in H1. destruct (node_pred_dec (marked g1) (dst g1 (x, L))).
    + destruct H1 as [[_ [_ [_ [? _]]]] ?]. simpl in H0, H2. unfold gamma in H0. inversion H0.
      rewrite H4. symmetry in H4. rewrite H2 in H4. rewrite <- H4. f_equal. symmetry. apply H1.
      - intro. inversion H3.
      - apply (@right_valid _ _ _ _ g1 _ _ (biGraph g1)) in H; auto.
      - apply (@right_valid _ _ _ _ g2 _ _ (biGraph g2)) in Hvg2; auto.
    + destruct H1 as [[_ ?] [[_ [_ [_ ?]]] _]].
      assert (marked g1 x) by (simpl in *; unfold gamma in H0; inversion H0; auto).
      assert (~ g1 |= dst g1 (x, L) ~o~> x satisfying (unmarked g1)) by (intro HS; apply reachable_by_foot_prop in HS; auto).
      assert (marked g2 x) by (rewrite <- H1; auto).
      simpl in H5. rewrite <- H5. f_equal.
      simpl in H2. unfold predicate_weak_evalid in H2.
      simpl in H0. unfold gamma in H0. inversion H0. symmetry. apply H2; split.
      - apply (@right_valid _ _ _ _ g1 _ _ (biGraph g1) x); auto.
      - rewrite (@right_sound _ _ _ _ _ _ g1 (biGraph g1) x). auto.
      - apply (@right_valid _ _ _ _ g2 _ _ (biGraph g2) x); auto.
      - rewrite (@right_sound _ _ _ _ _ _ g2 (biGraph g2) x). auto.
  Qed.

  Lemma spanning_tree_left_reachable:
    forall (g1 g2: Graph) x l r, vvalid g1 x -> vvalid g1 r -> vgamma g1 x = (true, l, r) ->
                                 spanning_tree g1 l g2 -> Included (reachable g2 r) (reachable g1 x).
  Proof.
    intros. intro v. unfold Ensembles.In . intros.
    assert (X: ReachDecidable g1 l (unmarked g1)). {
      apply Graph_reachable_by_dec.
      apply weak_valid_vvalid_dec.
      apply (gamma_left_weak_valid g1 x true l r); auto.
    } destruct (X v).
    + apply reachable_by_is_reachable in r0. apply edge_reachable_by with l; auto. split; [|split]; auto.
      - apply reachable_head_valid in r0. auto.
      - simpl in H1. unfold gamma in H1. inversion H1. exists (x, L); auto.
        * apply (@left_valid _ _ _ _ g1 _ _ (biGraph g1)); auto.
        * apply (@left_sound _ _ _ _ _ _ g1 (biGraph g1)).
    + apply edge_reachable_by with r; auto.
      - split; [|split]; auto. rewrite (gamma_step g1 x true l r); auto.
      - apply (spanning_tree_not_reachable g1 l g2 r v) in H3; auto.
        rewrite reachable_by_eq_partialgraph_reachable in H3.
        destruct H2 as [? [? ?]]. rewrite <- H4 in H3.
        rewrite <- reachable_by_eq_partialgraph_reachable in H3.
        apply reachable_by_is_reachable in H3. apply H3.
  Qed.

  Lemma edge_spanning_tree_left_reachable:
    forall (g1 g2: Graph) x l r, vvalid g1 x -> vvalid g1 r -> vgamma g1 x = (true, l, r) ->
                                 edge_spanning_tree g1 (x, L) g2 -> Included (reachable g2 r) (reachable g1 x).
  Proof.
    intros. hnf in H2.
    assert (l = dst g1 (x, L)) by (simpl in H1; unfold gamma in H1; inversion H1; auto).
    rewrite <- H3 in H2. destruct (node_pred_dec (marked g1) l).
    + destruct H2 as [[? [? [? [? ?]]]] ?]. intro v. unfold Ensembles.In .
      intros. apply edge_reachable_by with r; auto.
      - split; [|split]; auto. rewrite (gamma_step g1 x true l r); auto.
      - change (g1 |= r ~o~> v satisfying (fun _ : addr => True)) with (reachable g1 r v).
        rewrite reachable_ind_reachable in H9. clear H1. induction H9.
        * rewrite reachable_ind_reachable. constructor. rewrite H2; auto.
        * destruct H1 as [? [? ?]]. apply edge_reachable with y. apply IHreachable. rewrite H2; auto.
          split; [|split]; [rewrite H2; auto .. |]. rewrite step_spec in H11 |- *.
          destruct H11 as [e [? [? ?]]]. exists e.
          assert (e <> (x, L)) by (intro; subst; destruct H7; [|destruct H3]; auto).
          specialize (H4 _ H14). specialize (H5 _ H14). specialize (H6 _ H14).
          subst x0. subst y. intuition.
    + apply (spanning_tree_left_reachable g1 g2 x l r); auto.
  Qed.

  Lemma graph_ramify_aux1_right: forall (g1 g2: Graph) x l r,
      vvalid g1 x -> vgamma g1 x = (true, l, r) ->
      edge_spanning_tree g1 (x, L) g2 -> unmarked g2 r ->
      (forall gg, spanning_tree g2 r gg -> edge_spanning_tree g2 (x, R) gg) ->
      vvalid g1 r ->
      (vertices_at (reachable g1 x) g2: pred) |-- graph r g2 *
      ((EX g': Graph, !! spanning_tree g2 r g' && vertices_at (reachable g2 r) g') -*
       (EX g': Graph, !! edge_spanning_tree g2 (x, R) g' && vertices_at (reachable g1 x) g')).
  Proof.
    intros. destruct (edge_spanning_tree_left_vgamma g1 g2 x l r H H0 H1) as [l' ?].
    apply graph_ramify_aux1'; auto.
    + apply weak_valid_vvalid_dec.
      apply (gamma_right_weak_valid g2 x true l' r); auto.
      rewrite <- (edge_spanning_tree_left_vvalid g1 g2 x true l r); eauto.
    + simpl in H5. unfold gamma in H5. inversion H5; auto.
    + apply (edge_spanning_tree_left_reachable g1 g2 x l r); auto.
    + apply (edge_spanning_tree_left_reachable_vvalid g1 g2 x true l r); auto.
  Qed.

  Lemma graph_gen_right_null_ramify: forall (g1 g2: Graph) (x : addr) d (l r : addr),
      vvalid g1 x -> vgamma g2 x = (d, l, r) ->
      (vertices_at (reachable g1 x) g2 : pred) |--
                  vertex_at x (d, l, r) * (vertex_at x (d, l, null) -* vertices_at (reachable g1 x) (Graph_gen_right_null g2 x)).
  Proof.
    intros.
    replace (@vertex_at _ _ _ _ _ SGP x (d, l, r)) with (graph_cell g2 x).
    Focus 2. {
      unfold graph_cell; simpl.
      simpl in H0; rewrite H0; auto.
    } Unfocus.
    replace (@vertex_at _ _ _ _ _ SGP x (d, l, null)) with (graph_cell (Graph_gen_right_null g2 x) x).
    Focus 2. {
      unfold graph_cell; simpl.
      unfold gamma. simpl.
      unfold graph_gen.update_dst.
      destruct_eq_dec (x, R) (x, L). inversion H1.
      destruct_eq_dec (x, R) (x, R). 2: exfalso; apply H2; auto.
      simpl in H0; unfold gamma in H0. inversion H0; auto.
    } Unfocus.
    apply pred_sepcon_ramify1; auto.
    + apply reachable_by_refl; auto.
    + intuition.
    + intros. unfold graph_cell; simpl.
      unfold gamma; simpl. unfold graph_gen.update_dst.
      destruct_eq_dec (x, R) (y, L). inversion H2. 
      destruct_eq_dec (x, R) (y, R). inversion H3. exfalso; auto. auto.
  Qed.

  Lemma edge_spanning_tree_right_null:
    forall (g: Graph) x d l r, vvalid g x -> vgamma g x = (d, l, r) -> (marked g) r ->
                               edge_spanning_tree g (x, R) (Graph_gen_right_null g x).
  Proof.
    intros. assert (r = dst g (x, R)) by (simpl in H0; unfold gamma in H0; inversion H0; auto).
    hnf. destruct (node_pred_dec (marked g) (dst g (x, R))). 2: subst r; exfalso; auto.
    split.
    + hnf. simpl. split; [| split; [|split; [| split]]]; [tauto | tauto | tauto | | ].
      - intros. unfold graph_gen.update_dst.
        destruct (equiv_dec (x, R) e); intuition.
      - right. split; auto. unfold graph_gen.update_dst.
        destruct (equiv_dec (x, R) (x, R)); intuition.
        * apply (valid_not_null g) in H3; auto. rewrite is_null_def. auto.
        * split; auto. apply (@right_valid _ _ _ _ g _ _ (biGraph g)) in H; auto.
    + simpl. tauto.
  Qed.

  Lemma edge_spanning_tree_spanning_tree: forall (g g1 g2 g3 : Graph) x l l' r,
      vvalid g x -> vvalid g1 x -> vvalid g2 x ->
      vgamma g x = (false, l, r) ->
      vgamma g1 x = (true, l, r) ->
      vgamma g2 x = (true, l', r) ->
      mark1 g x g1 ->
      edge_spanning_tree g1 (x, L) g2 ->
      edge_spanning_tree g2 (x, R) g3 ->
      spanning_tree g x g3.
  Proof.
  Abort.

End SPATIAL_GRAPH_DISPOSE_BI.
