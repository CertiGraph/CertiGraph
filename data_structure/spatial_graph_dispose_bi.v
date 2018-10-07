Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import Coq.Lists.List.
Require Import RamifyCoq.msl_ext.ramification_lemmas.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.spanning_tree.
Require Import RamifyCoq.graph.BiGraph.
Require Import RamifyCoq.graph.MathGraph.
Require Import RamifyCoq.graph.FiniteGraph.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GraphBi.
Require Import RamifyCoq.msl_application.GraphBi_Mark.
Require RamifyCoq.graph.weak_mark_lemmas.
Import RamifyCoq.graph.weak_mark_lemmas.WeakMarkGraph.

(* TODO: Put some pure lemmas into some file like: graph/bi_spanning. *)

Instance MGS: MarkGraphSetting bool.
  apply (Build_MarkGraphSetting bool
          (eq true));
  intros.
  + destruct x; [left | right]; congruence.
Defined.

Section SPATIAL_GRAPH_DISPOSE_BI.

  Context {pSGG_Bi: pPointwiseGraph_Graph_Bi}.
  Context {sSGG_Bi: sPointwiseGraph_Graph_Bi bool unit}.

  Existing Instances maGraph biGraph finGraph.

  Local Open Scope logic.
  Local Coercion Graph_LGraph: Graph >-> LGraph.
  Local Coercion LGraph_SGraph: LGraph >-> SGraph.
  Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
  Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
  Local Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.
  Local Coercion pg_lg: LabeledGraph >-> PreGraph.

  Notation Graph := (@Graph pSGG_Bi bool unit unit).

  Lemma vgamma_is_true: forall (g : Graph) (x l r : addr), vgamma g x = (true, l, r) -> marked g x.
  Proof. intros. simpl in H. simpl. destruct (vlabel g x) eqn:? . auto. inversion H. Qed.
  
  Lemma vgamma_is_false: forall (g : Graph) (x l r : addr), vgamma g x = (false, l, r) -> unmarked g x.
  Proof.
    intros. simpl in H. hnf. unfold Ensembles.In. simpl. intro.
    destruct (vlabel g x) eqn:? . inversion H. simpl in H0. inversion H0.
  Qed.
  
  Lemma edge_spanning_tree_left_null:
    forall (g: Graph) x d l r, vvalid g x -> vgamma g x = (d, l, r) -> (marked g) l ->
                               edge_spanning_tree g (x, L) (Graph_gen_left_null g x).
  Proof.
    intros. assert (l = dst g (x, L)) by (simpl in H0; inversion H0; auto).
    hnf. change (lg_gg g) with (g: LGraph). destruct (node_pred_dec (marked g) (dst g (x, L))). 2: subst l; exfalso; auto.
    split.
    + hnf. simpl. split; [| split; [|split; [| split]]]; [tauto | tauto | tauto | | ].
      - intros. unfold updateEdgeFunc.
        destruct (equiv_dec (x, L) e); intuition.
      - right. unfold updateEdgeFunc.
        destruct (equiv_dec (x, L) (x, L)); intuition.
        * apply (valid_not_null g) in H3; auto. reflexivity.
        * apply (@left_valid _ _ _ _ _ _ g (biGraph g)) in H; auto.
    + simpl. tauto.
  Qed.

  Lemma graph_gen_left_null_ramify:
    forall (g: Graph) (x : addr) d (l r : addr),
      vvalid g x -> vgamma g x = (d, l, r) ->
      (reachable_vertices_at x g : pred) |-- vertex_at x (d, l, r) * (vertex_at x (d, null, r) -* vertices_at (reachable g x) (Graph_gen_left_null g x)).
  Proof.
    intros.
    replace (@vertex_at _ _ _ _ _ SGP x (d, l, r)) with (graph_vcell g x).
    2: {
      unfold graph_vcell; simpl.
      simpl in H0; rewrite H0; auto.
    }
    replace (@vertex_at _ _ _ _ _ SGP x (d, null, r)) with (graph_vcell (Graph_gen_left_null g x) x).
    2: {
      unfold graph_vcell; simpl.
      unfold updateEdgeFunc.
      destruct_eq_dec (x, L) (x, L). 2: exfalso; auto.
      destruct_eq_dec (x, L) (x, R). inversion H2.
      simpl in H0; inversion H0; auto.
    }
    apply vertices_at_ramif_1; auto.
    eexists; split; [| split].
    + apply Ensemble_join_Intersection_Complement.
      - unfold Included, Ensembles.In; intros; subst; apply reachable_by_refl; auto.
      - intros; destruct_eq_dec x x0; auto.
    + apply Ensemble_join_Intersection_Complement.
      - unfold Included, Ensembles.In; intros; subst; apply reachable_by_refl; auto.
      - intros; destruct_eq_dec x x0; auto.
    + rewrite vertices_identical_spec.
      simpl; intros.
      change (lg_gg g) with (g: LGraph).
      rewrite Intersection_spec in H1.
      destruct H1; unfold Complement, Ensembles.In in H2.
      simpl. unfold updateEdgeFunc.
      destruct_eq_dec (x, L) (x0, L).
      - inversion H3. exfalso; auto.
      - destruct_eq_dec (x, L) (x0, R). inversion H4. auto.
  Qed.

  Lemma graph_gen_left_null_ramify_weak:
    forall (g: Graph) (x : addr) d (l r : addr),
      vvalid g x -> vgamma g x = (d, l, r) ->
      (reachable_vertices_at x g : pred) |-- vertex_at x (d, l, r) * (vertex_at x (d, null, r) -* (reachable_vertices_at x (Graph_gen_left_null g x) * TT)).
  Proof.
    intros. pose proof (graph_gen_left_null_ramify g x d l r H H0).
    apply log_normalize.sepcon_weaken with (vertex_at x (d, null, r) -* vertices_at (reachable g x) (Graph_gen_left_null g x)); auto.
    apply wand_derives; auto. unfold reachable_vertices_at.
    cut ((vertices_at (reachable g x) (Graph_gen_left_null g x) : pred)
                     |-- vertices_at (reachable (Graph_gen_left_null g x) x)
                     (Graph_gen_left_null g x) * TT). auto. unfold vertices_at.
    apply iter_sepcon.pred_sepcon_prop_true_weak.
    - apply Graph_reachable_dec, weak_valid_vvalid_dec. right.
      unfold Graph_gen_left_null. simpl. apply H.
    - intro y. unfold Graph_gen_left_null. simpl.
      apply is_partial_graph_reachable, pregraph_gen_dst_is_partial_graph.
      apply invalid_null.
  Qed.

  Lemma graph_ramify_aux1_left: forall (g: Graph) x d l r,
      vvalid g x -> vgamma g x = (d, l, r) ->
      (reachable_vertices_at x g : pred) |-- reachable_vertices_at l g *
      (ALL  g' : Graph , !!spanning_tree g l g' --> (vertices_at (reachable g l) g' -* vertices_at (reachable g x) g')).
  Proof.
    intros. eapply vertices_at_ramif_xQ; auto.
    eexists; split; [| split].
    + eapply Prop_join_reachable_left; eauto.
    + intros. eapply Prop_join_reachable_left; eauto.
    + intros; rewrite vertices_identical_spec.
      intros.
      rewrite Intersection_spec in H2. unfold Complement, Ensembles.In in H2.
      destruct H2. simpl. f_equal; [f_equal |].
      - apply vlabel_eq. destruct H1. specialize (H1 x0).
        pose proof reachable_by_is_reachable g l x0 (unmarked g).
        tauto.
      - destruct H1 as [_ [? _]]. hnf in H1. simpl in H1.
        unfold predicate_weak_evalid in H1. destruct H1 as [_ [? [_ ?]]].
        specialize (H1 (x0, L)). specialize (H4 (x0, L)).
        assert (src g (x0, L) = x0)
          by (apply (@left_sound _ _ _ _ _ _ g (biGraph g) x0); apply reachable_foot_valid in H2; auto).
        change (lg_gg g) with (g: LGraph) in *.
        rewrite H5 in *.
        assert (evalid g (x0, L) /\ ~ g |= l ~o~> x0 satisfying (unmarked g)). {
          split.
          + apply reachable_foot_valid in H2.
            apply (@left_valid _ _ _ _ _ _ g (biGraph g)); auto.
          + intro; apply H3; apply reachable_by_is_reachable in H6; auto.
        } apply H4; intuition.
      - destruct H1 as [_ [? _]]. hnf in H1. simpl in H1.
        unfold predicate_weak_evalid in H1. destruct H1 as [_ [? [_ ?]]].
        specialize (H1 (x0, R)). specialize (H4 (x0, R)).
        assert (src g (x0, R) = x0)
          by (apply (@right_sound _ _ _ _ _ _ g (biGraph g) x0); apply reachable_foot_valid in H2; auto).
        change (lg_gg g) with (g: LGraph) in *.
        rewrite H5 in *.
        assert (evalid g (x0, R) /\ ~ g |= l ~o~> x0 satisfying (unmarked g)). {
          split.
          + apply reachable_foot_valid in H2.
            apply (@right_valid _ _ _ _ _ _ g (biGraph g)); auto.
          + intro; apply H3; apply reachable_by_is_reachable in H6; auto.
        } apply H4; intuition.
  Qed.

  Lemma totally_unmarked_root_ST_reachable_eq: forall (g1 g2: Graph) root,
      totally_unmarked g1 root -> spanning_tree g1 root g2 ->
      vertices_at (reachable g1 root) g2 = reachable_vertices_at root g2.
  Proof.
    intros. apply vertices_at_Same_set. rewrite Same_set_spec. hnf.
    apply spanning_tree_totally_unmarked_root_reachable; auto. intros.
    apply Graph_reachable_by_dec, weak_valid_vvalid_dec; right; auto.
  Qed.

  Lemma totally_unmarked_parent_ST_reachable_eq: forall (g1 g2: Graph) x l r,
      vvalid g1 x -> vgamma g1 x = (true, l, r) -> totally_unmarked g1 l ->
      spanning_tree g1 l g2 ->
      vertices_at (reachable g1 x) g2 = reachable_vertices_at x g2.
  Proof.
    intros. apply vertices_at_Same_set. rewrite Same_set_spec. hnf.
    assert (l = dst (lg_gg g1) (x, L)) by (simpl in H0; inversion H0; auto).
    apply spanning_tree_totally_unmarked_parent_reachable with (e := (x, L));
      auto; try rewrite <- H3; auto.
      - hnf. split.
        + apply (@left_valid _ _ _ _ _ _ g1 (biGraph g1)); auto.
        + apply (@left_sound _ _ _ _ _ _ g1 (biGraph g1) x); auto.
      - apply vgamma_is_true in H0. auto.
      - intros; apply Graph_reachable_by_dec, weak_valid_vvalid_dec; right; auto.
  Qed.
(*
  Lemma graph_ramify_aux1_left_weak: forall (g: Graph) x l r,
      vvalid g x -> vgamma g x = (true, l, r) -> totally_unmarked g l ->
      (reachable_vertices_at x g : pred) |-- reachable_vertices_at l g *
      (ALL  g' : Graph , !!spanning_tree g l g' --> (reachable_vertices_at l g' -* reachable_vertices_at x g')).
  Proof.
    intros. pose proof (@graph_ramify_aux1_left g x true l r H H0).
    eapply log_normalize.sepcon_weaken. 2: apply H2. clear H2.
    apply allp_derives. intros p. destruct p as [? g2]. simpl.
    rewrite <- imp_andp_adjoint. apply derives_extract_prop'. intros.
    rewrite prop_imp; auto. apply wand_derives.
    - rewrite <- totally_unmarked_root_ST_reachable_eq; auto.
    - rewrite (totally_unmarked_parent_ST_reachable_eq _ _ _ l r); auto.
  Qed.
*)
  Lemma edge_spanning_tree_left_vvalid: forall (g1 g2: Graph) x n,
      vvalid g1 x -> edge_spanning_tree g1 (x, L) g2 -> (vvalid g1 n <-> vvalid g2 n).
  Proof.
    intros. apply (edge_spanning_tree_vvalid g1 g2 (x, L) n); auto.
  Qed.

  Lemma edge_spanning_tree_right_vvalid: forall (g1 g2: Graph) x n,
      vvalid g1 x -> edge_spanning_tree g1 (x, R) g2 -> (vvalid g1 n <-> vvalid g2 n).
  Proof.
    intros. apply (edge_spanning_tree_vvalid g1 g2 (x, R) n); auto.
  Qed.

  Lemma edge_spanning_tree_left_reachable_vvalid: forall (g1 g2: Graph) x d l r,
      vvalid g1 x -> vgamma g1 x = (d, l, r) -> edge_spanning_tree g1 (x, L) g2 -> Included (reachable g1 x) (vvalid g2).
  Proof.
    intros. assert (x = src g1 (x, L)) by (symmetry; apply (@left_sound _ _ _ _ _ _ g1 (biGraph g1) x); auto).
    rewrite H2. apply edge_spanning_tree_reachable_vvalid; auto.
  Qed.

  Lemma edge_spanning_tree_left_vgamma: forall (g1 g2: Graph) x l r,
      vvalid g1 x -> vgamma g1 x = (true, l, r) -> edge_spanning_tree g1 (x, L) g2 -> exists l', vgamma g2 x = (true, l', r).
  Proof.
    intros. simpl. exists (dst g2 (x, L)).
    assert (Hvg2: vvalid g2 x) by (rewrite <- edge_spanning_tree_left_vvalid; eauto).
    unfold edge_spanning_tree in H1.
    change (lg_gg g1) with (g1: LGraph) in H1.
    destruct (node_pred_dec (marked g1) (dst g1 (x, L))).
    + destruct H1 as [[_ [_ [_ [? _]]]] ?]. simpl in H0, H2. inversion H0.
      rewrite H4. symmetry in H4. rewrite H2 in H4.
      change (lg_gg g2) with (g2: LGraph) in H4.
      rewrite <- H4. f_equal. symmetry. apply H1.
      - intro. inversion H3.
      - apply (@right_valid _ _ _ _ _ _ g1 (biGraph g1)) in H; auto.
      - apply (@right_valid _ _ _ _ _ _ g2 (biGraph g2)) in Hvg2; auto.
    + destruct H1 as [? [[_ [_ [_ ?]]] _]].
      assert (marked g1 x) by (simpl in *; inversion H0; auto).
      assert (~ g1 |= dst g1 (x, L) ~o~> x satisfying (unmarked g1)) by (intro HS; apply reachable_by_foot_prop in HS; auto).
      assert (marked g2 x) by (specialize (H1 x); tauto).
      simpl in H5. rewrite <- H5. f_equal.
      simpl in H2. unfold predicate_weak_evalid in H2.
      simpl in H0. inversion H0. symmetry.
      change (lg_gg g1) with (g1: LGraph) in *.
      change (lg_gg g2) with (g2: LGraph) in *.
      apply H2; split.
      - apply (@right_valid _ _ _ _ _ _ g1 (biGraph g1) x); auto.
      - rewrite (@right_sound _ _ _ _ _ _ g1 (biGraph g1) x); auto.
      - apply (@right_valid _ _ _ _ _ _ g2 (biGraph g2) x); auto.
      - rewrite (@right_sound _ _ _ _ _ _ g2 (biGraph g2) x); auto.
  Qed.

  Lemma spanning_tree_left_reachable:
    forall (g1 g2: Graph) x l r,
      vvalid g1 x -> vgamma g1 x = (true, l, r) ->
      spanning_tree g1 l g2 -> Included (reachable g2 r) (reachable g1 x).
  Proof.
    intros. intro v. unfold Ensembles.In . intros.
    assert (X: ReachDecidable g1 l (unmarked g1)). {
      apply Graph_reachable_by_dec.
      apply weak_valid_vvalid_dec.
      apply (gamma_left_weak_valid g1 x true l r); auto.
    } destruct (X v).
    + apply reachable_by_is_reachable in r0. apply edge_reachable_by with l; auto.
      split; [|split]; auto.
      - apply reachable_head_valid in r0. auto.
      - simpl in H0. inversion H0. exists (x, L); auto.
        * apply (@left_valid _ _ _ _ _ _ g1 (biGraph g1)); auto.
        * apply (@left_sound _ _ _ _ _ _ g1 (biGraph g1)); auto.
    + apply edge_reachable_by with r; auto.
      - split; [|split]; auto.
        * apply reachable_head_valid in H2.
          rewrite (spanning_tree_vvalid g1 l g2); auto.
        * rewrite (gamma_step g1 x true l r); auto.
      - apply (spanning_tree_not_reachable g1 l g2 r v) in H2; auto.
        rewrite reachable_by_eq_partialgraph_reachable in H2.
        destruct H1 as [? [? ?]]. rewrite <- H3 in H2.
        rewrite <- reachable_by_eq_partialgraph_reachable in H2.
        apply reachable_by_is_reachable in H2. apply H2.
  Qed.

  Lemma edge_spanning_tree_left_reachable:
    forall (g1 g2: Graph) x l r,
      vvalid g1 x -> vgamma g1 x = (true, l, r) ->
      edge_spanning_tree g1 (x, L) g2 -> Included (reachable g2 r) (reachable g1 x).
  Proof.
    intros. assert (Hv: vvalid g2 r -> vvalid g1 r). {
      intros. rewrite (edge_spanning_tree_left_vvalid g1 g2 x r); auto.
    } hnf in H1.
    assert (l = dst g1 (x, L))
      by (simpl in H0; inversion H0; auto).
    change (lg_gg g1) with (g1: LGraph) in *.
    rewrite <- H2 in H1. destruct (node_pred_dec (marked g1) l).
    + destruct H1 as [[? [? [? [? ?]]]] ?]. intro v. unfold Ensembles.In .
      intros. apply edge_reachable_by with r; auto.
      - split; [|split]; auto.
        * apply Hv. apply reachable_head_valid in H8; auto.
        * rewrite (gamma_step g1 x true l r); auto.
      - change (g1 |= r ~o~> v satisfying (fun _ : addr => True))
        with (reachable g1 r v).
        rewrite reachable_ind_reachable in H8. clear H0. induction H8.
        * rewrite reachable_ind_reachable. constructor. rewrite H1; auto.
        * destruct H0 as [? [? ?]]. apply edge_reachable with y.
          apply IHreachable. rewrite H1; auto.
          split; [|split]; [rewrite H1; auto .. |]. rewrite step_spec in H10 |- *.
          destruct H10 as [e [? [? ?]]]. exists e.
          assert (e <> (x, L)) by (intro; subst; destruct H6; [|destruct H2]; auto).
          specialize (H3 _ H13). specialize (H4 _ H13). specialize (H5 _ H13).
          subst x0. subst y. intuition.
    + apply (spanning_tree_left_reachable g1 g2 x l r); auto.
  Qed.

  Lemma Prop_join_EST_right: forall (g1 g2: Graph) x l r,
      vvalid g1 x -> vgamma g1 x = (true, l, r) ->
      edge_spanning_tree g1 (x, L) g2 ->
      Prop_join (reachable g2 r)
                (Intersection _ (reachable g1 x) (Complement addr (reachable g2 r)))
                (reachable g1 x).
  Proof.
    intros. apply Ensemble_join_Intersection_Complement.
    + eapply edge_spanning_tree_left_reachable; eauto.
    + intros.
      destruct (edge_spanning_tree_left_vgamma g1 g2 x l r H H0 H1) as [l' ?].
      apply gamma_right_weak_valid in H2.
      - apply decidable_prop_decidable, Graph_reachable_dec,
        weak_valid_vvalid_dec; auto.
      - apply (edge_spanning_tree_left_reachable_vvalid g1 g2 x true l r); auto.
        unfold Ensembles.In . apply reachable_by_refl; auto.
  Qed.

  Lemma graph_ramify_aux1_right: forall (g1 g2: Graph) x l r,
      vvalid g1 x -> vgamma g1 x = (true, l, r) ->
      edge_spanning_tree g1 (x, L) g2 ->
      (vertices_at (reachable g1 x) g2: pred) |-- reachable_vertices_at r g2 *
      (ALL  g' : Graph ,
                !!spanning_tree g2 r g' -->
                  (vertices_at (reachable g2 r) g' -*
                               vertices_at (reachable g1 x) g')).
  Proof.
    intros. eapply vertices_at_ramif_xQ; auto.
    eexists; split; [| split].
    + eapply Prop_join_EST_right; eauto.
    + intros. eapply Prop_join_EST_right; eauto.
    + intros; rewrite vertices_identical_spec.
      intros. simpl.
      rewrite Intersection_spec in H3; unfold Complement, Ensembles.In in H3.
      destruct H3. f_equal; [f_equal |].
      - apply vlabel_eq. destruct H2 as [? _]. specialize (H2 x0).
        pose proof reachable_by_is_reachable g2 r x0 (unmarked g2).
        tauto.
      - destruct H2 as [_ [? _]]. hnf in H2. simpl in H2.
        unfold predicate_weak_evalid in H2. destruct H2 as [_ [? [_ ?]]].
        specialize (H2 (x0, L)). specialize (H5 (x0, L)).
        assert (src g2 (x0, L) = x0).
        1: {
          apply (@left_sound _ _ _ _ _ _ g2 (biGraph g2) x0).
          rewrite <- (edge_spanning_tree_left_vvalid g1 g2 x x0 H H1).
          apply reachable_foot_valid in H3; auto.
        }
        change (lg_gg g2) with (g2: LGraph) in *.
        rewrite H6 in *.
        assert (evalid g2 (x0, L) /\ ~ g2 |= r ~o~> x0 satisfying (unmarked g2)). {
          split.
          + apply reachable_foot_valid in H3.
            apply (@left_valid _ _ _ _ _ _ g2 (biGraph g2)).
            rewrite <- (edge_spanning_tree_left_vvalid g1 g2 x); eauto.
          + intro; apply H4; apply reachable_by_is_reachable in H7; auto.
        } apply H5; intuition.
      - destruct H2 as [_ [? _]]. hnf in H2. simpl in H2.
        unfold predicate_weak_evalid in H2. destruct H2 as [_ [? [_ ?]]].
        specialize (H2 (x0, R)). specialize (H5 (x0, R)).
        assert (src g2 (x0, R) = x0).
        1: {
          apply (@right_sound _ _ _ _ _ _ g2 (biGraph g2) x0).
          rewrite <- (edge_spanning_tree_left_vvalid g1 g2 x x0 H H1).
          apply reachable_foot_valid in H3; auto.
        }
        change (lg_gg g2) with (g2: LGraph) in *.
        rewrite H6 in *.
        assert (evalid g2 (x0, R) /\ ~ g2 |= r ~o~> x0 satisfying (unmarked g2)). {
          split.
          + apply reachable_foot_valid in H3.
            apply (@right_valid _ _ _ _ _ _ g2 (biGraph g2)).
            rewrite <- (edge_spanning_tree_left_vvalid g1 g2 x); eauto.
          + intro; apply H4; apply reachable_by_is_reachable in H7; auto.
        } apply H5; intuition.
  Qed.

  Lemma graph_gen_right_null_ramify: forall (g1 g2: Graph) (x : addr) d (l r : addr),
      vvalid g1 x -> vgamma g2 x = (d, l, r) ->
      (vertices_at (reachable g1 x) g2 : pred) |--
                  vertex_at x (d, l, r) * (vertex_at x (d, l, null) -* vertices_at (reachable g1 x) (Graph_gen_right_null g2 x)).
  Proof.
    intros.
    replace (@vertex_at _ _ _ _ _ SGP x (d, l, r)) with (graph_vcell g2 x).
    2: {
      unfold graph_vcell; simpl.
      simpl in H0; rewrite H0; auto.
    }
    replace (@vertex_at _ _ _ _ _ SGP x (d, l, null)) with (graph_vcell (Graph_gen_right_null g2 x) x).
    2: {
      unfold graph_vcell; simpl.
      unfold updateEdgeFunc.
      destruct_eq_dec (x, R) (x, L). inversion H1.
      destruct_eq_dec (x, R) (x, R). 2: exfalso; apply H2; auto.
      simpl in H0; inversion H0; auto.
    }
    apply vertices_at_ramif_1; auto.
    eexists; split; [| split].
    + apply Ensemble_join_Intersection_Complement.
      - unfold Included, Ensembles.In; intros; subst; apply reachable_by_refl; auto.
      - intros; destruct_eq_dec x x0; auto.
    + apply Ensemble_join_Intersection_Complement.
      - unfold Included, Ensembles.In; intros; subst; apply reachable_by_refl; auto.
      - intros; destruct_eq_dec x x0; auto.
    + rewrite vertices_identical_spec.
      simpl; intros.
      change (lg_gg g2) with (g2: LGraph).
      rewrite Intersection_spec in H1.
      destruct H1; unfold Complement, Ensembles.In in H2.
      simpl. unfold updateEdgeFunc.
      destruct_eq_dec (x, R) (x0, L).
      - inversion H3.
      - destruct_eq_dec (x, R) (x0, R).
        * inversion H4. exfalso; auto.
        * auto.
  Qed.

  Lemma graph_gen_right_null_ramify_weak: forall (g2: Graph) (x : addr) d (l r : addr),
      vvalid g2 x -> vgamma g2 x = (d, l, r) ->
      (reachable_vertices_at x g2 : pred) |-- vertex_at x (d, l, r) * (vertex_at x (d, l, null) -* (reachable_vertices_at x (Graph_gen_right_null g2 x) * TT)).
  Proof.
    intros. pose proof (graph_gen_right_null_ramify g2 g2 x d l r H H0).
    apply log_normalize.sepcon_weaken with (vertex_at x (d, l, null) -* vertices_at (reachable g2 x) (Graph_gen_right_null g2 x)); auto.
    apply wand_derives; auto. unfold reachable_vertices_at.
    cut ((vertices_at (reachable g2 x) (Graph_gen_right_null g2 x): pred)
           |-- vertices_at (reachable (Graph_gen_right_null g2 x) x)
           (Graph_gen_right_null g2 x) * TT). auto. unfold vertices_at.
    apply iter_sepcon.pred_sepcon_prop_true_weak.
    - apply Graph_reachable_dec, weak_valid_vvalid_dec. right.
      unfold Graph_gen_left_null. simpl. apply H.
    - intro y. unfold Graph_gen_left_null. simpl.
      apply is_partial_graph_reachable, pregraph_gen_dst_is_partial_graph.
      apply invalid_null.
  Qed.

  Lemma edge_spanning_tree_right_null:
    forall (g: Graph) x d l r, vvalid g x -> vgamma g x = (d, l, r) -> (marked g) r ->
                               edge_spanning_tree g (x, R) (Graph_gen_right_null g x).
  Proof.
    intros. assert (r = dst g (x, R)) by (simpl in H0; inversion H0; auto).
    hnf.
    change (lg_gg g) with (g: LGraph). destruct (node_pred_dec (marked g) (dst g (x, R))). 2: subst r; exfalso; auto.
    split.
    + hnf. simpl. split; [| split; [|split; [| split]]]; [tauto | tauto | tauto | | ].
      - intros. unfold updateEdgeFunc.
        destruct (equiv_dec (x, R) e); intuition.
      - right. split; auto. unfold updateEdgeFunc.
        destruct (equiv_dec (x, R) (x, R)); intuition.
        * apply (valid_not_null g) in H3; auto. reflexivity.
        * split; auto. apply (@right_valid _ _ _ _ _ _ g (biGraph g)) in H; auto.
    + simpl. tauto.
  Qed.

  Lemma edge_spanning_tree_spanning_tree: forall (g g1 g2 g3 : Graph) x l r,
      vvalid g x -> vvalid g1 x -> vvalid g2 x ->
      vgamma g x = (false, l, r) ->
      vgamma g1 x = (true, l, r) ->
      mark1 x g g1 ->
      edge_spanning_tree g1 (x, L) g2 ->
      edge_spanning_tree g2 (x, R) g3 ->
      spanning_tree g x g3.
  Proof.
    intros.
    apply (spanning_list_spanning_tree2 _ g1 _ _ (x, L) (x, R)); auto; intros.
    + intro. inversion H7.
    + pose proof (only_two_edges x e H). simpl in H7 |-* .
      split; intros.
      - destruct H8 as [? | [? | ?]]; [subst e..|exfalso; auto].
        * split; [|intuition]. apply (@left_valid _ _ _ _ _ _ g (biGraph g)); auto.
        * split; [|intuition]. apply (@right_valid _ _ _ _ _ _ g (biGraph g)); auto.
      - destruct H8. intuition.
    + apply Graph_reachable_by_dec. apply weak_valid_vvalid_dec. pose proof H3.
      simpl in H3. inversion H3. subst l.
      apply (gamma_left_weak_valid g1 x true (dst g1 (x, L)) r); auto.
    + unfold unmarked. rewrite negateP_spec. unfold marked. simpl. simpl in H2.
      inversion H2.
      change (lg_gg g) with (g: LGraph).
      rewrite H8. intuition.
    + apply spanning_list_cons with g2; auto.
      apply spanning_list_cons with g3; auto.
      apply spanning_list_nil. auto.
  Qed.

End SPATIAL_GRAPH_DISPOSE_BI.
