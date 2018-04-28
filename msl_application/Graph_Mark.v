Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.msl_ext.ramification_lemmas.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.dag.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.msl_application.Graph.
Require Import Coq.Logic.Classical.

Local Open Scope logic.

Section PointwiseGraph_Mark.

Context {V E: Type}.
Context {GV GE Pred: Type}.
Context {SGBA: PointwiseGraphBasicAssum V E}.
Context {SGC: PointwiseGraphConstructor V E bool unit unit GV GE}.
Context {L_SGC: Local_PointwiseGraphConstructor V E bool unit unit GV GE}.
Context {SGP: PointwiseGraphPred V E GV GE Pred}.
Context {SGA: PointwiseGraphAssum SGP}.

Instance MGS: WeakMarkGraph.MarkGraphSetting bool.
Proof.
  apply (WeakMarkGraph.Build_MarkGraphSetting _ (eq true)).
  intros; destruct x; [left | right]; congruence.
Defined.

Global Existing Instance MGS.

Notation Graph := (LabeledGraph V E bool unit unit).
Notation SGraph := (PointwiseGraph V E GV GE).

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition mark1 x (G1: Graph) (G2: Graph) := WeakMarkGraph.mark1 x G1 G2.
Definition mark x (G1: Graph) (G2: Graph) := WeakMarkGraph.mark x G1 G2 /\ G1 ~=~ G2.

Definition mark_list xs g1 g2 := relation_list (map mark xs) g1 g2.

Lemma mark_invalid_refl: forall (g: Graph) root, ~ vvalid g root -> mark root g g.
Proof.
  intros.
  split.
  + apply WeakMarkGraph.mark_invalid_refl; auto.
  + reflexivity.
Qed.

Lemma mark_marked_root_refl: forall (g: Graph) root, WeakMarkGraph.marked g root -> mark root g g.
Proof.
  intros.
  split.
  + apply WeakMarkGraph.mark_marked_root_refl; auto.
  + reflexivity.
Qed.

Lemma mark_list_eq: forall root xs g1 g2,
  mark_list xs g1 g2 ->
  WeakMarkGraph.componded_mark_list root xs g1 g2 /\ g1 ~=~ g2.
Proof.
  intros.
  change (mark_list xs g1 g2) with
    (relation_list (map (fun x => relation_conjunction (WeakMarkGraph.mark x) (respectful_relation pg_lg structurally_identical)) xs) g1 g2) in H.
  eapply relation_list_conjunction in H.
  rewrite relation_conjunction_iff in H.
  split.
  + destruct H as [? _].
    eapply relation_list_inclusion; [| exact H].
    intros ? _.
    clear.
    intros g1 g2 ?.
    exists g2; [| apply WeakMarkGraph.eq_do_nothing; auto].
    exists g1; [apply WeakMarkGraph.eq_do_nothing; auto |].
    auto.
  + eapply si_list.
    exact (proj2 H).
Qed.

Lemma mark1_mark_list_mark: forall root l (g g': Graph),
  vvalid g root ->
  (WeakMarkGraph.unmarked g) root ->
  step_list g root l ->
  relation_list (mark1 root :: mark_list l :: nil) g g' ->
  mark root g g'.
Proof.
  intros.
  destruct_relation_list g0 in H2.
  eapply (mark_list_eq root) in H2.
  destruct H2; simpl in H2.
  split.
  + eapply WeakMarkGraph.mark1_componded_mark_list_mark; eauto.
    split_relation_list (g :: g0 :: g0 :: g' :: nil); auto;
    apply WeakMarkGraph.eq_do_nothing; auto.
  + destruct H3 as [? _].
    rewrite H3; auto.
Qed.

Lemma mark_partial_labeled_graph_equiv: forall x (g g': Graph),
  mark x g g' ->
  ((predicate_partial_labeledgraph g (Complement _ (reachable g x))) ~=~
  (predicate_partial_labeledgraph g' (Complement _ (reachable g x))))%LabeledGraph.
Proof.
  intros.
  split; [| split].
  + destruct H.
    simpl;
    rewrite <- H0.
    reflexivity.
  + destruct H as [[? ?] _].
    simpl in *; intros.
    specialize (H0 v).
    assert (~ g |= x ~o~> v satisfying (WeakMarkGraph.unmarked g)).
    1: {
      destruct H1.
      intro; apply H3.
      apply reachable_by_is_reachable in H4; auto.
    }
    clear - H0 H3.
    destruct (vlabel g v), (vlabel g' v).
    - auto.
    - rewrite H0; auto.
    - symmetry; tauto.
    - auto.
  + intros; simpl.
    destruct (elabel g e), (elabel g' e); auto.
Qed.

Lemma root_stable_ramify: forall (g: Graph) (x: V) (gx: GV),
  vgamma (Graph_PointwiseGraph g) x = gx ->
  vvalid g x ->
  @derives Pred _
    (reachable_vertices_at x g)
    (vertex_at x gx * (vertex_at x gx -* reachable_vertices_at x g)).
Proof. apply va_reachable_root_stable_ramify. Qed.

Lemma root_update_ramify: forall (g: Graph) (x: V) (lx: bool) (gx gx': GV),
  vvalid g x ->
  vgamma (Graph_PointwiseGraph g) x = gx ->
  vgamma (Graph_PointwiseGraph (labeledgraph_vgen g x lx)) x = gx' ->
  Included (Intersection V (reachable g x) (Complement V (eq x))) (vguard g) ->
  Included (Intersection V (reachable g x) (Complement V (eq x))) (vguard (labeledgraph_vgen g x lx)) ->
  @derives Pred _
    (reachable_vertices_at x g)
    (vertex_at x gx *
      (vertex_at x gx' -* reachable_vertices_at x (labeledgraph_vgen g x lx))).
Proof. apply va_reachable_root_update_ramify. Qed.

(* TODO: remove this lemma? *)
Lemma exp_mark1: forall (g: Graph) (x: V) (lx: bool),
  WeakMarkGraph.label_marked lx ->
  @derives Pred _ (reachable_vertices_at x (labeledgraph_vgen g x lx)) (EX g': Graph, !! (mark1 x g g') && reachable_vertices_at x g').
Proof.
  intros.
  apply (exp_right (labeledgraph_vgen g x lx)).
  apply andp_right; [apply prop_right | auto].
  apply WeakMarkGraph.vertex_update_mark1; auto.
Qed.

Lemma mark_neighbor_ramify: forall {A} (g1: Graph) (g2: A -> Graph) x y,
  (forall (g: Graph) x y, reachable g x y \/ ~ reachable g x y) ->
  vvalid g1 x ->
  step g1 x y ->
  Included (Intersection V (reachable g1 x) (Complement V (reachable g1 y)))
     (vguard g1) ->
  (forall a, mark y g1 (g2 a) -> Included (Intersection V (reachable g1 x) (Complement V (reachable g1 y))) (vguard (g2 a))) ->
  @derives Pred _
    (reachable_vertices_at x g1)
    (reachable_vertices_at y g1 *
      (ALL a: A, !! mark y g1 (g2 a) -->
        (reachable_vertices_at y (g2 a) -*
         reachable_vertices_at x (g2 a)))).
Proof.
  intros.
  assert (Included (reachable g1 y) (reachable g1 x)).
  1: {
    hnf; unfold Ensembles.In; intros.
    apply step_reachable with y; auto.
  }  
  apply vertices_at_ramif_xQ. eexists. split; [|split].
  + apply Ensemble_join_Intersection_Complement; auto. 
  + intros. destruct H5 as [_ ?].
    rewrite <- H5; clear H5.
    apply Ensemble_join_Intersection_Complement; auto.
  + intros.
    apply GSG_PartialGraphPreserve; auto.
    - unfold Included, Ensembles.In; intros.
      rewrite Intersection_spec in H6; destruct H6 as [? _].
      apply reachable_foot_valid in H6; auto.
    - destruct H5.
      rewrite H6; clear H6.
      unfold Included, Ensembles.In; intros.
      rewrite Intersection_spec in H6; destruct H6 as [? _].
      apply reachable_foot_valid in H6; auto.
    - apply mark_partial_labeled_graph_equiv in H5.
      eapply si_stronger_partial_labeledgraph_simple; [| eassumption].
      unfold Included, Ensembles.In; intros.
      rewrite Intersection_spec in H6.
      tauto.
Qed.

Lemma mark_list_mark_ramify: forall {A} (g1 g2: Graph) (g3: A -> Graph) x l y l',
  (forall (g: Graph) x y, reachable g x y \/ ~ reachable g x y) ->
  vvalid g1 x ->
  step_list g1 x (l ++ y :: l') ->
  relation_list (mark1 x :: mark_list l :: nil) g1 g2 ->
  Included (Intersection V (reachable g2 x) (Complement V (reachable g2 y)))
     (vguard g2) ->
  (forall a, mark y g2 (g3 a) -> Included (Intersection V (reachable g2 x) (Complement V (reachable g2 y))) (vguard (g3 a))) ->
  @derives Pred _
    (reachable_vertices_at x g2)
    (reachable_vertices_at y g2 *
      (ALL a: A, !! mark y g2 (g3 a) -->
        (reachable_vertices_at y (g3 a) -*
         reachable_vertices_at x (g3 a)))).
Proof.
  intros. 
  destruct_relation_list g1' in H2.
  destruct H5 as [? _].
  apply (mark_list_eq x) in H2.
  destruct H2 as [_ ?].
  rewrite <- H5 in H2; clear g1' H5.
  apply mark_neighbor_ramify; auto.
  + destruct H2. rewrite <- (H2 x). auto.
  + rewrite <- (step_si g1); auto. hnf in H1. rewrite <- H1.
    rewrite in_app_iff. right. apply in_eq.
Qed.

End PointwiseGraph_Mark.
