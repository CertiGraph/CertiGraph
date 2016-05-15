Require Import RamifyCoq.lib.Ensembles_ext.
Require Import Coq.Lists.List.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.msl.ramification_lemmas.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Morphisms_ext.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.dag.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.graph_morphism.
Require Import RamifyCoq.graph.local_graph_copy.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GraphBi.
Require Import RamifyCoq.msl_application.Graph_Copy.
Require Import Coq.Logic.Classical.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Open Scope logic.

Section SpatialGraph_Copy_Bi.

Context {pSGG_Bi: pSpatialGraph_Graph_Bi}.
Context {sSGG_Bi: sSpatialGraph_Graph_Bi addr (addr * LR)}.

Existing Instances pSGG_Bi sSGG_Bi.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_SpatialGraph: SGraph >-> SpatialGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Notation Graph := (@Graph pSGG_Bi addr (addr * LR)).

Instance CCS: CompactCopySetting addr (addr * LR).
  apply (Build_CompactCopySetting _ _ null (null, L)).
Defined.

Global Existing Instance CCS.

Definition empty_Graph: Graph := empty_Graph null (null, L).

Definition initial_copied_Graph (x x0: addr) (g: Graph): LGraph := single_vertex_labeledgraph (LocalGraphCopy.vmap (Graph_gen g x x0) x) null (null, L).

Opaque empty_Graph initial_copied_Graph.

Lemma copy_null_refl: forall (g: Graph),
  copy null g g empty_Graph.
Proof. intros; apply copy_invalid_refl, invalid_null; auto. Qed.

Lemma copy_vgamma_not_null_refl: forall (g: Graph) (root: addr) d l r,
  vgamma g root = (d, l, r) ->
  d <> null ->
  copy root g g empty_Graph.
Proof.
  intros; apply marked_root_copy_refl.
  simpl.
  inversion H.
  subst; congruence.
Qed.

Lemma root_stable_ramify: forall (g: Graph) (x: addr) (gx: addr * addr * addr),
  vgamma g x = gx ->
  vvalid g x ->
  @derives pred _
    (reachable_vertices_at x g)
    (vertex_at x gx *
      (vertex_at x gx -* reachable_vertices_at x g)).
Proof. intros; apply va_reachable_root_stable_ramify; auto. Qed.

Lemma root_update_ramify: forall (g: Graph) (x x0: addr) (lx: addr) (gx gx': addr * addr * addr) F,
  vgamma g x = gx ->
  vgamma (Graph_gen g x lx) x = gx' ->
  vvalid g x ->
  @derives pred _
    (F * reachable_vertices_at x g)
    (vertex_at x gx *
      (vertex_at x gx' -*
       F * (vertices_at (fun u => vvalid (initial_copied_Graph x x0 g) u /\ x0 <> u) (initial_copied_Graph x x0 g) * reachable_vertices_at x (Graph_gen g x lx)))).
Proof.
  intros.
  rewrite !(sepcon_comm F).
  apply RAMIF_PLAIN.frame.
  assert (vertices_at (fun u : addr => vvalid (initial_copied_Graph x x0 g) u /\ x0 <> u) (initial_copied_Graph x x0 g) = emp).
  Focus 1. {
    erewrite <- vertices_at_False.
    apply vertices_at_Same_set.
    rewrite Same_set_spec; intros ?.
Transparent initial_copied_Graph. simpl. Opaque initial_copied_Graph.
    unfold update_vlabel.
    if_tac; [| congruence].
    split; [intros [? ?]; congruence | tauto].
  } Unfocus.
  rewrite H2, emp_sepcon.
  apply va_reachable_root_update_ramify; auto.
Qed.

Lemma not_null_copy1: forall (G: Graph) (x x0: addr) l r,
  vgamma G x = (null, l, r) ->
  vvalid G x ->
  x0 <> null ->
  vcopy1 x G (Graph_gen G x x0) (initial_copied_Graph x x0 G) /\ x0 = LocalGraphCopy.vmap (Graph_gen G x x0) x.
Proof.
  intros.
  split; [split; [| split] |].
  + reflexivity.
  + split; [| split].
    - reflexivity.
    - simpl.
      unfold update_vlabel.
      destruct_eq_dec x x; congruence.
    - intros.
      simpl.
      unfold update_vlabel; simpl.
      destruct_eq_dec x n'; [congruence |].
      tauto.
  + split; [| split; [| split]].
    - reflexivity.
    - apply guarded_pointwise_relation_spec; intros.
      simpl.
      unfold update_vlabel; simpl.
      destruct_eq_dec x x1; [congruence | auto].
    - apply guarded_pointwise_relation_spec; intros.
      auto.
    - reflexivity.
  + simpl.
    unfold update_vlabel; simpl.
    destruct_eq_dec x x; [auto | congruence].
Qed.

Lemma left_weak_valid: forall (G G1: Graph) (G1': LGraph) (x l r: addr),
  vgamma G x = (null, l, r) ->
  vvalid G x ->
  vcopy1 x G G1 G1' ->
  @weak_valid _ _ _ _ G1 (maGraph _) l.
Proof.
  intros.
  destruct H1 as [? _].
  eapply weak_valid_si; [symmetry; exact H1 |].
  eapply gamma_left_weak_valid; eauto.
Qed.

Lemma right_weak_valid: forall (G G1 G3: Graph) (G1' G3': LGraph) (x l r: addr),
  vgamma G x = (null, l, r) ->
  vvalid G x ->
  vcopy1 x G G1 G1' ->
  edge_copy G (x, L) (G1: LGraph, G1') (G3: LGraph, G3') ->
  @weak_valid _ _ _ _ G3 (maGraph _) r.
Proof.
  intros.
  destruct H1 as [? _].
  unfold edge_copy in H2.
  destruct_relation_list GG2 in H2.
  destruct GG2 as [G2 G2'].
  destruct H3 as [? _].
  destruct H2 as [? _].
  rewrite <- H3, <- H1 in H2.
  eapply weak_valid_si; [symmetry; eauto |].
  eapply gamma_right_weak_valid; eauto.
Qed.

Lemma graph_ramify_left: forall {RamUnit: Type} (g g1: Graph) (g1': LGraph) (x l r: addr) (F1 F2: pred),
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  F1 * (F2 * reachable_vertices_at x g1) |--
  reachable_vertices_at l g1 *
   (ALL a: RamUnit * Graph * Graph * addr,
     !! (copy l g1 (snd (fst a)) (snd (fst (fst a))) /\ (l = null /\ snd a = null \/ snd a = LocalGraphCopy.vmap (snd (fst a)) l)) -->
     (reachable_vertices_at l (snd (fst a)) * reachable_vertices_at (snd a) (snd (fst (fst a))) -*
      F1 * (F2 * (reachable_vertices_at x (snd (fst a)) * reachable_vertices_at (snd a) (snd (fst (fst a))))))).
Proof.
  intros.
  destruct H1 as [? [? ?]].
  rewrite <- sepcon_assoc, (sepcon_comm (F1 * F2)).
  RAMIF_Q'.formalize.
  match goal with
  | |- _ |-- _ * allp (_ --> (_ -* ?A)) =>
    replace A with
    (fun p : RamUnit * Graph * Graph * addr =>
            reachable_vertices_at x (snd (fst p)) *
            reachable_vertices_at (snd p) (snd (fst (fst p))) * (F1 * F2)) by
    (extensionality p; rewrite <- (sepcon_assoc F1 F2), (sepcon_comm _ (F1 * F2)); auto)
  end.
  apply RAMIF_Q'.frame; [auto |].
  apply RAMIF_Q'.frame_post; [auto |].
  simpl.

  eapply vertices_at_ramif_xQ.
  eexists.
  split; [| split].
  + rewrite <- H1.
    eapply Prop_join_reachable_left; eauto.
  + intros.
    destruct H4 as [[? [? ?]] _].
    rewrite <- H4, <- H1.
    eapply Prop_join_reachable_left; eauto.
  + intros [[[? ?] ?] ?] [? _].
    simpl in H4 |- *; clear r0.
    apply GSG_PartialGraphPreserve.
    - rewrite H1.
      unfold Included, Ensembles.In.
      intros.
      apply vvalid_vguard.
      rewrite Intersection_spec in H5; destruct H5.
      apply reachable_foot_valid in H5; auto.
    - rewrite H1.
      destruct H4 as [? _]; rewrite H4.
      unfold Included, Ensembles.In.
      intros.
      apply vvalid_vguard.
      rewrite Intersection_spec in H5; destruct H5.
      apply reachable_foot_valid in H5; auto.
    - rewrite H1.
      unfold Included, Ensembles.In.
      intros.
      rewrite Intersection_spec in H5; destruct H5.
      apply reachable_foot_valid in H5; auto.
    - rewrite H1.
      destruct H4 as [? _]; rewrite H4.
      unfold Included, Ensembles.In.
      intros.
      rewrite Intersection_spec in H5; destruct H5.
      apply reachable_foot_valid in H5; auto.
    - admit.
Qed.

Lemma extend_copy_left: forall (g g1 g2: Graph) (g1' g2'': LGraph) (x l r x0 l0: addr),
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  copy l g1 g2 g2'' ->
  x0 = LocalGraphCopy.vmap g1 x ->
  l = null /\ l0 = null \/ l0 = LocalGraphCopy.vmap g2 l ->
  @derives pred _
  (vertices_at (fun x => vvalid g1' x /\ x0 <> x) g1' * reachable_vertices_at l0 g2'') 
  (EX g2': LGraph,
    !! edge_copy g (x, L) (g1: LGraph, g1') (g2: LGraph, g2') && 
    vertices_at (fun x => vvalid g2' x /\ x0 <> x) g2').
Proof.
  intros.
  pose proof vcopy1_edge_copy_list_copy_extended_copy x ((x, L) :: (x, R) :: nil) nil (x, L) ((x, R) :: nil) g g1 g1 g1' g1' g2 g2''.
Admitted.
(*
  intros.
  pose proof WeakMarkGraph.triple_mark1 x g g g1 as HH1.
  spec HH1; [apply WeakMarkGraph.eq_do_nothing; auto |].
  spec HH1; [destruct H1 as [? [? ?]]; auto |].
  cbv zeta in HH1; destruct HH1 as [_ HH1].
  pose proof LocalGraphCopy.copy_extend_copy g g1 g2 g1' g2' x
    ((x, L):: (x,R) :: nil) nil (x, L) ((x, R) :: nil) (WeakMarkGraph.marked g) as HH2.
  spec HH2; [auto |].
  spec HH2; [simpl in H0 |- *; inversion H0; congruence |].
  spec HH2; [intros; apply (@biGraph_out_edges _ _ _ _ _ _ g (biGraph g)); auto |].
  spec HH2; [simpl; repeat constructor; simpl; [clear; intros [HH | []]; inversion HH | tauto] |].
  spec HH2; [reflexivity |].
  spec HH2; [intros; apply decidable_prop_decidable; apply node_pred_dec |].
  hnf in HH2.
  spec HH2; [simpl map; rewrite <- HH1; destruct H2 as [_ [_ ?]]; inversion H0; rewrite H5; exact H2 |].
  unfold full_vertices_at.
  rewrite (add_andp _ _ (vertex_at_sepcon_unique_x1 g2' x' (vvalid g2') dx')).
  normalize.
  spec HH2.
  Focus 1. {
    clear HH2.
    split.
    + simpl in x' |- *.
      rewrite Disjoint_spec.
      intros; subst.
      subst x'; tauto.
    + simpl.
      rewrite Disjoint_spec.
      auto.
  } Unfocus.
  spec HH2.
  Focus 1. {
    clear HH2.
    intros.
    simpl map.
    rewrite <- (app_same_set HH1).
    apply decidable_prop_decidable; apply node_pred_dec.
  } Unfocus.
  destruct HH2 as [g2'' [? [? ?]]]; apply (exp_right g2'').
  apply andp_right.
  + apply prop_right.
    split; [| split]; destruct H2 as [? [? ?]]; auto.
    simpl map in H4; rewrite <- HH1 in H4.
    inversion H0; auto.
  + apply sepcon_derives; [| auto].
    apply derives_refl'; apply vertices_at_subgraph_eq.
    - apply Included_refl.
    - unfold Included, Ensembles.In.
      intros; tauto.
    - unfold LGraph_SGraph.
      rewrite @GSG_SubGraphPreserve.
SearchAbout predicate_sub_spatialgraph (_ -> validly_identical _ _).
Locate GSG_PartialGraphPreserve.
*)

(*
Lemma graph_ramify_right: forall {RamUnit: Type} (g g1 g2: Graph) x l r,
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 ->
  c l g1 g2 ->
  (graph x g2: pred) |-- graph r g2 *
   (ALL a: RamUnit * Graph,
     !! (mark r g2 (snd a)) -->
     (graph r (snd a) -* graph x (snd a))).
Proof.
  intros.
  destruct H1 as [? _].
  destruct H2 as [_ ?].
  eapply vertices_at_ramify_Q; auto.
  + rewrite <- H2, <- H1.
    eapply Prop_join_reachable_right; eauto.
  + intros.
    destruct H3 as [_ ?].
    rewrite <- H3, <- H2, <- H1.
    eapply Prop_join_reachable_right; eauto.
  + intros ? [? ?] ? ?.
    simpl; unfold gamma.
    rewrite Intersection_spec in H5; unfold Complement, Ensembles.In in H5; destruct H5.
    f_equal; [f_equal |].
    - apply vlabel_eq.
      rewrite (proj2 H3).
      rewrite <- H2, <- H1.
      pose proof reachable_by_subset_reachable g r (WeakMarkGraph.unmarked g2) x0.
      unfold Ensembles.In in H7.
      tauto.
    - apply dst_L_eq; auto.
      rewrite H1, H2 in H5.
      apply reachable_foot_valid in H5; auto.
    - apply dst_R_eq; auto.
      rewrite H1, H2 in H5.
      apply reachable_foot_valid in H5; auto.
Qed.

Lemma mark1_mark_left_mark_right: forall (g1 g2 g3 g4: Graph) root l r,
  vvalid g1 root ->
  vgamma g1 root = (false, l, r) ->
  mark1 root g1 g2 ->
  mark l g2 g3 ->
  mark r g3 g4 ->
  mark root g1 g4.
Proof.
  intros.
  apply (mark1_mark_list_mark root (l :: r :: nil)); auto.
  + intros; simpl.
    inversion H0.
    unfold Complement, Ensembles.In.
    rewrite H5; congruence.
  + hnf; intros.
    apply gamma_step with (y := n') in H0; auto.
    rewrite H0; simpl.
    pose proof eq_sym_iff n' l.
    pose proof eq_sym_iff n' r.
    tauto.
  + split_relation_list ((lg_gg g2) :: nil); eauto.
    unfold mark_list.
    simpl map.
    split_relation_list ((lg_gg g3) :: nil); eauto.
Qed.
*)

End SpatialGraph_Copy_Bi.


