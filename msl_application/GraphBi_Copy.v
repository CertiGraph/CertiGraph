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

Instance MGS: WeakMarkGraph.MarkGraphSetting addr.
  apply (WeakMarkGraph.Build_MarkGraphSetting addr
          (fun x => ~ (x = null))).
  intros.
  destruct_eq_dec x null; [right | left]; auto.
Defined.

Instance GMS: GraphMorphismSetting addr (addr * LR) addr (addr * LR) addr (addr * LR).
  apply (Build_GraphMorphismSetting _ _ _ _ _ _ (fun x => x) (fun x => x) null (null, L)).
Defined.

Instance CCSS: CompactCopySpatialSetting SGP.
  apply (Build_CompactCopySpatialSetting _ _ _ _ _ _ _  _ null (null, L) SGAvn).
Defined.

(*
Lemma vlabel_eq: forall (g1 g2: Graph) x1 x2, (WeakMarkGraph.marked g1 x1 <-> WeakMarkGraph.marked g2 x2) -> vlabel g1 x1 = vlabel g2 x2.
Proof.
  intros.
  simpl in H.
  destruct H.
  destruct (vlabel g1 x1), (vlabel g2 x2); try congruence.
  + tauto.
  + symmetry; tauto.
Qed.

Lemma mark_null_refl: forall (g: Graph), mark null g g.
Proof. intros. apply mark_invalid_refl, invalid_null. Qed.

Lemma mark_vgamma_true_refl: forall (g: Graph) root d l r, vgamma g root = (d, l, r) -> d = true -> mark root g g.
Proof.
  intros.
  apply mark_marked_root_refl.
  inversion H.
  simpl; congruence.
Qed.
*)

Lemma Graph_gen_true_mark1: forall (G: Graph) (x y: addr) l r,
  vgamma G x = (null, l, r) ->
  vvalid G x ->
  y <> null ->
  vcopy1 x (G: LabeledGraph _ _ _ _) (Graph_gen G x y: LabeledGraph _ _ _ _).
Proof.
  intros.
  split; [| split].
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
  + split; [| split].
    - reflexivity.
    - apply guarded_pointwise_relation_spec; intros.
      simpl.
      unfold update_vlabel; simpl.
      destruct_eq_dec x x0; [congruence | auto].
    - apply guarded_pointwise_relation_spec; intros.
      auto.
Qed.

Lemma graph_ramify_left: forall {RamUnit: Type} (g g1: Graph) x l r l' (F: pred),
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 ->
  reachable_vertices_at x g1 * F |-- reachable_vertices_at l g1 *
   (ALL a: RamUnit * Graph * Graph,
     !! (copy l g1 (snd (fst a)) (snd a)) -->
     ((reachable_vertices_at l (snd (fst a)) * reachable_vertices_at l' (snd a)) -* (reachable_vertices_at x (snd (fst a))) * reachable_vertices_at l' (snd a) * F)).
Proof.
  intros.
  destruct H1 as [? [? ?]].
  RAMIF_Q'.formalize.
  apply RAMIF_Q'.frame; [auto |].
  apply RAMIF_Q'.frame_post; [auto |].
  simpl.
  eapply vertices_at_ramif_xQ.
  eexists.
  split; [| split].
  + rewrite <- H1.
    eapply Prop_join_reachable_left; eauto.
  + intros.
    destruct H4 as [? [? ?]].
    rewrite <- H4, <- H1.
    eapply Prop_join_reachable_left; eauto.
  + intros [[? ?] ?] ?.
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

Lemma extend_copy_left: forall (g g1 g2 g2': Graph) (x l r: addr) dx',
  let g1': LGraph := single_vertex_labeledgraph (LocalGraphCopy.vmap g1 x) null (null, L) in
  let x' := (LocalGraphCopy.vmap g1 x) in
  let l' := (LocalGraphCopy.vmap g2 l) in
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 ->
  copy l g1 g2 g2' -> 
  (full_vertices_at g2': pred) * vertex_at x' dx' |-- 
  EX g2'': LGraph,
    !! extended_copy l (g1: LGraph, g1') (g2: LGraph, g2'') && 
    (vertices_at (fun x => vvalid g2'' x /\ x' <> x) g2'' * vertex_at x' dx').
Proof.
 Abort.
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


