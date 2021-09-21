Require Import CertiGraph.lib.Ensembles_ext.
Require Import Coq.Lists.List.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.msl.ramification_lemmas.
Require Import VST.msl.Coqlib2.
Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.relation_list.
Require Import CertiGraph.lib.Morphisms_ext.
Require Import CertiGraph.msl_ext.log_normalize.
Require Import CertiGraph.msl_ext.iter_sepcon.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.path_lemmas.
Require Import CertiGraph.graph.reachable_computable.
Require Import CertiGraph.graph.reachable_ind.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.graph_relation.
Require Import CertiGraph.graph.subgraph2.
Require Import CertiGraph.graph.dag.
Require Import CertiGraph.graph.weak_mark_lemmas.
Require Import CertiGraph.graph.graph_morphism.
Require Import CertiGraph.graph.local_graph_copy.
Require Import CertiGraph.msl_application.Graph.
Require Import CertiGraph.msl_application.GraphBi.
Require Import CertiGraph.msl_application.Graph_Copy.
Require Import Coq.Logic.Classical.

Open Scope logic.

Section PointwiseGraph_Copy_Bi.

Context {pSGG_Bi: pPointwiseGraph_Graph_Bi}.
Context {sSGG_Bi: sPointwiseGraph_Graph_Bi addr (addr * LR)}.

Existing Instances pSGG_Bi sSGG_Bi SGAvn.

Local Coercion Graph'_LGraph: Graph' >-> LGraph.
Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion Graph'_GeneralGraph: Graph' >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Notation Graph := (@Graph pSGG_Bi addr (addr * LR) unit).
Notation Graph' := (@Graph' pSGG_Bi addr (addr * LR) unit).

Instance CCS: CompactCopySetting addr (addr * LR) unit.
  apply (Build_CompactCopySetting _ _ _ null (null, L) tt).
Defined.

Global Existing Instance CCS.

Definition empty_Graph': Graph' := empty_Graph' null (null, L) tt.

Definition initial_copied_Graph (x x0: addr) (g: Graph): LGraph 
  := single_vertex_labeledgraph (LocalGraphCopy.vmap (Graph_vgen g x x0) x) null (null, L) tt.

Opaque empty_Graph initial_copied_Graph.

Lemma vertex_at_not_null: forall (x: addr) (gx: addr * addr * addr),
  @derives pred _
    (vertex_at x gx) (!! (null <> x)).
Proof.
  intros.
  destruct (classic (null = x)).
  + subst x.
    apply derives_trans with FF.
    apply vertex_at_not_null.
    apply FF_left.
  + apply prop_right; auto.
Qed.

Lemma copy_null_refl: forall (g: Graph),
  copy null g g empty_Graph'.
Proof. intros; apply copy_invalid_refl, invalid_null; auto. Qed.

Lemma copy_vgamma_not_null_refl: forall (g: Graph) (root: addr) d l r,
  vgamma g root = (d, l, r) ->
  d <> null ->
  copy root g g empty_Graph'.
Proof.
  intros; apply marked_root_copy_refl.
  simpl.
  inversion H.
  subst; congruence.
Qed.

Lemma vmap_weaken: forall (g1: Graph) (g2: Graph') x x0 BLA,
  (x = null /\ x0 = null \/ x0 = BLA) ->
  (~ vvalid g1 x /\ ~ vvalid g2 x0 \/ x0 = BLA).
Proof.
  intros.
  destruct H; [left | right]; auto.
  destruct H.
  pose proof (@valid_not_null _ _ _ _ g1 _ (maGraph g1) x).
  pose proof (@valid_not_null' _ _ _ _ g2 _ (maGraph' g2) x0).
  unfold is_null_SGBA in *; simpl in *.
  auto.
Qed.

Lemma root_stable_ramify: forall (g: Graph) (x: addr) (gx: addr * addr * addr),
  vgamma g x = gx ->
  vvalid g x ->
  @derives pred _
    (reachable_vertices_at x g)
    (vertex_at x gx *
      (vertex_at x gx -* reachable_vertices_at x g)).
Proof. intros; apply va_reachable_root_stable_ramify; auto. Qed.

Lemma root_update_ramify1: forall (g: Graph) (x x0: addr) (lx: addr) (gx gx': addr * addr * addr),
  vvalid g x ->
  vertices_at (Intersection _ (vvalid (initial_copied_Graph x x0 g)) (fun u : addr => x0 <> u)) (initial_copied_Graph x x0 g) = emp.
Proof.
  intros.
    erewrite <- vertices_at_False.
    apply vertices_at_Same_set.
    rewrite Same_set_spec; intros ?.
Transparent initial_copied_Graph. simpl. Opaque initial_copied_Graph.
    unfold update_vlabel.
    if_tac; [| congruence].
    split; [intros [? ?]; congruence | tauto].
Qed.

Lemma root_update_ramify2: forall (g: Graph) (x x0: addr) (lx: addr) (gx gx': addr * addr * addr) F,
  vgamma g x = gx ->
  vgamma (Graph_vgen g x lx) x = gx' ->
  vvalid g x ->
  @derives pred _
    (F * reachable_vertices_at x g)
    (vertex_at x gx *
      (vertex_at x gx' -*
       F * (emp * reachable_vertices_at x (Graph_vgen g x lx)))).
Proof.
  intros.
  rewrite !(sepcon_comm F).
  apply RAMIF_PLAIN.frame.
  rewrite emp_sepcon.
  apply va_reachable_root_update_ramify; auto.
Qed.

Lemma root_update_ramify (* {sSGG_Bi': sPointwiseGraph_Graph_Bi addr (addr * LR)} *): forall (g: Graph) (x x0: addr) (lx: addr) (gx gx': addr * addr * addr) F,
  vgamma g x = gx ->
  vgamma (Graph_vgen g x lx) x = gx' ->
  vvalid g x ->
  @derives pred _
    (F * @reachable_vertices_at _ _ _ _ (@SGBA pSGG_Bi) _ _ _ (@SGC_Bi pSGG_Bi _ _ _) _ (@SGP pSGG_Bi _ _ sSGG_Bi) (@SGA pSGG_Bi _ _ sSGG_Bi) x g)
    (vertex_at x gx *
      (vertex_at x gx' -*
       F * (@vertices_at _ _ _ _ (@SGBA pSGG_Bi) _ (@SGP pSGG_Bi _ _ sSGG_Bi) _ (Intersection _ (vvalid (initial_copied_Graph x x0 g)) (fun u : addr => x0 <> u)) (initial_copied_Graph x x0 g) * reachable_vertices_at x (Graph_vgen g x lx)))).
Proof.
  intros.
  rewrite !(sepcon_comm F).
  apply RAMIF_PLAIN.frame.
  assert (@vertices_at _ _ _ _ (@SGBA pSGG_Bi) _ (@SGP pSGG_Bi _ _ sSGG_Bi) _ (Intersection _ (vvalid (initial_copied_Graph x x0 g)) (fun u : addr => x0 <> u)) (initial_copied_Graph x x0 g) = emp).
  {
    erewrite <- vertices_at_False.
    apply vertices_at_Same_set.
    rewrite Same_set_spec; intros ?.
Transparent initial_copied_Graph. simpl. Opaque initial_copied_Graph.
    unfold update_vlabel.
    if_tac; [| congruence].
    split; [intros [? ?]; congruence | tauto].
  }
  rewrite H2, emp_sepcon.
  apply va_reachable_root_update_ramify; auto.
Qed.
        
Lemma not_null_copy1: forall (G: Graph) (x x0: addr) l r,
  vgamma G x = (null, l, r) ->
  vvalid G x ->
  x0 <> null ->
  vcopy1 x G (Graph_vgen G x x0) (initial_copied_Graph x x0 G) /\
  x0 = LocalGraphCopy.vmap (Graph_vgen G x x0) x /\
  is_guarded_BiMaFin' (fun v => x0 <> v) (fun e => ~ In e nil) (initial_copied_Graph x x0 G).
Proof.
  intros.
  split; [split; [| split] | split].
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
  + assert (LocalGraphCopy.vmap (Graph_vgen G x x0) x = x0).
    1: {
      simpl.
      unfold update_vlabel; simpl.
      destruct_eq_dec x x; auto; congruence.
    }
    pattern x0 at 1; rewrite <- H2.
    apply single_vertex_guarded_BiMaFin'.
Qed.

Lemma left_weak_valid: forall (G G1: Graph) (G1': LGraph) (x l r: addr),
  vgamma G x = (null, l, r) ->
  vvalid G x ->
  vcopy1 x G G1 G1' ->
  @weak_valid _ _ _ _ G1 _ (maGraph _) l.
Proof.
  intros.
  destruct H1 as [? _].
  eapply weak_valid_si; [symmetry; exact H1 |].
  eapply gamma_left_weak_valid; eauto.
Qed.

Lemma right_weak_valid: forall (G G1 G2 G3: Graph) (G1' G2' G3': LGraph) (x l r: addr),
  vgamma G x = (null, l, r) ->
  vvalid G x ->
  vcopy1 x G G1 G1' ->
  extended_copy l (G1: LGraph, G1') (G2: LGraph, G2') ->
  ecopy1 (x, L) (G2: LGraph, G2') (G3: LGraph, G3') ->
  @weak_valid _ _ _ _ G3 _ (maGraph _) r.
Proof.
  intros.
  destruct H1 as [? _], H2 as [? _], H3 as [? _].
  rewrite <- H2, <- H1 in H3.
  eapply weak_valid_si; [symmetry; eauto |].
  eapply gamma_right_weak_valid; eauto.
Qed.

Lemma graph_ramify_left: forall (g g1: Graph) (g1': LGraph) (x l r: addr) (F1 F2: pred) F3,
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  F1 * (F2 * reachable_vertices_at x g1) |--
  reachable_vertices_at l g1 *
   (ALL a: Graph' * Graph * addr,
     !! (copy l g1 (snd (fst a)) (fst (fst a)) /\ (l = null /\ snd a = null \/ snd a = LocalGraphCopy.vmap (snd (fst a)) l)) -->
     (reachable_vertices_at l (snd (fst a)) * F3 (snd a) (fst (fst a)) -*
      F1 * (F2 * (reachable_vertices_at x (snd (fst a)) * F3 (snd a) (fst (fst a)))))).
Proof.
  intros.
  destruct H1 as [? [? ?]].
  rewrite <- sepcon_assoc, (sepcon_comm (F1 * F2)).
  RAMIF_Q'.formalize.
  match goal with
  | |- _ |-- _ * allp (_ --> (_ -* ?A)) =>
    replace A with
    (fun p : Graph' * Graph * addr =>
            reachable_vertices_at x (snd (fst p)) *
            F3 (snd p) (fst (fst p)) * (F1 * F2)) by
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
  + intros [[? ?] ?] [? _].
    simpl in H4 |- *.
    rewrite vertices_identical_spec.
    intros.
    simpl.
    destruct H4 as [? [? ?]].
    f_equal; [f_equal |].
    - destruct H7 as [_ [? _]].
      rewrite guarded_pointwise_relation_spec in H7.
      apply H7; clear H7.
      unfold Complement, Ensembles.In.
      intro.
      apply reachable_by_is_reachable in H7.
      rewrite Intersection_spec in H5.
      rewrite <- H1 in H7.
      destruct H5; auto.
    - apply dst_L_eq; auto.
      rewrite Intersection_spec in H5.
      destruct H5 as [? _].
      rewrite H1 in H5.
      apply reachable_foot_valid in H5; auto.
    - apply dst_R_eq; auto.
      rewrite Intersection_spec in H5.
      destruct H5 as [? _].
      rewrite H1 in H5.
      apply reachable_foot_valid in H5; auto.
Qed.

Lemma graph_ramify_right: forall (g g1 g2 g3: Graph) (g1' g2' g3': LGraph) (x l r: addr) (F1 F2: pred) F3,
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  extended_copy l (g1: LGraph, g1') (g2: LGraph, g2') ->
  ecopy1 (x, L) (g2: LGraph, g2') (g3: LGraph, g3') ->
  F1 * (F2 * reachable_vertices_at x g3) |--
  reachable_vertices_at r g3 *
   (ALL a: Graph' * Graph * addr,
     !! (copy r g3 (snd (fst a)) (fst (fst a)) /\ (r = null /\ snd a = null \/ snd a = LocalGraphCopy.vmap (snd (fst a)) r)) -->
     (reachable_vertices_at r (snd (fst a)) * F3 (snd a) (fst (fst a)) -*
      F1 * (F2 * (reachable_vertices_at x (snd (fst a)) * F3 (snd a) (fst (fst a)))))).
Proof.
  intros.
  destruct H1 as [? [? ?]].
  rewrite <- sepcon_assoc, (sepcon_comm (F1 * F2)).
  RAMIF_Q'.formalize.
  match goal with
  | |- _ |-- _ * allp (_ --> (_ -* ?A)) =>
    replace A with
    (fun p : Graph' * Graph * addr =>
            reachable_vertices_at x (snd (fst p)) *
            F3 (snd p) (fst (fst p)) * (F1 * F2)) by
    (extensionality p; rewrite <- (sepcon_assoc F1 F2), (sepcon_comm _ (F1 * F2)); auto)
  end.
  apply RAMIF_Q'.frame; [auto |].
  apply RAMIF_Q'.frame_post; [auto |].
  simpl.

  eapply vertices_at_ramif_xQ.
  eexists.
  split; [| split].
  + destruct H2 as [? _], H3 as [? _]; rewrite <- s0, <- s, <- H1.
    eapply Prop_join_reachable_right; eauto.
  + intros.
    destruct H6 as [[? [? ?]] _].
    destruct H2 as [? _], H3 as [? _]. rewrite <- H6, <- H3, <- H2, <- H1.
    eapply Prop_join_reachable_right; eauto.
  + intros [[[? ?] ?] ?] [? _].
    destruct H2 as [? _], H3 as [? _]; rewrite H2, H3 in H1.
    simpl in H6 |- *.
    rewrite vertices_identical_spec.
    intros.
    simpl.
    destruct H6 as [? [? ?]].
    f_equal; [f_equal |].
    - destruct H9 as [_ [? _]].
      rewrite guarded_pointwise_relation_spec in H9.
      apply H9; clear H9.
      unfold Complement, Ensembles.In.
      intro.
      apply reachable_by_is_reachable in H9.
      rewrite Intersection_spec in H7.
      rewrite <- H1 in H9.
      destruct H7; auto.
    - apply dst_L_eq; auto.
      rewrite Intersection_spec in H7.
      destruct H7 as [? _].
      rewrite H1 in H7.
      apply reachable_foot_valid in H7; auto.
    - apply dst_R_eq; auto.
      rewrite Intersection_spec in H7.
      destruct H7 as [? _].
      rewrite H1 in H7.
      apply reachable_foot_valid in H7; auto.
Qed.

Lemma is_BiMaFin_disjoint_guard: forall (g1':  @LGraph pSGG_Bi (@addr pSGG_Bi) (prod (@addr pSGG_Bi) LR) unit) (g2'': Graph') x0 es0,
  is_guarded_BiMaFin' (fun v => x0 <> v) (fun e => ~ In e es0) g1' ->
  vvalid g1' x0 ->
  (forall e, In e es0 -> fst e = x0) ->
  Disjoint addr (vvalid g2'') (vvalid g1') ->
  disjointed_guard (vvalid g2'') (vvalid g1') (evalid g2'') (evalid g1').
Proof.
  intros.
  split; auto.
  rewrite Disjoint_spec in *.
  intros e ? ?.
  pose proof @valid_graph' _ _ _ _ g2'' _ (maGraph' _) e H3.
  apply (H2 _ H5).
  destruct (in_dec equiv_dec e es0); destruct e as [v lr].
  + specialize (H1 _ i).
    simpl in H1.
    rewrite left_right_sound0' by auto.
    subst; auto.
  + destruct H as [X _].
    pose (pg1 := Build_GeneralGraph _ _ _ (fun g: LGraph => BiMaFin' g) (gpredicate_sub_labeledgraph (fun v => x0 <> v) (fun e => ~ In e es0) g1') X: Graph').
    assert (evalid pg1 (v, lr)) by (simpl; rewrite Intersection_spec; split; auto).
    assert (src g2'' (v, lr) = src pg1 (v, lr)) by (rewrite !left_right_sound0'; auto).
    apply (@valid_graph' _ _ _ _ pg1 _ (maGraph' _)) in H.
    rewrite H6; auto.
    destruct H; auto.
Qed.

Lemma is_BiMaFin_not_evalid: forall (g1': @LGraph pSGG_Bi (@addr pSGG_Bi) (prod (@addr pSGG_Bi) LR) unit)x0 es0 e0,
  is_guarded_BiMaFin' (fun v => x0 <> v) (fun e => ~ In e es0) g1' ->
  vvalid g1' x0 ->
  (forall e, In e es0 -> fst e = x0) ->
  fst e0 = x0 ->
  ~ In e0 es0 ->
  ~ evalid g1' e0.
Proof.
  intros.
  intro.
  destruct H as [X ?].
  set (G := (Build_GeneralGraph _ _ _ (fun g => BiMaFin' (pg_lg g)) _ X: Graph')).
  assert (evalid G e0).
  1: {
    simpl.
    rewrite Intersection_spec; auto.
  }
  pose proof @valid_graph' _ _ _ _ G _ (maGraph' _) _ H5.
  destruct e0.
  simpl in H2; subst a.
  rewrite (left_right_sound0' _ _ _ H5) in H6.
  simpl in H6.
  rewrite Intersection_spec in H6.
  destruct H6.
  auto.
Qed.

Lemma extend_copy_left: forall (g g1 g2: Graph) (g1': LGraph) (g2'': Graph') (x l r x0 l0: addr) d0,
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  copy l g1 g2 g2'' ->
  x0 = LocalGraphCopy.vmap g1 x ->
  l = null /\ l0 = null \/ l0 = LocalGraphCopy.vmap g2 l ->
  is_guarded_BiMaFin' (fun v => x0 <> v) (fun e => ~ In e nil) g1' ->
  @derives pred _
  (vertex_at x0 d0 * vertices_at (Intersection _ (vvalid g1') (fun x => x0 <> x)) g1' * reachable_vertices_at l0 g2'') 
  (EX g2': LGraph,
    !! (extended_copy l (g1: LGraph, g1') (g2: LGraph, g2') /\ is_guarded_BiMaFin' (fun v => x0 <> v) (fun e => ~ In e nil) g2') && 
    (vertex_at x0 d0 * vertices_at (Intersection _ (vvalid g2') (fun x => x0 <> x)) g2')).
Proof.
  intros.
  rename H5 into BMF.
  inversion H0.
  pose proof @vcopy1_edge_copy_list_weak_copy_extended_copy' _ _ _ _ _ _ _ _ _ _ BiMaFin'_Normal x ((x, L) :: (x, R) :: nil) nil (x, L) ((x, R) :: nil) g g1 g1 g1' g1' g2 g2'' x0 H.
  spec H5; [simpl; unfold Complement, Ensembles.In; congruence |].
  spec H5; [reflexivity |].
  spec H5; [intros; apply (biGraph_out_edges g (biGraph _)); auto |].
  spec H5; [repeat constructor; intro HH; inversion HH; inversion H9 |].
  spec H5; [auto |].
  spec H5; [hnf; auto |].
  spec H5; [auto |].
  spec H5; [subst l; auto |].

  unfold reachable_vertices_at.
  pose proof vertices_at_sepcon_unique_1x (Graph_PointwiseGraph g2'') x0 (reachable g2'' l0) d0.
  pose proof vertices_at_sepcon_unique_xx g1' (Graph_PointwiseGraph g2'') (Intersection _ (vvalid g1') (fun x => x0 <> x)) (reachable g2'' l0).

  rewrite sepcon_assoc, (add_andp _ _ H10); normalize.
  rewrite (sepcon_comm (vertices_at _ _)), <- sepcon_assoc, (add_andp _ _ H9); normalize.
  clear H9 H10.
  spec H5.
  {
    apply is_BiMaFin_disjoint_guard with (x0 := x0) (es0 := nil); auto.
    + eapply vcopy1_copied_root_valid in H1; auto.
      subst x0; auto.
    + intros ? [].
    + apply (vmap_weaken g1 g2'') in H4.
      rewrite (copy_vvalid_weak_eq g1 g2 g2'' l l0 H4 H2).
      apply Disjoint_comm.
      apply (Disjoint_x1' _ _ _ H11 H12).
  }

  unfold map in H5; rewrite H3 in BMF.
  rewrite <- H3 in BMF;
  specialize (H5 BMF).
  specialize (H5 (Graph'_is_BiMaFin' _)).

  destruct H5 as [g2' [? [? [? ?]]]].
  apply (exp_right g2').

  pose proof vertex_at_not_null x0 d0.
  rewrite (add_andp _ _ H14) at 1.
  rewrite andp_comm, !sepcon_andp_prop'.
  apply derives_extract_prop.
  intro.
  clear H14. assert (x0 <> null) by congruence; clear H15.
  
  apply andp_right; [apply prop_right; split; auto | rewrite sepcon_assoc; apply sepcon_derives; auto].
  assert (Prop_join (vvalid g1') (vvalid g2'') (vvalid g2')) as HPJ.
  1: {
    eapply copy_and_extended_copy; eauto.
    rewrite <- H7; auto.
  }
  assert (Prop_join (Intersection addr (vvalid g1') (fun x1 : addr => x0 <> x1))
                (vvalid g2'')
                (Intersection addr (vvalid g2') (fun x1 : addr => x0 <> x1))) as HPJ1.
  1: {
    apply Prop_join_shrink1; auto.
    eapply vcopy1_copied_root_valid in H1; auto.
    rewrite H3; auto.
  }
  rewrite (vertices_at_vertices_identical (Graph_PointwiseGraph g2'') (LGraph_SGraph g2')).
  rewrite (vertices_at_vertices_identical (LGraph_SGraph g1') (LGraph_SGraph g2')).
  + erewrite vertices_at_sepcon_xx; [apply derives_refl |].
    rewrite Prop_join_comm.
    apply (vmap_weaken g1 g2'') in H4.
    rewrite <- (copy_vvalid_weak_eq g1 g2 g2'' l l0 H4 H2).
    auto.
  + rewrite <- H3 in H13.
    apply H13.
    - unfold Included, Ensembles.In; intros.
      destruct BMF as [BMF _].
      pose (pg1 := Build_GeneralGraph _ _ _ (fun g: LGraph => BiMaFin' g) (gpredicate_sub_labeledgraph (fun v => x0 <> v) (fun e : addr * LR => ~ In e nil) g1') BMF: Graph').
      assert (vvalid pg1 x1) by (simpl; auto).
      apply vvalid_vguard' in H16.
      simpl in H16.
      rewrite !Intersection_spec in H16.
      simpl; tauto.
    - unfold Included, Ensembles.In; intros.
      destruct H9 as [X _].
      pose (pg2 := Build_GeneralGraph _ _ _ (fun g: LGraph => BiMaFin' g) (gpredicate_sub_labeledgraph (fun v => x0 <> v) (fun e : addr * LR => ~ In e nil) g2') X: Graph').
      assert (vvalid pg2 x1). simpl. rewrite Intersection_spec in H15 |- *. rewrite (proj1 HPJ); tauto.
      apply vvalid_vguard' in H9.
      simpl in H9.
      rewrite !Intersection_spec in H9.
      simpl; tauto.
  + apply (vmap_weaken g1 g2'') in H4.
    pose proof copy_vvalid_weak_eq _ _ _ _ _ H4 H2.
    rewrite <- H15.
    apply H10.
    - intros ? ?; apply vvalid_vguard'; auto.
    - unfold Included, Ensembles.In; intros.
      destruct H9 as [X _].
      pose (pg2 := Build_GeneralGraph _ _ _ (fun g: LGraph => BiMaFin' g) (gpredicate_sub_labeledgraph (fun v => x0 <> v) (fun e : addr * LR => ~ In e nil) g2') X: Graph').
      assert (vvalid pg2 x1). simpl. rewrite (proj1 HPJ1). tauto.
      apply vvalid_vguard' in H9.
      simpl in H9.
      rewrite !Intersection_spec in H9.
      simpl; tauto.
Qed.

Lemma labeledgraph_add_edge_ecopy1_left: forall (g g1 g2: Graph) (g1' g2': LGraph) (x l r x0 l0: addr),
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  extended_copy l (g1: LGraph, g1') (g2: LGraph, g2') ->
  x0 = LocalGraphCopy.vmap g1 x ->
  l = null /\ l0 = null \/ l0 = LocalGraphCopy.vmap g2 l ->
  is_guarded_BiMaFin' (fun v => x0 <> v) (fun e => ~ In e nil) g2' ->
  x0 <> null ->
  let g3 := Graph_egen g2 (x, L) (x0, L): Graph in
  let g3' := labeledgraph_add_edge g2' (x0, L) x0 l0 (null, L): LGraph in
  ecopy1 (x, L) (g2: LGraph, g2') (g3: LGraph, g3') /\
  is_guarded_BiMaFin' (fun v => x0 <> v) (fun e => ~ In e ((x0, L) :: nil)) g3' /\
  (x0, L) = LocalGraphCopy.emap g3 (x, L) /\
  dst g3' (x0, L) = l0.
Proof.
  intros.
  unfold ecopy1.
  assert (~ evalid g2' (x0, L)) as HH.
  1: {
    eapply is_BiMaFin_not_evalid; eauto; [| intros ? []].
    eapply extended_copy_vvalid_mono in H2; [exact H2 |].
    eapply vcopy1_copied_root_valid in H1; auto.
    subst x0; auto.
  }
  split; [split; [| split] | split; [| split]].
  + reflexivity.
  + apply WeakMarkGraph.labeledgraph_egen_do_nothing.
  + assert (g ~=~ g2) as HH0.
    1: {
      destruct H1 as [? _], H2 as [? _].
      rewrite <- H2, <- H1; reflexivity.
    }
    assert (x0 = LocalGraphCopy.vmap g2 (src g2 (x, L))) as HH1.
    1: {
      rewrite left_right_sound by (rewrite <- (proj1 HH0); auto).
      destruct H1 as [_ [? _]], H2 as [_ [_ ?]].
      subst x0.
      destruct H2 as [_ [? _]].
      rewrite guarded_pointwise_relation_spec in H2.
      apply H2.
      unfold Complement, Ensembles.In; intro.
      apply reachable_by_foot_prop in H3.
      apply H3.
      destruct H1 as [_ [? _]]; auto.
    }
    destruct H4.
    - pose proof LocalGraphCopy.labeledgraph_egen_ecopy1_not_vvalid g2 g2' (x, L) (x0, L) x0 l0.
      apply H7; clear H7; auto.
      * destruct H4.
        subst l0.
        destruct H5 as [[? ? ?] _].
        pose proof @valid_not_null' _ _ _ _ (gpredicate_sub_labeledgraph (fun v : addr => x0 <> v)
            (fun e : addr * LR => ~ In e nil) g2') _ ma' null.
        intro.
        apply H5; [| reflexivity].
        simpl.
        rewrite Intersection_spec; split; auto.
      * inversion H0.
        rewrite <- (si_dst1 _ _ _ HH0); [| apply (@left_valid _ _ _ _ _ _ g (biGraph _)); auto].
        destruct H4; rewrite H9; subst l.
        intro.
        apply (@valid_not_null _ _ _ _ g2 _ (maGraph _) null); auto; reflexivity.
    - pose proof LocalGraphCopy.labeledgraph_egen_ecopy1 g2 g2' (x, L) (x0, L) x0 l0.
      apply H7; clear H7; auto.

      subst l0.
      f_equal.
      inversion H0.
      destruct H1 as [? _], H2 as [? _].
      rewrite <- H1 in H2.
      rewrite (si_dst1 _ _ _ H2); auto.
      apply (@left_valid _ _ _ _ _ _ g (biGraph _)); auto.
  + eapply is_guarded_BiMaFin'_labeledgraph_add_edge; [auto | | exact H5].
    rewrite Same_set_spec; intro e; simpl.
    rewrite Intersection_spec.
    assert (e = (x0, L) <-> (x0, L) = e) by (split; intros; congruence).
    tauto.
  + simpl.
    unfold update_elabel; simpl.
    destruct_eq_dec (x, L) (x, L); auto; congruence.
  + subst g3'.
    simpl.
    unfold updateEdgeFunc.
    rewrite if_true; reflexivity.
Qed.

Lemma va_labeledgraph_add_edge_left: forall (g g1 g2: Graph) (g1' g2': LGraph) (x l r x0 l0: addr),
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  extended_copy l (g1: LGraph, g1') (g2: LGraph, g2') ->
  x0 = LocalGraphCopy.vmap g1 x ->
  is_guarded_BiMaFin' (fun x => x0 <> x) (fun e => ~ In e nil) g2' ->
  vertices_at (Intersection _ (vvalid g2') (fun x => x0 <> x)) g2' = vertices_at (Intersection _ (vvalid (labeledgraph_add_edge g2' (x0, L) x0 l0 (null, L))) (fun x => x0 <> x)) (LGraph_SGraph (labeledgraph_add_edge g2' (x0, L) x0 l0 (null, L))).
Proof.
  intros.
  eapply va_labeledgraph_add_edge_eq'; eauto.
  eapply is_BiMaFin_not_evalid; eauto.
  + eapply extended_copy_vvalid_mono in H2; [exact H2 |].
    eapply vcopy1_copied_root_valid in H1; auto.
    subst x0; auto.
  + intros ? [].
Qed.

Lemma va_labeledgraph_egen_left: forall (g2: Graph) (x x0: addr),
  reachable_vertices_at x g2 = reachable_vertices_at x (Graph_egen g2 (x, L) (x0, L)).
Proof.
  intros.
  apply va_labeledgraph_egen_eq.
Qed.

Lemma extend_copy_right: forall (g g1 g2 g3 g4: Graph) (g1' g2' g3': LGraph) (g4'': Graph') (x l r x0 r0: addr) d0,
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  extended_copy l (g1: LGraph, g1') (g2: LGraph, g2') ->
  ecopy1 (x, L) (g2: LGraph, g2') (g3: LGraph, g3') ->
  copy r g3 g4 g4'' ->
  x0 = LocalGraphCopy.vmap g1 x ->
  (x0, L) = LocalGraphCopy.emap g3 (x, L) ->
  r = null /\ r0 = null \/ r0 = LocalGraphCopy.vmap g4 r ->
  is_guarded_BiMaFin' (fun v => x0 <> v) (fun e => ~ In e ((x0, L) :: nil)) g3' ->
  @derives pred _
  (vertex_at x0 d0 * vertices_at (Intersection _ (vvalid g3') (fun x => x0 <> x)) g3' * reachable_vertices_at r0 g4'') 
  (EX g4': LGraph,
    !! (extended_copy r (g3: LGraph, g3') (g4: LGraph, g4') /\ is_guarded_BiMaFin' (fun v => x0 <> v) (fun e => ~ In e ((x0, L) :: nil)) g4') && 
   (vertex_at x0 d0 * vertices_at (Intersection _ (vvalid g4') (fun x => x0 <> x)) g4')).
Proof.
  intros.
  rename H8 into BMF.
  inversion H0.
  pose proof @vcopy1_edge_copy_list_weak_copy_extended_copy' _ _ _ _ _ _ _ _ _ _ BiMaFin'_Normal x ((x, L) :: (x, R) :: nil) ((x, L) :: nil) (x, R) nil g g1 g3 g1' g3' g4 g4'' x0 H.
  spec H8; [simpl; unfold Complement, Ensembles.In; congruence |].
  spec H8; [reflexivity |].
  spec H8; [intros; apply (biGraph_out_edges g (biGraph _)); auto |].
  spec H8; [repeat constructor; intro HH; inversion HH; inversion H12 |].
  spec H8; [auto |].
  spec H8.
  1: {
    unfold edge_copy_list; simpl map.
    split_relation_list (@nil (@LGraph _ addr (addr * LR) unit * @LGraph _ addr (addr * LR) unit)).
    unfold edge_copy.
    split_relation_list ((g2: LGraph, g2') :: nil); auto.
    rewrite H10; auto.
  }
  spec H8; [subst r; auto |].
  spec H8; [subst r; auto |].

  unfold reachable_vertices_at.
  pose proof vertices_at_sepcon_unique_1x (Graph_PointwiseGraph g4'') x0 (reachable g4'' r0) d0.
  pose proof vertices_at_sepcon_unique_xx g3' (Graph_PointwiseGraph g4'') (Intersection _ (vvalid g3') (fun x => x0 <> x)) (reachable g4'' r0).

  rewrite sepcon_assoc, (add_andp _ _ H13); normalize.
  rewrite (sepcon_comm (vertices_at _ _)), <- sepcon_assoc, (add_andp _ _ H12); normalize.
  clear H12 H13.
  spec H8.
  1: {
    apply is_BiMaFin_disjoint_guard with (x0 := x0) (es0 := (x0, L) :: nil); auto.
    + eapply ecopy1_vvalid_mono in H3; [exact H3 |].
      eapply extended_copy_vvalid_mono in H2; [exact H2 |].
      eapply vcopy1_copied_root_valid in H1; auto.
      subst x0; auto.
    + intros ? [? | []].
      subst e; auto.
    + apply (vmap_weaken g3 g4'') in H7.
      rewrite (copy_vvalid_weak_eq g3 g4 g4'' r r0 H7 H4).
      apply Disjoint_comm.
      apply (Disjoint_x1' _ _ _ H14 H15).
  }

  unfold map in H8. rewrite H6 in BMF.
  specialize (H8 BMF).
  specialize (H8 (Graph'_is_BiMaFin' _)).

  destruct H8 as [g4' [? [? [? ?]]]].
  apply (exp_right g4').

  pose proof vertex_at_not_null x0 d0.
  rewrite (add_andp _ _ H17) at 1.
  rewrite andp_comm, !sepcon_andp_prop'.
  apply derives_extract_prop.
  intro.
  clear H17. assert (x0 <> null) by congruence; clear H18.

  pose proof (extend_copy_emap_root g g1 g3 g4 g1' g3' g4' x ((x, L) :: (x, R) :: nil) ((x, L) :: nil) (x, R) nil H).
  spec H18; [simpl; unfold Complement, Ensembles.In; congruence |].
  spec H18; [reflexivity |].
  spec H18; [intros; apply (biGraph_out_edges g (biGraph _)); auto |].
  spec H18; [repeat constructor; intro HH; inversion HH; inversion H19 |].
  spec H18; [auto |].
  spec H18.
  1: {
    unfold edge_copy_list; simpl map.
    split_relation_list (@nil (@LGraph _ addr (addr * LR) unit * @LGraph _ addr (addr * LR) unit)).
    unfold edge_copy.
    split_relation_list ((g2: LGraph, g2') :: nil); auto.
    rewrite H10; auto.
  }
  spec H18; [subst r; auto |].
  rewrite H6.
  replace ((@LocalGraphCopy.emap _ _ _ _ _ _ _ _ _ _ _ _ GMS g3 (x, L)) :: nil) with (LocalGraphCopy.emap g4 (x, L) :: nil) by (symmetry; auto).
  simpl in H18.

  apply andp_right; [apply prop_right; split; auto | rewrite sepcon_assoc; apply sepcon_derives; auto].
  assert (Prop_join (vvalid g3') (vvalid g4'') (vvalid g4')).
  1: {
    eapply copy_and_extended_copy; eauto.
    rewrite <- H11; auto.
  }
  assert (Prop_join (Intersection addr (vvalid g3') (fun x1 : addr => x0 <> x1))
                (vvalid g4'')
                (Intersection addr (vvalid g4') (fun x1 : addr => x0 <> x1))) as HPJ1.
  1: {
    apply Prop_join_shrink1; auto.
    eapply ecopy1_vvalid_mono in H3; [exact H3 |].
    eapply extended_copy_vvalid_mono in H2; [exact H2 |].
    eapply vcopy1_copied_root_valid in H1; auto.
    rewrite H5; auto.
  }
  rewrite (vertices_at_vertices_identical (Graph_PointwiseGraph g4'') (LGraph_SGraph g4')).
  rewrite (vertices_at_vertices_identical (LGraph_SGraph g3') (LGraph_SGraph g4')).
  + erewrite vertices_at_sepcon_xx; [apply derives_refl |].
    rewrite Prop_join_comm.
    apply (vmap_weaken g3 g4'') in H7.
    rewrite <- (copy_vvalid_weak_eq g3 g4 g4'' r r0 H7 H4).
    auto.
  + rewrite <- H5 in H16.
    apply H16.
    - unfold Included, Ensembles.In; intros.
      destruct BMF as [BMF _].
      pose (pg1 := Build_GeneralGraph _ _ _ (fun g: LGraph => BiMaFin' g) (gpredicate_sub_labeledgraph (fun v => x0 <> v) (fun e : addr * LR => ~ In e (LocalGraphCopy.emap g3 (x, L) :: nil)) g3') BMF: Graph').
      assert (vvalid pg1 x1) by (simpl; auto).
      apply vvalid_vguard' in H21.
      simpl in H21.
      rewrite !Intersection_spec in H21.
      simpl; tauto.
    - unfold Included, Ensembles.In; intros.
      destruct H12 as [X _].
      pose (pg2 := Build_GeneralGraph _ _ _ (fun g: LGraph => BiMaFin' g) (gpredicate_sub_labeledgraph (fun v => x0 <> v) (fun e : addr * LR => ~ In e (LocalGraphCopy.emap g4 (x, L) :: nil)) g4') X: Graph').
      assert (vvalid pg2 x1). simpl. rewrite (proj1 HPJ1); tauto.
      apply vvalid_vguard' in H12.
      simpl in H12.
      rewrite !Intersection_spec in H12.
      simpl; tauto.
  + apply (vmap_weaken g3 g4'') in H7.
    pose proof copy_vvalid_weak_eq _ _ _ _ _ H7 H4.
    rewrite <- H20.
    apply H13.
    - intros ? ?; apply vvalid_vguard'; auto.
    - unfold Included, Ensembles.In; intros.
      destruct H12 as [X _].
      pose (pg2 := Build_GeneralGraph _ _ _ (fun g: LGraph => BiMaFin' g) (gpredicate_sub_labeledgraph (fun v => x0 <> v) (fun e : addr * LR => ~ In e _) g4') X: Graph').
      assert (vvalid pg2 x1). simpl. rewrite (proj1 HPJ1). tauto.
      apply vvalid_vguard' in H12.
      simpl in H12.
      rewrite !Intersection_spec in H12.
      simpl; tauto.
Qed.

Lemma labeledgraph_add_edge_ecopy1_right: forall (g g1 g2 g3 g4: Graph) (g1' g2' g3' g4': LGraph) (x l r x0 r0: addr),
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  extended_copy l (g1: LGraph, g1') (g2: LGraph, g2') ->
  ecopy1 (x, L) (g2: LGraph, g2') (g3: LGraph, g3') ->
  extended_copy r (g3: LGraph, g3') (g4: LGraph, g4') ->
  x0 = LocalGraphCopy.vmap g1 x ->
  (x0, L) = LocalGraphCopy.emap g3 (x, L) ->
  r = null /\ r0 = null \/ r0 = LocalGraphCopy.vmap g4 r ->
  is_guarded_BiMaFin' (fun v => x0 <> v) (fun e => ~ In e ((x0, L) :: nil)) g4' ->
  x0 <> null ->
  let g5 := Graph_egen g4 (x, R) (x0, R): Graph in
  let g5' := labeledgraph_add_edge g4' (x0, R) x0 r0 (null, L): LGraph in
  ecopy1 (x, R) (g4: LGraph, g4') (g5: LGraph, g5') /\
  is_guarded_BiMaFin' (fun v => x0 <> v) (fun e => ~ In e ((x0, L) :: (x0, R) :: nil)) g5' /\
  (x0, R) = LocalGraphCopy.emap g5 (x, R) /\
  dst g5' (x0, R) = r0.
Proof.
  intros.
  unfold ecopy1.
  assert (~ evalid g4' (x0, R)) as HH.
  1: {
    eapply is_BiMaFin_not_evalid; eauto.
    + eapply extended_copy_vvalid_mono in H4; [exact H4 |].
      eapply ecopy1_vvalid_mono in H3; [exact H3 |].
      eapply extended_copy_vvalid_mono in H2; [exact H2 |].
      eapply vcopy1_copied_root_valid in H1; auto.
      subst x0; auto.
    + intros ? [? | []].
      subst e; auto.
    + intros [? | []].
      inversion H10.
  }
  split; [split; [| split] | split; [| split]].
  + reflexivity.
  + apply WeakMarkGraph.labeledgraph_egen_do_nothing.
  + assert (g ~=~ g4) as HH0.
    1: {
      destruct H1 as [? _], H2 as [? _], H3 as [? _], H4 as [? _].
      rewrite <- H4, <- H3, <- H2, <- H1; reflexivity.
    }
    assert (x0 = LocalGraphCopy.vmap g4 (src g4 (x, R))) as HH1.
    1: {
      rewrite left_right_sound by (rewrite <- (proj1 HH0); auto).
      subst x0.
      assert (WeakMarkGraph.marked g1 x).
      1: {
        destruct H1 as [_ [? _]].
        destruct H1 as [_ [? _]]; auto.
      }
      assert (WeakMarkGraph.marked g3 x).
      1: {
        destruct H3 as [_ [? _]].
        rewrite <- (proj2 H3).
        eapply WeakMarkGraph.mark_marked; [destruct H2 as [_ [H2 _]]; exact H2 | auto].
      }
      rewrite (extended_copy_vmap_root g1 g2 g1' g2' l x) by auto.
      rewrite (ecopy1_vmap_root g2 g3 g2' g3' (x, L) x H3).
      rewrite (extended_copy_vmap_root g3 g4 g3' g4' r x) by auto.
      reflexivity.
    }
    destruct H7.
    - pose proof LocalGraphCopy.labeledgraph_egen_ecopy1_not_vvalid g4 g4' (x, R) (x0, R) x0 r0.
      apply H10; clear H10; auto.
      * destruct H7.
        subst r0.
        destruct H8 as [[? ? ?] _].
        pose proof @valid_not_null' _ _ _ _ (gpredicate_sub_labeledgraph (fun v : addr => x0 <> v)
            (fun e : addr * LR => ~ In e ((x0, L) :: nil)) g4') _ ma' null.
        intro.
        apply H8; [| reflexivity].
        simpl.
        rewrite Intersection_spec; split; auto.
      * inversion H0.
        rewrite <- (si_dst1 _ _ _ HH0); [| apply (@right_valid _ _ _ _ _ _ g (biGraph _)); auto].
        destruct H7; rewrite H13; subst r.
        intro.
        apply (@valid_not_null _ _ _ _ g4 _ (maGraph _) null); auto; reflexivity.
    - pose proof LocalGraphCopy.labeledgraph_egen_ecopy1 g4 g4' (x, R) (x0, R) x0 r0.
      apply H10; clear H10; auto.

      subst r0.
      f_equal.
      inversion H0.
      rewrite (si_dst1 _ _ _ HH0); auto.
      apply (@right_valid _ _ _ _ _ _ g (biGraph _)); auto.
  + eapply is_guarded_BiMaFin'_labeledgraph_add_edge; [auto | | exact H8].
    rewrite Same_set_spec; intro e; simpl.
    rewrite Intersection_spec.
    assert (e = (x0, R) <-> (x0, R) = e) by (split; intros; congruence).
    tauto.
  + simpl.
    unfold update_elabel; simpl.
    destruct_eq_dec (x, R) (x, R); auto; congruence.
  + subst g5'.
    simpl.
    unfold updateEdgeFunc.
    rewrite if_true; reflexivity.
Qed.

Lemma va_labeledgraph_add_edge_right: forall (g g1 g2 g3 g4: Graph) (g1' g2' g3' g4': LGraph) (x l r x0 r0: addr),
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  extended_copy l (g1: LGraph, g1') (g2: LGraph, g2') ->
  ecopy1 (x, L) (g2: LGraph, g2') (g3: LGraph, g3') ->
  extended_copy r (g3: LGraph, g3') (g4: LGraph, g4') ->
  x0 = LocalGraphCopy.vmap g1 x ->
  is_guarded_BiMaFin' (fun x => x0 <> x) (fun e => ~ In e ((x0, L) :: nil)) g4' ->
  vertices_at (Intersection _ (vvalid g4') (fun x => x0 <> x)) g4' = vertices_at (Intersection _ (vvalid (labeledgraph_add_edge g4' (x0, R) x0 r0 (null, L))) (fun x => x0 <> x)) (LGraph_SGraph (labeledgraph_add_edge g4' (x0, R) x0 r0 (null, L))).
Proof.
  intros.
  eapply va_labeledgraph_add_edge_eq'; eauto.
  eapply is_BiMaFin_not_evalid; eauto.
  + eapply extended_copy_vvalid_mono in H4; [exact H4 |].
    eapply ecopy1_vvalid_mono in H3; [exact H3 |].
    eapply extended_copy_vvalid_mono in H2; [exact H2 |].
    eapply vcopy1_copied_root_valid in H1; auto.
    subst x0; auto.
  + intros ? [? | []].
    subst e; auto.
  + intros [? | []].
    inversion H7.
Qed.

Lemma va_labeledgraph_egen_right: forall (g2: Graph) (x x0: addr),
  reachable_vertices_at x g2 = reachable_vertices_at x (Graph_egen g2 (x, R) (x0, R)).
Proof.
  intros.
  apply va_labeledgraph_egen_eq.
Qed.

Lemma copy_final: forall (g g1 g2 g3 g4 g5: Graph) (g1' g2' g3' g4' g5': LGraph) x l r x0 l0 r0,
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  x0 = LocalGraphCopy.vmap g1 x ->
  l = null /\ l0 = null \/ l0 = LocalGraphCopy.vmap g2 l ->
  forall (H999: dst g3' (x0, L) = l0), 
  (x0, L) = LocalGraphCopy.emap g3 (x, L) ->
  r = null /\ r0 = null \/ r0 = LocalGraphCopy.vmap g4 r ->
  forall (H998: dst g5' (x0, R) = r0), 
  (x0, R) = LocalGraphCopy.emap g5 (x, R) ->
  is_guarded_BiMaFin'
    (fun v => x0 <> v)
    (fun e => ~ In e ((x0, L) :: (x0, R) :: nil)) g5' ->
  vcopy1 x g g1 g1' ->
  extended_copy l (g1: LGraph, g1') (g2: LGraph, g2') ->
  ecopy1 (x, L) (g2: LGraph, g2') (g3: LGraph, g3') ->
  extended_copy r (g3: LGraph, g3') (g4: LGraph, g4') ->
  ecopy1 (x, R) (g4: LGraph, g4') (g5: LGraph, g5') ->
  @derives pred _
  (vertex_at x0 (null, l0, r0) * vertices_at (Intersection _ (vvalid g5') (fun v => x0 <> v)) g5')
  (EX gg5': Graph',
  !! (copy x g g5 gg5' /\ LocalGraphCopy.vmap g1 x = LocalGraphCopy.vmap g5 x) && reachable_vertices_at x0 gg5').
Proof.
  intros.
  assert (copy x g g5 g5').
  {
    eapply vcopy1_edge_copy_list_copy.
    + assumption.
    + simpl in H0 |- *; unfold Complement, Ensembles.In. congruence.
    + intros; apply (biGraph_out_edges g (biGraph _)); auto.
    + repeat constructor; intro HH; inversion HH; inversion H12.
    + exact H7.
    + hnf.
      exists (g3: LGraph, g3').
      - exists (g1: LGraph, g1'); auto.
        exists (g2: LGraph, g2').
        * exists (g1: LGraph, g1'); auto.
          simpl in H0.
          inversion H0.
          rewrite H14.
          exact H8.
        * exact H9.
      - hnf.
        exists (g4: LGraph, g4').
        * exists (g3: LGraph, g3'); auto.
          simpl in H0.
          inversion H0.
          rewrite H15.
          exact H10.
        * exact H11.
  }
  rewrite (add_andp _ _ (vertex_at_not_null x0 (null, l0, r0))).
  normalize.
  assert (x0 <> null) as LOCAL' by congruence; clear H13.

  assert (LocalGraphCopy.vmap g5 x = x0 /\
          src g5' (x0, L) = x0 /\
          src g5' (x0, R) = x0 /\
          dst g5' (x0, L) = l0 /\
          dst g5' (x0, R) = r0 /\
          evalid g5' (x0, L) /\
          evalid g5' (x0, R) /\
          vvalid g5' x0) as LOCAL.
  {
    pose proof fun H => extended_copy_vmap_root _ _ _ _ _ x H H8 as Hvmap12.
    specialize (Hvmap12 ltac:(simpl in H1 |- *; subst x0; congruence)).
    pose proof ecopy1_vmap_root _ _ _ _ _ x H9 as Hvmap23.
    pose proof fun H => extended_copy_vmap_root _ _ _ _ _ x H H10 as Hvmap34.
    specialize (Hvmap34 ltac:(simpl in H1, Hvmap12, Hvmap23 |- *; subst x0; congruence)).
    pose proof ecopy1_vmap_root _ _ _ _ _ x H11 as Hvmap45.
    split; [congruence |].
    pose proof vcopy1_copied_root_valid _ _ _ _ _ H7 H1 as Hx0_g5'.
    apply (extended_copy_vvalid_mono _ _ _ _ _ _ H8) in Hx0_g5'.
    apply (ecopy1_vvalid_mono _ _ _ _ _ _ H9) in Hx0_g5'.
    apply (extended_copy_vvalid_mono _ _ _ _ _ _ H10) in Hx0_g5'.
    apply (ecopy1_vvalid_mono _ _ _ _ _ _ H11) in Hx0_g5'.
    assert (vvalid g2 x) as Hx_g2.
    {
      rewrite <- (proj1 (proj1 H8)), <- (proj1 (proj1 H7)).
      auto.
    }
    assert (vvalid g3 x) as Hx_g3.
    {
      rewrite <- (proj1 (proj1 H9)).
      auto.
    }
    assert (vvalid g4 x) as Hx_g4.
    {
      rewrite <- (proj1 (proj1 H10)).
      auto.
    }
    assert (vvalid g5 x) as Hx_g5.
    {
      rewrite <- (proj1 (proj1 H11)).
      auto.
    }
    assert (src g3' (x0, L) = x0 /\ dst g3' (x0, L) = l0 /\ evalid g3' (x0, L)) as [Hx0L_src [Hx0L_dst Hx0L_v]].
    {
      destruct H9 as [_ [_ ?]].
      destruct H9 as [? [? [? [? [? ?]]]]].
      destruct H15 as [_ [? _]].
      destruct H15 as [? _].
      rewrite (H15 (x0, L)).
      rewrite left_right_sound in H16 by auto.
      rewrite <- H3 in *.
      rewrite <- H16 by auto.
      simpl in H0; inversion H0.
      split; [congruence | split; tauto].
    }
    pose proof (extended_copy_evalid_mono _ _ _ _ _ _ H10 Hx0L_v) as Hx0L_v'.
    pose proof proj2 (proj2 H10).
    destruct H13 as [_ [_ [_ [? [_ _]]]]].
    destruct H13 as [_ [_ [? ?]]].
    rewrite H13 in Hx0L_src by auto.
    rewrite H14 in Hx0L_dst by auto.
    clear H13 H14 Hx0L_v; rename Hx0L_v' into Hx0L_v.
    pose proof (ecopy1_evalid_mono _ _ _ _ _ _ H11 Hx0L_v) as Hx0L_v'.
    pose proof proj2 (proj2 H11).
    destruct H13 as [_ [_ [_ [? [_ _]]]]].
    destruct H13 as [_ [_ [? ?]]].
    rewrite H13 in Hx0L_src by auto.
    rewrite H14 in Hx0L_dst by auto.
    clear H13 H14 Hx0L_v; rename Hx0L_v' into Hx0L_v.
    assert (src g5' (x0, R) = x0 /\ dst g5' (x0, R) = r0 /\ evalid g5' (x0, R)) as [Hx0R_src [Hx0R_dst Hx0R_v]].
    {
      destruct H11 as [_ [_ ?]].
      destruct H11 as [? [? [? [? [? ?]]]]].
      destruct H15 as [_ [? _]].
      destruct H15 as [? _].
      rewrite (H15 (x0, R)).
      rewrite left_right_sound in H16 by auto.
      rewrite <- H5 in *.
      rewrite <- H16 by auto.
      simpl in H0; inversion H0.
      split; [congruence | split; tauto].
    }
    tauto.
  }
  pose proof H6.
  destruct H13 as [? _].
  assert (BiMaFin' g5').
  {
    constructor.
    + constructor.
      - intros.
        congruence.
      - intros.
        destruct (classic (x0 = x2)).
        * subst x2.
          destruct (classic (e = (x0, L))); [| destruct (classic (e = (x0, R)))].
         ++ subst e; tauto.
         ++ subst e; tauto.
         ++ split; [intros [? ?]; exfalso | tauto].
            pose proof @ma' _ _ x1.
            pose proof @valid_graph' _ _ _ _ _ _ H18 e.
            simpl in H19.
            rewrite !Intersection_spec in H19.
            specialize (H19 ltac:(pose proof @eq_sym _ (x0, L) e; pose proof @eq_sym _ (x0, R) e; tauto)).
            rewrite H16 in H19. tauto.
        * pose proof @bi' _ _ x1.
          pose proof @only_two_edges _ _ _ _ _ _ _ H15 x2 e.
          simpl in H16.
          rewrite !Intersection_spec in H16.
          specialize (H16 ltac:(tauto)).
          rewrite <- H16; split; [| tauto].
          intros [? ?]; repeat split; auto.
          intros [| [| []]]; subst e; rewrite <- H17 in H14; apply H14; symmetry; tauto.
    + constructor.
      - intros.
        destruct (classic ((x0, L) = e)); [| destruct (classic ((x0, R) = e))].
        * unfold is_null_SGBA; simpl.
          subst e.
          replace (src g5' (x0, L)) with x0 by (symmetry; tauto).
          tauto.
        * unfold is_null_SGBA; simpl.
          subst e.
          replace (src g5' (x0, R)) with x0 by (symmetry; tauto).
          tauto.
        * pose proof @ma' _ _ x1.
          pose proof @valid_graph' _ _ _ _ _ _ H16.
          unfold weak_valid in H17.
          simpl in H17.
          specialize (H17 e).
          rewrite !Intersection_spec in H17.
          specialize (H17 ltac:(tauto)).
          tauto.
      - intros.
        pose proof @ma' _ _ x1.
        pose proof @valid_not_null' _ _ _ _ _ _ H15.
        specialize (H16 x2).
        simpl in H16.
        rewrite Intersection_spec in H16.
        destruct (classic (x0 = x2)); [subst x2 |]; tauto.
    + assert (FiniteGraph
           (gpredicate_sub_labeledgraph (fun v : addr => x0 = v)
              (fun e : addr * LR => In e ((x0, L) :: (x0, R) :: nil)) g5')).
      {
        constructor; simpl.
        - exists (x0 :: nil).
          split; [repeat constructor; intros [] |].
          intros.
          rewrite Intersection_spec.
          split; intros.
          * destruct H13 as [|[]].
            subst x2.
            tauto.
          * left.
            tauto.
        - exists ((x0, L) :: (x0, R) :: nil).
          split; [repeat constructor; [intros [| []]; congruence | intros []] |].
          intros.
          rewrite Intersection_spec.
          split; intros.
          * destruct H13 as [| [| []]];
            subst x2; tauto.
          * simpl. tauto.
      }
      apply (@fin' _ _) in x1.
      pose proof fun H H0 => finite_graph_join g5' _ _ (fun _ => True) _ _ (fun _ => True) H H0 x1 X.
      spec X0.
    {
      split.
      + intros; tauto.
      + intros; tauto.
    }
    spec X0.
    {
      split.
      + intros; tauto.
      + intros; tauto.
    }
    pose proof @gpredicate_sub_labeledgraph_equiv _ _ _ _ _ _ _ g5' (fun _ => True) (vvalid g5') (fun _ => True) (evalid g5').
    spec H13.
      { rewrite Same_set_spec; intro; rewrite !Intersection_spec; tauto. }
    spec H13.
      { rewrite Same_set_spec; intro; rewrite !Intersection_spec; tauto. }
    pose proof finite_graph_si _ _ (proj1 H13); clear H13.
    pose proof @gpredicate_sub_labeledgraph_self _ _ _ _ _ _ _ g5'.
    pose proof finite_graph_si _ _ (proj1 H13); clear H13.
    apply X2, X1, X0.
  }
  apply (exp_right (Build_GeneralGraph _ _ _ _ (labeledgraph_vgen g5' x0 null) X)); clear x1.
  apply andp_right.
  + apply prop_right.
    split; auto.
    rewrite <- H1; symmetry; tauto.
  + match goal with
    | |- _ |-- _ ?A => change A with (labeledgraph_vgen g5' x0 null)
    end.
    replace (vertices_at (Intersection addr (vvalid g5') (fun v : addr => x0 <> v)) g5')
      with (vertices_at (Intersection addr (vvalid g5') (fun v : addr => x0 <> v)) (LGraph_SGraph (labeledgraph_vgen g5' x0 null))).
    2: {
       apply vertices_at_vertices_identical.
       rewrite (update_irr _ g5' x0) by (rewrite Intersection_spec; tauto).
       apply (GSG_VGenPreserve (Intersection addr (vvalid g5') (fun v : addr => x0 <> v)) g5').
       + reflexivity.
       + unfold Included, Ensembles.In; intro; rewrite Intersection_spec.
         intros [? _]. apply (vvalid_vguard' (Build_GeneralGraph _ _ _ _ g5' X)), H13.
       + unfold Included, Ensembles.In; intro; rewrite Intersection_spec.
         intros [? _]. apply (vvalid_vguard' (Build_GeneralGraph _ _ _ _ g5' X)), H13.
    }
    change (vvalid g5') with (vvalid (labeledgraph_vgen g5' x0 null)).
    apply derives_refl', vertices_at_sepcon_1x.
    - apply Prop_join_comm.
      rewrite <- copy_vvalid_weak_eq; [apply Ensemble_join_Intersection_Complement | .. | exact H12].
      * unfold Included, Ensembles.In; intros; subst; tauto.
      * intros; tauto. 
      * right; symmetry; tauto.
    - change (vgamma (Graph_PointwiseGraph (labeledgraph_vgen g5' x0 null)) x0)
        with (vgamma (LGraph_SGraph (labeledgraph_vgen g5' x0 null)) x0).
      simpl.
      unfold update_vlabel. rewrite if_true by reflexivity.
      repeat f_equal; tauto.
Qed.

End PointwiseGraph_Copy_Bi.

