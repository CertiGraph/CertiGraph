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
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
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

Definition initial_copied_Graph (x x0: addr) (g: Graph): LGraph := single_vertex_labeledgraph (LocalGraphCopy.vmap (Graph_vgen g x x0) x) null (null, L).

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

Lemma vmap_weaken: forall (g1 g2: Graph) x x0 BLA,
  (x = null /\ x0 = null \/ x0 = BLA) ->
  (~ vvalid g1 x /\ ~ vvalid g2 x0 \/ x0 = BLA).
Proof.
  intros.
  destruct H; [left | right]; auto.
  destruct H.
  pose proof (@valid_not_null _ _ _ _ g1 _ (maGraph g1) x).
  pose proof (@valid_not_null _ _ _ _ g2 _ (maGraph g2) x0).
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

Lemma root_update_ramify: forall (g: Graph) (x x0: addr) (lx: addr) (gx gx': addr * addr * addr) F,
  vgamma g x = gx ->
  vgamma (Graph_vgen g x lx) x = gx' ->
  vvalid g x ->
  @derives pred _
    (F * reachable_vertices_at x g)
    (vertex_at x gx *
      (vertex_at x gx' -*
       F * (vertices_at (fun u => vvalid (initial_copied_Graph x x0 g) u /\ x0 <> u) (initial_copied_Graph x x0 g) * reachable_vertices_at x (Graph_vgen g x lx)))).
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
  vcopy1 x G (Graph_vgen G x x0) (initial_copied_Graph x x0 G) /\ x0 = LocalGraphCopy.vmap (Graph_vgen G x x0) x.
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
  @weak_valid _ _ _ _ G1 _ (maGraph _) l.
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
  @weak_valid _ _ _ _ G3 _ (maGraph _) r.
Proof.
  intros.
  destruct H1 as [? _].
  apply edge_copy_si in H2.
  rewrite <- H1 in H2.
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

Lemma graph_ramify_right: forall {RamUnit: Type} (g g1 g2: Graph) (g1' g2': LGraph) (x l r: addr) (F1 F2: pred),
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  edge_copy g (x, L) (g1: LGraph, g1') (g2: LGraph, g2') ->
  F1 * (F2 * reachable_vertices_at x g2) |--
  reachable_vertices_at r g2 *
   (ALL a: RamUnit * Graph * Graph * addr,
     !! (copy r g2 (snd (fst a)) (snd (fst (fst a))) /\ (r = null /\ snd a = null \/ snd a = LocalGraphCopy.vmap (snd (fst a)) r)) -->
     (reachable_vertices_at r (snd (fst a)) * reachable_vertices_at (snd a) (snd (fst (fst a))) -*
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
  + apply edge_copy_si in H2; rewrite <- H2, <- H1.
    eapply Prop_join_reachable_right; eauto.
  + intros.
    destruct H5 as [[? [? ?]] _].
    apply edge_copy_si in H2; rewrite <- H5, <- H2, <- H1.
    eapply Prop_join_reachable_right; eauto.
  + intros [[[? ?] ?] ?] [? _].
    rewrite (edge_copy_si _ _ _ _ _ _ H2) in H1.
    simpl in H5 |- *; clear r0.
    rewrite vertices_identical_spec.
    intros.
    simpl.
    destruct H5 as [? [? ?]].
    f_equal; [f_equal |].
    - destruct H8 as [_ [? _]].
      rewrite guarded_pointwise_relation_spec in H8.
      apply H8; clear H8.
      unfold Complement, Ensembles.In.
      intro.
      apply reachable_by_is_reachable in H8.
      rewrite Intersection_spec in H6.
      rewrite <- H1 in H8.
      destruct H6; auto.
    - apply dst_L_eq; auto.
      rewrite Intersection_spec in H6.
      destruct H6 as [? _].
      rewrite H1 in H6.
      apply reachable_foot_valid in H6; auto.
    - apply dst_R_eq; auto.
      rewrite Intersection_spec in H6.
      destruct H6 as [? _].
      rewrite H1 in H6.
      apply reachable_foot_valid in H6; auto.
Qed.

Lemma is_BiMaFin_disjoint_guard: forall (g1':  @LGraph pSGG_Bi (@addr pSGG_Bi) (prod (@addr pSGG_Bi) LR)) (g2'': Graph) x0 es0,
  is_guarded_BiMaFin (fun v => x0 <> v) (fun e => ~ In e es0) g1' ->
  vvalid g1' x0 ->
  (forall e, In e es0 -> fst e = x0) ->
  Disjoint addr (vvalid g2'') (vvalid g1') ->
  disjointed_guard (vvalid g2'') (vvalid g1') (evalid g2'') (evalid g1').
Proof.
  intros.
  split; auto.
  rewrite Disjoint_spec in *.
  intros e ? ?.
  destruct (@valid_graph _ _ _ _ g2'' _ (maGraph _) e H3) as [? _].
  apply (H2 _ H5).
  destruct (in_dec equiv_dec e es0); destruct e as [v lr].
  + specialize (H1 _ i).
    simpl in H1.
    rewrite left_right_sound0 by auto.
    subst; auto.
  + destruct H as [X _].
    pose (pg1 := Build_GeneralGraph _ _ (fun g: LGraph => BiMaFin g) (gpredicate_sub_labeledgraph (fun v => x0 <> v) (fun e => ~ In e es0) g1') X: Graph).
    assert (evalid pg1 (v, lr)) by (simpl; rewrite Intersection_spec; split; auto).
    assert (src g2'' (v, lr) = src pg1 (v, lr)) by (rewrite !left_right_sound0; auto).
    apply (@valid_graph _ _ _ _ pg1 _ (maGraph _)) in H.
    destruct H as [? _].
    rewrite H6; auto.
    destruct H; auto.
Qed.

Lemma labeledgraph_add_edge_ecopy1_left: forall (g g1 g2: Graph) (g1' g2': LGraph) (x l r x0 l0: addr),
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  extended_copy (dst g (x, L)) (g1: LGraph, g1') (g2: LGraph, g2') ->
  x0 = LocalGraphCopy.vmap g1 x ->
  l = null /\ l0 = null \/ l0 = LocalGraphCopy.vmap g2 l ->
  let g3 := Graph_egen g2 (x, L) (x0, L): Graph in
  let g3' := labeledgraph_add_edge g2' (x0, L) x0 l0 (null, L): LGraph in
  ecopy1 (x, L) (g2: LGraph, g2') (g3: LGraph, g3').
Proof.
  intros.
  unfold ecopy1.
  split; [| split].
  + reflexivity.
  + apply WeakMarkGraph.labeledgraph_egen_do_nothing.
  + destruct H4; [admit |].
    pose proof LocalGraphCopy.labeledgraph_egen_ecopy1 g2 g2' (x, L) (x0, L).
    rewrite !left_right_sound in H5 by admit.
    replace (dst g2 (x, L)) with l in H5 by admit.
    replace (@LocalGraphCopy.vmap (@addr pSGG_Bi)
                  (prod (@addr pSGG_Bi) LR) (@addr pSGG_Bi)
                  (prod (@addr pSGG_Bi) LR)
                  (@SGBA_VE (@addr pSGG_Bi) (prod (@addr pSGG_Bi) LR)
                     (@SGBA pSGG_Bi))
                  (@SGBA_EE (@addr pSGG_Bi) (prod (@addr pSGG_Bi) LR)
                     (@SGBA pSGG_Bi)) (@addr pSGG_Bi)
                  (prod (@addr pSGG_Bi) LR) (@addr pSGG_Bi)
                  (prod (@addr pSGG_Bi) LR)
                  (@GMS (@addr pSGG_Bi) (prod (@addr pSGG_Bi) LR) CCS)
                  (@Graph_LGraph pSGG_Bi (@addr pSGG_Bi)
                     (prod (@addr pSGG_Bi) LR) g2) x)
      with (@LocalGraphCopy.vmap (@addr pSGG_Bi)
                  (prod (@addr pSGG_Bi) LR) (@addr pSGG_Bi)
                  (prod (@addr pSGG_Bi) LR)
                  (@SGBA_VE (@addr pSGG_Bi) (prod (@addr pSGG_Bi) LR)
                     (@SGBA pSGG_Bi))
                  (@SGBA_EE (@addr pSGG_Bi) (prod (@addr pSGG_Bi) LR)
                     (@SGBA pSGG_Bi)) (@addr pSGG_Bi)
                  (prod (@addr pSGG_Bi) LR) (@addr pSGG_Bi)
                  (prod (@addr pSGG_Bi) LR)
                  (@GMS (@addr pSGG_Bi) (prod (@addr pSGG_Bi) LR) CCS)
                  (@Graph_LGraph pSGG_Bi (@addr pSGG_Bi)
                     (prod (@addr pSGG_Bi) LR) g1) x) in H5 by admit.
    rewrite <- H3, <- H4 in H5.
    apply H5.
split; [| split; [| split; [| split; [| split; [| split]]]]].
    - reflexivity.
    - intros v; reflexivity.
    - rewrite guarded_pointwise_relation_spec; intros.
      simpl.
      unfold update_elabel; simpl.
      destruct_eq_dec (x, L) x1; auto.
      unfold Complement, Ensembles.In in H6; congruence.
    - intros.
      simpl.
      unfold update_elabel.
      destruct_eq_dec (x, L) (x, L); [| congruence].
      destruct_eq_dec (x, L) e0; auto.
      change (elabel (lg_gg g2) e0) with (LocalGraphCopy.emap g2 e0).
      (* assert (evalid g2' (LocalGraphCopy.emap g2 e0)); [| intro HH; rewrite HH in *; tauto]. *)
      Print LocalGraphCopy.ecopy1.
      admit.
    - split; [| split; [| split]]; simpl.
      * apply Prop_join_Empty.
      * unfold update_elabel, add_evalid; simpl.
        destruct_eq_dec (x, L) (x, L); [| congruence].
        apply Prop_join_x1.
        admit.
      * unfold update_src, add_evalid; simpl.
        intros. admit.
      * admit.
    - simpl.
      unfold update_src, update_elabel; simpl.
      destruct_eq_dec (x, L) (x, L); [| congruence].
      destruct_eq_dec (x0, L) (x0, L); [| congruence].
      admit.
    - simpl.
      unfold update_dst, update_elabel; simpl.
      destruct_eq_dec (x, L) (x, L); [| congruence].
      destruct_eq_dec (x0, L) (x0, L); [| congruence].
      admit.
Qed.


Lemma extend_copy_left: forall (g g1 g2: Graph) (g1': LGraph) (g2'': Graph) (x l r x0 l0: addr) d0,
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  copy l g1 g2 g2'' ->
  x0 = LocalGraphCopy.vmap g1 x ->
  l = null /\ l0 = null \/ l0 = LocalGraphCopy.vmap g2 l ->
  is_guarded_BiMaFin (fun v => x0 <> v) (fun e => ~ In e nil) g1' ->
  let g3 := Graph_egen g2 (x, L) (x0, L): Graph in
  @derives pred _
  (vertex_at x0 d0 * vertices_at (fun x => vvalid g1' x /\ x0 <> x) g1' * reachable_vertices_at l0 g2'') 
  (EX g3': LGraph,
    !! (edge_copy g (x, L) (g1: LGraph, g1') (g3: LGraph, g3') /\ is_guarded_BiMaFin (fun v => x0 <> v) (fun e => ~ In e ((x0, L) :: nil)) g3') && 
    (vertex_at x0 d0 * vertices_at (fun x => vvalid g3' x /\ x0 <> x) g3')).
Proof.
  intros.
  rename H5 into BMF.
  inversion H0.
  pose proof @vcopy1_edge_copy_list_weak_copy_extended_copy _ _ _ _ _ BiMaFin_Normal x ((x, L) :: (x, R) :: nil) nil (x, L) ((x, R) :: nil) g g1 g1 g1' g1' g2 g2'' l l0 H.
  spec H5; [simpl; unfold Complement, Ensembles.In; congruence |].
  spec H5; [reflexivity |].
  spec H5; [intros; apply (biGraph_out_edges g (biGraph _)); auto |].
  spec H5; [repeat constructor; [intros [|[]]; intro HH; inversion HH | intros []] |].
  spec H5; [auto |].
  spec H5; [hnf; auto |].
  spec H5; [auto |].
  spec H5; [subst l; auto |].

  unfold reachable_vertices_at.
  pose proof vertices_at_sepcon_unique_1x (Graph_SpatialGraph g2'') x0 (reachable g2'' l0) d0.
  pose proof vertices_at_sepcon_unique_xx g1' (Graph_SpatialGraph g2'') (fun x1 : addr => vvalid g1' x1 /\ x0 <> x1) (reachable g2'' l0).
  rewrite sepcon_assoc, (add_andp _ _ H10); normalize.
  rewrite (sepcon_comm (vertices_at _ _)), <- sepcon_assoc, (add_andp _ _ H9); normalize.
  clear H9 H10.
  spec H5.
  Focus 1. {
    apply is_BiMaFin_disjoint_guard with (x0 := x0) (es0 := nil); auto.
    + destruct H1 as [_ [_ ?]].
      destruct H1 as [_ [_ [_ ?]]].
      subst g1' x0.
      simpl; auto.
    + intros ? [].
    + destruct H2 as [? [? ?]].
      apply (vmap_weaken g1 g2'') in H4.
      rewrite (LocalGraphCopy.copy_vvalid_weak_eq g1 g2 g2'' (WeakMarkGraph.marked g1) l l0 H4 H10).
      apply Disjoint_comm.
      apply (Disjoint_x1 _ _ _ H11 H12).
  } Unfocus.

  unfold map in H5; rewrite H3 in BMF.
  specialize (H5 BMF).
  specialize (H5 (Graph_is_BiMaFin _)).

  destruct H5 as [g2' [? [? [? ?]]]].
  pose (g3' := labeledgraph_add_edge g2' (x0, L) x0 l0 (null, L) : LGraph).
  apply (exp_right g3').
  apply andp_right; [apply prop_right; split | rewrite sepcon_assoc; apply sepcon_derives; auto].
  + unfold edge_copy.
    split_relation_list ((g2: LGraph, g2' : LGraph) :: nil); auto.
    
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

Lemma extend_copy_right: forall (g g1 g2 g3: Graph) (g1' g2' g3'': LGraph) (x l r x0 r0: addr),
  vvalid g x ->
  vgamma g x = (null, l, r) ->
  vcopy1 x g g1 g1' ->
  edge_copy g (x, L) (g1: LGraph, g1') (g2: LGraph, g2') ->
  copy r g2 g3 g3'' ->
  x0 = LocalGraphCopy.vmap g1 x ->
  r = null /\ r0 = null \/ r0 = LocalGraphCopy.vmap g3 r ->
  @derives pred _
  (vertices_at (fun x => vvalid g2' x /\ x0 <> x) g2' * reachable_vertices_at r0 g3'') 
  (EX g3': LGraph,
    !! edge_copy g (x, R) (g2: LGraph, g2') (g3: LGraph, g3') && 
    vertices_at (fun x => vvalid g3' x /\ x0 <> x) g3').
Proof.
  intros.
  pose proof vcopy1_edge_copy_list_copy_extended_copy x ((x, L) :: (x, R) :: nil) ((x, L) :: nil) (x, R) nil g g1 g2 g1' g2' g3 g3''.
Admitted.

End SpatialGraph_Copy_Bi.


