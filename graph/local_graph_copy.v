Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Morphisms_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas. Import RamifyCoq.graph.path_lemmas.PathNotation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_morphism.

Module LocalGraphCopy.

Section LocalGraphCopy.

Import GraphMorphism.

Context {V E V' E': Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {EV': EqDec V' eq}.
Context {EE': EqDec E' eq}.
Context {DV DE: Type}.
Context {GMS: GraphMorphismSetting DV DE V' E'}.

Notation Graph := (LabeledGraph V E DV DE).

Notation Graph' := (PreGraph V' E').

Definition vmap (g: Graph): V -> V' := fun v => co_vertex (vlabel g v).

Definition emap (g: Graph): E -> E' := fun e => co_edge (elabel g e).

Definition vcopy1 root (g1 g2: Graph) :=
  let PV_root := eq root in
  let PE_root := Intersection _ (weak_edge_prop PV_root g1) (evalid g1) in
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ PV_root) eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ PE_root) eq (emap g1) (emap g2).

Definition ecopy1 e (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  pointwise_relation V eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ (eq e)) eq (emap g1) (emap g2) /\
  (forall e0, e <> e0 -> emap g2 e <> emap g2 e0) /\
  pregraph_join (Empty_set _) (eq (emap g2 e)) g1' g2' /\
  vmap g2 (src g2 e) = src g2' (emap g2 e) /\
  vmap g2 (dst g2 e) = dst g2' (emap g2 e).

Definition copy (P: V -> Prop) root (g1 g2: Graph) (g2': Graph') :=
  let PV := reachable_by g1 root P in
  let PE := Intersection _ (weak_edge_prop PV g1) (evalid g1) in
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ PV) eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ PE) eq (emap g1) (emap g2) /\
  Same_set (vvalid g2') (image_set (vmap g2) PV) /\
  Same_set (evalid g2') (image_set (emap g2) PE) /\
  (forall e, PE e -> ~ PV (dst g1 e) -> vmap g2 (dst g1 e) = dst g2' (emap g2 e)) /\
  guarded_bij PV PE (vmap g2) (emap g2) g2 g2'.

Definition extended_copy (P: V -> Prop) root (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  let PV := reachable_by g1 root P in
  let PE := Intersection _ (weak_edge_prop PV g1) (evalid g1) in
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ PV) eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ PE) eq (emap g1) (emap g2) /\
  pregraph_join (image_set (vmap g2) PV) (image_set (emap g2) PE) g1' g2' /\
  (forall e, PE e -> ~ PV (dst g1 e) -> vmap g2 (dst g1 e) = dst g2' (emap g2 e)) /\
  guarded_bij PV PE (vmap g2) (emap g2) g2 g2'.

Definition side_condition (g: Graph) (root: V) (P: V -> Prop) (l: list E * E) (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  let (es_done, e0) := l in
  let P0 := Intersection _ P (Complement _ (eq root)) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  disjointed_guard
     (Union _ (image_set (vmap g2) PV1) (image_set (vmap g2) (eq root))) (image_set (vmap g2) PV0)
     (Union _ (image_set (emap g2) PE1) (image_set (emap g2) PE1_root)) (image_set (emap g2) PE0) /\ (* From spatial fact *)
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _). (* From weak mark lemma *)

Definition edge_copy (g: Graph) (root: V) (P: V -> Prop) (l: list E * E) :=
  let (es_done, e0) := l in
  let P0 := Intersection _ P (Complement _ (eq root)) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  relation_list (relation_conjunction (extended_copy P_rec (dst g e0)) (side_condition g root P l) :: ecopy1 e0 :: nil).

Definition edge_copy_list (g: Graph) (root: V) es (P: V -> Prop) :=
  relation_list (map (edge_copy g root P) (combine (prefixes es) es)).

Lemma triple_vcopy1: forall (g1 g2: Graph) root,
  vvalid g1 root ->
  vcopy1 root g1 g2 ->
  guarded_bij (eq root) (Empty_set _) (vmap g2) (emap g2) g2 (single_vertex_pregraph (vmap g2 root)).
Proof.
  intros g1 g2 root ? [VCOPY_si [VCOPY_gprv VCOPY_gpre]].
  split; [.. | split]; intros.
  + congruence.
  + inversion H0.
  + subst v.
    unfold single_vertex_pregraph; simpl.
    destruct_eq_dec (vmap g2 root) (vmap g2 root); [| congruence].
    rewrite (proj1 VCOPY_si) in H.
    tauto.
  + inversion H0.
  + inversion H0.
  + inversion H0.
Qed.

Lemma triple_aux1_copy: forall (g: Graph) (P0: V -> Prop) es_done e0,
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _) ->
  Same_set PV2 (Union _ PV1 (reachable_by g (dst g e0) (Intersection _ P0 (Complement _ PV1)))).
Proof.
  intros.
  unfold PV1, PV2.
  rewrite map_app; simpl map.
  rewrite reachable_by_through_app_strong' by auto.
  rewrite reachable_by_through_singleton'.
  reflexivity.
Qed.

Lemma triple_aux2_copy: forall (g: Graph) (P0: V -> Prop) es_done e0,
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _) ->
  Same_set PE2 (Union _ PE1 (Intersection _ (weak_edge_prop (reachable_by g (dst g e0) (Intersection _ P0 (Complement _ PV1))) g) (evalid g))).
Proof.
  intros.
  unfold PE1, PE2, PV2, PV1.
  rewrite triple_aux1_copy by auto.
  rewrite weak_edge_prop_Union.
  rewrite Intersection_Union_distr_l.
  reflexivity.
Qed.

Lemma triple_aux3_copy: forall (g: Graph) (P0: V -> Prop) es_done,
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  forall son e,
  PE1 e ->
  reachable_by g son (Intersection V P0 (Complement V PV1)) (dst g e) ->
  False.
Proof.
  intros.
  pose proof reachable_by_foot_valid _ _ _ _ H0.
  apply reachable_by_foot_prop in H0.
  unfold PE1, weak_edge_prop in H.
  rewrite Intersection_spec in H, H0; destruct H, H0.
  apply H3; clear H3; unfold Ensembles.In.
  unfold PV1 in H |- *.
  apply reachable_by_through_set_step with (src g e); auto.
  exists e; auto.
Qed.

Lemma triple_aux4_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P0: V -> Prop) es_done,
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  g ~=~ g1 ->
  forall son,
    extended_copy (Intersection _ P0 (Complement _ PV1)) son (g1, g1') (g2, g2') ->
    forall e,
       Intersection E
         (weak_edge_prop
            (reachable_by g son
               (Intersection V P0 (Complement V PV1))) g) 
         (evalid g) e ->
       ~
       g |= son ~o~> dst g e
       satisfying (Intersection V P0 (Complement V PV1)) ->
       vmap g2 (dst g e) = dst g2' (emap g2 e).
Proof.
  intros.
  destruct H0 as [COPY_si [COPY_gprv [COPY_gpre [? [? COPY_bij]]]]].
  assert (evalid g e) by (rewrite Intersection_spec in H1; tauto).
  assert (evalid g1 e) by (rewrite <- (proj1 (proj2 H)); auto).
  rewrite (proj2 (proj2 (proj2 H))) by auto.
  apply H3.
  + pose proof weak_edge_prop_si (reachable_by g1 son (Intersection V P0 (Complement V PV1))) _ _ H.
    rewrite <- H in H6 at 1.
    rewrite Same_set_spec in H6.
    rewrite <- (H6 e); auto.
  + rewrite <- (proj2 (proj2 (proj2 H))) by auto.
    rewrite <- H.
    auto.
Qed.

Lemma triple_aux5_copy: forall (g: Graph) (P0: V -> Prop) es_done e0,
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  Disjoint _ PV1 PV0.
Proof.
  intros.
  rewrite Disjoint_spec; intros.
  apply reachable_by_foot_prop in H0.
  unfold P_rec in H0.
  rewrite Intersection_spec in H0; unfold Complement, Ensembles.In in H0.
  tauto.
Qed.

Lemma triple_aux6_copy: forall (g: Graph) (P0: V -> Prop) es_done e0,
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  Disjoint _ PE1 PE0.
Proof.
  intros.
  rewrite Disjoint_spec; unfold PE1, PE0; intros.
  rewrite Intersection_spec in H, H0.
  unfold weak_edge_prop in H, H0.
  generalize (src g x), (proj1 H), (proj1 H0).
  rewrite <- Disjoint_spec.
  apply triple_aux5_copy.
Qed.

Lemma triple_aux7_copy: forall (g: Graph) (P: V -> Prop) root es_done e0,
  let P0 := Intersection _ P (Complement _ (eq root)) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  Disjoint _ (eq root) PV0.
Proof.
  intros.
  rewrite Disjoint_spec.
  intros.
  subst x.
  apply reachable_by_foot_prop in H0.
  unfold P_rec, P0 in H0.
  rewrite !Intersection_spec in H0.
  apply (proj2 (proj1 H0)), eq_refl.
Qed.

Lemma triple_aux8_copy: forall (g: Graph) (P: V -> Prop) root es es_done e0 es_later,
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1_root e := In e es_done in
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  Disjoint _ PE1_root PE0.
Proof.
  intros.
  rewrite Disjoint_spec.
  intros e ? ?.
  assert (In e es) by (rewrite H0; rewrite in_app_iff; tauto).
  rewrite H in H3.
  unfold out_edges in H3.
  unfold PE0 in H2.
  rewrite Intersection_spec in H2.
  unfold weak_edge_prop in H2.
  rewrite (proj2 H3) in H2.
  destruct H2.
  apply reachable_by_foot_prop in H2.
  unfold P_rec, P0 in H2.
  rewrite !Intersection_spec in H2.
  apply (proj2 (proj1 H2)), eq_refl.
Qed.

Lemma triple_aux9_copy: forall (g: Graph) (P: V -> Prop) root es es_done e0 es_later,
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE_root e := In e es in
  forall PE_sr,
  Included PE_sr PE_root ->
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  Disjoint _ PE_sr PE0.
Proof.
  intros.
  rewrite Disjoint_spec.
  intros e ? ?.
  apply H1 in H2.
  unfold PE_root, Ensembles.In in H2; rewrite H in H2.
  unfold out_edges in H2.
  unfold PE0 in H3.
  rewrite Intersection_spec in H3.
  unfold weak_edge_prop in H3.
  rewrite (proj2 H2) in H3.
  destruct H3.
  apply reachable_by_foot_prop in H3.
  unfold P_rec, P0 in H3.
  rewrite !Intersection_spec in H3.
  apply (proj2 (proj1 H3)), eq_refl.
Qed.

Lemma triple1_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  guarded_bij PV1 PE1 (vmap g1) (emap g1) g g1' /\
  g ~=~ g1 ->
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  extended_copy P_rec (dst g e0) (g1, g1') (g2, g2') ->
  disjointed_guard
    (image_set (vmap g2) PV1) (image_set (vmap g2) PV0)
    (image_set (emap g2) PE1) (image_set (emap g2) PE0) -> (* From spatial fact *)
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _) -> (* From weak mark lemma *)
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  guarded_bij PV2 PE2 (vmap g2) (emap g2) g g2'.
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 PE1 [PRE_bij PRE_si]
         P_rec PV0 PE0 COPY DISJ PV1_DEC PV2 PE2.
  assert (Same_set PV2 (Union _ PV1 PV0)) as PV2_spec by (apply triple_aux1_copy; auto).
  assert (Same_set PE2 (Union _ PE1 PE0)) as PE2_spec by (apply triple_aux2_copy; auto).
  rewrite PV2_spec, PE2_spec.
  assert (forall e,
       PE0 e ->
       ~ g |= dst g e0 ~o~> dst g e satisfying P_rec ->
       vmap g2 (dst g e) = dst g2' (emap g2 e))
  by (eapply triple_aux4_copy; eauto).

  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [? [? COPY_bij]]]]].

  assert (guarded_bij PV0 PE0 (vmap g2) (emap g2) g g2').
  Focus 1. {
    eapply guarded_bij_proper_aux3.
    1: unfold PV0; rewrite PRE_si at 1; reflexivity.
    1: unfold PE0, PV0; rewrite PRE_si at 1; rewrite (weak_edge_prop_si _ _ _ PRE_si); reflexivity.
    eapply guarded_bij_proper_aux1; [| | exact COPY_bij].
    1: apply si_guarded_si; rewrite PRE_si; symmetry; auto.
    1: reflexivity.
  } Unfocus.

  assert (guarded_bij PV1 PE1 (vmap g2) (emap g2) g g2').
  Focus 1. {
    eapply guarded_bij_proper_aux1;
    [reflexivity | | eapply guarded_bij_proper_aux2; [| |  exact PRE_bij]].
    + pose proof pregraph_join_guarded_si _ _ _ _ H0.
      destruct DISJ.
      eapply guarded_si_weaken; [| | exact H3].
      * apply Included_Complement_Disjoint.
        rewrite <- PRE_si; exact H4.
      * apply Included_Complement_Disjoint.
        rewrite <- PRE_si at 1; rewrite <- (weak_edge_prop_si _ _ _ PRE_si).
        exact H5.
    + eapply guarded_pointwise_relation_weaken; [| eassumption].
      apply Included_Complement_Disjoint.
      rewrite <- PRE_si.
      apply triple_aux5_copy.
    + eapply guarded_pointwise_relation_weaken; [| eassumption].
      rewrite <- PRE_si at 1.
      erewrite <- (weak_edge_prop_si _ g g1) by eassumption.
      apply Included_Complement_Disjoint.
      apply triple_aux6_copy.
  } Unfocus.

  apply guarded_bij_disjointed_weak_edge_prop_union; auto.
  + intros.
    exfalso.
    eapply (triple_aux3_copy g P0); eauto.
  + intros.
    apply H; auto.
    generalize (dst g e), H5. unfold not. rewrite <- Disjoint_spec.
    apply triple_aux5_copy.
Qed.

Lemma triple2_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  g ~=~ g1 ->
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  extended_copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) (g1, g1') (g2, g2') ->
  disjointed_guard
    (image_set (vmap g2) PV1) (image_set (vmap g2) PV0)
    (image_set (emap g2) PE1) (image_set (emap g2) PE0) -> (* From spatial fact *)
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _) -> (* From weak mark lemma *)
  g ~=~ g2.
Proof.
  intros.
  rename H5 into DISJ.
  destruct H4 as [? [? [? [? [? [? ?]]]]]].
  transitivity g1; auto.
Qed.

Lemma triple3_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  guarded_bij PV1 PE1 (vmap g1) (emap g1) g g1' /\
  g ~=~ g1 /\
  (forall e, PE1 e -> ~ PV1 (dst g e) -> vmap g1 (dst g e) = dst g1' (emap g1 e)) ->
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  extended_copy P_rec (dst g e0) (g1, g1') (g2, g2') ->
  disjointed_guard
    (image_set (vmap g2) PV1) (image_set (vmap g2) PV0)
    (image_set (emap g2) PE1) (image_set (emap g2) PE0) -> (* From spatial fact *)
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _) -> (* From weak mark lemma *)
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  (forall e, PE2 e -> ~ PV2 (dst g e) -> vmap g2 (dst g e) = dst g2' (emap g2 e)).
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 PE1 [PRE_bij [PRE_si PRE_consi]]
         P_rec PV0 PE0 COPY DISJ PV1_DEC PV2 PE2.
  assert (Same_set PV2 (Union _ PV1 PV0)) as PV2_spec
    by (apply triple_aux1_copy; auto).
  assert (Same_set PE2 (Union _ PE1 PE0)) as PE2_spec
    by (apply triple_aux2_copy; auto).
  assert (forall e,
       PE0 e ->
       ~ g |= dst g e0 ~o~> dst g e satisfying P_rec ->
       vmap g2 (dst g e) = dst g2' (emap g2 e))
  by (eapply triple_aux4_copy; eauto).
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [? [? COPY_bij]]]]].

  intros.
  rewrite Same_set_spec in PE2_spec. rewrite (PE2_spec e) in H2.
  assert (~ PV1 (dst g e)) by (rewrite Same_set_spec in PV2_spec; rewrite (PV2_spec (dst g e)) in H3; rewrite Union_spec in H3; tauto).
  rewrite Union_spec in H2.
  destruct H2.
  + rewrite <- PRE_si in H0 at 1.
    rewrite <- weak_edge_prop_si in H0 by (exact PRE_si).
    rewrite <- PRE_si in H0 at 1.
    replace (vmap g2 (dst g e)) with (vmap g1 (dst g e)).
    Focus 2. {
      rewrite guarded_pointwise_relation_spec in COPY_gprv.
      apply COPY_gprv.
      generalize (dst g e), H3.
      apply (Complement_Included_rev _ _ PV2).
      rewrite PV2_spec, <- PRE_si.
      apply right_Included_Union.
    } Unfocus.
    assert (emap g1 e = emap g2 e).
    Focus 1. {
      rewrite guarded_pointwise_relation_spec in COPY_gpre.
      apply COPY_gpre.
      generalize e, H2.
      apply Included_Complement_Disjoint.
      rewrite <- PRE_si at 1; rewrite <- (weak_edge_prop_si _ g g1 PRE_si).
      apply triple_aux6_copy; eauto.
    } Unfocus.
    rewrite PRE_consi by auto.
    pose proof pregraph_join_guarded_si _ _ _ _ H0.    
    rewrite guarded_si_spec in H6.
    assert (Complement E' (image_set (emap g2) PE0) (emap g1 e)).
    Focus 1. {
      destruct DISJ.
      rewrite Disjoint_spec in H8.
      refine (H8 (emap g1 e) _).
      rewrite H5.
      constructor; auto.
    } Unfocus.
    assert (evalid g1' (emap g1 e)).
    Focus 1. {
      pose proof evalid_preserved PRE_bij.
      specialize (H8 _ H2).
      rewrite <- H8.
      unfold PE1 in H2.
      rewrite Intersection_spec in H2; tauto.
    } Unfocus.
    assert (evalid g2' (emap g1 e)) by (rewrite (proj1 (proj2 H6)) in H8; auto).
    rewrite <- H5.
    apply (proj2 (proj2 (proj2 H6))); auto.
  + apply H; auto.
    rewrite Same_set_spec in PV2_spec; rewrite (PV2_spec (dst g e)) in H3.
    rewrite Union_spec in H3; tauto.
Qed.

Lemma triple4_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1_root e := In e es_done in
  guarded_bij (eq root) PE1_root (vmap g1) (emap g1) g1 g1' /\
  g ~=~ g1 ->
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  extended_copy P_rec (dst g e0) (g1, g1') (g2, g2') ->
  disjointed_guard
    (image_set (vmap g2) (eq root)) (image_set (vmap g2) PV0)
    (image_set (emap g2) PE1_root) (image_set (emap g2) PE0) -> (* From spatial fact *)
  guarded_bij (eq root) PE1_root (vmap g2) (emap g2) g2 g2'.
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 PE1_root [PRE_bij_root PRE_si]
         P_rec PV0 PE0 COPY DISJ.
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [? [? COPY_bij]]]]].

  eapply guarded_bij_proper_aux1; [.. | eapply guarded_bij_proper_aux2; [.. |exact PRE_bij_root]].
  + apply si_guarded_si; auto.
  + destruct DISJ.
    rewrite <- PRE_si in H at 1; rewrite <- weak_edge_prop_si in H by exact PRE_si.
    eapply guarded_si_weaken; [.. | exact (pregraph_join_guarded_si _ _ _ _ H)];
    rewrite Included_Complement_Disjoint; auto.
    rewrite <- PRE_si; auto.
  + eapply guarded_pointwise_relation_weaken; [.. | exact COPY_gprv].
    intros ? ? ?.
    unfold Ensembles.In in *.
    apply reachable_by_foot_prop in H2.
    unfold P_rec in H2; rewrite Intersection_spec in H2.
    unfold P0 in H2; destruct H2 as [? _].
    rewrite Intersection_spec in H2.
    destruct H2 as [_ ?]; apply H2; auto.
  + eapply guarded_pointwise_relation_weaken; [.. | exact COPY_gpre].
    rewrite <- weak_edge_prop_si, <- PRE_si by eauto.
    intros e ? ?.
    unfold Ensembles.In, weak_edge_prop in *.
    rewrite Intersection_spec in H2; destruct H2 as [? _].
    apply reachable_by_foot_prop in H2.
    unfold P_rec in H2; rewrite Intersection_spec in H2; destruct H2 as [? _].
    unfold P0 in H2.
    rewrite Intersection_spec in H2; destruct H2 as [_ ?].
    apply H2. 
    unfold Ensembles.In.
    assert (In e es) by (rewrite H_ES; rewrite in_app_iff; tauto).
    rewrite H_OUT_EDGES in H3.
    unfold out_edges in H3.
    symmetry; tauto.
Qed.

Lemma triple5_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1_root e := In e es_done in
  guarded_bij (eq root) PE1_root (vmap g1) (emap g1) g1 g1' /\
  g ~=~ g1 /\
  (forall e, PE1_root e -> vmap g1 (dst g e) = dst g1' (emap g1 e)) ->
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  extended_copy P_rec (dst g e0) (g1, g1') (g2, g2') ->
  disjointed_guard
    (image_set (vmap g2) (eq root)) (image_set (vmap g2) PV0)
    (image_set (emap g2) PE1_root) (image_set (emap g2) PE0) -> (* From spatial fact *)
  (forall e, PE1_root e -> vmap g2 (dst g e) = dst g2' (emap g2 e)).
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 PE1_root [PRE_bij_root [PRE_si PRE_consi_root]]
         P_rec PV0 PE0 COPY DISJ.
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [? [? COPY_bij]]]]].
  intros.
  specialize (PRE_consi_root e H1).
    replace (vmap g2 (dst g e)) with (vmap g1 (dst g e)).
    Focus 2. {
      rewrite guarded_pointwise_relation_spec in COPY_gprv.
      apply COPY_gprv.
      unfold Complement at 1, Ensembles.In.
      rewrite <- PRE_si.
      intro.
      unfold PE1_root in H1.
      pose proof reachable_by_foot_valid _ _ _ _ H2.
      eapply reachable_by_foot_prop in H2.
      unfold P_rec in H2; rewrite Intersection_spec in H2; destruct H2 as [? ?].
      apply H4; clear H4; unfold Ensembles.In.
      exists (dst g e).
      split.
      + rewrite in_map_iff; eauto.
      + apply reachable_by_refl; auto.
    } Unfocus.
    assert (emap g1 e = emap g2 e).
    Focus 1. {
      rewrite guarded_pointwise_relation_spec in COPY_gpre.
      apply COPY_gpre.
      unfold Complement at 1, Ensembles.In.
      intro.
      pose proof weak_edge_prop_si
       (reachable_by g1 (dst g e0) (Intersection V P0 (Complement V PV1)))
        g g1 PRE_si.
      rewrite Same_set_spec in H3.
      unfold P_rec in H2; rewrite <- (H3 e) in H2; clear H3.
      rewrite Intersection_spec in H2.
      destruct H2 as [? _]; unfold weak_edge_prop in H2.
      rewrite <- PRE_si in H2.
      apply reachable_by_foot_prop in H2.
      unfold PE1_root in H1.
      rewrite Intersection_spec in H2.
      destruct H2 as [? _].
      assert (In e es) by (rewrite H_ES; rewrite in_app_iff; tauto).
      rewrite H_OUT_EDGES in H3.
      destruct H3.
      unfold P0 in H2.
      rewrite Intersection_spec in H2; destruct H2 as [_ ?].
      apply H2.
      unfold Ensembles.In; congruence.
    } Unfocus.
    rewrite PRE_consi_root by auto.
    rewrite <- PRE_si in H at 1 2.
    rewrite <- weak_edge_prop_si in H by exact PRE_si.
    pose proof pregraph_join_guarded_si _ _ _ _ H.
    rewrite guarded_si_spec in H3.
    assert (Complement E' (image_set (emap g2) PE0) (emap g1 e)).
    Focus 1. {
      destruct DISJ.
      rewrite Disjoint_spec in H5.
      refine (H5 (emap g1 e) _).
      rewrite H2.
      constructor; auto.
    } Unfocus.
    assert (evalid g1' (emap g1 e)).
    Focus 1. {
      apply (evalid_preserved PRE_bij_root); auto.
      assert (In e es) by (rewrite H_ES; rewrite in_app_iff; tauto).
      rewrite H_OUT_EDGES in H5.
      destruct H5 as [? _].
      rewrite <- (proj1 (proj2 PRE_si)); auto.
    } Unfocus.
    assert (evalid g2' (emap g1 e))
      by (rewrite (proj1 (proj2 H3)) in H5; auto).
    rewrite <- H2.
    apply (proj2 (proj2 (proj2 H3))); auto.
Qed.

Lemma triple6_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  g ~=~ g1 /\
  guarded_pointwise_relation (Complement V (reachable_by g root P)) eq (vmap g) (vmap g1) ->
  extended_copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) (g1, g1') (g2, g2') ->
  guarded_pointwise_relation (Complement V (reachable_by g root P)) eq (vmap g) (vmap g2).
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 [PRE_si PRE_gpr] COPY.
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [? [? COPY_bij]]]]].
  transitivity (vmap g1); auto.
  eapply guarded_pointwise_relation_weaken; [| eauto].
  rewrite <- PRE_si.
  apply Complement_Included_rev.
  unfold Included, Ensembles.In; intros.
  apply step_reachable_by with (dst g e0); auto.
  + assert (In e0 es) by (rewrite H_ES, in_app_iff; simpl; tauto).
    rewrite H_OUT_EDGES in H2.
    destruct H2.
    exists e0; auto.
  + eapply reachable_by_weaken; eauto.
    unfold Included, Ensembles.In; intros.
    unfold P0 in H2.
    rewrite !Intersection_spec in H2.
    tauto.
Qed.

Lemma triple7_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later,
  let PV := reachable_by g root P in
  let PE := Intersection E (weak_edge_prop PV g) (evalid g) in
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  g ~=~ g1 /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g1) ->
  extended_copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) (g1, g1') (g2, g2') ->
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g2).
Proof.
  intros until es_later.
  intros PV PE H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 [PRE_si PRE_gpr] COPY.
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [? [? COPY_bij]]]]].
  transitivity (emap g1); auto.
  eapply guarded_pointwise_relation_weaken; [| eauto].
  erewrite <- weak_edge_prop_si by eauto.
  rewrite <- PRE_si.
  apply Complement_Included_rev.
  unfold PE, Included, Ensembles.In; intros.
  rewrite Intersection_spec in H1 |- *; split; [| tauto].
  destruct H1.
  unfold weak_edge_prop in H1 |- *.
  apply step_reachable_by with (dst g e0); auto.
  + assert (In e0 es) by (rewrite H_ES, in_app_iff; simpl; tauto).
    rewrite H_OUT_EDGES in H3.
    destruct H3.
    exists e0; auto.
  + eapply reachable_by_weaken; eauto.
    unfold Included, Ensembles.In; intros.
    unfold P0 in H3.
    rewrite !Intersection_spec in H3.
    tauto.
Qed.

Lemma triple8_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  g ~=~ g1 /\
  disjointed_guard (image_set (vmap g1) PV1) (image_set (vmap g1) (eq root))
     (image_set (emap g1) PE1) (image_set (emap g1) PE1_root) ->
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  extended_copy P_rec (dst g e0) (g1, g1') (g2, g2') ->
  disjointed_guard
    (image_set (vmap g2) (eq root)) (image_set (vmap g2) PV0)
    (image_set (emap g2) PE1_root) (image_set (emap g2) PE0) -> (* From spatial fact *)
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _) ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  disjointed_guard (image_set (vmap g2) PV2) (image_set (vmap g2) (eq root))
     (image_set (emap g2) PE2) (image_set (emap g2) PE1_root).
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 PE1 PE1_root [PRE_si PRE_disj]
         P_rec PV0 PE0 COPY DISJ PV1_DEC PV2 PE2.
  assert (Same_set PV2 (Union _ PV1 PV0)) as PV2_spec
    by (apply triple_aux1_copy; auto).
  assert (Same_set PE2 (Union _ PE1 PE0)) as PE2_spec
    by (apply triple_aux2_copy; auto).
  destruct PRE_disj as [PRE_vdisj PRE_edisj].
  destruct DISJ as [vDISJ eDISJ].
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [? [? COPY_bij]]]]].

  split.
  + rewrite PV2_spec.
    rewrite image_Union.
    apply Union_left_Disjoint; split.
    - eapply Disjoint_proper; [.. | exact PRE_vdisj];
      apply image_set_proper_strong.
      * symmetry.
        eapply guarded_pointwise_relation_weaken; [.. | exact COPY_gprv].
        apply Included_Complement_Disjoint.
        rewrite <- PRE_si.
        apply triple_aux5_copy.
      * symmetry.
        eapply guarded_pointwise_relation_weaken; [.. | exact COPY_gprv].
        apply Included_Complement_Disjoint.
        rewrite <- PRE_si.
        apply triple_aux7_copy.
    - apply Disjoint_comm; auto.
  + rewrite PE2_spec.
    rewrite image_Union.
    apply Union_left_Disjoint; split.
    - eapply Disjoint_proper; [.. | exact PRE_edisj];
      apply image_set_proper_strong.
      * symmetry.
        eapply guarded_pointwise_relation_weaken; [.. | exact COPY_gpre].
        apply Included_Complement_Disjoint.
        rewrite <- PRE_si at 1; rewrite <- weak_edge_prop_si by exact PRE_si.
        apply triple_aux6_copy.
      * symmetry.
        eapply guarded_pointwise_relation_weaken; [.. | exact COPY_gpre].
        apply Included_Complement_Disjoint.
        rewrite <- PRE_si at 1; rewrite <- weak_edge_prop_si by exact PRE_si.
        eapply triple_aux8_copy; eauto.
    - apply Disjoint_comm; auto.
Qed.

Lemma triple9_copy: forall (g g1 g2: Graph) (g' g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  g ~=~ g1 /\
  pregraph_join
   (image_set (vmap g1) (Union _ (eq root) PV1))
   (image_set (emap g1) (Union _ PE1_root PE1)) g' g1' ->
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  extended_copy P_rec (dst g e0) (g1, g1') (g2, g2') ->
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _) ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  pregraph_join
   (image_set (vmap g2) (Union _ (eq root) PV2))
   (image_set (emap g2) (Union _ PE1_root PE2)) g' g2'.
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 PE1 PE1_root [PRE_si PRE_pj]
         P_rec PV0 PE0 COPY PV1_DEC PV2 PE2.
  assert (Same_set PV2 (Union _ PV1 PV0)) as PV2_spec
    by (apply triple_aux1_copy; auto).
  assert (Same_set PE2 (Union _ PE1 PE0)) as PE2_spec
    by (apply triple_aux2_copy; auto).
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [? [? COPY_bij]]]]].
  
  rewrite image_set_proper_strong with (f2 := vmap g2) in PRE_pj.
  Focus 2. {
    eapply guarded_pointwise_relation_weaken; [| exact COPY_gprv].
    apply Included_Complement_Disjoint.
    rewrite <- PRE_si at 1.
    apply Union_left_Disjoint; split.
    + apply triple_aux7_copy.
    + apply triple_aux5_copy.
  } Unfocus.
  rewrite image_set_proper_strong with (f2 := emap g2) in PRE_pj.
  Focus 2. {
    eapply guarded_pointwise_relation_weaken; [| exact COPY_gpre].
    apply Included_Complement_Disjoint.
    rewrite <- PRE_si at 1.
    erewrite <- weak_edge_prop_si by exact PRE_si.
    apply Union_left_Disjoint; split.
    + eapply triple_aux8_copy; eauto.
    + apply triple_aux6_copy.
  } Unfocus.
  intros.
  rewrite <- PRE_si in H at 1 2.
  erewrite <- weak_edge_prop_si in H by exact PRE_si.
  rewrite PV2_spec, PE2_spec.
  rewrite <- !Union_assoc.
  rewrite !(image_Union _ (Union _ _ _)).
  apply pregraph_join_pregraph_join with g1'; auto.
Qed.

Lemma triple_aux1_ecopy: forall (g: Graph) (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  Included PE2 (Complement _ (eq e0)).
Proof.
  intros.
  unfold PE2, Included, Complement, Ensembles.In; intros e ?.
  rewrite Intersection_spec in H3.
  destruct H3 as [? _].
  unfold weak_edge_prop, PV2 in H3.
  apply reachable_by_through_set_foot_prop in H3.
  unfold P0, Complement, Ensembles.In in H3; rewrite Intersection_spec in H3.
  intro; apply (proj2 H3); clear H3.
  subst e.
  assert (In e0 es) by (rewrite H2, in_app_iff; simpl; tauto).
  rewrite H1 in H3.
  destruct H3.
  congruence.
Qed.

Lemma triple_aux2_ecopy: forall es_done e0,
  let PE2_root := fun e => In e es_done in
  let PE3_root := fun e => In e (es_done +:: e0) in
  Same_set PE3_root (Union E PE2_root (eq e0)).
Proof.
  intros.
  rewrite Same_set_spec; intro e.
  unfold PE3_root, PE2_root.
  rewrite in_app_iff; simpl.
  rewrite Union_spec.
  tauto.
Qed.

Lemma triple_aux3_ecopy: forall (g: Graph) (P: V -> Prop) root es es_done e0 es_later,
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  Disjoint E PE2 (eq e0).
Proof.
  intros.
  rewrite Disjoint_spec; intro e; intros.
  subst e.
  unfold PE2, weak_edge_prop in H1.
  rewrite Intersection_spec in H1; destruct H1 as [? _].
  replace (src g e0) with root in H1.
  Focus 2. {
    assert (In e0 es) by (rewrite H0, in_app_iff; simpl; tauto).
    rewrite H in H2.
    destruct H2; congruence.
  } Unfocus.
  unfold PV2 in H1.
  apply reachable_by_through_set_foot_prop in H1.
  unfold P0 in H1; rewrite Intersection_spec in H1.
  apply (proj2 H1).
  reflexivity.
Qed.

Lemma triple1_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  guarded_bij PV2 PE2 (vmap g2) (emap g2) g g2' /\
  g ~=~ g2 ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  guarded_bij PV2 PE2 (vmap g3) (emap g3) g g3'.
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV2 PE2 [PRE_bij PRE_si]
         ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]]. 

  eapply guarded_bij_proper_aux1; [.. | eapply guarded_bij_proper_aux2; [.. |exact PRE_bij]].
  + reflexivity.
  + apply pregraph_join_guarded_si in H0.
    eapply guarded_si_weaken; [| | exact H0].
    1: rewrite Complement_Empty_set; apply Included_Full_set.
    unfold Included, Complement, Ensembles.In; intros e' ?.
    rewrite image_set_spec in H3.
    destruct H3 as [e [? ?]].
    subst e'.
    apply H.
    generalize e, H3. eapply triple_aux1_ecopy; eauto.
  + apply guarded_pointwise_relation_pointwise_relation; auto.
  + eapply guarded_pointwise_relation_weaken; [| apply ECOPY_gpre].
    eapply triple_aux1_ecopy; eauto.
Qed.

Lemma triple2_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  g ~=~ g2 ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  g ~=~ g3.
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV2 PE2 PRE_si ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]].
  rewrite PRE_si; auto.
Qed.

Lemma triple3_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  guarded_bij PV2 PE2 (vmap g2) (emap g2) g g2' /\
  g ~=~ g2 /\
  (forall e, PE2 e -> ~ PV2 (dst g e) -> vmap g2 (dst g e) = dst g2' (emap g2 e)) ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  (forall e, PE2 e -> ~ PV2 (dst g e) -> vmap g3 (dst g e) = dst g3' (emap g3 e)).
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV2 PE2 [PRE_bij [PRE_si PRE_disj]]
         ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]]. 

  intros.
  replace (vmap g3 (dst g e)) with (vmap g2 (dst g e)) by (apply ECOPY_prv).
  assert (emap g2 e = emap g3 e).
  Focus 1. {
    rewrite guarded_pointwise_relation_spec in ECOPY_gpre.
    apply ECOPY_gpre.
    exact (triple_aux1_ecopy g P root _ _ _ _ H_VVALID H_P H_OUT_EDGES H_ES e H3).
  } Unfocus.
  replace (dst g3' (emap g3 e)) with (dst g2' (emap g2 e)); [apply PRE_disj; auto |].
  assert (evalid g2' (emap g2 e)).
  Focus 1. {
    rewrite <- (evalid_preserved PRE_bij) by auto.
    unfold PE2 in H3; rewrite Intersection_spec in H3.
    tauto.
  } Unfocus.
  assert (e0 <> e) by (generalize e, H3; eapply triple_aux1_ecopy; eauto).
  rewrite H5 in H6 |- *.
  assert (evalid g3' (emap g3 e)).
  Focus 1. {
    apply pregraph_join_guarded_si in H0.
    rewrite guarded_si_spec in H0.
    destruct H0 as [_ [? _]].
    rewrite <- H0; [auto |].
    apply H; auto.
  } Unfocus.
  apply pregraph_join_guarded_si in H0.
  rewrite guarded_si_spec in H0.
  destruct H0 as [_ [_ [_ ?]]].
  apply H0; auto.
  apply H; auto.
Qed.

Lemma triple4_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  let PV2 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE2_root e := In e es_done in
  guarded_bij (eq root) PE2_root (vmap g2) (emap g2) g2 g2' /\
  g ~=~ g2 ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE3_root e := In e (es_done ++ e0 :: nil) in
  guarded_bij (eq root) PE3_root (vmap g3) (emap g3) g3 g3'.
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_NODUP H_ES PV2 PE2_root [PRE_bij_root PRE_si] ECOPY PV3 PE3_root.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]].
  rewrite <- (Union_Empty_set (eq root)).
  assert (Same_set PE3_root (Union _ PE2_root (eq e0))).
  Focus 1. {
    rewrite Same_set_spec; intros e; rewrite Union_spec.
    unfold PE3_root; rewrite in_app_iff; simpl; tauto.
  } Unfocus.
  rewrite H3; clear H3.
  eapply guarded_bij_disjointed_union.
  + split.
    - rewrite image_Empty. apply Disjoint_Empty_set_right.
    - rewrite Disjoint_spec; intros e' ? ?.
      rewrite image_set_spec in H3.
      rewrite image_set_spec in H4.
      destruct H3 as [e [? ?]].
      subst e'.
      destruct H4 as [e00 [? ?]].
      subst e00.
      symmetry in H5; revert H5; apply H.
      unfold PE2_root in H3.
      rewrite H_ES in H_NODUP.
      apply NoDup_app_not_in with (y := e) in H_NODUP; auto.
      simpl in H_NODUP; tauto.
  + eapply guarded_bij_proper_aux1; [.. | eapply guarded_bij_proper_aux2; [.. |exact PRE_bij_root]].
    - apply si_guarded_si; auto.
    - apply pregraph_join_guarded_si in H0.
      eapply guarded_si_weaken; [ | | exact H0].
      1: rewrite Complement_Empty_set; apply Included_Full_set.
      unfold Included, Complement, Ensembles.In; intros e' ?.
      rewrite image_set_spec in H3.
      destruct H3 as [e [? ?]].
      subst e'.
      apply H.
      unfold PE2_root in H3.
      rewrite H_ES in H_NODUP.
      apply NoDup_app_not_in with (y := e) in H_NODUP; auto.
      simpl in H_NODUP; tauto.
    - apply guarded_pointwise_relation_pointwise_relation; auto.
    - eapply guarded_pointwise_relation_weaken; [| exact ECOPY_gpre].
      unfold Included, Complement, Ensembles.In; intros e ?.
      rewrite H_ES in H_NODUP.
      apply NoDup_app_not_in with (y := e) in H_NODUP; [| auto].
      simpl in H_NODUP; tauto.
  + split; [.. | split]; intros.
    - inversion H3.
    - congruence.
    - inversion H3.
    - subst e.
      assert (evalid g3 e0).
      Focus 1. {
        assert (In e0 es) by (rewrite H_ES, in_app_iff; simpl; tauto).
        rewrite H_OUT_EDGES in H3.
        destruct H3 as [? _].
        pose proof proj1 (proj2 PRE_si) e0.
        pose proof proj1 (proj2 ECOPY_si) e0.
        tauto.
      } Unfocus.
      assert (evalid g3' (emap g3 e0)).
      Focus 1. {
        destruct H0 as [_ [[? _] _]].
        specialize (H0 (emap g3 e0)).
        tauto.
      } Unfocus.
      tauto.
    - inversion H4.
    - inversion H4.
  + split; [| split; [| split]]; intros.
    - inversion H4.
    - subst e.
      auto.
    - inversion H4.
    - subst e.
      auto.
Qed.

Lemma triple5_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  let PV2 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE2_root e := In e es_done in
  guarded_bij (eq root) PE2_root (vmap g2) (emap g2) g2 g2' /\
  g ~=~ g2 /\
  (forall e, PE2_root e -> vmap g2 (dst g e) = dst g2' (emap g2 e)) ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE3_root e := In e (es_done ++ e0 :: nil) in
  (forall e, PE3_root e -> vmap g3 (dst g e) = dst g3' (emap g3 e)).
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_NODUP H_ES PV2 PE2_root [PRE_bij_root [PRE_si PRE_consi_root]] ECOPY PV3 PE3_root.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]].
  intros.
  unfold PE3_root in H3; rewrite in_app_iff in H3.
  destruct H3.
  - specialize (PRE_consi_root _ H3).
    replace (vmap g3 (dst g e)) with (vmap g2 (dst g e)) by (apply ECOPY_prv).
    assert (emap g2 e = emap g3 e).
    Focus 1. {
      rewrite guarded_pointwise_relation_spec in ECOPY_gpre.
      apply ECOPY_gpre.
      unfold Complement, Ensembles.In; intros ?.
      rewrite H_ES in H_NODUP.
      apply NoDup_app_not_in with (y := e) in H_NODUP; [| auto].
      simpl in H_NODUP; tauto.
    } Unfocus.
    replace (dst g3' (emap g3 e)) with (dst g2' (emap g2 e)); auto.
    assert (evalid g2' (emap g2 e)).
    Focus 1. {
      rewrite <- (evalid_preserved PRE_bij_root) by auto.
      assert (In e es) by (rewrite H_ES, in_app_iff; tauto).
      rewrite H_OUT_EDGES in H5.
      destruct H5 as [? _].
      pose proof proj1 (proj2 ECOPY_si) e.
      pose proof proj1 (proj2 PRE_si) e.
      tauto.
    } Unfocus.
    rewrite H4 in H5 |- *.
    assert (evalid g3' (emap g3 e)).
    Focus 1. {
      apply pregraph_join_guarded_si in H0.
      rewrite guarded_si_spec in H0.
      destruct H0 as [_ [? _]].
      rewrite <- H0; auto.
      apply H.
      rewrite H_ES in H_NODUP.
      apply NoDup_app_not_in with (y := e) in H_NODUP; [| auto].
      simpl in H_NODUP; tauto.
    } Unfocus.
    apply pregraph_join_guarded_si in H0.
    rewrite guarded_si_spec in H0.
    destruct H0 as [_ [_ [_ ?]]].
    apply H0; auto.
    apply H.
    rewrite H_ES in H_NODUP.
    apply NoDup_app_not_in with (y := e) in H_NODUP; [| auto].
    simpl in H_NODUP; tauto.
  - destruct H3; [subst e | inv H3].
    replace (dst g e0) with (dst g3 e0); auto.
    rewrite <- PRE_si in ECOPY_si.
    assert (In e0 es) by (rewrite H_ES, in_app_iff; simpl; tauto).
    rewrite H_OUT_EDGES in H3.
    destruct H3 as [? _].
    pose proof proj1 (proj2 ECOPY_si) e0.
    pose proof proj2 (proj2 (proj2 ECOPY_si)) e0.
    symmetry; tauto.
Qed.

Lemma triple6_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  guarded_pointwise_relation (Complement V (reachable_by g root P)) eq (vmap g) (vmap g2) ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  guarded_pointwise_relation (Complement V (reachable_by g root P)) eq (vmap g) (vmap g3).
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PRE_gpr ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]].
  transitivity (vmap g2); auto.
  eapply guarded_pointwise_relation_pointwise_relation; auto.
Qed.

Lemma triple7_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later,
  let PV := reachable_by g root P in
  let PE := Intersection E (weak_edge_prop PV g) (evalid g) in
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  g ~=~ g2 /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g2) ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g3).
Proof.
  intros until es_later.
  intros PV PE H_VVALID H_P P0 H_OUT_EDGES H_ES [PRE_si PRE_gpr] ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]].
  transitivity (emap g2); auto.
  eapply guarded_pointwise_relation_weaken; [| eauto].
  apply Complement_Included_rev.
  assert (In e0 es) by (rewrite H_ES, in_app_iff; simpl; tauto).
  rewrite H_OUT_EDGES in H3.
  destruct H3.
  unfold PE, Included, Ensembles.In; intros.
  subst x.
  rewrite Intersection_spec; split; [| auto].
  unfold weak_edge_prop, PV.
  rewrite H4.
  apply reachable_by_refl; auto.
Qed.

Lemma triple8_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  let PE2_root e := In e es_done in
  g ~=~ g2 /\
  disjointed_guard
     (image_set (vmap g2) PV2) (image_set (vmap g2) (eq root))
     (image_set (emap g2) PE2) (image_set (emap g2) PE2_root) ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  let PE3_root e := In e (es_done ++ e0 :: nil) in
  disjointed_guard
     (image_set (vmap g3) PV2) (image_set (vmap g3) (eq root))
     (image_set (emap g3) PE2) (image_set (emap g3) PE3_root).
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_NODUP H_ES PV2 PE2 PE2_root [PRE_si PRE_disj]
         ECOPY PE3_root.

  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]].
  destruct PRE_disj as [PRE_disjv PRE_disje].

  split.
  + eapply Disjoint_proper; [.. | exact PRE_disjv];
    apply image_set_proper_strong; symmetry;
    apply guarded_pointwise_relation_pointwise_relation; auto.
  + assert (Same_set PE3_root (Union _ PE2_root (eq e0))).
    Focus 1. {
      rewrite Same_set_spec; unfold PE3_root, PE2_root; intro e.
      rewrite in_app_iff, Union_spec; simpl; tauto.
    } Unfocus.
    rewrite H3; clear H3.
    rewrite image_Union.
    apply Union_right_Disjoint; split.
    - eapply Disjoint_proper; [.. | exact PRE_disje].
      * apply image_set_proper_strong; symmetry.
        eapply guarded_pointwise_relation_weaken; [| apply ECOPY_gpre].
        eapply triple_aux1_ecopy; eauto.
      * apply image_set_proper_strong; symmetry.
        eapply guarded_pointwise_relation_weaken; [| apply ECOPY_gpre].
        unfold Included, Complement, Ensembles.In, PE2_root.
        intros e ?.
        intro; subst e.
        rewrite H_ES in H_NODUP.
        apply NoDup_app_not_in with (y := e0) in H_NODUP; auto.
        simpl in H_NODUP; tauto.
    - rewrite Disjoint_spec; intros e' ? ?.
      rewrite image_set_spec in H3, H4.
      destruct H3 as [e [? ?]], H4 as [e1 [? ?]]; subst e1 e'.
      rewrite <- H6 in H; apply (H e); auto; clear H H6.
      generalize e, H3.
      eapply triple_aux1_ecopy; eauto.
Qed.

Lemma triple9_ecopy1: forall (g g2 g3: Graph) (g' g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  let PE2_root e := In e es_done in
  pregraph_join
   (image_set (vmap g2) (Union _ (eq root) PV2))
   (image_set (emap g2) (Union _ PE2_root PE2)) g' g2' ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  let PE3_root e := In e (es_done ++ e0 :: nil) in
  pregraph_join
   (image_set (vmap g3) (Union _ (eq root) PV2))
   (image_set (emap g3) (Union _ PE3_root PE2)) g' g3'.
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_NODUP H_ES PV2 PE2 PE2_root
         PRE_pj ECOPY PE3_root.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]].
  assert
   (Same_set
     (image_set (emap g3) (Union E PE3_root PE2))
     (Union _ (image_set (emap g3) (Union E PE2_root PE2)) (eq (emap g3 e0)))).
  Focus 1. {
    unfold PE3_root. rewrite triple_aux2_ecopy.
    rewrite !image_Union, !Union_assoc.
    rewrite image_single.
    rewrite (Union_comm _ (eq _)).
    reflexivity.
  } Unfocus.
  rewrite H3; clear H3.
  rewrite <- Union_Empty_set.
  rewrite image_set_proper_strong with (f2 := vmap g3) in PRE_pj
    by (apply guarded_pointwise_relation_pointwise_relation; auto).
  rewrite image_set_proper_strong with (f2 := emap g3) in PRE_pj.
  Focus 2. {
    eapply guarded_pointwise_relation_weaken; [| exact ECOPY_gpre].
    apply Included_Complement_Disjoint.
    rewrite Union_left_Disjoint; split.
    + rewrite Disjoint_spec; intros.
      subst x.
      unfold PE2_root in H3.
      rewrite H_ES in H_NODUP.
      apply (NoDup_app_not_in _ _ _ H_NODUP) with (y := e0); auto.
      simpl; auto.
    + eapply triple_aux3_ecopy; eauto.
  } Unfocus.
  apply pregraph_join_pregraph_join with (G2 := g2'); auto.
Qed.

Lemma triple_loop: forall (g g1 g3: Graph) (g' g1' g3': Graph') (P: V -> Prop) root es es_done e0 es_later,
  let PV := reachable_by g root P in
  let PE := Intersection E (weak_edge_prop PV g) (evalid g) in
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  guarded_bij PV1 PE1 (vmap g1) (emap g1) g g1' /\
  g ~=~ g1 /\
  (forall e, PE1 e -> ~ PV1 (dst g e) -> vmap g1 (dst g e) = dst g1' (emap g1 e)) /\
  guarded_bij (eq root) PE1_root (vmap g1) (emap g1) g1 g1' /\
  (forall e, PE1_root e -> vmap g1 (dst g e) = dst g1' (emap g1 e)) /\
  guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g1) /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g1) /\
  disjointed_guard
     (image_set (vmap g1) PV1) (image_set (vmap g1) (eq root))
     (image_set (emap g1) PE1) (image_set (emap g1) PE1_root) /\
  pregraph_join
     (image_set (vmap g1) (Union _ (eq root) PV1))
     (image_set (emap g1) (Union _ PE1_root PE1)) g' g1' ->
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  edge_copy g root P (es_done, e0) (g1, g1') (g3, g3') ->
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE3 := Intersection _ (weak_edge_prop PV3 g) (evalid g) in
  let PE3_root e := In e (es_done ++ e0 :: nil) in
  guarded_bij PV3 PE3 (vmap g3) (emap g3) g g3' /\
  g ~=~ g3 /\
  (forall e, PE3 e -> ~ PV3 (dst g e) -> vmap g3 (dst g e) = dst g3' (emap g3 e)) /\
  guarded_bij (eq root) PE3_root (vmap g3) (emap g3) g3 g3' /\
  (forall e, PE3_root e -> vmap g3 (dst g e) = dst g3' (emap g3 e)) /\
  guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g3) /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g3) /\
  disjointed_guard
     (image_set (vmap g3) PV3) (image_set (vmap g3) (eq root))
     (image_set (emap g3) PE3) (image_set (emap g3) PE3_root) /\
  pregraph_join
     (image_set (vmap g3) (Union _ (eq root) PV3))
     (image_set (emap g3) (Union _ PE3_root PE3)) g' g3'.
Proof.
  intros.
  unfold edge_copy in H5.
  destruct_relation_list p in H5; destruct p as [g2 g2'].
  destruct H6 as [COPY [DISJ DEC]].
  rename H5 into ECOPY.
  apply disjointed_guard_left_union in DISJ.
  destruct DISJ as [DISJ DISJ_root].

  assert
   (guarded_bij PV3 PE3 (vmap g2) (emap g2) g g2' /\
    g ~=~ g2 /\
    (forall e : E,
     PE3 e -> ~ PV3 (dst g e) -> vmap g2 (dst g e) = dst g2' (emap g2 e)) /\
    guarded_bij (eq root) PE1_root
      (vmap g2) (emap g2) g2 g2' /\
    (forall e : E,
     PE1_root e ->
     vmap g2 (dst g e) = dst g2' (emap g2 e)) /\
    guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g2) /\
    guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g2) /\
    disjointed_guard
     (image_set (vmap g2) PV3) (image_set (vmap g2) (eq root))
     (image_set (emap g2) PE3) (image_set (emap g2) PE1_root) /\
    pregraph_join
     (image_set (vmap g2) (Union _ (eq root) PV3))
     (image_set (emap g2) (Union _ PE1_root PE3)) g' g2') as PRE;
  [clear g3 g3' ECOPY; rename H4 into PRE | clear COPY H4].
  + split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
    - eapply triple1_copy; eauto.
      tauto.
    - eapply triple2_copy; eauto.
      tauto.
    - clear DISJ_root.
      eapply triple3_copy; eauto.
      tauto.
    - clear DISJ.
      eapply triple4_copy; eauto.
      tauto.
    - clear DISJ.
      eapply triple5_copy; eauto.
      tauto.
    - eapply triple6_copy; eauto.
      tauto.
    - eapply triple7_copy; eauto.
      tauto.
    - clear DISJ.
      eapply triple8_copy; eauto.
      tauto.
    - eapply triple9_copy; eauto.
      tauto.
  + split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
    - eapply triple1_ecopy1; eauto.
      tauto.
    - eapply triple2_ecopy1; eauto.
      tauto.
    - eapply triple3_ecopy1; eauto.
      tauto.
    - eapply triple4_ecopy1; eauto.
      tauto.
    - eapply triple5_ecopy1; eauto.
      tauto.
    - eapply triple6_ecopy1; eauto.
      tauto.
    - eapply triple7_ecopy1; eauto.
      tauto.
    - eapply triple8_ecopy1; eauto.
      tauto.
    - eapply triple9_ecopy1; eauto.
      tauto.
Qed.

Lemma triple_final: forall (g g1: Graph) (g1': Graph') (P: V -> Prop) root es,
  let PV := reachable_by g root P in
  let PE := Intersection E (weak_edge_prop PV g) (evalid g) in
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  let PV1 := reachable_by_through_set g (map (dst g) es) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es in
  let g' := empty_pregraph (vmap g root) in
  guarded_bij PV1 PE1 (vmap g1) (emap g1) g g1' /\
  g ~=~ g1 /\
  (forall e, PE1 e -> ~ PV1 (dst g e) -> vmap g1 (dst g e) = dst g1' (emap g1 e)) /\
  guarded_bij (eq root) PE1_root (vmap g1) (emap g1) g1 g1' /\
  (forall e, PE1_root e -> vmap g1 (dst g e) = dst g1' (emap g1 e)) /\
  guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g1) /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g1) /\
  disjointed_guard
     (image_set (vmap g1) PV1) (image_set (vmap g1) (eq root))
     (image_set (emap g1) PE1) (image_set (emap g1) PE1_root) /\
  pregraph_join
     (image_set (vmap g1) (Union _ (eq root) PV1))
     (image_set (emap g1) (Union _ PE1_root PE1)) g' g1' ->
  copy P root g g1 g1'.
Proof.
  intros.
  assert (step_list g root (map (dst g) es)).
  Focus 1. {
    intro x.
    rewrite in_map_iff.
    split.
    + intros [e [? ?]].
      rewrite H1 in H5.
      destruct H5.
      exists e; auto.
    + intros.
      destruct H4 as [e ? ?].
      exists e.
      rewrite H1.
      unfold out_edges; auto.
  } Unfocus.
  destruct H3 as [?PRE [?PRE [?PRE [?PRE [?PRE [?PRE [?PRE [?PRE ?PRE]]]]]]]].
  assert (Same_set (reachable_by g root P) (Union _ PV1 (eq root))).
  Focus 1. {
    rewrite Same_set_spec.
    intro v.
    erewrite reachable_by_ind_equiv by eauto.
    rewrite Union_spec.
    tauto.
  } Unfocus.
  assert (Same_set (Intersection E (weak_edge_prop (reachable_by g root P) g) (evalid g)) (Union _ PE1 PE1_root)).
  Focus 1. {
    rewrite Same_set_spec.
    intro e.
    rewrite Intersection_spec; unfold weak_edge_prop.
    erewrite reachable_by_ind_equiv by eauto.
    unfold PE1.
    rewrite Union_spec, Intersection_spec.
    unfold weak_edge_prop, PV1, P0, PE1_root.
    rewrite H1.
    unfold out_edges.
    assert (root = src g e <-> src g e = root) by (split; intro; congruence).
    tauto.
  } Unfocus.
  unfold copy.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  + auto.
  + tauto.
  + tauto.
  + destruct PRE7 as [? _].
    rewrite Union_comm, <- H3 in H6.
    clear - H6; destruct H6.
    rewrite Same_set_spec; intro v; firstorder.
  + destruct PRE7 as [_ [? _]].
    rewrite Union_comm, <- H5 in H6.
    clear - H6; destruct H6.
    rewrite Same_set_spec; intro v; firstorder.
  + intros.
    rewrite Intersection_spec in H6.
    destruct H6.
    unfold weak_edge_prop in H6.
    rewrite reachable_by_ind_equiv in H6 by eauto.
    destruct H6.
    - apply PRE3.
      unfold PE1_root.
      rewrite H1.
      split; auto.
    - apply PRE1.
      unfold PE1.
      rewrite Intersection_spec; auto.
      unfold PV1.
      intro; apply H7; clear H7.
      rewrite reachable_by_ind_equiv by eauto.
      right.
      auto.
  + rewrite H5, H3; clear H3 H5.
    eapply guarded_bij_proper_aux1.
    1: apply si_guarded_si; eauto.
    1: reflexivity.
    apply guarded_bij_disjointed_union; auto.
    - eapply guarded_bij_proper_aux1; [| reflexivity | exact PRE2].
      apply si_guarded_si; symmetry; auto.
    - split; [| split; [| split]].
      * intros.
        exfalso.
        unfold PE1 in H3.
        rewrite Intersection_spec in H3.
        destruct H3 as [? _]; unfold weak_edge_prop, PV1 in H3.
        apply reachable_by_through_set_foot_prop in H3.
        unfold P0 in H3.
        rewrite Intersection_spec in H3.
        unfold Complement, Ensembles.In in H3.
        tauto.
      * intros.
        exfalso.
        unfold PE1_root in H3.
        rewrite H1 in H3; destruct H3.
        symmetry in H7.
        unfold PV1 in H5.
        apply reachable_by_through_set_foot_prop in H5.
        unfold P0 in H5.
        rewrite Intersection_spec in H5.
        unfold Complement, Ensembles.In in H5.
        tauto.
      * intros; apply PRE1; auto.
        intro.
        unfold PV1 in H7.
        apply reachable_by_through_set_foot_prop in H7.
        unfold P0 in H7.
        rewrite Intersection_spec in H7.
        unfold Complement, Ensembles.In in H7.
        tauto.
      * intros; apply PRE3; auto.
Qed.

Lemma vcopy1_edge_copy_list_copy: forall (g g1 g2: Graph) g2' root es (P: V -> Prop),
  let g1' := single_vertex_pregraph (vmap g1 root) in
  vvalid g root ->
  P root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  vcopy1 root g g1 ->
  edge_copy_list g root es P (g1, g1') (g2, g2') ->
  copy P root g g2 g2'.
Proof.
  intros.
  set (PV := reachable_by g root P).
  set (PE := Intersection E (weak_edge_prop PV g) (evalid g)).
  set (g' := empty_pregraph (vmap g root)).
  assert
   (let P0 := Intersection _ P (Complement _ (eq root)) in
    let PV1 := reachable_by_through_set g (map (dst g) nil) P0 in
    let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
    let PE1_root e := In e nil in
    guarded_bij PV1 PE1 (vmap g1) (emap g1) g g1' /\
    g ~=~ g1 /\
    (forall e, PE1 e -> ~ PV1 (dst g e) -> vmap g1 (dst g e) = dst g1' (emap g1 e)) /\
    guarded_bij (eq root) PE1_root (vmap g1) (emap g1) g1 g1' /\
    (forall e, PE1_root e -> vmap g1 (dst g e) = dst g1' (emap g1 e)) /\
    guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g1) /\
    guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g1) /\
    disjointed_guard
       (image_set (vmap g1) PV1) (image_set (vmap g1) (eq root))
       (image_set (emap g1) PE1) (image_set (emap g1) PE1_root) /\
    pregraph_join
       (image_set (vmap g1) (Union _ (eq root) PV1))
       (image_set (emap g1) (Union _ PE1_root PE1)) g' g1').
  Focus 1. {
    pose proof triple_vcopy1 _ _ _ H H3.
    intros.
    assert (Same_set PV1 (Empty_set _)).
    Focus 1. {
      rewrite Same_set_spec; intro v.
      split; [intros [? [? ?]] | intros []].
      inv H6.
    } Unfocus.
    assert (Same_set PE1 (Empty_set _)).
    Focus 1. {
      rewrite Same_set_spec; intro v.
      split; [intro | intros []].
      unfold PE1 in H7; rewrite Intersection_spec in H7.
      destruct H7 as [[? [? ?]] ?].
      inv H7.
    } Unfocus.
    assert (Same_set PE1_root (Empty_set _)).
    Focus 1. {
      rewrite Same_set_spec; intro v.
      split; [intros [] | intros []].
    } Unfocus.
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
    + eapply guarded_bij_proper_aux1; [.. | eapply guarded_bij_weaken; [.. | exact H5]].
      - symmetry.
        apply si_guarded_si.
        destruct H3; auto.
      - reflexivity.
      - rewrite H6.
        apply Constructive_sets.Included_Empty.
      - rewrite H7.
        apply Included_refl.
    + destruct H3; auto.
    + intros.
      rewrite (H7 e) in H9.
      inv H9.
    + rewrite H8; apply H5.
    + intros.
      rewrite (H8 e) in H9.
      inv H9.
    + destruct H3 as [_ [? _]].
      eapply guarded_pointwise_relation_weaken; [| exact H3].
      apply Complement_Included_rev.
      unfold Included, Ensembles.In; intros.
      subst x; unfold PV.
      apply reachable_by_refl; auto.
    + destruct H3 as [_ [_ ?]].
      eapply guarded_pointwise_relation_weaken; [| exact H3].
      apply Complement_Included_rev.
      unfold Included, Ensembles.In; intros.
      unfold PE; rewrite Intersection_spec in H9 |- *.
      split; [destruct H9 as [? _] | tauto].
      unfold weak_edge_prop in H9 |- *.
      rewrite <- H9.
      apply reachable_by_refl; auto.
    + split.
      - rewrite H6, image_Empty.
        apply Disjoint_Empty_set_left.
      - rewrite H7, image_Empty.
        apply Disjoint_Empty_set_left.
    + rewrite H6, H7, H8, !Union_Empty_set.
      rewrite image_single, image_Empty.
      apply pregraph_join_empty_single.
  } Unfocus.
  apply triple_final with (es := es); auto.
  clear H3.

  set (es_done := es) in H4 |- *.
  set (es_later := @nil E).
  assert (es = es_done ++ es_later) by (unfold es_later; rewrite app_nil_r; auto).
  clearbody es_done es_later.
  revert g2 g2' es_later H3 H4; rev_induction es_done; intros.
  + unfold edge_copy_list, relation_list in H4.
    simpl in H4.
    inversion H4; subst g2 g2'.
    auto.
  + clear H5.
    rewrite <- app_assoc in H4.
    unfold edge_copy_list in H6. rewrite combine_prefixes_app_1, map_app in H6; simpl in H6.
    apply (proj1 ((proj1 (same_relation_spec _ _) (relation_list_tail _ _)) _ _)) in H6.
    rename g2 into g3, g2' into g3'.
    apply compond_relation_spec in H6; destruct H6 as [[g2 g2'] [? ?]].

    eapply triple_loop; [auto | auto | eauto | auto | eauto | ..].
    1: eapply H3; eauto.
    auto.
Qed.

End LocalGraphCopy.

End LocalGraphCopy.
