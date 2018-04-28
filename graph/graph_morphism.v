Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Morphisms_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas. Import RamifyCoq.graph.path_lemmas.PathNotation.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.

Module GraphMorphism.

Section GraphMorphism0.

Context {V V' E E': Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {EV': EqDec V' eq}.
Context {EE': EqDec E' eq}.

Variables (PV: V -> Prop) (PE: E -> Prop) (vmap: V -> V') (emap: E -> E') (G: PreGraph V E) (G': PreGraph V' E').

Record guarded_morphism: Prop := {
  vvalid_preserved: forall v, PV v -> (vvalid G v <-> vvalid G' (vmap v));
  evalid_preserved: forall e, PE e -> (evalid G e <-> evalid G' (emap e));
  src_preserved: forall e, PE e -> PV (src G e) -> evalid G e ->
                   vmap (src G e) = src G' (emap e);
  dst_preserved: forall e, PE e -> PV (dst G e) -> evalid G e -> vmap (dst G e) = dst G' (emap e)
}.

Record guarded_bij: Prop := {
  vmap_inj: is_guarded_inj PV vmap;
  emap_inj: is_guarded_inj PE emap;
  bij_is_morphism :> guarded_morphism
}.

Lemma guarded_morphsm_evalid:
  guarded_morphism ->
  Included PE (evalid G) ->
  Included (image_set PE emap) (evalid G').
Proof.
  intros.
  unfold Included, Ensembles.In in H0 |- *.
  intros.
  rewrite image_set_spec in H1.
  destruct H1 as [e [? ?]]; subst.
  pose proof evalid_preserved H.
  firstorder.
Qed.

Lemma guarded_morphism_weak_edge_prop:
  guarded_morphism ->
  Included PE (weak_edge_prop PV G) ->
  Included PE (evalid G) ->
  Included (image_set PE emap) (weak_edge_prop (image_set PV vmap) G').
Proof.
  intros.
  unfold Included, Ensembles.In in H0, H1 |- *.
  intros.
  rewrite image_set_spec in H2.
  destruct H2 as [e [? ?]]; subst.
  unfold weak_edge_prop.
  rewrite image_set_spec.
  exists (src G e).
  split.
  + apply H0; auto.
  + symmetry; apply (src_preserved H); auto.
    apply H0; auto.
Qed.

Lemma guarded_morphism_weak'_edge_prop:
  guarded_morphism ->
  Included PE (weak'_edge_prop PV G) ->
  Included PE (evalid G) ->
  Included (image_set PE emap) (weak'_edge_prop (image_set PV vmap) G').
Proof.
  intros.
  unfold Included, Ensembles.In in H0, H1 |- *.
  intros.
  rewrite image_set_spec in H2.
  destruct H2 as [e [? ?]]; subst.
  unfold weak'_edge_prop.
  rewrite image_set_spec.
  exists (dst G e).
  split.
  + apply H0; auto.
  + symmetry; apply (dst_preserved H); auto.
    apply H0; auto.
Qed.

End GraphMorphism0.

Arguments vvalid_preserved {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} g _ _.
Arguments evalid_preserved {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} g _ _.
Arguments src_preserved {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} g _ _ _ _.
Arguments dst_preserved {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} g _ _ _ _.
Arguments vmap_inj {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} g.
Arguments emap_inj {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} g.

Section GraphMorphism1.

Context {V V' E E': Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {EV': EqDec V' eq}.
Context {EE': EqDec E' eq}.

Lemma guarded_morphism_proper_aux1: forall PV PE vmap emap (G1 G2: PreGraph V E) (G1' G2': PreGraph V' E'),
  guarded_structurally_identical PV PE G1 G2 ->
  guarded_structurally_identical (image_set PV vmap) (image_set PE emap) G1' G2' ->
  guarded_morphism PV PE vmap emap G1 G1' ->
  guarded_morphism PV PE vmap emap G2 G2'.
Proof.
  intros.
  destruct (proj1 (guarded_si_spec _ _ _ _) H) as [? [? [? ?]]].
  destruct (proj1 (guarded_si_spec _ _ _ _) H0) as [? [? [? ?]]].
  assert (forall v : V, PV v -> (vvalid G2 v <-> vvalid G2' (vmap v))).
  1: {
    intros.
    rewrite <- H2 by auto.
    rewrite <- H6 by (constructor; auto).
    apply (vvalid_preserved H1); auto.
  }
  assert (forall e : E, PE e -> (evalid G2 e <-> evalid G2' (emap e))).
  1: {
    intros.
    rewrite <- H3 by auto.
    rewrite <- H7 by (constructor; auto).
    apply (evalid_preserved H1); auto.
  }
  split; auto; intros.
  + assert (evalid G1 e) by (rewrite H3 by auto; auto).
    rewrite <- H8.
    2: constructor; auto.
    2: rewrite <- (evalid_preserved H1), H3 by auto; auto.
    2: rewrite <- H11 by auto; auto.
    rewrite <- H4 by auto.
    apply (src_preserved H1); auto.
    rewrite H4 by auto; auto.
  + assert (evalid G1 e) by (rewrite H3 by auto; auto).
    rewrite <- H9.
    2: constructor; auto.
    2: rewrite <- (evalid_preserved H1), H3 by auto; auto.
    2: rewrite <- H11 by auto; auto.
    rewrite <- H5 by auto.
    apply (dst_preserved H1); auto.
    rewrite H5 by auto; auto.
Qed.

Lemma guarded_morphism_proper_aux2: forall PV PE vmap1 vmap2 emap1 emap2 (G: PreGraph V E) (G': PreGraph V' E'),
  guarded_pointwise_relation PV eq vmap1 vmap2 ->
  guarded_pointwise_relation PE eq emap1 emap2 ->
  guarded_morphism PV PE vmap1 emap1 G G' ->
  guarded_morphism PV PE vmap2 emap2 G G'.
Proof.
  intros.
  rewrite guarded_pointwise_relation_spec in H.
  rewrite guarded_pointwise_relation_spec in H0.
  split; intros.
  + intros.
    rewrite <- H by auto.
    apply (vvalid_preserved H1); auto.
  + intros.
    rewrite <- H0 by auto.
    apply (evalid_preserved H1); auto.
  + rewrite <- H0 by auto.
    rewrite <- H by auto.
    apply (src_preserved H1); auto.
  + rewrite <- H0 by auto.
    rewrite <- H by auto.
    apply (dst_preserved H1); auto.
Qed.

Lemma guarded_morphism_proper_aux3: forall PV1 PV2 PE1 PE2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  Same_set PV1 PV2 ->
  Same_set PE1 PE2 ->
  guarded_morphism PV1 PE1 vmap emap G G' ->
  guarded_morphism PV2 PE2 vmap emap G G'.
Proof.
  intros.
  rewrite Same_set_spec in *.
  split; intros.
  + apply (vvalid_preserved H1), H; auto.
  + apply (evalid_preserved H1), H0; auto.
  + apply (src_preserved H1); auto.
    - apply H0; auto.
    - apply H; auto.
  + apply (dst_preserved H1); auto.
    - apply H0; auto.
    - apply H; auto.
Qed.

Lemma guarded_bij_proper_aux1: forall PV PE vmap emap (G1 G2: PreGraph V E) (G1' G2': PreGraph V' E'),
  guarded_structurally_identical PV PE G1 G2 ->
  guarded_structurally_identical (image_set PV vmap) (image_set PE emap) G1' G2' ->
  guarded_bij PV PE vmap emap G1 G1' ->
  guarded_bij PV PE vmap emap G2 G2'.
Proof.
  intros.
  split; intros.
  + apply (vmap_inj H1); auto.
  + apply (emap_inj H1); auto.
  + eapply guarded_morphism_proper_aux1; eauto.
    apply bij_is_morphism; auto.
Qed.

Lemma guarded_bij_proper_aux2: forall PV PE vmap1 vmap2 emap1 emap2 (G: PreGraph V E) (G': PreGraph V' E'),
  guarded_pointwise_relation PV eq vmap1 vmap2 ->
  guarded_pointwise_relation PE eq emap1 emap2 ->
  guarded_bij PV PE vmap1 emap1 G G' ->
  guarded_bij PV PE vmap2 emap2 G G'.
Proof.
  intros.
  split; intros.
  + rewrite <- H.
    apply (vmap_inj H1); auto.
  + rewrite <- H0.
    apply (emap_inj H1); auto.
  + eapply guarded_morphism_proper_aux2; eauto.
    apply bij_is_morphism; auto.
Qed.

Lemma guarded_bij_proper_aux3: forall PV1 PV2 PE1 PE2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  Same_set PV1 PV2 ->
  Same_set PE1 PE2 ->
  guarded_bij PV1 PE1 vmap emap G G' ->
  guarded_bij PV2 PE2 vmap emap G G'.
Proof.
  intros.
  split; intros.
  + rewrite <- H.
    apply (vmap_inj H1); auto.
  + rewrite <- H0.
    apply (emap_inj H1); auto.
  + eapply guarded_morphism_proper_aux3; eauto.
    apply bij_is_morphism; auto.
Qed.

Instance guarded_morphism_proper1 (PV: V -> Prop) (PE: E -> Prop) (vmap: V -> V') (emap: E -> E'): Proper (guarded_structurally_identical PV PE ==> guarded_structurally_identical (image_set PV vmap) (image_set PE emap) ==> iff) (guarded_morphism PV PE vmap emap).
Proof.
  intros.
  do 2 (hnf; intros).
  split; apply guarded_morphism_proper_aux1; auto; symmetry; auto.
Defined.
Global Existing Instance guarded_morphism_proper1.

Instance guarded_morphism_proper2 (PV: V -> Prop) (PE: E -> Prop) : Proper (guarded_pointwise_relation PV eq ==> guarded_pointwise_relation PE eq ==> eq ==> @eq (PreGraph V' E') ==> iff) (guarded_morphism PV PE).
Proof.
  intros.
  do 4 (hnf; intros); subst.
  split; apply guarded_morphism_proper_aux2; auto; symmetry; auto.
Defined.
Global Existing Instance guarded_morphism_proper2.

Instance guarded_morphism_proper3: Proper (@Same_set V ==> @Same_set E ==> @eq (V -> V') ==> @eq (E -> E') ==> eq ==> eq ==> iff) guarded_morphism.
Proof.
  intros.
  do 6 (hnf; intros).
  subst.
  split; eapply guarded_morphism_proper_aux3; eauto; symmetry; auto.
Defined.
Global Existing Instance guarded_morphism_proper3.

Instance guarded_bij_proper1 (PV: V -> Prop) (PE: E -> Prop) (vmap: V -> V') (emap: E -> E'): Proper (guarded_structurally_identical PV PE ==> guarded_structurally_identical (image_set PV vmap) (image_set PE emap) ==> iff) (guarded_bij PV PE vmap emap).
Proof.
  intros.
  do 2 (hnf; intros).
  split; apply guarded_bij_proper_aux1; auto; symmetry; auto.
Defined.
Global Existing Instance guarded_bij_proper1.

Instance guarded_bij_proper2 (PV: V -> Prop) (PE: E -> Prop) : Proper (guarded_pointwise_relation PV eq ==> guarded_pointwise_relation PE eq ==> eq ==> @eq (PreGraph V' E') ==> iff) (guarded_bij PV PE).
Proof.
  intros.
  do 4 (hnf; intros); subst.
  split; apply guarded_bij_proper_aux2; auto; symmetry; auto.
Defined.
Global Existing Instance guarded_bij_proper2.

Instance guarded_bij_proper3: Proper (@Same_set V ==> @Same_set E ==> @eq (V -> V') ==> @eq (E -> E') ==> eq ==> eq ==> iff) guarded_bij.
Proof.
  intros.
  do 6 (hnf; intros).
  subst.
  split; eapply guarded_bij_proper_aux3; eauto; symmetry; auto.
Qed.
Global Existing Instance guarded_bij_proper3.

Lemma guarded_morphism_step: forall {PV: V -> Prop} {PE: E -> Prop} {vmap emap n m} {g: PreGraph V E} {g': PreGraph V' E'},
  guarded_morphism PV PE vmap emap g g' ->
  Included (Intersection _ (weak_edge_prop PV g) (evalid g)) PE ->
  PV n ->
  PV m ->
  step g n m ->
  step g' (vmap n) (vmap m).
Proof.
  intros.
  rewrite !@step_spec in H3 |- *.
  destruct H3 as [e [? [? ?]]].
  exists (emap e).
  assert (PE e) by
   (apply H0; unfold Ensembles.In; rewrite Intersection_spec; subst; auto).
  split; [| split].
  + eapply (evalid_preserved H); eauto.
  + symmetry; subst; eapply (src_preserved H); eauto.
  + symmetry; subst; eapply (dst_preserved H); eauto.
Qed.

Lemma guarded_morphism_edge: forall {PV: V -> Prop} {PE: E -> Prop} {vmap emap n m} {g: PreGraph V E} {g': PreGraph V' E'},
  guarded_morphism PV PE vmap emap g g' ->
  Included (Intersection _ (weak_edge_prop PV g) (evalid g)) PE ->
  PV n ->
  PV m ->
  edge g n m ->
  edge g' (vmap n) (vmap m).
Proof.
  unfold edge.
  intros.
  destruct H3 as [? [? ?]].
  split; [| split].
  + eapply (vvalid_preserved H); eauto.
  + eapply (vvalid_preserved H); eauto.
  + eapply guarded_morphism_step; eauto.
Qed.

Lemma guarded_morphism_reachable: forall {PV: V -> Prop} {PE: E -> Prop} {vmap emap n m} {g: PreGraph V E} {g': PreGraph V' E'},
  guarded_morphism PV PE vmap emap g g' ->
  Included (Intersection _ (weak_edge_prop PV g) (evalid g)) PE ->
  reachable_by g n PV m ->
  reachable g' (vmap n) (vmap m).
Proof.
  intros.
  rewrite reachable_by_eq_partialgraph_reachable in H1.
  pattern m.
  eapply (@reachable_general_ind V E) with (x := n); [| exact H1 |].
  + intros.
    apply reachable_edge with (vmap x); auto.
    rewrite <- partialgraph_edge_iff in H2.
    destruct H2 as [? [? ?]].
    eapply guarded_morphism_edge; eauto.
  + apply reachable_refl.
    rewrite <- reachable_by_eq_partialgraph_reachable in H1.
    eapply (vvalid_preserved H); eauto.
    - apply reachable_by_head_prop in H1; auto.
    - apply reachable_by_head_valid in H1; auto.
Qed.

End GraphMorphism1.

Lemma disjointed_guard_left_union: forall {V E} (PV1 PV2 PV3: V -> Prop) (PE1 PE2 PE3: E -> Prop),
  disjointed_guard (Union _ PV1 PV2) PV3 (Union _ PE1 PE2) PE3 ->
  disjointed_guard PV1 PV3 PE1 PE3 /\
  disjointed_guard PV2 PV3 PE2 PE3.
Proof.
  intros.
  destruct H.
  rewrite Union_left_Disjoint in H, H0.
  split; split; tauto.
Qed.

Section GraphMorphism2.

Context {V V' E E': Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {EV': EqDec V' eq}.
Context {EE': EqDec E' eq}.

Definition boundary_src_consistent (PE1: E -> Prop) (PV2: V -> Prop) vmap emap (G: PreGraph V E) (G': PreGraph V' E') := 
  forall e, PE1 e -> PV2 (src G e) -> evalid G e -> vmap (src G e) = src G' (emap e).

Definition boundary_dst_consistent (PE1: E -> Prop) (PV2: V -> Prop) vmap emap (G: PreGraph V E) (G': PreGraph V' E') := 
  forall e, PE1 e -> PV2 (dst G e) -> evalid G e -> vmap (dst G e) = dst G' (emap e).

Instance boundary_src_consistent_proper: Proper (Same_set ==> Same_set ==> eq ==> eq ==> eq ==> eq ==> iff) boundary_src_consistent.
Proof.
  do 6 (hnf; intros); subst.
  rewrite Same_set_spec in H, H0.
  hnf in H, H0.
  unfold boundary_src_consistent.
  firstorder.
Qed.
Global Existing Instance boundary_src_consistent_proper.

Instance boundary_dst_consistent_proper: Proper (Same_set ==> Same_set ==> eq ==> eq ==> eq ==> eq ==> iff) boundary_dst_consistent.
Proof.
  do 6 (hnf; intros); subst.
  rewrite Same_set_spec in H, H0.
  hnf in H, H0.
  unfold boundary_dst_consistent.
  firstorder.
Qed.
Global Existing Instance boundary_dst_consistent_proper.

Lemma boundary_dst_consistent_si: forall (PE1: E -> Prop) (PV1 PV2: V -> Prop) vmap emap G G1' G2',
  guarded_morphism PV1 PE1 vmap emap G G1' ->
  guarded_morphism PV1 PE1 vmap emap G G2' ->
  boundary_dst_consistent PE1 PV2 vmap emap G G1' ->
  guarded_structurally_identical (image_set PV1 vmap) (image_set PE1 emap) G1' G2' ->
  boundary_dst_consistent PE1 PV2 vmap emap G G2'.
Proof.
  intros.
  hnf in H |- *.
  intros.
  rewrite (H1 e) by auto; clear H1.
  rewrite guarded_si_spec in H2.
  destruct H2 as [? [? [? ?]]].
  apply H7.
  + constructor; auto.
  + rewrite <- (evalid_preserved H); auto.
  + rewrite <- (evalid_preserved H0); auto.
Qed.

Definition boundary_edge_consistent (PE1: E -> Prop) (PV2: V -> Prop) vmap emap (G: PreGraph V E) (G': PreGraph V' E') := 
  boundary_src_consistent PE1 PV2 vmap emap G G' /\
  boundary_dst_consistent PE1 PV2 vmap emap G G'.

Definition boundary_consistent (PV1 PV2: V -> Prop) (PE1 PE2: E -> Prop) vmap emap (G: PreGraph V E) (G': PreGraph V' E') := 
  boundary_edge_consistent PE1 PV2 vmap emap G G' /\
  boundary_edge_consistent PE2 PV1 vmap emap G G'.

Lemma guarded_bij_vmap_image_dec: forall (PV: V -> Prop) (PE: E -> Prop) vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  guarded_bij PV PE vmap emap G G' ->
  exists f: forall v, Decidable (image_set PV vmap v), True.
Proof.
  intros.
  pose proof vmap_inj H.
  destruct H0 as [f ?].
  assert (forall v, Decidable (image_set PV vmap v)).
  1: {
    intros.
    specialize (H0 v).
    destruct (f v) eqn:?H; [left | right]; rewrite image_set_spec.
    + exists v0.
      destruct H0; split; auto.
      specialize (H2 _ H0).
      symmetry; apply H2; auto.
    + intros [v0 [? ?]].
      apply (H0 v0 H2).
      symmetry; auto.
  }
  exists X; auto.
Qed.

Lemma guarded_bij_emap_image_dec: forall (PV: V -> Prop) (PE: E -> Prop) vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  guarded_bij PV PE vmap emap G G' ->
  exists f: forall e, Decidable (image_set PE emap e), True.
Proof.
  intros.
  pose proof emap_inj H.
  destruct H0 as [f ?].
  assert (forall e, Decidable (image_set PE emap e)).
  1: {
    intros.
    specialize (H0 e).
    destruct (f e) eqn:?H; [left | right]; rewrite image_set_spec.
    + exists e0.
      destruct H0; split; auto.
      specialize (H2 _ H0).
      symmetry; apply H2; auto.
    + intros [e0 [? ?]].
      apply (H0 e0 H2).
      symmetry; auto.
  }
  exists X; auto.
Qed.

Lemma guarded_bij_empty_empty: forall vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  guarded_bij (Empty_set V) (Empty_set E) vmap emap G G'.
Proof.
  intros.
  split; [.. | split].
  + apply is_guarded_inj_empty.
  + apply is_guarded_inj_empty.
  + intros. inversion H.
  + intros. inversion H.
  + intros. inversion H.
  + intros. inversion H.
Qed.

Lemma guarded_morphism_disjointed_union: forall PV1 PE1 PV2 PE2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  guarded_morphism PV1 PE1 vmap emap G G' ->
  guarded_morphism PV2 PE2 vmap emap G G' ->
  boundary_consistent PV1 PV2 PE1 PE2 vmap emap G G' ->
  guarded_morphism (Union _ PV1 PV2) (Union _ PE1 PE2) vmap emap G G'.
Proof.
  intros.
  destruct H1 as [[? ?] [? ?]].
  split; intros.
  + rewrite Union_spec in *.
    destruct H5; [apply (vvalid_preserved H) | apply (vvalid_preserved H0)];
    auto.
  + rewrite Union_spec in *.
    destruct H5; [apply (evalid_preserved H) | apply (evalid_preserved H0)];
    auto.
  + rewrite Union_spec in H5, H6.
    destruct H5, H6; 
    [ apply (src_preserved H)
    | apply H1
    | apply H3
    | apply (src_preserved H0)];
    auto.
  + rewrite Union_spec in H5, H6.
    destruct H5, H6; 
    [ apply (dst_preserved H)
    | apply H2
    | apply H4
    | apply (dst_preserved H0)];
    auto.
Qed.

Lemma guarded_bij_disjointed_union: forall PV1 PE1 PV2 PE2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  disjointed_guard
    (image_set PV1 vmap) (image_set PV2 vmap) 
    (image_set PE1 emap) (image_set PE2 emap) ->
  guarded_bij PV1 PE1 vmap emap G G' ->
  guarded_bij PV2 PE2 vmap emap G G' ->
  boundary_consistent PV1 PV2 PE1 PE2 vmap emap G G' ->
  guarded_bij (Union _ PV1 PV2) (Union _ PE1 PE2) vmap emap G G'.
Proof.
  intros.
  destruct H as [vDISJ eDISJ].
  split; intros.
  + pose proof image_Disjoint_rev _ _  _ vDISJ.
    apply Disjoint_Union_Prop_join in H.
    eapply is_guarded_inj_disjoint_union; eauto.
    - apply (vmap_inj H0); auto.
    - apply (vmap_inj H1); auto.
    - rewrite Disjoint_spec in vDISJ.
      intros v1 v2 ? ? ?.
      apply (vDISJ (vmap v1)).
      * constructor; auto.
      * rewrite H5; constructor; auto.
  + pose proof image_Disjoint_rev _ _  _ eDISJ.
    apply Disjoint_Union_Prop_join in H.
    eapply is_guarded_inj_disjoint_union; eauto.
    - apply (emap_inj H0); auto.
    - apply (emap_inj H1); auto.
    - rewrite Disjoint_spec in eDISJ.
      intros e1 e2 ? ? ?.
      apply (eDISJ (emap e1)).
      * constructor; auto.
      * rewrite H5; constructor; auto.
  + apply guarded_morphism_disjointed_union; auto; apply bij_is_morphism; auto.
Qed.

Lemma guarded_bij_disjointed_weak_edge_prop_union: forall PV1 PV2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  let PE1 := Intersection _ (weak_edge_prop PV1 G) (evalid G) in
  let PE2 := Intersection _ (weak_edge_prop PV2 G) (evalid G) in
  disjointed_guard
    (image_set PV1 vmap) (image_set PV2 vmap) 
    (image_set PE1 emap) (image_set PE2 emap) ->
  guarded_bij PV1 PE1 vmap emap G G' ->
  guarded_bij PV2 PE2 vmap emap G G' ->
  boundary_dst_consistent PE1 PV2 vmap emap G G' ->
  boundary_dst_consistent PE2 PV1 vmap emap G G' ->
  guarded_bij (Union _ PV1 PV2) (Union _ PE1 PE2) vmap emap G G'.
Proof.
  intros.
  apply guarded_bij_disjointed_union; auto.
  destruct H.
  assert (Disjoint _ PV1 PV2) by (eapply image_Disjoint_rev; eauto).
  split; split; auto; hnf; intros.
  + rewrite Disjoint_spec in H5.
    unfold PE1, weak_edge_prop in H6; rewrite Intersection_spec in H6.
    pose proof H5 _ (proj1 H6) H7; tauto.
  + rewrite Disjoint_spec in H5.
    unfold PE2, weak_edge_prop in H6; rewrite Intersection_spec in H6.
    pose proof H5 _  H7 (proj1 H6); tauto.
Qed.

Lemma guarded_bij_disjointed_union_strong: forall PV1 PE1 PV2 PE2 vmap emap (G: PreGraph V E) (G1' G2': PreGraph V' E'),
  disjointed_guard
    (image_set PV1 vmap) (image_set PV2 vmap) 
    (image_set PE1 emap) (image_set PE2 emap) ->
  guarded_bij PV1 PE1 vmap emap G G1' ->
  guarded_bij PV2 PE2 vmap emap G G2' ->
  boundary_edge_consistent PE1 PV2 vmap emap G G1' ->
  boundary_edge_consistent PE2 PV1 vmap emap G G2' ->
  exists G',
  guarded_bij (Union _ PV1 PV2) (Union _ PE1 PE2) vmap emap G G' /\
  guarded_structurally_identical (image_set PV1 vmap) (image_set PE1 emap) G1' G' /\
  guarded_structurally_identical (image_set PV2 vmap) (image_set PE2 emap) G2' G'.
Proof.
  intros.
  destruct (vmap_inj H0) as [vg1 ?].
  destruct (vmap_inj H1) as [vg2 ?].
  destruct (emap_inj H0) as [eg1 ?].
  destruct (emap_inj H1) as [eg2 ?].
  set (vg := fun v' => match vg1 v' with Some v => Some v | _ => vg2 v' end).
  set (eg := fun e' => match eg1 e' with Some e => Some e | _ => eg2 e' end).
  exists
   (@Build_PreGraph V' E' _ _
    (fun v' => match vg1 v' with Some _ => vvalid G1' v' | _ => vvalid G2' v' end)
    (fun e' => match eg1 e' with Some _ => evalid G1' e' | _ => evalid G2' e' end)
    (fun e' => match eg1 e' with Some _ => src G1' e' | _ => src G2' e' end)
    (fun e' => match eg1 e' with Some _ => dst G1' e' | _ => dst G2' e' end)).
  split; [| split].
  + split; [.. | split].
    - eapply is_guarded_inj_disjoint_union.
      * apply Disjoint_Union_Prop_join.
        clear - H; destruct H.
        apply image_Disjoint_rev in H; auto.
      * apply (vmap_inj H0).
      * apply (vmap_inj H1).
      * clear - H; destruct H.
        rewrite Disjoint_spec in H.
        intros.
        pose proof (H (vmap a1)).
        intro.
        rewrite !image_set_spec in H3.
        spec H3; [exists a1; auto |].
        spec H3; [exists a2; auto |].
        auto.
    - eapply is_guarded_inj_disjoint_union.
      * apply Disjoint_Union_Prop_join.
        clear - H; destruct H.
        apply image_Disjoint_rev in H0; auto.
      * apply (emap_inj H0).
      * apply (emap_inj H1).
      * clear - H; destruct H.
        rewrite Disjoint_spec in H0.
        intros.
        pose proof (H0 (emap a1)).
        intro.
        rewrite !image_set_spec in H3.
        spec H3; [exists a1; auto |].
        spec H3; [exists a2; auto |].
        auto.
    - simpl; intros.
      rewrite Union_spec in H8; destruct H8.
      * rewrite (is_guarded_inj_rev_aux PV1 vmap vg1) by auto.
        apply (vvalid_preserved H0); auto.
      * destruct H.
        rewrite (is_guarded_inj_rev_aux' PV1 PV2 vmap vg1) by auto.
        apply (vvalid_preserved H1); auto.
    - simpl; intros.
      rewrite Union_spec in H8; destruct H8.
      * rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
        apply (evalid_preserved H0); auto.
      * destruct H.
        rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by auto.
        apply (evalid_preserved H1); auto.
    - simpl; intros.
      rewrite Union_spec in H8, H9.
      destruct H8, H9.
      * rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
        apply (src_preserved H0); auto.
      * rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
        apply (proj1 H2); auto.
      * rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
        apply (proj1 H3); auto.
      * rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
        apply (src_preserved H1); auto.
    - simpl; intros.
      rewrite Union_spec in H8, H9.
      destruct H8, H9.
      * rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
        apply (dst_preserved H0); auto.
      * rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
        apply (proj2 H2); auto.
      * rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
        apply (proj2 H3); auto.
      * rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
        apply (dst_preserved H1); auto.
  + rewrite guarded_si_spec; simpl.
    split; [| split; [| split]].
    - intros v' ?.
      rewrite image_set_spec in H8; destruct H8 as [v [? ?]]; subst v'.
      rewrite (is_guarded_inj_rev_aux PV1 vmap vg1) by auto.
      tauto.
    - intros e' ?.
      rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
      rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
      tauto.
    - intros e' ? ? ?.
      rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
      rewrite (is_guarded_inj_rev_aux PE1 emap eg1) in H10 |- * by auto.
      auto.
    - intros e' ? ? ?.
      rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
      rewrite (is_guarded_inj_rev_aux PE1 emap eg1) in H10 |- * by auto.
      auto.
  + rewrite guarded_si_spec; simpl.
    split; [| split; [| split]].
    - intros v' ?.
      rewrite image_set_spec in H8; destruct H8 as [v [? ?]]; subst v'.
      rewrite (is_guarded_inj_rev_aux' PV1 PV2 vmap vg1) by (destruct H; auto).
      tauto.
    - intros e' ?.
      rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
      rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
      tauto.
    - intros e' ? ? ?.
      rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
      rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
      auto.
    - intros e' ? ? ?.
      rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
      rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
      auto.
Qed.

Lemma guarded_bij_pregraph_join: forall PV1 PE1 PV2 PE2 vmap emap (G: PreGraph V E) (G1' G2': PreGraph V' E'),
  disjointed_guard
    (image_set PV1 vmap) (image_set PV2 vmap) 
    (image_set PE1 emap) (image_set PE2 emap) ->
  guarded_bij PV1 PE1 vmap emap G G1' ->
  guarded_bij PV2 PE2 vmap emap G G2' ->
  boundary_edge_consistent PE1 PV2 vmap emap G G1' ->
  boundary_edge_consistent PE2 PV1 vmap emap G G2' ->
  Same_set (vvalid G1') (image_set PV1 vmap) ->
  Same_set (evalid G1') (image_set PE1 emap) ->
  Same_set (vvalid G2') (image_set PV2 vmap) ->
  Same_set (evalid G2') (image_set PE2 emap) ->
  exists G',
  guarded_bij (Union _ PV1 PV2) (Union _ PE1 PE2) vmap emap G G' /\
  pregraph_join (image_set PV2 vmap) (image_set PE2 emap) G1' G' /\
  pregraph_join (image_set PV1 vmap) (image_set PE1 emap) G2' G'.
Proof.
  intros.
  rename H4 into Hv1, H5 into He1, H6 into Hv2, H7 into He2.
  destruct (vmap_inj H0) as [vg1 ?].
  destruct (vmap_inj H1) as [vg2 ?].
  destruct (emap_inj H0) as [eg1 ?].
  destruct (emap_inj H1) as [eg2 ?].
  set (vg := fun v' => match vg1 v' with Some v => Some v | _ => vg2 v' end).
  set (eg := fun e' => match eg1 e' with Some e => Some e | _ => eg2 e' end).
  exists
   (@Build_PreGraph V' E' _ _
    (fun v' => match vg1 v' with Some _ => vvalid G1' v' | _ => vvalid G2' v' end)
    (fun e' => match eg1 e' with Some _ => evalid G1' e' | _ => evalid G2' e' end)
    (fun e' => match eg1 e' with Some _ => src G1' e' | _ => src G2' e' end)
    (fun e' => match eg1 e' with Some _ => dst G1' e' | _ => dst G2' e' end)).
  split; [| split].
  + split; [.. | split].
    - eapply is_guarded_inj_disjoint_union.
      * apply Disjoint_Union_Prop_join.
        clear - H; destruct H.
        apply image_Disjoint_rev in H; auto.
      * apply (vmap_inj H0).
      * apply (vmap_inj H1).
      * clear - H; destruct H.
        rewrite Disjoint_spec in H.
        intros.
        pose proof (H (vmap a1)).
        intro.
        rewrite !image_set_spec in H3.
        spec H3; [exists a1; auto |].
        spec H3; [exists a2; auto |].
        auto.
    - eapply is_guarded_inj_disjoint_union.
      * apply Disjoint_Union_Prop_join.
        clear - H; destruct H.
        apply image_Disjoint_rev in H0; auto.
      * apply (emap_inj H0).
      * apply (emap_inj H1).
      * clear - H; destruct H.
        rewrite Disjoint_spec in H0.
        intros.
        pose proof (H0 (emap a1)).
        intro.
        rewrite !image_set_spec in H3.
        spec H3; [exists a1; auto |].
        spec H3; [exists a2; auto |].
        auto.
    - simpl; intros.
      rewrite Union_spec in H8; destruct H8.
      * rewrite (is_guarded_inj_rev_aux PV1 vmap vg1) by auto.
        apply (vvalid_preserved H0); auto.
      * destruct H.
        rewrite (is_guarded_inj_rev_aux' PV1 PV2 vmap vg1) by auto.
        apply (vvalid_preserved H1); auto.
    - simpl; intros.
      rewrite Union_spec in H8; destruct H8.
      * rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
        apply (evalid_preserved H0); auto.
      * destruct H.
        rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by auto.
        apply (evalid_preserved H1); auto.
    - simpl; intros.
      rewrite Union_spec in H8, H9.
      destruct H8, H9.
      * rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
        apply (src_preserved H0); auto.
      * rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
        apply (proj1 H2); auto.
      * rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
        apply (proj1 H3); auto.
      * rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
        apply (src_preserved H1); auto.
    - simpl; intros.
      rewrite Union_spec in H8, H9.
      destruct H8, H9.
      * rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
        apply (dst_preserved H0); auto.
      * rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
        apply (proj2 H2); auto.
      * rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
        apply (proj2 H3); auto.
      * rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
        apply (dst_preserved H1); auto.
  + split; [| split; [| split]]; [split | split | |].
    - intro v'; simpl.
      rewrite <- (Hv2 v').
      split; [destruct (vg1 v'); auto |].
      intros [? | ?].
      * rewrite (Hv1 v') in H8.
        rewrite image_set_spec in H8; destruct H8 as [v [? ?]]; subst v'.
        rewrite (is_guarded_inj_rev_aux PV1 vmap vg1) by auto.
        rewrite (Hv1 (vmap v)).
        constructor; auto.
      * rewrite (Hv2 v') in H8.
        rewrite image_set_spec in H8; destruct H8 as [v [? ?]]; subst v'.
        rewrite (is_guarded_inj_rev_aux' PV1 PV2 vmap vg1) by (destruct H; auto).
        rewrite (Hv2 (vmap v)).
        constructor; auto.
    - intros v' ? ?.
      rewrite (Hv1 v') in H8.
      generalize v', H8, H9.
      apply Disjoint_spec.
      destruct H; auto.
    - intro e'; simpl.
      rewrite <- (He2 e').
      split; [destruct (eg1 e'); auto |].
      intros [? | ?].
      * rewrite (He1 e') in H8.
        rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
        rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
        rewrite (He1 (emap e)).
        constructor; auto.
      * rewrite (He2 e') in H8.
        rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
        rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
        rewrite (He2 (emap e)).
        constructor; auto.
    - intros e' ? ?.
      rewrite (He1 e') in H8.
      generalize e', H8, H9.
      apply Disjoint_spec.
      destruct H; auto.
    - intros e' ? _; simpl.
      rewrite (He1 e') in H8.
      rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
      rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
      auto.
    - intros e' ? _; simpl.
      rewrite (He1 e') in H8.
      rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
      rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
      auto.
  + split; [| split; [| split]]; [split | split | |].
    - intro v'; simpl.
      rewrite <- (Hv1 v').
      split; [destruct (vg1 v'); auto |].
      intros [? | ?].
      * rewrite (Hv2 v') in H8.
        rewrite image_set_spec in H8; destruct H8 as [v [? ?]]; subst v'.
        rewrite (is_guarded_inj_rev_aux' PV1 PV2 vmap vg1) by (destruct H; auto).
        rewrite (Hv2 (vmap v)).
        constructor; auto.
      * rewrite (Hv1 v') in H8.
        rewrite image_set_spec in H8; destruct H8 as [v [? ?]]; subst v'.
        rewrite (is_guarded_inj_rev_aux PV1 vmap vg1) by auto.
        rewrite (Hv1 (vmap v)).
        constructor; auto.
    - intros v' ? ?.
      rewrite (Hv2 v') in H8.
      generalize v', H8, H9.
      apply Disjoint_spec, Disjoint_comm.
      destruct H; auto.
    - intro e'; simpl.
      rewrite <- (He1 e').
      split; [destruct (eg1 e'); auto |].
      intros [? | ?].
      * rewrite (He2 e') in H8.
        rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
        rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
        rewrite (He2 (emap e)).
        constructor; auto.
      * rewrite (He1 e') in H8.
        rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
        rewrite (is_guarded_inj_rev_aux PE1 emap eg1) by auto.
        rewrite (He1 (emap e)).
        constructor; auto.
    - intros e' ? ?.
      rewrite (He2 e') in H8.
      generalize e', H8, H9.
      apply Disjoint_spec, Disjoint_comm.
      destruct H; auto.
    - intros e' ? _; simpl.
      rewrite (He2 e') in H8.
      rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
      rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
      auto.
    - intros e' ? _; simpl.
      rewrite (He2 e') in H8.
      rewrite image_set_spec in H8; destruct H8 as [e [? ?]]; subst e'.
      rewrite (is_guarded_inj_rev_aux' PE1 PE2 emap eg1) by (destruct H; auto).
      auto.
Qed.
  
Lemma guarded_morphism_weaken: forall PV1 PE1 PV2 PE2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  Included PV2 PV1 ->
  Included PE2 PE1 ->
  guarded_morphism PV1 PE1 vmap emap G G' ->
  guarded_morphism PV2 PE2 vmap emap G G'.
Proof.
  intros.
  split; intros.
  + apply (vvalid_preserved H1), H; auto.
  + apply (evalid_preserved H1), H0; auto.
  + apply (src_preserved H1); auto.
    - apply H0; auto.
    - apply H; auto.
  + apply (dst_preserved H1); auto.
    - apply H0; auto.
    - apply H; auto.
Qed.

Lemma guarded_bij_weak_edge_prop: forall PV PE PV0 PE0 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  Included PV0 PV ->
  Included PE0 PE ->
  Included PE0 (Intersection _ (weak_edge_prop PV0 G) (evalid G)) ->
  guarded_morphism PV PE vmap emap G G' ->
  forall e', 
    (image_set PE0 emap) e' ->
    (Intersection _ (weak_edge_prop (image_set PV0 vmap) G') (evalid G')) e'.
Proof.
  intros.
  rewrite image_set_spec in H3.
  destruct H3 as [e [? ?]].
  subst e'.
  pose proof H1 _ H3.
  unfold Ensembles.In in H4; rewrite Intersection_spec in H4 |- *.
  destruct H4; split.
  + unfold weak_edge_prop.
    rewrite <- (src_preserved H2).
    - constructor; auto.
    - apply H0; auto.
    - apply H; auto.
    - auto.
  + apply (evalid_preserved H2).
    - apply H0; auto.
    - auto.
Qed.

End GraphMorphism2.

End GraphMorphism.

(*
Require Import Coq.Classes.Morphisms.
Definition respectful {A B : Type}
  (R : relation A) (R' : relation B) : relation (A -> B) :=
  Eval compute in @respectful_hetero A A (fun _ => B) (fun _ => B) R (fun _ _ => R').

PRETTY SURPRISING THAT THIS SYNTAX IS LEGAL!!!!!!!!!!!!!!!!!!!!!!!!!!

*)

