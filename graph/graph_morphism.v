Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Morphisms_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas. Import RamifyCoq.graph.path_lemmas.PathNotation.
Require Import RamifyCoq.graph.subgraph2.

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
  vmap_inj: forall v1 v2, PV v1 -> PV v2 -> v1 <> v2 -> vmap v1 <> vmap v2;
  emap_inj: forall e1 e2, PE e1 -> PE e2 -> e1 <> e2 -> emap e1 <> emap e2;
  bij_is_morphism :> guarded_morphism
}.

Lemma guarded_morphsm_evalid:
  guarded_morphism ->
  Included PE (evalid G) ->
  Included (image_set emap PE) (evalid G').
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
  Included (image_set emap PE) (weak_edge_prop (image_set vmap PV) G').
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
  Included (image_set emap PE) (weak'_edge_prop (image_set vmap PV) G').
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
Arguments vmap_inj {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} g _ _ _ _ _ _.
Arguments emap_inj {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} g _ _ _ _ _ _.

Section GraphMorphism1.

Context {V V' E E': Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {EV': EqDec V' eq}.
Context {EE': EqDec E' eq}.

Lemma guarded_morphism_proper_aux1: forall PV PE vmap emap (G1 G2: PreGraph V E) (G1' G2': PreGraph V' E'),
  guarded_structurally_identical PV PE G1 G2 ->
  guarded_structurally_identical (image_set vmap PV) (image_set emap PE) G1' G2' ->
  guarded_morphism PV PE vmap emap G1 G1' ->
  guarded_morphism PV PE vmap emap G2 G2'.
Proof.
  intros.
  destruct (proj1 (guarded_si_spec _ _ _ _) H) as [? [? [? ?]]].
  destruct (proj1 (guarded_si_spec _ _ _ _) H0) as [? [? [? ?]]].
  assert (forall v : V, PV v -> (vvalid G2 v <-> vvalid G2' (vmap v))).
  Focus 1. {
    intros.
    rewrite <- H2 by auto.
    rewrite <- H6 by (constructor; auto).
    apply (vvalid_preserved H1); auto.
  } Unfocus.
  assert (forall e : E, PE e -> (evalid G2 e <-> evalid G2' (emap e))).
  Focus 1. {
    intros.
    rewrite <- H3 by auto.
    rewrite <- H7 by (constructor; auto).
    apply (evalid_preserved H1); auto.
  } Unfocus.
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
  guarded_structurally_identical (image_set vmap PV) (image_set emap PE) G1' G2' ->
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
  + rewrite guarded_pointwise_relation_spec in H.
    rewrite <- !H by auto.
    apply (vmap_inj H1); auto.
  + rewrite guarded_pointwise_relation_spec in H0.
    rewrite <- !H0 by auto.
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
  + rewrite Same_set_spec in H.
    apply (vmap_inj H1); auto; apply H; auto.
  + rewrite Same_set_spec in H0.
    apply (emap_inj H1); auto; apply H0; auto.
  + eapply guarded_morphism_proper_aux3; eauto.
    apply bij_is_morphism; auto.
Qed.

(*
Instance guarded_morphism_proper1 (PV: V -> Prop) (PE: E -> Prop) : Proper (guarded_pointwise_relation PV eq ==> guarded_pointwise_relation PE eq ==> guarded_structurally_identical PV PE ==> guarded_structurally_identical (image_set vmap1 PV) (image_set emap1 PE) ==> iff) (guarded_morphism PV PE).
Proof.
  intros.
  do 4 (hnf; intros).
  split; apply guarded_morphism_proper_aux1; auto; symmetry; auto.
Defined.
Global Existing Instance guarded_morphism_proper1.
*)

Instance guarded_morphism_proper3: Proper (@Same_set V ==> @Same_set E ==> @eq (V -> V') ==> @eq (E -> E') ==> eq ==> eq ==> iff) guarded_morphism.
Proof.
  intros.
  do 6 (hnf; intros).
  subst.
  split; eapply guarded_morphism_proper_aux3; eauto; symmetry; auto.
Defined.
Global Existing Instance guarded_morphism_proper3.

(*
Instance guarded_bij_proper1 (PV: V -> Prop) (PE: E -> Prop) (PV': V' -> Prop) (PE': E' -> Prop): Proper (guarded_pointwise_relation PV eq ==> guarded_pointwise_relation PE eq ==> guarded_structurally_identical PV PE ==> guarded_structurally_identical PV' PE' ==> iff) (guarded_bij PV PE PV' PE').
Proof.
  intros.
  do 4 (hnf; intros).
  split; apply guarded_bij_proper_aux1; auto; symmetry; auto.
Defined.
Global Existing Instance guarded_bij_proper1.
*)
Instance guarded_bij_proper3: Proper (@Same_set V ==> @Same_set E ==> @eq (V -> V') ==> @eq (E -> E') ==> eq ==> eq ==> iff) guarded_bij.
Proof.
  intros.
  do 6 (hnf; intros).
  subst.
  split; eapply guarded_bij_proper_aux3; eauto; symmetry; auto.
Qed.
Global Existing Instance guarded_bij_proper3.

End GraphMorphism1.

Definition disjointed_guard {V E} (PV1 PV2: V -> Prop) (PE1 PE2: E -> Prop) :=
  Disjoint _ PV1 PV2 /\ Disjoint _ PE1 PE2.

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

Definition boundary_consistent (PV1 PV2: V -> Prop) (PE1 PE2: E -> Prop) vmap emap (G: PreGraph V E) (G': PreGraph V' E') := 
  (forall e, PE1 e -> PV2 (src G e) -> evalid G e ->
     vmap (src G e) = src G' (emap e)) /\
  (forall e, PE2 e -> PV1 (src G e) -> evalid G e ->
     vmap (src G e) = src G' (emap e)) /\
  (forall e, PE1 e -> PV2 (dst G e) -> evalid G e ->
     vmap (dst G e) = dst G' (emap e)) /\
  (forall e, PE2 e -> PV1 (dst G e) -> evalid G e ->
     vmap (dst G e) = dst G' (emap e)).

Lemma guarded_morphism_disjointed_union: forall PV1 PE1 PV2 PE2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  guarded_morphism PV1 PE1 vmap emap G G' ->
  guarded_morphism PV2 PE2 vmap emap G G' ->
  boundary_consistent PV1 PV2 PE1 PE2 vmap emap G G' ->
  guarded_morphism (Union _ PV1 PV2) (Union _ PE1 PE2) vmap emap G G'.
Proof.
  intros.
  destruct H1 as [? [? [? ?]]].
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
    | apply H2
    | apply (src_preserved H0)];
    auto.
  + rewrite Union_spec in H5, H6.
    destruct H5, H6; 
    [ apply (dst_preserved H)
    | apply H3
    | apply H4
    | apply (dst_preserved H0)];
    auto.
Qed.

Lemma guarded_bij_disjointed_union: forall PV1 PE1 PV2 PE2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  disjointed_guard
    (image_set vmap PV1) (image_set vmap PV2) 
    (image_set emap PE1) (image_set emap PE2) ->
  guarded_bij PV1 PE1 vmap emap G G' ->
  guarded_bij PV2 PE2 vmap emap G G' ->
  boundary_consistent PV1 PV2 PE1 PE2 vmap emap G G' ->
  guarded_bij (Union _ PV1 PV2) (Union _ PE1 PE2) vmap emap G G'.
Proof.
  intros.
  destruct H as [vDISJ eDISJ].
  rewrite Disjoint_spec in vDISJ, eDISJ.
  split; intros.
  + rewrite Union_spec in *.
    destruct H, H3.
    - apply (vmap_inj H0); auto.
    - intro.
      apply (vDISJ (vmap v1)).
      * constructor; auto.
      * rewrite H5; constructor; auto.
    - intro.
      apply (vDISJ (vmap v2)).
      * constructor; auto.
      * rewrite <- H5; constructor; auto.
    - apply (vmap_inj H1); eauto.
  + rewrite Union_spec in *.
    destruct H, H3.
    - apply (emap_inj H0); auto.
    - intro.
      apply (eDISJ (emap e1)).
      * constructor; auto.
      * rewrite H5; constructor; auto.
    - intro.
      apply (eDISJ (emap e2)).
      * constructor; auto.
      * rewrite <- H5; constructor; auto.
    - apply (emap_inj H1); eauto.
  + apply guarded_morphism_disjointed_union; auto; apply bij_is_morphism; auto.
Qed.

Lemma guarded_bij_disjointed_weak_edge_prop_union: forall PV1 PV2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  let PE1 := Intersection _ (weak_edge_prop PV1 G) (evalid G) in
  let PE2 := Intersection _ (weak_edge_prop PV2 G) (evalid G) in
  disjointed_guard
    (image_set vmap PV1) (image_set vmap PV2) 
    (image_set emap PE1) (image_set emap PE2) ->
  guarded_bij PV1 PE1 vmap emap G G' ->
  guarded_bij PV2 PE2 vmap emap G G' ->
  (forall e, PE1 e -> PV2 (dst G e) -> vmap (dst G e) = dst G' (emap e)) ->
  (forall e, PE2 e -> PV1 (dst G e) -> vmap (dst G e) = dst G' (emap e)) ->
  guarded_bij (Union _ PV1 PV2) (Union _ PE1 PE2) vmap emap G G'.
Proof.
  intros.
  apply guarded_bij_disjointed_union; auto.
  destruct H.
  assert (Disjoint _ PV1 PV2) by (eapply image_Disjoint_rev; eauto).
  split; [| split; [| split]]; intros.
  + rewrite Disjoint_spec in H5.
    unfold PE1, weak_edge_prop in H6; rewrite Intersection_spec in H6.
    pose proof H5 _ (proj1 H6) H7; tauto.
  + rewrite Disjoint_spec in H5.
    unfold PE2, weak_edge_prop in H6; rewrite Intersection_spec in H6.
    pose proof H5 _  H7 (proj1 H6); tauto.
  + intros; apply (H2 e); auto.
  + intros; apply (H3 e); auto.
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

Lemma guarded_bij_weaken: forall PV1 PE1 PV2 PE2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  Included PV2 PV1 ->
  Included PE2 PE1 ->
  guarded_bij PV1 PE1 vmap emap G G' ->
  guarded_bij PV2 PE2 vmap emap G G'.
Proof.
  intros.
  split; intros.
  + apply (vmap_inj H1); auto;
    apply H; auto.
  + apply (emap_inj H1); auto;
    apply H0; auto.
  + eapply guarded_morphism_weaken; eauto; apply bij_is_morphism; auto.
Qed.

Class GraphMorphismSetting (DV DE V' E': Type): Type := {
  co_vertex: DV -> V';
  co_edge: DE -> E'
}.

End GraphMorphism2.

End GraphMorphism.

(*
Require Import Coq.Classes.Morphisms.
Definition respectful {A B : Type}
  (R : relation A) (R' : relation B) : relation (A -> B) :=
  Eval compute in @respectful_hetero A A (fun _ => B) (fun _ => B) R (fun _ _ => R').

PRETTY SURPRISING THAT THIS SYNTAX IS LEGAL!!!!!!!!!!!!!!!!!!!!!!!!!!

*)

