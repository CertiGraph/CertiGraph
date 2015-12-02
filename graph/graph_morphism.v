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

Lemma guarded_morphism_proper_aux1: forall PV PE vmap1 vmap2 emap1 emap2 (G1 G2: PreGraph V E) (G1' G2': PreGraph V' E'),
  guarded_pointwise_relation PV eq vmap1 vmap2 ->
  guarded_pointwise_relation PE eq emap1 emap2 ->
  guarded_structurally_identical PV PE G1 G2 ->
  guarded_structurally_identical (image_set vmap1 PV) (image_set emap1 PE) G1' G2' ->
  guarded_morphism PV PE vmap1 emap1 G1 G1' ->
  guarded_morphism PV PE vmap2 emap2 G2 G2'.
Proof.
  intros.
  rewrite guarded_pointwise_relation_spec in H.
  rewrite guarded_pointwise_relation_spec in H0.
  destruct (proj1 (guarded_si_spec _ _ _ _) H1) as [? [? [? ?]]].
  destruct (proj1 (guarded_si_spec _ _ _ _) H2) as [? [? [? ?]]].
  assert (forall v : V, PV v -> (vvalid G2 v <-> vvalid G2' (vmap2 v))).
  Focus 1. {
    intros.
    rewrite <- H4 by auto.
    rewrite <- H by auto.
    rewrite <- H8 by (constructor; auto).
    apply (vvalid_preserved H3); auto.
  } Unfocus.
  assert (forall e : E, PE e -> (evalid G2 e <-> evalid G2' (emap2 e))).
  Focus 1. {
    intros.
    rewrite <- H5 by auto.
    rewrite <- H0 by auto.
    rewrite <- H9 by (constructor; auto).
    apply (evalid_preserved H3); auto.
  } Unfocus.
  split; auto; intros.
  + assert (evalid G1 e) by (rewrite H5 by auto; auto).
    rewrite <- H10.
    2: rewrite <- H0 by auto; constructor; auto.
    2: rewrite <- H0, <- (evalid_preserved H3), H5 by auto; auto.
    2: rewrite <- H13 by auto; auto.
    rewrite <- H0 by auto.
    rewrite <- H by auto.
    rewrite <- H6 by auto.
    apply (src_preserved H3); auto.
    rewrite H6 by auto; auto.
  + assert (evalid G1 e) by (rewrite H5 by auto; auto).
    rewrite <- H11.
    2: rewrite <- H0 by auto; constructor; auto.
    2: rewrite <- H0, <- (evalid_preserved H3), H5 by auto; auto.
    2: rewrite <- H13 by auto; auto.
    rewrite <- H0 by auto.
    rewrite <- H by auto.
    rewrite <- H7 by auto.
    apply (dst_preserved H3); auto.
    rewrite H7 by auto; auto.
Qed.

Lemma guarded_morphism_proper_aux2: forall PV1 PV2 PE1 PE2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
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

Lemma guarded_bij_proper_aux1: forall PV PE vmap1 vmap2 emap1 emap2 (G1 G2: PreGraph V E) (G1' G2': PreGraph V' E'),
  guarded_pointwise_relation PV eq vmap1 vmap2 ->
  guarded_pointwise_relation PE eq emap1 emap2 ->
  guarded_structurally_identical PV PE G1 G2 ->
  guarded_structurally_identical (image_set vmap1 PV) (image_set emap1 PE) G1' G2' ->
  guarded_bij PV PE vmap1 emap1 G1 G1' ->
  guarded_bij PV PE vmap2 emap2 G2 G2'.
Proof.
  intros.
  split; intros.
  + rewrite guarded_pointwise_relation_spec in H.
    rewrite <- !H by auto.
    apply (vmap_inj H3); auto.
  + rewrite guarded_pointwise_relation_spec in H0.
    rewrite <- !H0 by auto.
    apply (emap_inj H3); auto.
  + eapply guarded_morphism_proper_aux1; eauto.
    apply bij_is_morphism; auto.
Qed.

Lemma guarded_bij_proper_aux2: forall PV1 PV2 PE1 PE2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
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
  + eapply guarded_morphism_proper_aux2; eauto.
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

Instance guarded_morphism_proper2: Proper (@Same_set V ==> @Same_set E ==> @eq (V -> V') ==> @eq (E -> E') ==> eq ==> eq ==> iff) guarded_morphism.
Proof.
  intros.
  do 6 (hnf; intros).
  subst.
  split; eapply guarded_morphism_proper_aux2; eauto; symmetry; auto.
Defined.
Global Existing Instance guarded_morphism_proper2.

(*
Instance guarded_bij_proper1 (PV: V -> Prop) (PE: E -> Prop) (PV': V' -> Prop) (PE': E' -> Prop): Proper (guarded_pointwise_relation PV eq ==> guarded_pointwise_relation PE eq ==> guarded_structurally_identical PV PE ==> guarded_structurally_identical PV' PE' ==> iff) (guarded_bij PV PE PV' PE').
Proof.
  intros.
  do 4 (hnf; intros).
  split; apply guarded_bij_proper_aux1; auto; symmetry; auto.
Defined.
Global Existing Instance guarded_bij_proper1.
*)
Instance guarded_bij_proper2: Proper (@Same_set V ==> @Same_set E ==> @eq (V -> V') ==> @eq (E -> E') ==> eq ==> eq ==> iff) guarded_bij.
Proof.
  intros.
  do 6 (hnf; intros).
  subst.
  split; eapply guarded_bij_proper_aux2; eauto; symmetry; auto.
Qed.
Global Existing Instance guarded_bij_proper2.

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

Lemma guarded_bij_disjointed_weak_edge_prop_union: forall PV1 PV1' PE1' PV2 PV2' PE2' vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  let PE1 := Intersection _ (weak_edge_prop PV1 G) (evalid G) in
  let PE2 := Intersection _ (weak_edge_prop PV2 G) (evalid G) in
  disjointed_guard PV1' PV2' PE1' PE2' ->
  guarded_bij PV1 PE1 PV1' PE1' vmap emap G G' ->
  guarded_bij PV2 PE2 PV2' PE2' vmap emap G G' ->
  (forall e, PE1 e -> PV2 (dst G e) -> vmap (dst G e) = dst G' (emap e)) ->
  (forall e, PE2 e -> PV1 (dst G e) -> vmap (dst G e) = dst G' (emap e)) ->
  guarded_bij (Union _ PV1 PV2) (Union _ PE1 PE2)
    (Union _ PV1' PV2') (Union _ PE1' PE2') vmap emap G G'.
Proof.
  intros.
  apply guarded_bij_disjointed_union; auto.
  assert (Disjoint _ PV1 PV2).
  Focus 1. {
    rewrite Disjoint_spec; intros v ? ?.
    apply (proj1 (proj2 (proj2 (proj2 (proj2 H0))))) in H4.
    apply (proj1 (proj2 (proj2 (proj2 (proj2 H1))))) in H5.
    destruct H.
    rewrite Disjoint_spec in H.
    eapply H; eauto.
  } Unfocus.
  split; [| split; [| split]].
  + intros.
    destruct H5.
    unfold Ensembles.In, weak_edge_prop in H5.
    rewrite Disjoint_spec in H4.
    pose proof H4 _ H5 H6; tauto.
  + intros.
    destruct H5.
    unfold Ensembles.In, weak_edge_prop in H5.
    rewrite Disjoint_spec in H4.
    pose proof H4 _ H6 H5; tauto.
  + intros; apply (H2 e); auto.
  + intros; apply (H3 e); auto.
Qed.
    
Lemma guarded_morphism_weaken: forall PV1 PE1 PV1' PE1' PV2 PE2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  Included PV2 PV1 ->
  Included PE2 PE1 ->
  guarded_morphism PV1 PE1 PV1' PE1' vmap emap G G' ->
  guarded_morphism PV2 PE2
    (fun v' => exists v, PV2 v /\ vmap v = v')
    (fun e' => exists e, PE2 e /\ emap e = e') vmap emap G G'.
Proof.
  intros.
  destruct H1 as [? [? [? [? [? ?]]]]].
  split; [| split; [| split; [| split; [| split]]]]; intros.
  + eauto.
  + eauto.
  + apply H3.
    apply H; auto.
  + apply H4.
    apply H0; auto.
  + apply H5.
    apply H0; auto.
    apply H; auto.
    auto.
  + apply H6.
    apply H0; auto.
    apply H; auto.
    auto.
Qed.

Lemma guarded_bij_weaken: forall PV1 PE1 PV1' PE1' PV2 PE2 vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  Included PV2 PV1 ->
  Included PE2 PE1 ->
  guarded_bij PV1 PE1 PV1' PE1' vmap emap G G' ->
  guarded_bij PV2 PE2
    (fun v' => exists v, PV2 v /\ vmap v = v')
    (fun e' => exists e, PE2 e /\ emap e = e') vmap emap G G'.
Proof.
  intros.
  destruct H1 as [? [? [? [? ?]]]].
  split; [| split; [| split; [| split]]]; intros.
  + apply H1; auto;
    apply H; auto.
  + apply H2; auto;
    apply H0; auto.
  + auto.
  + auto.
  + eapply guarded_morphism_weaken; eauto.
Qed.
    
Class GraphMorphismSetting (DV DE V' E': Type): Type := {
  co_vertex: DV -> V';
  co_edge: DE -> E'
}.

End GraphMorphism2.

End GraphMorphism.

Module GlobalCopyGraph.

Section GlobalCopyGraph.

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

Definition nothing (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  pointwise_relation V eq (vmap g1) (vmap g2) /\
  pointwise_relation E eq (emap g1) (emap g2) /\
  g1' ~=~ g2'.

Definition vcopy1 x (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  exists y,
  g1 ~=~ g2 /\
  vvalid g1 x /\
  guarded_pointwise_relation (Complement _ (eq x)) eq (vmap g1) (vmap g2) /\
  pointwise_relation _ eq (emap g1) (emap g2) /\
  y = vmap g2 x /\
  (forall x, y <> vmap g1 x) /\
  (forall e, y <> src g2' (emap g1 e)) /\
  vertex_join (eq y) g1' g2'.

Definition ecopy1 e (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  exists e',
  g1 ~=~ g2 /\
  evalid g1 e /\
  pointwise_relation V eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ (eq e)) eq (emap g1) (emap g2) /\
  e' = emap g2 e /\
  (forall e, e' <> emap g1 e) /\
  edge_union (eq e') g1' g2' /\
  vmap g2 (src g2 e) = src g2' e' /\
  vmap g2 (dst g2 e) = dst g2' e'.

Definition copy P (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  exists P',
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ P) eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ (weak_edge_prop P g1)) eq (emap g1) (emap g2) /\
  boundary_consistent (Complement _ P) P (Complement _ (weak_edge_prop P g1)) (weak_edge_prop P g1) (vmap g2) (emap g2) g2 g2' /\
  guarded_bij P (weak_edge_prop P g2) P' (weak_edge_prop P' g2') (vmap g2) (emap g2) g2 g2' /\
  Prop_join (vvalid g1') P' (vvalid g2') /\
  Prop_join (evalid g1') (weak_edge_prop P' g2') (evalid g2').

Definition gcopy (PV: V -> Prop) (PE: E -> Prop) (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  exists PV' PE',
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ PV) eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ PE) eq (emap g1) (emap g2) /\
  forall fPV fPE fPV' fPE',
    disjointed_guard fPV PV fPE PE ->
    guarded_bij fPV fPE fPV' fPE' (vmap g1) (emap g1) g1 g1' ->
    guarded_bij (Union _ fPV PV) (Union _ fPE PE)
     (Union _ fPV' PV') (Union _ fPE' PE') (vmap g2) (emap g2) g2 g2'.

Definition edge_copy (g: Graph) (P: V -> Prop) (l: list E * E) :=
  let (es, e) := l in
  let P0 := Intersection _ (reachable_by g (dst g e) P)
               (Complement _ (reachable_by_through_set g (map (dst g) es) P)) in
  relation_list (nothing :: copy P0 :: nothing :: ecopy1 e :: nothing :: nil).

Definition edge_copy_list (g: Graph) es (P: V -> Prop) :=
  relation_list (map (edge_copy g P) (combine (prefixes es) es)).

Lemma eq_do_nothing: inclusion _ eq nothing.
Proof.
  intros; hnf; intros.
  hnf; destruct x as [g1 g1'], y as [g2 g2'].
  inversion H; subst.
  split; [| split; [| split]].
  + reflexivity.
  + intro; reflexivity.
  + intro; reflexivity.
  + reflexivity.
Qed.

(*
Require Import Coq.Classes.Morphisms.
Definition respectful {A B : Type}
  (R : relation A) (R' : relation B) : relation (A -> B) :=
  Eval compute in @respectful_hetero A A (fun _ => B) (fun _ => B) R (fun _ _ => R').

PRETTY SURPRISING THAT THIS SYNTAX IS LEGAL!!!!!!!!!!!!!!!!!!!!!!!!!!

*)

Lemma vcopy1_is_gcopy: forall x (p1 p2: Graph * Graph'),
  let (g1, _) := p1 in
  vcopy1 x p1 p2 ->
  gcopy (eq x) (Empty_set _) p1 p2.
Proof.
  intros.
  destruct p1 as [g1 g1'], p2 as [g2 g2'].
  intros.
  destruct H as [y [? [? [? [? [? [? [? ?]]]]]]]].
  exists (eq y), (Empty_set _).
  split; [| split; [| split]]; auto.
  1: apply guarded_pointwise_relation_pointwise_relation; auto.
  intros.
(*
  pose proof vertex_join_guarded_si _ _ _ H4.
  pose proof vertex_join_DisjointV _ _ _ H4.
  pose proof vertex_join_DisjointE _ _ _ H4.
*)
  assert (Disjoint V' fPV' (eq y)).
  Focus 1. {
    apply (guarded_surj_Disjoint (vmap g1) fPV); auto.
    destruct H8 as [_ [_ [? _]]]; auto.
  } Unfocus.
  assert (Disjoint E' fPE' (weak_edge_prop (eq y) g2')).
  Focus 1. {
    apply (guarded_surj_Disjoint (emap g1) fPE).
    + destruct H8 as [_ [_ [_ [? _]]]]; auto.
    + intros; apply H5.
  } Unfocus.
  apply guarded_bij_disjointed_union.
  + split; auto.
    rewrite Disjoint_spec; intros.
    inversion H12.
  + eapply guarded_bij_proper_aux1; [.. | exact H8].
    - eapply guarded_pointwise_relation_weaken; [| apply H1].
      apply Included_Complement_Disjoint; destruct H7; auto.
    - eapply guarded_pointwise_relation_weaken; [apply Included_Full_set |].
      apply guarded_pointwise_relation_pointwise_relation; auto.
    - apply si_guarded_si; auto.
    - eapply guarded_si_weaken; [| | apply vertex_join_guarded_si; eauto];
      apply Included_Complement_Disjoint; auto.
  + split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]; intros.
    - congruence.
    - inversion H11.
    - exists x; subst; auto.
    - inversion H11.
    - subst; auto.
    - inversion H11.
    - subst.
      destruct H6 as [[HH _ ] _].
      specialize (HH (vmap g2 v)).
      rewrite (proj1 H) in H0.
      tauto.
    - inversion H11.
    - inversion H11.
    - inversion H11.
  + split; [| split; [| split]]; intros.
    - subst.
Abort.

Lemma vcopy1_edge_copy_list_copy: forall root es (p1 p2: Graph * Graph') (P: V -> Prop),
  let (g1, _) := p1 in
  vvalid g1 root ->
  P root ->
  (forall e, In e es <-> out_edges g1 root e) ->
  relation_list (nothing :: vcopy1 root :: nothing :: edge_copy_list g1 es (Intersection _ P (Complement _ (eq root))) :: nothing :: nil) p1 p2 ->
  copy (reachable_by g1 root P) p1 p2.
Proof.
  intros.
  destruct p1 as [g1 g1'], p2 as [g2 g2'].
  intros.
  destruct_relation_list p3 p4 p5 p6 in H2.
Abort.

End GlobalCopyGraph.

End GlobalCopyGraph.

Module LocalCopyGraph.

Section LocalCopyGraph.

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

Hint Resolve guarded_bij_surj.

Definition vmap (g: Graph): V -> V' := fun v => co_vertex (vlabel g v).

Definition emap (g: Graph): E -> E' := fun e => co_edge (elabel g e).

Definition nothing (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  pointwise_relation V eq (vmap g1) (vmap g2) /\
  pointwise_relation E eq (emap g1) (emap g2) /\
  g1' ~=~ g2'.

Definition vcopy1 (P: V -> Prop) root root' (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ (eq root)) eq (vmap g1) (vmap g2) /\
  pointwise_relation _ eq (emap g1) (emap g2) /\
  root' = vmap g2 root /\
  vertex_join (eq root') g1' g2'.

Definition ecopy1 e e' (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  evalid g1 e /\
  pointwise_relation V eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ (eq e)) eq (emap g1) (emap g2) /\
  e' = emap g2 e /\
  (forall e, e' <> emap g1 e) /\
  edge_union (eq e') g1' g2' /\
  vmap g2 (src g2 e) = src g2' e' /\
  vmap g2 (dst g2 e) = dst g2' e'.

Definition copy (P: V -> Prop) root root' PV' PE' (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  let PV := reachable_by g1 root P in
  let PE := Intersection _ (weak_edge_prop PV g1) (evalid g1) in
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ PV) eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ PE) eq (emap g1) (emap g2) /\
  root' = vmap g2 root /\
  pregraph_join PV' PE' g1' g2' /\
  (forall e, PE e -> ~ PV (dst g1 e) -> vmap g2 (dst g1 e) = dst g2' (emap g2 e)) /\
  guarded_bij PV PE PV' PE' (vmap g2) (emap g2) g2 g2'.

(*
Definition edge_copy (g: Graph) (P: V -> Prop) (l: list E * E) :=
  let (es, e) := l in
  let P0 := Intersection _ (reachable_by g (dst g e) P)
               (Complement _ (reachable_by_through_set g (map (dst g) es) P)) in
  relation_list (nothing :: copy P0 :: nothing :: ecopy1 e :: nothing :: nil).

Definition edge_copy_list (g: Graph) es (P: V -> Prop) :=
  relation_list (map (edge_copy g P) (combine (prefixes es) es)).
*)

Lemma eq_do_nothing: inclusion _ eq nothing.
Proof.
  intros; hnf; intros.
  hnf; destruct x as [g1 g1'], y as [g2 g2'].
  inversion H; subst.
  split; [| split; [| split]].
  + reflexivity.
  + intro; reflexivity.
  + intro; reflexivity.
  + reflexivity.
Qed.


Lemma triple_vcopy1: forall (g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root root',
  P root ->
  vvalid g1 root ->
  vcopy1 P root root' (g1, g1') (g2, g2') ->
  guarded_bij (eq root) (Empty_set _) (eq root') (Empty_set _) (vmap g2) (emap g2) g2 g2'.
Proof.
  intros g1 g2 g1' g2' P root root' ? ? [? [? [? [? ?]]]].
  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]; intros.
  + congruence.
  + inversion H6.
  + exists root; subst; auto.
  + inversion H6.
  + subst v; auto.
  + inversion H6.
  + subst v.
    destruct H5 as [[HH _ ] _].
    specialize (HH (vmap g2 root)).
    rewrite (proj1 H1) in H0.
    tauto.
  + inversion H6.
  + inversion H6.
  + inversion H6.
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
  forall son son' PV' PE',
    copy (Intersection _ P0 (Complement _ PV1)) son son' PV' PE' (g1, g1') (g2, g2') ->
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
  destruct H0 as [COPY_si [COPY_gprv [COPY_gpre [COPY_son' [? [? COPY_bij]]]]]].
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

Lemma triple1_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later son',
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  forall PV1' PE1',
  guarded_bij PV1 PE1 PV1' PE1' (vmap g1) (emap g1) g g1' /\
  g ~=~ g1 (* /\
  (forall e, PE1 e -> ~ PV1 (dst g e) -> vmap g1 (dst g e) = dst g1' (emap g1 e))*) ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  forall PV' PE',
  copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) son' PV' PE' (g1, g1') (g2, g2') ->
  disjointed_guard PV1' PV' PE1' PE' -> (* From spatial fact *)
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _) -> (* From weak mark lemma *)
  let PV2' := Union _ PV1' PV' in
  let PE2' := Union _ PE1' PE' in
  guarded_bij PV2 PE2 PV2' PE2' (vmap g2) (emap g2) g g2'.
Proof.
  intros until son'.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 PE1 PV1' PE1' [PRE_bij PRE_si]
         PV2 PE2 PV' PE' COPY DISJ PV1_DEC PV2' PE2'.
  assert (Same_set PV2 (Union _ PV1 (reachable_by g (dst g e0) (Intersection _ P0 (Complement _ PV1))))) as PV2_spec
    by (apply triple_aux1_copy; auto).
  assert (Same_set PE2 (Union _ PE1 (Intersection _ (weak_edge_prop (reachable_by g (dst g e0) (Intersection _ P0 (Complement _ PV1))) g) (evalid g)))) as PE2_spec
    by (apply triple_aux2_copy; auto).
  rewrite PV2_spec, PE2_spec.
  assert (forall e,
       Intersection E
         (weak_edge_prop
            (reachable_by g (dst g e0)
               (Intersection V P0 (Complement V PV1))) g) 
         (evalid g) e ->
       ~
       g |= dst g e0 ~o~> dst g e
       satisfying (Intersection V P0 (Complement V PV1)) ->
       vmap g2 (dst g e) = dst g2' (emap g2 e))
  by (eapply triple_aux4_copy; eauto).

  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [COPY_son' [? [? COPY_bij]]]]]].

  assert (Same_set
    (Intersection E
      (weak_edge_prop
        (reachable_by g (dst g e0) (Intersection V P0 (Complement V PV1))) g) 
          (evalid g))
    (Intersection E
      (weak_edge_prop
        (reachable_by g1 (dst g e0) (Intersection V P0 (Complement V PV1))) g1)
          (evalid g1))).
  Focus 1. {
    rewrite PRE_si at 1.
    rewrite (weak_edge_prop_si _ _ _ PRE_si); reflexivity.
  } Unfocus.
  assert (guarded_bij
          (reachable_by g (dst g e0) (Intersection V P0 (Complement V PV1)))
          (Intersection E
             (weak_edge_prop
                (reachable_by g (dst g e0)
                   (Intersection V P0 (Complement V PV1))) g) 
             (evalid g)) PV' PE' (vmap g2) (emap g2) g g2').
  Focus 1. {
    eapply guarded_bij_proper2; [| eassumption | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
    1: rewrite PRE_si at 1; reflexivity.
    eapply guarded_bij_proper1; [reflexivity | reflexivity | | | exact COPY_bij].
    1: apply si_guarded_si; rewrite PRE_si; auto.
    1: reflexivity.
  } Unfocus.

  apply guarded_bij_disjointed_weak_edge_prop_union; auto.
  + eapply guarded_bij_proper_aux1; [.. | exact PRE_bij].
    - eapply guarded_pointwise_relation_weaken; [| eassumption].
      apply Included_Complement_Disjoint.
      rewrite Disjoint_spec; intros x ? ?.
      apply reachable_by_foot_prop in H5.
      rewrite Intersection_spec in H5; unfold Complement in H5; tauto.
    - eapply guarded_pointwise_relation_weaken; [| eassumption].
      rewrite <- PRE_si at 1.
      erewrite <- (weak_edge_prop_si _ g g1) by eassumption.
      apply Included_Complement_Disjoint.
      eapply Included_Disjoint; [apply Intersection1_Included, Included_refl | apply Intersection1_Included, Included_refl |].
      apply weak_edge_prop_Disjoint.
      rewrite Disjoint_spec; intros x ? ?.
      apply reachable_by_foot_prop in H5.
      rewrite Intersection_spec in H5; unfold Complement in H5; tauto.
    - reflexivity.
    - pose proof pregraph_join_guarded_si _ _ _ _ H0.
      destruct DISJ.
      eapply guarded_si_weaken; [| | exact H4].
      * apply Included_Complement_Disjoint; auto.
      * apply Included_Complement_Disjoint; auto.
  + intros.
    exfalso.
    eapply (triple_aux3_copy g P0); eauto.
  + intros.
    apply H; auto.
    intro.
    apply reachable_by_foot_prop in H6.
    rewrite Intersection_spec in H6.
    destruct H6 as [_ ?].
    destruct H6; auto.
Qed.

Lemma triple2_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later son',
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  forall PV1' PE1',
  g ~=~ g1 ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  forall PV' PE',
  copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) son' PV' PE' (g1, g1') (g2, g2') ->
  disjointed_guard PV1' PV' PE1' PE' -> (* From spatial fact *)
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _) -> (* From weak mark lemma *)
  let PV2' := Union _ PV1' PV' in
  let PE2' := Union _ PE1' PE' in
  g ~=~ g2.
Proof.
  intros.
  rename H5 into DISJ.
  destruct H4 as [? [? [? [? [? [? ?]]]]]].
  transitivity g1; auto.
Qed.

Lemma triple3_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later son',
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  forall PV1' PE1',
  guarded_bij PV1 PE1 PV1' PE1' (vmap g1) (emap g1) g g1' /\
  g ~=~ g1 /\
  (forall e, PE1 e -> ~ PV1 (dst g e) -> vmap g1 (dst g e) = dst g1' (emap g1 e)) ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  forall PV' PE',
  copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) son' PV' PE' (g1, g1') (g2, g2') ->
  disjointed_guard PV1' PV' PE1' PE' -> (* From spatial fact *)
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _) -> (* From weak mark lemma *)
  let PV2' := Union _ PV1' PV' in
  let PE2' := Union _ PE1' PE' in
  (forall e, PE2 e -> ~ PV2 (dst g e) -> vmap g2 (dst g e) = dst g2' (emap g2 e)).
Proof.
  intros until son'.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 PE1 PV1' PE1' [PRE_bij [PRE_si PRE_consi]]
         PV2 PE2 PV' PE' COPY DISJ PV1_DEC PV2' PE2'.
  assert (Same_set PV2 (Union _ PV1 (reachable_by g (dst g e0) (Intersection _ P0 (Complement _ PV1))))) as PV2_spec
    by (apply triple_aux1_copy; auto).
  assert (Same_set PE2 (Union _ PE1 (Intersection _ (weak_edge_prop (reachable_by g (dst g e0) (Intersection _ P0 (Complement _ PV1))) g) (evalid g)))) as PE2_spec
    by (apply triple_aux2_copy; auto).
  assert (forall e,
       Intersection E
         (weak_edge_prop
            (reachable_by g (dst g e0)
               (Intersection V P0 (Complement V PV1))) g) 
         (evalid g) e ->
       ~
       g |= dst g e0 ~o~> dst g e
       satisfying (Intersection V P0 (Complement V PV1)) ->
       vmap g2 (dst g e) = dst g2' (emap g2 e))
  by (eapply triple_aux4_copy; eauto).
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [COPY_son' [? [? COPY_bij]]]]]].

  intros.
  rewrite Same_set_spec in PE2_spec. rewrite (PE2_spec e) in H2.
  assert (~ PV1 (dst g e)) by (rewrite Same_set_spec in PV2_spec; rewrite (PV2_spec (dst g e)) in H3; rewrite Union_spec in H3; tauto).
  rewrite Union_spec in H2.
  destruct H2.
  + replace (vmap g2 (dst g e)) with (vmap g1 (dst g e)).
    Focus 2. {
      rewrite guarded_pointwise_relation_spec in COPY_gprv.
      apply COPY_gprv.
      unfold Complement at 1, Ensembles.In.
      rewrite <- PRE_si.
      intro.
      eapply (triple_aux3_copy g P0); eauto.
    } Unfocus.
    replace (emap g2 e) with (emap g1 e).
    Focus 2. {
      rewrite guarded_pointwise_relation_spec in COPY_gpre.
      apply COPY_gpre.
      unfold Complement at 1, Ensembles.In.
      intro.
      pose proof weak_edge_prop_si
       (reachable_by g1 (dst g e0) (Intersection V P0 (Complement V PV1)))
        g g1 PRE_si.
      rewrite Same_set_spec in H6.
      rewrite <- (H6 e) in H5; clear H6.
      rewrite Intersection_spec in H5.
      destruct H5 as [? _]; unfold weak_edge_prop in H5.
      rewrite <- PRE_si in H5.
      apply reachable_by_foot_prop in H5.
      unfold PE1 in H2.
      rewrite Intersection_spec in H2, H5.
      destruct H5 as [_ ?].
      unfold weak_edge_prop in H2; destruct H2 as [? _].
      apply H5; auto.
    } Unfocus.
    rewrite PRE_consi by auto.
    pose proof pregraph_join_guarded_si _ _ _ _ H0.
    rewrite guarded_si_spec in H5.
    assert (Complement E' PE' (emap g1 e)).
    Focus 1. {
      destruct DISJ.
      rewrite Disjoint_spec in H7.
      refine (H7 (emap g1 e) _).
      apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 PRE_bij)))))); auto.
    } Unfocus.
    assert (evalid g1' (emap g1 e)).
    Focus 1. {
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PRE_bij)))))))).
      specialize (H7 _ H2).
      rewrite <- H7.
      unfold PE1 in H2.
      rewrite Intersection_spec in H2; tauto.
    } Unfocus.
    assert (evalid g2' (emap g1 e))
      by (rewrite (proj1 (proj2 H5)) in H7; auto).
    apply (proj2 (proj2 (proj2 H5))); auto.
  + apply H; auto.
    rewrite Same_set_spec in PV2_spec; rewrite (PV2_spec (dst g e)) in H3.
    rewrite Union_spec in H3; tauto.
Qed.

Lemma triple4_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later root' son',
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1_root e := In e es_done in
  forall PE1'_root,
  guarded_bij (eq root) PE1_root (eq root') PE1'_root (vmap g1) (emap g1) g1 g1' /\
  g ~=~ g1 ->
  forall PV' PE',
  copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) son' PV' PE' (g1, g1') (g2, g2') ->
  disjointed_guard (eq root') PV' PE1'_root PE' -> (* From spatial fact *)
  guarded_bij (eq root) PE1_root (eq root') PE1'_root (vmap g2) (emap g2) g2 g2'.
Proof.
  intros until son'.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 PE1_root PE1'_root [PRE_bij_root PRE_si]
         PV' PE' COPY DISJ.
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [COPY_son' [? [? COPY_bij]]]]]].

  eapply guarded_bij_proper_aux1; [.. | exact PRE_bij_root].
  + eapply guarded_pointwise_relation_weaken; [.. | exact COPY_gprv].
    intros ? ? ?.
    unfold Ensembles.In in *.
    apply reachable_by_foot_prop in H2.
    rewrite Intersection_spec in H2.
    unfold P0 in H2; destruct H2 as [? _].
    rewrite Intersection_spec in H2.
    destruct H2 as [_ ?]; apply H2; auto.
  + eapply guarded_pointwise_relation_weaken; [.. | exact COPY_gpre].
    rewrite <- weak_edge_prop_si, <- PRE_si by eauto.
    intros e ? ?.
    unfold Ensembles.In, weak_edge_prop in *.
    rewrite Intersection_spec in H2; destruct H2 as [? _].
    apply reachable_by_foot_prop in H2.
    rewrite Intersection_spec in H2; destruct H2 as [? _].
    unfold P0 in H2.
    rewrite Intersection_spec in H2; destruct H2 as [_ ?].
    apply H2. 
    unfold Ensembles.In.
    assert (In e es) by (rewrite H_ES; rewrite in_app_iff; tauto).
    rewrite H_OUT_EDGES in H3.
    unfold out_edges in H3.
    symmetry; tauto.
  + apply si_guarded_si; auto.
  + destruct DISJ.
    eapply guarded_si_weaken; [.. | exact (pregraph_join_guarded_si _ _ _ _ H)];
    rewrite Included_Complement_Disjoint; auto.
Qed.

Lemma triple5_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later root' son',
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1_root e := In e es_done in
  forall PE1'_root,
  guarded_bij (eq root) PE1_root (eq root') PE1'_root (vmap g1) (emap g1) g1 g1' /\
  g ~=~ g1 /\
  (forall e, PE1_root e -> vmap g1 (dst g e) = dst g1' (emap g1 e)) ->
  forall PV' PE',
  copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) son' PV' PE' (g1, g1') (g2, g2') ->
  disjointed_guard (eq root') PV' PE1'_root PE' -> (* From spatial fact *)
  (forall e, PE1_root e -> vmap g2 (dst g e) = dst g2' (emap g2 e)).
Proof.
  intros until son'.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 PE1_root PE1'_root [PRE_bij_root [PRE_si PRE_consi_root]]
         PV' PE' COPY DISJ.
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [COPY_son' [? [? COPY_bij]]]]]].
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
      rewrite Intersection_spec in H2; destruct H2 as [? ?].
      apply H4; clear H4; unfold Ensembles.In.
      exists (dst g e).
      split.
      + rewrite in_map_iff; eauto.
      + apply reachable_by_refl; auto.
    } Unfocus.
    replace (emap g2 e) with (emap g1 e).
    Focus 2. {
      rewrite guarded_pointwise_relation_spec in COPY_gpre.
      apply COPY_gpre.
      unfold Complement at 1, Ensembles.In.
      intro.
      pose proof weak_edge_prop_si
       (reachable_by g1 (dst g e0) (Intersection V P0 (Complement V PV1)))
        g g1 PRE_si.
      rewrite Same_set_spec in H3.
      rewrite <- (H3 e) in H2; clear H3.
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
    pose proof pregraph_join_guarded_si _ _ _ _ H.
    rewrite guarded_si_spec in H2.
    assert (Complement E' PE' (emap g1 e)).
    Focus 1. {
      destruct DISJ.
      rewrite Disjoint_spec in H4.
      refine (H4 (emap g1 e) _).
      apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 PRE_bij_root)))))); auto.
    } Unfocus.
    assert (evalid g1' (emap g1 e)).
    Focus 1. {
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PRE_bij_root)))))))).
      specialize (H4 _ H1).
      rewrite <- H4.
      assert (In e es) by (rewrite H_ES; rewrite in_app_iff; tauto).
      rewrite H_OUT_EDGES in H5.
      destruct H5 as [? _].
      rewrite <- (proj1 (proj2 PRE_si)); auto.
    } Unfocus.
    assert (evalid g2' (emap g1 e))
      by (rewrite (proj1 (proj2 H2)) in H4; auto).
    apply (proj2 (proj2 (proj2 H2))); auto.
Qed.

Lemma triple6_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later son',
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  g ~=~ g1 /\
  guarded_pointwise_relation (Complement V (reachable_by g root P)) eq (vmap g) (vmap g1) ->
  forall PV' PE',
  copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) son' PV' PE' (g1, g1') (g2, g2') ->
  guarded_pointwise_relation (Complement V (reachable_by g root P)) eq (vmap g) (vmap g2).
Proof.
  intros until son'.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 [PRE_si PRE_gpr] PV' PE' COPY.
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [COPY_son' [? [? COPY_bij]]]]]].
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

Lemma triple7_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root es es_done e0 es_later son',
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
  forall PV' PE',
  copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) son' PV' PE' (g1, g1') (g2, g2') ->
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g2).
Proof.
  intros until son'.
  intros PV PE H_VVALID H_P P0 H_OUT_EDGES H_ES PV1 [PRE_si PRE_gpr] PV' PE' COPY.
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [COPY_son' [? [? COPY_bij]]]]]].
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

Lemma triple1_aux1_ecopy: forall (g: Graph) (P: V -> Prop) root es es_done e0 es_later,
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

Lemma triple1_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later e0',
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  forall PV2' PE2',
  guarded_bij PV2 PE2 PV2' PE2' (vmap g2) (emap g2) g g2' /\
  g ~=~ g2 ->
  ecopy1 e0 e0' (g2, g2') (g3, g3') ->
  guarded_bij PV2 PE2 PV2' PE2' (vmap g3) (emap g3) g g3'.
Proof.
  intros until e0'.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV2 PE2 PV2' PE2' [PRE_bij PRE_si]
         ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? [? ?]]]]]]]]. 

  eapply guarded_bij_proper_aux1; [.. | exact PRE_bij].
  + apply guarded_pointwise_relation_pointwise_relation; auto.
  + eapply guarded_pointwise_relation_weaken; [| apply ECOPY_gpre].
    eapply triple1_aux1_ecopy; eauto.
  + reflexivity.
  + apply edge_union_guarded_si in H1.
    eapply guarded_si_weaken; [apply Included_Full_set | | exact H1].
    unfold Included, Complement, Ensembles.In; intros e' ?.
    pose proof (proj1 (proj2 (proj2 (proj2 PRE_bij)))).
    specialize (H5 _ H4).
    destruct H5 as [e [? ?]].
    specialize (H0 e).
    rewrite H6 in H0; auto.
Qed.

Lemma triple2_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later e0',
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  g ~=~ g2 ->
  ecopy1 e0 e0' (g2, g2') (g3, g3') ->
  g ~=~ g3.
Proof.
  intros until e0'.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV2 PE2 PRE_si ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? [? ?]]]]]]]]. 
  rewrite PRE_si; auto.
Qed.

Lemma triple3_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later e0',
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV2 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  forall PV2' PE2',
  guarded_bij PV2 PE2 PV2' PE2' (vmap g2) (emap g2) g g2' /\
  g ~=~ g2 /\
  (forall e, PE2 e -> ~ PV2 (dst g e) -> vmap g2 (dst g e) = dst g2' (emap g2 e)) ->
  ecopy1 e0 e0' (g2, g2') (g3, g3') ->
  (forall e, PE2 e -> ~ PV2 (dst g e) -> vmap g3 (dst g e) = dst g3' (emap g3 e)).
Proof.
  intros until e0'.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PV2 PE2 PV2' PE2' [PRE_bij [PRE_si PRE_disj]]
         ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? [? ?]]]]]]]]. 

  intros.
  replace (vmap g3 (dst g e)) with (vmap g2 (dst g e)) by (apply ECOPY_prv).
  replace (emap g3 e) with (emap g2 e).
  Focus 2. {
    rewrite guarded_pointwise_relation_spec in ECOPY_gpre.
    apply ECOPY_gpre.
    exact (triple1_aux1_ecopy g P root _ _ _ _ H_VVALID H_P H_OUT_EDGES H_ES e H4).
  } Unfocus.
  replace (dst g3' (emap g2 e)) with (dst g2' (emap g2 e)).
  Focus 2. {
    assert (evalid g2' (emap g2 e)).
    Focus 1. {
      rewrite <- (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PRE_bij)))))))) by auto.
      unfold PE2 in H4; rewrite Intersection_spec in H4.
      tauto.
    } Unfocus.
    assert (evalid g3' (emap g2 e)).
    Focus 1. {
      apply edge_union_guarded_si in H1.
      rewrite guarded_si_spec in H1.
      destruct H1 as [_ [? _]].
      rewrite <- H1; [auto |].
      apply H0.
    } Unfocus.
    apply edge_union_guarded_si in H1.
    rewrite guarded_si_spec in H1.
    destruct H1 as [_ [_ [_ ?]]].
    apply H1; auto.
    apply H0.
  } Unfocus.
  apply PRE_disj; auto.
Qed.

Lemma triple4_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later root' e0',
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  let PV2 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE2_root e := In e es_done in
  forall PE2'_root,
  guarded_bij (eq root) PE2_root (eq root') PE2'_root (vmap g2) (emap g2) g2 g2' /\
  g ~=~ g2 ->
  ecopy1 e0 e0' (g2, g2') (g3, g3') ->
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE3_root e := In e (es_done ++ e0 :: nil) in
  let PE3'_root := Union _ PE2'_root (eq e0') in
  guarded_bij (eq root) PE3_root (eq root') PE3'_root (vmap g3) (emap g3) g3 g3'.
Proof.
  intros until e0'.
  intros H_VVALID H_P P0 H_OUT_EDGES H_NODUP H_ES PV2 PE2_root PE2'_root [PRE_bij_root PRE_si] ECOPY PV3 PE3_root PE3'_root.
  destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? [? ?]]]]]]]].
  rewrite <- (Union_Empty_set (eq root)).
  rewrite <- (Union_Empty_set (eq root')).
  assert (Same_set PE3_root (Union _ PE2_root (eq e0))).
  Focus 1. {
    rewrite Same_set_spec; intros e; rewrite Union_spec.
    unfold PE3_root; rewrite in_app_iff; simpl; tauto.
  } Unfocus.
  rewrite H4; clear H4.
  eapply guarded_bij_disjointed_union.
  + split.
    - apply Disjoint_Empty_set_right.
    - rewrite Disjoint_spec; intros e' ? ?.
      apply (proj1 (proj2 (proj2 (proj2 PRE_bij_root)))) in H4.
      destruct H4 as [e [? ?]].
      subst e'.
      revert H5; apply H0.
  + eapply guarded_bij_proper_aux1; [.. | exact PRE_bij_root].
    - apply guarded_pointwise_relation_pointwise_relation; auto.
    - eapply guarded_pointwise_relation_weaken; [| exact ECOPY_gpre].
      unfold Included, Complement, Ensembles.In; intros e ?.
      rewrite H_ES in H_NODUP.
      apply NoDup_app_not_in with (y := e) in H_NODUP; [| auto].
      simpl in H_NODUP; tauto.
    - apply si_guarded_si; auto.
    - apply edge_union_guarded_si in H1.
      eapply guarded_si_weaken; [apply Included_Full_set | | exact H1].
      unfold Included, Complement, Ensembles.In; intros e' ?.
      apply (proj1 (proj2 (proj2 (proj2 PRE_bij_root)))) in H4.
      destruct H4 as [e [? ?]].
      subst e'.
      apply H0.
  + split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]; intros.
    - inversion H4.
    - congruence.
    - inversion H4.
    - exists e0; split; [auto | congruence].
    - inversion H4.
    - subst e; congruence.
    - inversion H4.
    - subst e.
      assert (evalid g3 e0).
      Focus 1. {
        assert (In e0 es) by (rewrite H_ES, in_app_iff; simpl; tauto).
        rewrite H_OUT_EDGES in H4.
        destruct H4 as [? _].
        pose proof proj1 (proj2 PRE_si) e0.
        pose proof proj1 (proj2 ECOPY_si) e0.
        tauto.
      } Unfocus.
      assert (evalid g3' (emap g3 e0)).
      Focus 1. {
        rewrite <- H.
        destruct H1 as [_ [? _]].
        specialize (H1 e0').
        tauto.
      } Unfocus.
      tauto.
    - inversion H5.
    - inversion H5.
  + split; [| split; [| split]]; intros.
    - inversion H5.
    - subst e.
      rewrite <- H.
      auto.
    - inversion H5.
    - subst e.
      rewrite <- H.
      auto.
Qed.    

Lemma triple5_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (P: V -> Prop) root es es_done e0 es_later root' e0',
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  let PV2 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE2_root e := In e es_done in
  forall PE2'_root,
  guarded_bij (eq root) PE2_root (eq root') PE2'_root (vmap g2) (emap g2) g2 g2' /\
  g ~=~ g2 /\
  (forall e, PE2_root e -> vmap g2 (dst g e) = dst g2' (emap g2 e)) ->
  ecopy1 e0 e0' (g2, g2') (g3, g3') ->
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE3_root e := In e (es_done ++ e0 :: nil) in
  let PE3'_root := Union _ PE2'_root (eq e0') in
  (forall e, PE3_root e -> vmap g3 (dst g e) = dst g3' (emap g3 e)).
Proof.
  intros until e0'.
  intros H_VVALID H_P P0 H_OUT_EDGES H_NODUP H_ES PV2 PE2_root PE2'_root [PRE_bij_root [PRE_si PRE_consi_root]] ECOPY PV3 PE3_root PE3'_root.
  destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? [? ?]]]]]]]].
  intros.
  unfold PE3_root in H4; rewrite in_app_iff in H4.
  destruct H4.
  - specialize (PRE_consi_root _ H4).
    replace (vmap g3 (dst g e)) with (vmap g2 (dst g e)) by (apply ECOPY_prv).
    replace (emap g3 e) with (emap g2 e).
    Focus 2. {
      rewrite guarded_pointwise_relation_spec in ECOPY_gpre.
      apply ECOPY_gpre.
      unfold Complement, Ensembles.In; intros ?.
      rewrite H_ES in H_NODUP.
      apply NoDup_app_not_in with (y := e) in H_NODUP; [| auto].
      simpl in H_NODUP; tauto.
    } Unfocus.
    replace (dst g3' (emap g2 e)) with (dst g2' (emap g2 e)).
    Focus 2. {
      assert (evalid g2' (emap g2 e)).
      Focus 1. {
        rewrite <- (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 PRE_bij_root)))))))) by auto.
        assert (In e es) by (rewrite H_ES, in_app_iff; tauto).
        rewrite H_OUT_EDGES in H5.
        destruct H5 as [? _].
        pose proof proj1 (proj2 ECOPY_si) e.
        pose proof proj1 (proj2 PRE_si) e.
        tauto.
      } Unfocus.
      assert (evalid g3' (emap g2 e)).
      Focus 1. {
        apply edge_union_guarded_si in H1.
        rewrite guarded_si_spec in H1.
        destruct H1 as [_ [? _]].
        rewrite <- H1; [auto |].
        apply H0.
      } Unfocus.
      apply edge_union_guarded_si in H1.
      rewrite guarded_si_spec in H1.
      destruct H1 as [_ [_ [_ ?]]].
      apply H1; auto.
      apply H0.
    } Unfocus.
    auto.
  - destruct H4; [subst e | inv H4].
    rewrite <- H.
    replace (dst g e0) with (dst g3 e0); auto.
    rewrite <- PRE_si in ECOPY_si.
    assert (In e0 es) by (rewrite H_ES, in_app_iff; simpl; tauto).
    rewrite H_OUT_EDGES in H4.
    destruct H4 as [? _].
    pose proof proj1 (proj2 ECOPY_si) e0.
    pose proof proj2 (proj2 (proj2 ECOPY_si)) e0.
    symmetry; tauto.
Qed.

Lemma triple_loop: forall (g g1 g3: Graph) (g1' g3': Graph') (P: V -> Prop) root es es_done e0 es_later root',
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  forall PV1' PE1' PE1'_root,
  guarded_bij PV1 PE1 PV1' PE1' (vmap g1) (emap g1) g g1' /\
  g ~=~ g1 /\
  (forall e, PE1 e -> ~ PV1 (dst g e) -> vmap g1 (dst g e) = dst g1' (emap g1 e)) /\
  guarded_bij (eq root) PE1_root (eq root') PE1'_root (vmap g1) (emap g1) g1 g1' /\
  (forall e, PE1_root e -> vmap g1 (dst g e) = dst g1' (emap g1 e)) ->
  forall PV' PE' son' e0',
  compond_relation
    (copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) son' PV' PE')
    (ecopy1 e0 e0')
    (g1, g1') (g3, g3') /\
  disjointed_guard (Union _ PV1' (eq root')) PV' (Union _ PE1' PE1'_root) PE' /\ (* From spatial fact *)
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _) -> (* From weak mark lemma *)
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) P0 in
  let PE3 := Intersection _ (weak_edge_prop PV3 g) (evalid g) in
  let PE3_root e := In e (es_done ++ e0 :: nil) in
  let PV3' := Union _ PV1' PV' in
  let PE3' := Union _ PE1' PE' in
  let PE3'_root := Union _ PE1'_root (eq e0') in
  guarded_bij PV3 PE3 PV3' PE3' (vmap g3) (emap g3) g g3' /\
  g ~=~ g3 /\
  (forall e, PE3 e -> ~ PV3 (dst g e) -> vmap g3 (dst g e) = dst g3' (emap g3 e)) /\
  guarded_bij (eq root) PE3_root (eq root') PE3'_root (vmap g3) (emap g3) g3 g3' /\
  (forall e, PE3_root e -> vmap g3 (dst g e) = dst g3' (emap g3 e)).
Proof.
  intros.
  destruct H5 as [? [DISJ DEC]].
  apply disjointed_guard_left_union in DISJ.
  destruct DISJ as [DISJ DISJ_root].
  apply compond_relation_spec in H5.
  destruct H5 as [[g2 g2'] [COPY ECOPY]].
  assert
   (guarded_bij PV3 PE3 PV3' PE3' (vmap g2) (emap g2) g g2' /\
    g ~=~ g2 /\
    (forall e : E,
     PE3 e -> ~ PV3 (dst g e) -> vmap g2 (dst g e) = dst g2' (emap g2 e)) /\
    guarded_bij (eq root) PE1_root (eq root') PE1'_root 
      (vmap g2) (emap g2) g2 g2' /\
    (forall e : E,
     PE1_root e ->
     vmap g2 (dst g e) = dst g2' (emap g2 e))) as PRE;
  [clear g3 g3' ECOPY; rename H4 into PRE | clear COPY H4].
  + split; [| split; [| split; [| split]]].
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
  + split; [| split; [| split; [| split]]].
    - eapply triple1_ecopy1; eauto.
      tauto.
    - eapply triple2_ecopy1; eauto.
      tauto.
    - eapply triple3_ecopy1; eauto.
      instantiate (1 := PE3').
      instantiate (1 := PV3').
      tauto.
    - eapply triple4_ecopy1; eauto.
      tauto.
    - eapply triple5_ecopy1; eauto.
      instantiate (1 := PE1'_root).
      instantiate (1 := root').
      tauto.
Qed.

Lemma triple_final: forall (g g1: Graph) (g' g1': Graph') (P: V -> Prop) root es root',
  vvalid g root ->
  P root ->
  let P0 := Intersection _ P (Complement _ (eq root)) in
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  let PV1 := reachable_by_through_set g (map (dst g) es) P0 in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es in
  forall PV1' PE1' PE1'_root,
  guarded_bij PV1 PE1 PV1' PE1' (vmap g1) (emap g1) g g1' /\
  g ~=~ g1 /\
  (forall e, PE1 e -> ~ PV1 (dst g e) -> vmap g1 (dst g e) = dst g1' (emap g1 e)) /\
  guarded_bij (eq root) PE1_root (eq root') PE1'_root (vmap g1) (emap g1) g1 g1' /\
  (forall e, PE1_root e -> vmap g1 (dst g e) = dst g1' (emap g1 e)) ->
  copy P root root' (Union _ PV1' (eq root')) (Union _ PE1' PE1'_root) (g, g') (g1, g1').
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
  destruct H3 as [? [? [? [? ?]]]].
  unfold copy.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  + auto.
  + admit.
  + admit.
  + admit.
  + admit.
  + intros.
    rewrite Intersection_spec in H9.
    destruct H9.
    unfold weak_edge_prop in H9.
    rewrite reachable_by_ind_equiv in H9 by eauto.
    destruct H9.
    - apply H8.
      unfold PE1_root.
      rewrite H1.
      split; auto.
    - apply H6.
      unfold PE1.
      rewrite Intersection_spec; auto.
      unfold PV1.
      intro; apply H10; clear H10.
      rewrite reachable_by_ind_equiv by eauto.
      right.
      auto.
  + assert (Same_set (reachable_by g root P) (Union _ PV1 (eq root))).
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
    rewrite H10, H9; clear H9 H10.
    eapply guarded_bij_proper_aux1.
    1: reflexivity.
    1: reflexivity.
    1: apply si_guarded_si; eauto.
    1: reflexivity.
    apply guarded_bij_disjointed_union; auto.
    - admit.
    - auto. admit.
    - split; [| split; [| split]].
      * intros.
        exfalso.
        unfold PE1 in H9.
        rewrite Intersection_spec in H9.
        destruct H9 as [? _]; unfold weak_edge_prop, PV1 in H9.
        apply reachable_by_through_set_foot_prop in H9.
        unfold P0 in H9.
        rewrite Intersection_spec in H9.
        unfold Complement, Ensembles.In in H9.
        tauto.
      * intros.
        exfalso.
        unfold PE1_root in H9.
        rewrite H1 in H9; destruct H9.
        symmetry in H12.
        unfold PV1 in H10.
        apply reachable_by_through_set_foot_prop in H10.
        unfold P0 in H10.
        rewrite Intersection_spec in H10.
        unfold Complement, Ensembles.In in H10.
        tauto.
      * intros; apply H6; auto.
        intro.
        unfold PV1 in H12.
        apply reachable_by_through_set_foot_prop in H12.
        unfold P0 in H12.
        rewrite Intersection_spec in H12.
        unfold Complement, Ensembles.In in H12.
        tauto.
      * intros; apply H8; auto.
Qed.

End LocalCopyGraph.

End LocalCopyGraph.
