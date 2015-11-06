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

Variables (PV: V -> Prop) (PE: E -> Prop) (PV': V' -> Prop) (PE': E' -> Prop) (vmap: V -> V') (emap: E -> E') (G: PreGraph V E) (G': PreGraph V' E').

Definition guarded_morphism: Prop :=
  (forall v, PV v -> PV' (vmap v)) /\
  (forall e, PE e -> PE' (emap e)) /\
  (forall v, PV v -> (vvalid G v <-> vvalid G' (vmap v))) /\
  (forall e, PE e -> (evalid G e <-> evalid G' (emap e))) /\
  (forall e, PE e -> PV (src G e) -> evalid G e -> vmap (src G e) = src G' (emap e)) /\
  (forall e, PE e -> PV (dst G e) -> evalid G e -> vmap (dst G e) = dst G' (emap e)).

Definition guarded_inj: Prop :=
  (forall v1 v2, PV v1 -> PV v2 -> v1 <> v2 -> vmap v1 <> vmap v2) /\
  (forall e1 e2, PE e1 -> PE e2 -> e1 <> e2 -> emap e1 <> emap e2) /\
  guarded_morphism.

Definition guarded_surj: Prop :=
  (forall v', PV' v' -> exists v, PV v /\ vmap v = v') /\
  (forall e', PE' e' -> exists e, PE e /\ emap e = e') /\
  guarded_morphism.

Definition guarded_bij: Prop :=
  (forall v1 v2, PV v1 -> PV v2 -> v1 <> v2 -> vmap v1 <> vmap v2) /\
  (forall e1 e2, PE e1 -> PE e2 -> e1 <> e2 -> emap e1 <> emap e2) /\
  (forall v', PV' v' -> exists v, PV v /\ vmap v = v') /\
  (forall e', PE' e' -> exists e, PE e /\ emap e = e') /\
  guarded_morphism.

Lemma guarded_bij_surj: guarded_bij -> guarded_surj.
Proof.
  unfold guarded_bij, guarded_surj.
  tauto.
Qed.

Lemma guarded_bij_inj: guarded_bij -> guarded_inj.
Proof.
  unfold guarded_bij, guarded_inj.
  tauto.
Qed.

Lemma guarded_surj_evalid:
  guarded_surj ->
  Included PE (evalid G) ->
  Included PE' (evalid G').
Proof.
  intros [? [? [? [? [? [? [? ?]]]]]]] ?.
  eapply guarded_surj_Included; [eauto |].
  intros e ?.
  pose proof H7 _ H8; unfold Ensembles.In in H9; clear H7.
  rewrite <- H4 by auto.
  auto.
Qed.

Lemma guarded_surj_weak_edge_prop:
  guarded_surj ->
  Included PE (weak_edge_prop PV G) ->
  Included PE (evalid G) ->
  Included PE' (weak_edge_prop PV' G').
Proof.
  intros [? [? [? [? [? [? [? ?]]]]]]] ? ?.
  eapply guarded_surj_Included; [eauto |].
  intros e ?.
  pose proof H7 _ H9; unfold Ensembles.In in H10; clear H7.
  pose proof H8 _ H9; unfold Ensembles.In in H7; clear H8.
  unfold weak_edge_prop in *.
  rewrite <- H5 by auto.
  apply H1, H10.
Qed.

Lemma guarded_surj_weak'_edge_prop:
  guarded_surj ->
  Included PE (weak'_edge_prop PV G) ->
  Included PE (evalid G) ->
  Included PE' (weak'_edge_prop PV' G').
Proof.
  intros [? [? [? [? [? [? [? ?]]]]]]] ? ?.
  eapply guarded_surj_Included; [eauto |].
  intros e ?.
  pose proof H7 _ H9; unfold Ensembles.In in H10; clear H7.
  pose proof H8 _ H9; unfold Ensembles.In in H7; clear H8.
  unfold weak'_edge_prop in *.
  rewrite <- H6 by auto.
  apply H1, H10.
Qed.

End GraphMorphism0.

Section GraphMorphism1.

Context {V V' E E': Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {EV': EqDec V' eq}.
Context {EE': EqDec E' eq}.

Lemma guarded_morphism_proper_aux1: forall PV PE PV' PE' vmap1 vmap2 emap1 emap2 (G1 G2: PreGraph V E) (G1' G2': PreGraph V' E'),
  guarded_pointwise_relation PV eq vmap1 vmap2 ->
  guarded_pointwise_relation PE eq emap1 emap2 ->
  guarded_structurally_identical PV PE G1 G2 ->
  guarded_structurally_identical PV' PE' G1' G2' ->
  guarded_morphism PV PE PV' PE' vmap1 emap1 G1 G1' ->
  guarded_morphism PV PE PV' PE' vmap2 emap2 G2 G2'.
Proof.
  unfold guarded_morphism.
  intros.
  rewrite guarded_pointwise_relation_spec in H.
  rewrite guarded_pointwise_relation_spec in H0.
  destruct H3 as [? [? [? [? [? ?]]]]].
  destruct (proj1 (guarded_si_spec _ _ _ _) H1) as [? [? [? ?]]].
  destruct (proj1 (guarded_si_spec _ _ _ _) H2) as [? [? [? ?]]].
  assert (forall v : V, PV v -> PV' (vmap2 v))
    by (intros; rewrite <- H by auto; apply H3; auto).
  assert (forall e : E, PE e -> PE' (emap2 e))
    by (intros; rewrite <- H0 by auto; apply H4; auto).
  assert (forall v : V, PV v -> (vvalid G2 v <-> vvalid G2' (vmap2 v))).
  Focus 1. {
    intros.
    rewrite <- H9 by auto.
    rewrite <- H by auto.
    rewrite <- H13 by auto.
    apply H5; auto.
  } Unfocus.
  assert (forall e : E, PE e -> (evalid G2 e <-> evalid G2' (emap2 e))).
  Focus 1. {
    intros.
    rewrite <- H10 by auto.
    rewrite <- H0 by auto.
    rewrite <- H14 by auto.
    apply H6; auto.
  } Unfocus.
  split; [| split; [| split; [| split; [| split]]]]; auto; intros.
  + assert (evalid G1 e) by (rewrite H10 by auto; auto).
    rewrite <- H15.
    2: apply H18; auto.
    2: rewrite <- H0, <- H6, H10 by auto; auto.
    2: rewrite <- H20 by auto; auto.
    rewrite <- H0 by auto.
    rewrite <- H by auto.
    rewrite <- H11 by auto.
    apply H7; auto.
    rewrite H11 by auto; auto.
  + assert (evalid G1 e) by (rewrite H10 by auto; auto).
    rewrite <- H16.
    2: apply H18; auto.
    2: rewrite <- H0, <- H6, H10 by auto; auto.
    2: rewrite <- H20 by auto; auto.
    rewrite <- H0 by auto.
    rewrite <- H by auto.
    rewrite <- H12 by auto.
    apply H8; auto.
    rewrite H12 by auto; auto.
Qed.

Lemma guarded_morphism_proper_aux2: forall PV1 PV2 PE1 PE2 PV1' PV2' PE1' PE2' vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  Same_set PV1 PV2 ->
  Same_set PE1 PE2 ->
  Same_set PV1' PV2' ->
  Same_set PE1' PE2' ->
  guarded_morphism PV1 PE1 PV1' PE1' vmap emap G G' ->
  guarded_morphism PV2 PE2 PV2' PE2' vmap emap G G'.
Proof.
  intros.
  rewrite Same_set_spec in *.
  destruct H3 as [? [? [? [? [? ?]]]]].
  split; [| split; [| split; [| split; [| split]]]]; intros.
  + apply H1; apply H in H9; auto.
  + apply H2; apply H0 in H9; auto.
  + apply H in H9; auto.
  + apply H0 in H9; auto.
  + apply H in H10; apply H0 in H9; auto.
  + apply H in H10; apply H0 in H9; auto.
Qed.

Lemma guarded_bij_proper_aux1: forall PV PE PV' PE' vmap1 vmap2 emap1 emap2 (G1 G2: PreGraph V E) (G1' G2': PreGraph V' E'),
  guarded_pointwise_relation PV eq vmap1 vmap2 ->
  guarded_pointwise_relation PE eq emap1 emap2 ->
  guarded_structurally_identical PV PE G1 G2 ->
  guarded_structurally_identical PV' PE' G1' G2' ->
  guarded_bij PV PE PV' PE' vmap1 emap1 G1 G1' ->
  guarded_bij PV PE PV' PE' vmap2 emap2 G2 G2'.
Proof.
  unfold guarded_bij.
  intros.
  assert (guarded_morphism PV PE PV' PE' vmap2 emap2 G2 G2') by (eapply guarded_morphism_proper_aux1; eauto; tauto).
  rewrite guarded_pointwise_relation_spec in H.
  rewrite guarded_pointwise_relation_spec in H0.
  destruct H3 as [? [? [? [? _]]]].
  split; [| split; [| split; [| split]]]; intros.
  + rewrite <- !H by auto.
    apply H3; auto.
  + rewrite <- !H0 by auto.
    apply H5; auto.
  + apply H6 in H8.
    destruct H8 as [v [? ?]]; exists v.
    rewrite <- H by auto; auto.
  + apply H7 in H8.
    destruct H8 as [e [? ?]]; exists e.
    rewrite <- H0 by auto; auto.
  + auto.
Qed.

Lemma guarded_bij_proper_aux2: forall PV1 PV2 PE1 PE2 PV1' PV2' PE1' PE2' vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  Same_set PV1 PV2 ->
  Same_set PE1 PE2 ->
  Same_set PV1' PV2' ->
  Same_set PE1' PE2' ->
  guarded_bij PV1 PE1 PV1' PE1' vmap emap G G' ->
  guarded_bij PV2 PE2 PV2' PE2' vmap emap G G'.
Proof.
  intros.
  destruct H3 as [? [? [? [? HH]]]].
  assert (HH': guarded_morphism PV2 PE2 PV2' PE2' vmap emap G G') by (eapply guarded_morphism_proper_aux2; eauto).
  rewrite Same_set_spec in *.
  split; [| split; [| split; [| split]]]; intros.
  + apply H in H7; apply H in H8; auto.
  + apply H0 in H7; apply H0 in H8; auto.
  + apply H1, H5 in H7.
    destruct H7 as [v [? ?]]; exists v.
    apply H in H7; auto.
  + apply H2, H6 in H7.
    destruct H7 as [e [? ?]]; exists e.
    apply H0 in H7; auto.
  + auto.
Qed.

Instance guarded_morphism_proper1 (PV: V -> Prop) (PE: E -> Prop) (PV': V' -> Prop) (PE': E' -> Prop): Proper (guarded_pointwise_relation PV eq ==> guarded_pointwise_relation PE eq ==> guarded_structurally_identical PV PE ==> guarded_structurally_identical PV' PE' ==> iff) (guarded_morphism PV PE PV' PE').
Proof.
  intros.
  do 4 (hnf; intros).
  split; apply guarded_morphism_proper_aux1; auto; symmetry; auto.
Defined.
Global Existing Instance guarded_morphism_proper1.

Instance guarded_morphism_proper2: Proper (@Same_set V ==> @Same_set E==> @Same_set V' ==> @Same_set E' ==> eq ==> eq ==> eq ==> eq ==> iff) guarded_morphism.
Proof.
  intros.
  do 8 (hnf; intros).
  subst.
  split; eapply guarded_morphism_proper_aux2; eauto; symmetry; auto.
Defined.
Global Existing Instance guarded_morphism_proper2.

Instance guarded_bij_proper1 (PV: V -> Prop) (PE: E -> Prop) (PV': V' -> Prop) (PE': E' -> Prop): Proper (guarded_pointwise_relation PV eq ==> guarded_pointwise_relation PE eq ==> guarded_structurally_identical PV PE ==> guarded_structurally_identical PV' PE' ==> iff) (guarded_bij PV PE PV' PE').
Proof.
  intros.
  do 4 (hnf; intros).
  split; apply guarded_bij_proper_aux1; auto; symmetry; auto.
Defined.
Global Existing Instance guarded_bij_proper1.

Instance guarded_bij_proper2: Proper (@Same_set V ==> @Same_set E==> @Same_set V' ==> @Same_set E' ==> eq ==> eq ==> eq ==> eq ==> iff) guarded_bij.
Proof.
  intros.
  do 8 (hnf; intros).
  subst.
  split; eapply guarded_bij_proper_aux2; eauto; symmetry; auto.
Qed.
Global Existing Instance guarded_bij_proper2.

End GraphMorphism1.

Definition disjointed_guard {V E} (PV1 PV2: V -> Prop) (PE1 PE2: E -> Prop) :=
  Disjoint _ PV1 PV2 /\ Disjoint _ PE1 PE2.

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

Lemma guarded_morphism_disjointed_union: forall PV1 PE1 PV1' PE1' PV2 PE2 PV2' PE2' vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  guarded_morphism PV1 PE1 PV1' PE1' vmap emap G G' ->
  guarded_morphism PV2 PE2 PV2' PE2' vmap emap G G' ->
  boundary_consistent PV1 PV2 PE1 PE2 vmap emap G G' ->
  guarded_morphism (Union _ PV1 PV2) (Union _ PE1 PE2)
    (Union _ PV1' PV2') (Union _ PE1' PE2') vmap emap G G'.
Proof.
  intros.
  destruct H as [? [? [? [? [? ?]]]]], H0 as [? [? [? [? [? ?]]]]], H1 as [? [? [? ?]]].
  split; [| split; [| split; [| split; [| split]]]]; intros.
  + rewrite Union_spec in *.
    destruct H15; [left | right]; auto.
  + rewrite Union_spec in *.
    destruct H15; [left | right]; auto.
  + rewrite Union_spec in H15.
    destruct H15; auto.
  + rewrite Union_spec in H15.
    destruct H15; auto.
  + rewrite Union_spec in *.
    destruct H15, H16; auto.
  + rewrite Union_spec in *.
    destruct H15, H16; auto.
Qed.

Lemma guarded_bij_disjointed_union: forall PV1 PE1 PV1' PE1' PV2 PE2 PV2' PE2' vmap emap (G: PreGraph V E) (G': PreGraph V' E'),
  disjointed_guard PV1' PV2' PE1' PE2' ->
  guarded_bij PV1 PE1 PV1' PE1' vmap emap G G' ->
  guarded_bij PV2 PE2 PV2' PE2' vmap emap G G' ->
  boundary_consistent PV1 PV2 PE1 PE2 vmap emap G G' ->
  guarded_bij (Union _ PV1 PV2) (Union _ PE1 PE2)
    (Union _ PV1' PV2') (Union _ PE1' PE2') vmap emap G G'.
Proof.
  intros.
  assert (HH: guarded_morphism (Union V PV1 PV2) (Union E PE1 PE2) 
               (Union V' PV1' PV2') (Union E' PE1' PE2') vmap emap G G')
  by (apply guarded_morphism_disjointed_union; destruct H0, H1; tauto).
  destruct H as [? ?], H0 as [? [? [? [? ?]]]], H1 as [? [? [? [? ?]]]], H2 as [? [? [? ?]]].
  rewrite Disjoint_spec in H, H3.
  split; [| split; [| split; [| split]]]; intros.
  + rewrite Union_spec in *.
    destruct H7 as [? _], H11 as [? _].
    destruct H15, H16; auto.
    - apply H7 in H15.
      apply H11 in H16.
      intro.
      rewrite H18 in H15; eapply H; eauto.
    - apply H11 in H15.
      apply H7 in H16.
      intro.
      rewrite H18 in H15; eapply H; eauto.
  + rewrite Union_spec in *.
    destruct H7 as [_ [? _]], H11 as [_ [? _]].
    destruct H15, H16; auto.
    - apply H7 in H15.
      apply H11 in H16.
      intro.
      rewrite H18 in H15; eapply H3; eauto.
    - apply H11 in H15.
      apply H7 in H16.
      intro.
      rewrite H18 in H15; eapply H3; eauto.
  + rewrite Union_spec in H15.
    destruct H15; [apply H5 in H15 | apply H9 in H15];
    destruct H15 as [v [? ?]]; exists v;
    rewrite Union_spec; auto.
  + rewrite Union_spec in H15.
    destruct H15; [apply H6 in H15 | apply H10 in H15];
    destruct H15 as [v [? ?]]; exists v;
    rewrite Union_spec; auto.
  + auto.
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

Definition vcopy1 (P: V -> Prop) root root' (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  let PV := (Intersection _ (reachable g1 root) (Complement _ (reachable_by g1 root P))) in
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ (eq root)) eq (vmap g1) (vmap g2) /\
  pointwise_relation _ eq (emap g1) (emap g2) /\
  root' = vmap g2 root /\
  (forall x, PV x -> root' <> vmap g1 x) /\
  vertex_join (eq root') g1' g2'.

Lemma triple_vcopy1: forall (g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root root',
  let PV := (Intersection _ (reachable g1 root) (Complement _ (reachable_by g1 root P))) in
  forall PE PV' PE',
  P root ->
  vvalid g1 root ->
  vcopy1 P root root' (g1, g1') (g2, g2') ->
  Included PE (weak_edge_prop PV g1) ->
  Included PE (evalid g1) ->
  Disjoint _ PE (weak'_edge_prop P g1) ->
  guarded_bij PV PE PV' PE' (vmap g1) (emap g1) g1 g1' ->
  guarded_bij (Union _ PV (eq root)) PE (Union _ PV' (eq root')) PE' (vmap g2) (emap g2) g2 g2'.
Proof.
  intros g1 g2 g1' g2' P root root' PV PE PV' PE'
         ? ? [? [? [? [? [? ?]]]]] ? ? ? ?.
  rewrite <- (Union_Empty_set PE'), <- (Union_Empty_set PE).
  assert (Disjoint V' PV' (eq root')).
  Focus 1. {
    apply (guarded_surj_Disjoint (vmap g1) PV); auto.
    destruct H10 as [_ [_ [? _]]]; auto.
  } Unfocus.
  assert (Included PV (Complement V (eq root))).
  Focus 1. {
    apply Intersection2_Included, Complement_Included_rev.
    hnf; unfold Ensembles.In; intros; subst x.
    apply reachable_by_refl; auto.
  } Unfocus.
  assert (Disjoint E' PE' (weak_edge_prop (eq root') g2')).
  Focus 1. {
    eapply Included_Disjoint; [| apply Included_refl |].
    2: apply vertex_join_DisjointE; eauto.
    eapply (guarded_surj_evalid _ _ _ _ _ _ _ _ (guarded_bij_surj _ _ _ _ _ _ _ _ H10)).
    auto.
  } Unfocus.
  apply guarded_bij_disjointed_union.
  + split; auto.
    apply Disjoint_Empty_set_right.
  + eapply guarded_bij_proper_aux1; [.. | exact H10].
    - eapply guarded_pointwise_relation_weaken; eauto.
    - apply guarded_pointwise_relation_pointwise_relation; auto.
    - apply si_guarded_si; auto.
    - eapply guarded_si_weaken; [| | apply vertex_join_guarded_si; eauto];
      apply Included_Complement_Disjoint; auto.
  + split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]; intros.
    - congruence.
    - inversion H14.
    - exists root; subst; auto.
    - inversion H14.
    - subst v; auto.
    - inversion H14.
    - subst v.
      destruct H6 as [[HH _ ] _].
      specialize (HH (vmap g2 root)).
      rewrite (proj1 H1) in H0.
      tauto.
    - inversion H14.
    - inversion H14.
    - inversion H14.
  + split; [| split; [| split]]; intros.
    - apply H7 in H14.
      unfold weak_edge_prop, Ensembles.In in H14.
      assert (evalid g1 e) by (rewrite (proj1 (proj2 H1)); auto).
      rewrite <- (proj1 (proj2 (proj2 H1))) in H15 by auto.
      rewrite <- H15 in H14.
      unfold PV in H14; rewrite Intersection_spec in H14.
      destruct H14 as [_ ?]; exfalso; apply H14.
      apply reachable_by_refl; auto.
    - inversion H14.
    - rewrite Disjoint_spec in H9.
      specialize (H9 _ H14).
      unfold weak'_edge_prop in H9.
      assert (evalid g1 e) by (rewrite (proj1 (proj2 H1)); auto).
      rewrite <- (proj2 (proj2 (proj2 H1))) in H15 by auto.
      rewrite <- H15 in H9.
      tauto.
    - inversion H14.
Qed.
      
End LocalCopyGraph.

End LocalCopyGraph.
