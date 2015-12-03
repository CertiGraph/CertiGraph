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

Definition vmap (g: Graph): V -> V' := fun v => co_vertex (vlabel g v).

Definition emap (g: Graph): E -> E' := fun e => co_edge (elabel g e).

Definition nothing (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  pointwise_relation V eq (vmap g1) (vmap g2) /\
  pointwise_relation E eq (emap g1) (emap g2) /\
  g1' ~=~ g2'.

Definition vcopy1 (P: V -> Prop) root (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ (eq root)) eq (vmap g1) (vmap g2) /\
  pointwise_relation _ eq (emap g1) (emap g2) /\
  vertex_join (eq (vmap g2 root)) g1' g2'.

Definition ecopy1 e (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  evalid g1 e /\
  pointwise_relation V eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ (eq e)) eq (emap g1) (emap g2) /\
  (forall e0, emap g2 e <> emap g1 e0) /\
  edge_union (eq (emap g2 e)) g1' g2' /\
  vmap g2 (src g2 e) = src g2' (emap g2 e) /\
  vmap g2 (dst g2 e) = dst g2' (emap g2 e).

Definition copy (P: V -> Prop) root(p1 p2: Graph * Graph') :=
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

Lemma triple_vcopy1: forall (g1 g2: Graph) (g1' g2': Graph') (P: V -> Prop) root,
  P root ->
  vvalid g1 root ->
  vcopy1 P root (g1, g1') (g2, g2') ->
  guarded_bij (eq root) (Empty_set _) (vmap g2) (emap g2) g2 g2'.
Proof.
  intros g1 g2 g1' g2' P root ? ? [? [? [? ?]]].
  split; [.. | split]; intros.
  + congruence.
  + inversion H5.
  + subst v.
    destruct H4 as [[HH _ ] _].
    specialize (HH (vmap g2 root)).
    rewrite (proj1 H1) in H0.
    tauto.
  + inversion H5.
  + inversion H5.
  + inversion H5.
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
    copy (Intersection _ P0 (Complement _ PV1)) son (g1, g1') (g2, g2') ->
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
  copy P_rec (dst g e0) (g1, g1') (g2, g2') ->
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
  copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) (g1, g1') (g2, g2') ->
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
  copy P_rec (dst g e0) (g1, g1') (g2, g2') ->
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
  copy P_rec (dst g e0) (g1, g1') (g2, g2') ->
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
  copy P_rec (dst g e0) (g1, g1') (g2, g2') ->
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
  copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) (g1, g1') (g2, g2') ->
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
  copy (Intersection _ P0 (Complement _ PV1)) (dst g e0) (g1, g1') (g2, g2') ->
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
  copy P_rec (dst g e0) (g1, g1') (g2, g2') ->
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
  destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]]]. 

  eapply guarded_bij_proper_aux1; [.. | eapply guarded_bij_proper_aux2; [.. |exact PRE_bij]].
  + reflexivity.
  + apply edge_union_guarded_si in H0.
    eapply guarded_si_weaken; [apply Included_Full_set | | exact H0].
    unfold Included, Complement, Ensembles.In; intros e' ?.
    rewrite image_set_spec in H3.
    destruct H3 as [e [? ?]].
    specialize (H e).
    rewrite guarded_pointwise_relation_spec in ECOPY_gpre.
    rewrite <- (ECOPY_gpre e) in H4; [congruence |].
    unfold Complement, Ensembles.In; intro.
    subst e.
    unfold PE2 in H3.
    rewrite Intersection_spec in H3.
    destruct H3 as [? _].
    unfold weak_edge_prop in H3.
    assert (In e0 es) by (rewrite H_ES, in_app_iff; simpl; tauto).
    rewrite H_OUT_EDGES in H5.
    destruct H5.
    rewrite H6 in H3.
    apply reachable_by_through_set_foot_prop in H3.
    unfold P0 in H3.
    rewrite Intersection_spec in H3.
    apply (proj2 H3); reflexivity.
  + apply guarded_pointwise_relation_pointwise_relation; auto.
  + eapply guarded_pointwise_relation_weaken; [| apply ECOPY_gpre].
    eapply triple1_aux1_ecopy; eauto.
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
  destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]]]. 
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
  destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]]]. 

  intros.
  replace (vmap g3 (dst g e)) with (vmap g2 (dst g e)) by (apply ECOPY_prv).
  replace (emap g3 e) with (emap g2 e).
  Focus 2. {
    rewrite guarded_pointwise_relation_spec in ECOPY_gpre.
    apply ECOPY_gpre.
    exact (triple1_aux1_ecopy g P root _ _ _ _ H_VVALID H_P H_OUT_EDGES H_ES e H3).
  } Unfocus.
  replace (dst g3' (emap g2 e)) with (dst g2' (emap g2 e)).
  Focus 2. {
    assert (evalid g2' (emap g2 e)).
    Focus 1. {
      rewrite <- (evalid_preserved PRE_bij) by auto.
      unfold PE2 in H3; rewrite Intersection_spec in H3.
      tauto.
    } Unfocus.
    assert (evalid g3' (emap g2 e)).
    Focus 1. {
      apply edge_union_guarded_si in H0.
      rewrite guarded_si_spec in H0.
      destruct H0 as [_ [? _]].
      rewrite <- H0; [auto |].
      apply H.
    } Unfocus.
    apply edge_union_guarded_si in H0.
    rewrite guarded_si_spec in H0.
    destruct H0 as [_ [_ [_ ?]]].
    apply H0; auto.
    apply H.
  } Unfocus.
  apply PRE_disj; auto.
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
  destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]]].
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
      rewrite <- H5 in H.
      specialize (H e).
      rewrite guarded_pointwise_relation_spec in ECOPY_gpre.
      rewrite ECOPY_gpre in H; [congruence |].
      unfold Complement, Ensembles.In; intro.
      subst e.
      unfold PE2_root in H3.
      rewrite H_ES in H_NODUP.
      apply NoDup_app_not_in with (y := e0) in H_NODUP; auto.
      simpl in H_NODUP; tauto.
  + eapply guarded_bij_proper_aux1; [.. | eapply guarded_bij_proper_aux2; [.. |exact PRE_bij_root]].
    - apply si_guarded_si; auto.
    - apply edge_union_guarded_si in H0.
      eapply guarded_si_weaken; [apply Included_Full_set | | exact H0].
      unfold Included, Complement, Ensembles.In; intros e' ?.
      rewrite image_set_spec in H3.
      destruct H3 as [e [? ?]].
      subst e'.
      rewrite guarded_pointwise_relation_spec in ECOPY_gpre.
      rewrite <- (ECOPY_gpre e); [apply H |].
      unfold Complement, Ensembles.In; intro.
      subst e.
      unfold PE2_root in H3.
      rewrite H_ES in H_NODUP.
      apply NoDup_app_not_in with (y := e0) in H_NODUP; auto.
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
        destruct H0 as [_ [? _]].
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
  destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]]].
  intros.
  unfold PE3_root in H3; rewrite in_app_iff in H3.
  destruct H3.
  - specialize (PRE_consi_root _ H3).
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
        rewrite <- (evalid_preserved PRE_bij_root) by auto.
        assert (In e es) by (rewrite H_ES, in_app_iff; tauto).
        rewrite H_OUT_EDGES in H4.
        destruct H4 as [? _].
        pose proof proj1 (proj2 ECOPY_si) e.
        pose proof proj1 (proj2 PRE_si) e.
        tauto.
      } Unfocus.
      assert (evalid g3' (emap g2 e)).
      Focus 1. {
        apply edge_union_guarded_si in H0.
        rewrite guarded_si_spec in H0.
        destruct H0 as [_ [? _]].
        rewrite <- H0; [auto |].
        apply H.
      } Unfocus.
      apply edge_union_guarded_si in H0.
      rewrite guarded_si_spec in H0.
      destruct H0 as [_ [_ [_ ?]]].
      apply H0; auto.
      apply H.
    } Unfocus.
    auto.
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
  destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]]].
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
  destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]]].
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

  destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]]].
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
        eapply triple1_aux1_ecopy; eauto.
      * apply image_set_proper_strong; symmetry.
        eapply guarded_pointwise_relation_weaken; [| apply ECOPY_gpre].
        unfold Included, Complement, Ensembles.In, PE2_root.
        intros e ? ?; subst e.
        rewrite H_ES in H_NODUP.
        apply NoDup_app_not_in with (y := e0) in H_NODUP; auto.
        simpl in H_NODUP; tauto.
    - rewrite Disjoint_spec; intros e' ? ?.
      rewrite image_set_spec in H3, H4.
      destruct H3 as [e [? ?]], H4 as [e1 [? ?]]; subst e1 e'.
      rewrite <- H6 in H; apply (H e); clear H H6.
      symmetry; rewrite guarded_pointwise_relation_spec in ECOPY_gpre.
      apply ECOPY_gpre.
      generalize e, H3.
      eapply triple1_aux1_ecopy; eauto.
Qed.

Lemma triple_loop: forall (g g1 g3: Graph) (g1' g3': Graph') (P: V -> Prop) root es es_done e0 es_later,
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
     (image_set (emap g1) PE1) (image_set (emap g1) PE1_root) ->
  let P_rec := Intersection _ P0 (Complement _ PV1) in
  let PV0 := reachable_by g (dst g e0) P_rec in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  compond_relation (copy P_rec (dst g e0)) (ecopy1 e0) (g1, g1') (g3, g3') /\
  disjointed_guard
     (Union _ (image_set (vmap g3) PV1) (image_set (vmap g3) (eq root))) (image_set (vmap g3) PV0)
     (Union _ (image_set (emap g3) PE1) (image_set (emap g3) PE1_root)) (image_set (emap g3) PE0) /\ (* From spatial fact *)
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _) -> (* From weak mark lemma *)
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
     (image_set (emap g3) PE3) (image_set (emap g3) PE3_root).
Proof.
  intros.
  destruct H5 as [? [DISJ DEC]].
  apply compond_relation_spec in H5.
  destruct H5 as [[g2 g2'] [COPY ECOPY]].

  assert (disjointed_guard
           (Union V' (image_set (vmap g2) PV1)
              (image_set (vmap g2) (eq root))) (image_set (vmap g2) PV0)
           (Union E' (image_set (emap g2) PE1) (image_set (emap g2) PE1_root))
           (image_set (emap g2) PE0)) as DISJ2.
  Focus 1. {
    destruct DISJ.
    destruct ECOPY as [ECOPY_si [ECOPY_valid [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]]]. 

    split.
    + eapply Disjoint_proper; [apply Union_proper | | exact H5];
      apply image_set_proper_strong;
      apply guarded_pointwise_relation_pointwise_relation; exact ECOPY_prv.
    + assert (src g e0 = root).
      Focus 1. {
        assert (In e0 es) by (rewrite H3; rewrite in_app_iff; simpl; tauto).
        rewrite H1 in H11.
        unfold out_edges in H11.
        tauto.
      } Unfocus.
      eapply Disjoint_proper; [apply Union_proper | | exact H6];
      apply image_set_proper_strong;
      (eapply guarded_pointwise_relation_weaken; [ | exact ECOPY_gpre]);
      unfold Included, Complement, Ensembles.In; intros; intro; subst x.
      - unfold PE1, weak_edge_prop in H12.
        rewrite Intersection_spec in H12.
        rewrite H11 in H12; destruct H12 as [? _].
        apply reachable_by_through_set_foot_prop in H12.
        unfold P0 in H12.
        rewrite Intersection_spec in H12.
        apply (proj2 H12), eq_refl.
      - rewrite H3 in H2.
        apply NoDup_app_not_in with (y := e0) in H2; auto.
        simpl in H2; tauto.
      - unfold PE0, weak_edge_prop in H12.
        rewrite Intersection_spec in H12.
        rewrite H11 in H12; destruct H12 as [? _].
        apply reachable_by_foot_prop in H12.
        unfold P0 in H12.
        unfold P_rec, P0 in H12; rewrite !Intersection_spec in H12.
        apply (proj2 (proj1 H12)), eq_refl.
  } Unfocus.
  apply disjointed_guard_left_union in DISJ2; clear DISJ.
  destruct DISJ2 as [DISJ DISJ_root].

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
     (image_set (emap g2) PE3) (image_set (emap g2) PE1_root)) as PRE;
  [clear g3 g3' ECOPY; rename H4 into PRE | clear COPY H4].
  + split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
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
  + split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
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
Qed.

Lemma triple_final: forall (g g1: Graph) (g' g1': Graph') (P: V -> Prop) root es,
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
  guarded_bij PV1 PE1 (vmap g1) (emap g1) g g1' /\
  g ~=~ g1 /\
  (forall e, PE1 e -> ~ PV1 (dst g e) -> vmap g1 (dst g e) = dst g1' (emap g1 e)) /\
  guarded_bij (eq root) PE1_root (vmap g1) (emap g1) g1 g1' /\
  (forall e, PE1_root e -> vmap g1 (dst g e) = dst g1' (emap g1 e)) /\
  guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g1) /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g1) /\
  disjointed_guard
     (image_set (vmap g1) PV1) (image_set (vmap g1) (eq root))
     (image_set (emap g1) PE1) (image_set (emap g1) PE1_root) ->
  copy P root (g, g') (g1, g1').
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
  destruct H3 as [?PRE [?PRE [?PRE [?PRE [?PRE [?PRE [?PRE ?PRE]]]]]]].
  unfold copy.
  split; [| split; [| split; [| split; [| split]]]].
  + auto.
  + tauto.
  + tauto.
  + admit.
  + intros.
    rewrite Intersection_spec in H3.
    destruct H3.
    unfold weak_edge_prop in H3.
    rewrite reachable_by_ind_equiv in H3 by eauto.
    destruct H3.
    - apply PRE3.
      unfold PE1_root.
      rewrite H1.
      split; auto.
    - apply PRE1.
      unfold PE1.
      rewrite Intersection_spec; auto.
      unfold PV1.
      intro; apply H5; clear H5.
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
    rewrite H5, H3; clear H3 H5.
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

End LocalCopyGraph.

End LocalCopyGraph.
