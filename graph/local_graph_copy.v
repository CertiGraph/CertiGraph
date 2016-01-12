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

Definition copy (M: V -> Prop) root (g1 g2: Graph) (g2': Graph') :=
  let PV := reachable_by g1 root (Complement _ M) in
  let PE := Intersection _ (weak_edge_prop PV g1) (evalid g1) in
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ PV) eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ PE) eq (emap g1) (emap g2) /\
  Same_set (vvalid g2') (image_set PV (vmap g2)) /\
  Same_set (evalid g2') (image_set PE (emap g2)) /\
  (forall e, PE e -> ~ PV (dst g2 e) -> vmap g2 (dst g2 e) = dst g2' (emap g2 e)) /\
  guarded_bij PV PE (vmap g2) (emap g2) g2 g2'.

Definition extended_copy (M: V -> Prop) root (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  let PV := reachable_by g1 root (Complement _ M) in
  let PE := Intersection _ (weak_edge_prop PV g1) (evalid g1) in
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ PV) eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ PE) eq (emap g1) (emap g2) /\
  pregraph_join (image_set PV (vmap g2)) (image_set PE (emap g2)) g1' g2' /\
  (forall e, PE e -> ~ PV (dst g2 e) -> vmap g2 (dst g2 e) = dst g2' (emap g2 e)) /\
  (forall v, M v \/ ~ M v) /\
  guarded_bij PV PE (vmap g2) (emap g2) g2 g2'.

(*
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
     (image_set (Union _ PV1 (eq root)) (vmap g2)) (image_set PV0 (vmap g2))
     (image_set (Union _ PE1 PE1_root) (emap g2)) (image_set PE0 (emap g2)) /\ (* From spatial fact *)
  Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _). (* From weak mark lemma *)
*)

Definition edge_copy (g: Graph) (root: V) (M: V -> Prop) (l: list E * E) :=
  let (es_done, e0) := l in
  let M0 := Union _ M (eq root) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let M_rec := Union _ M0 PV1 in
  relation_list (extended_copy M_rec (dst g e0) :: ecopy1 e0 :: nil).

Definition edge_copy_list (g: Graph) (root: V) es (P: V -> Prop) :=
  relation_list (map (edge_copy g root P) (combine (prefixes es) es)).

Lemma triple_vcopy1: forall (g1 g2: Graph) root,
  vvalid g1 root ->
  vcopy1 root g1 g2 ->
  guarded_bij (eq root) (Empty_set _) (vmap g2) (emap g2) g2 (single_vertex_pregraph (vmap g2 root)).
Proof.
  intros g1 g2 root ? [VCOPY_si [VCOPY_gprv VCOPY_gpre]].
  split; [.. | split]; intros.
  + apply is_guarded_inj_single.
  + apply is_guarded_inj_empty.
  + subst v.
    unfold single_vertex_pregraph; simpl.
    destruct_eq_dec (vmap g2 root) (vmap g2 root); [| congruence].
    rewrite (proj1 VCOPY_si) in H.
    tauto.
  + inversion H0.
  + inversion H0.
  + inversion H0.
Qed.

Section MARK_AUX.

Variables (g: Graph) (M M0 M_rec: V -> Prop) (root: V).
Variables (e0: E) (es es_done es_later: list E).
Variables (PV1 PV3 PV0: V -> Prop) (PE1 PE1_root PE3 PE3_root PE0: E -> Prop).

Hypothesis H_ES:   es = es_done ++ e0 :: es_later.
Hypothesis H_M0:   M0 = Union _ M (eq root).
Hypothesis H_PV1:  PV1 = reachable_by_through_set g (map (dst g) es_done) (Complement _ M0).
Hypothesis H_PE1:  PE1 = Intersection _ (weak_edge_prop PV1 g) (evalid g).
Hypothesis H_PE1r: PE1_root = fun e => In e es_done.
Hypothesis H_PV3:  PV3 = reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) (Complement _ M0).
Hypothesis H_PE3:  PE3 = Intersection _ (weak_edge_prop PV3 g) (evalid g).
Hypothesis H_PE3r: PE3_root = fun e => In e (es_done ++ e0 :: nil).
Hypothesis H_Mrec: M_rec = Union _ M0 PV1.
Hypothesis H_PV0:  PV0 = reachable_by g (dst g e0) (Complement _ M_rec).
Hypothesis H_PE0:  PE0 = Intersection _ (weak_edge_prop PV0 g) (evalid g).
Hypothesis M_DEC: forall v, M v \/ ~ M v.
Hypothesis Mr_DEC: forall v, M_rec v \/ ~ M_rec v.
Hypothesis H_OUT_EDGE: forall e, In e es <-> out_edges g root e.
Hypothesis H_NODUP: NoDup es.

Lemma M0_DEC: forall v, M0 v \/ ~ M0 v.
Proof.
  intros.
  destruct (M_DEC v).
  + left.
    subst M0.
    rewrite Union_spec; left; auto.
  + destruct_eq_dec root v.
    - left.
      subst M0.
      rewrite Union_spec; right; auto.
    - right.
      subst M0.
      rewrite Union_spec.
      tauto.
Qed.

Lemma PV1_DEC: forall v, PV1 v \/ ~ PV1 v.
Proof.
  clear PE1 H_PE1.
  intros.
  subst M_rec.
  destruct (Mr_DEC v) as [[|]|].
  + right.
    intro.
    subst PV1.
    apply reachable_by_through_set_foot_prop in H0.
    apply H0, H.
  + left; apply H.
  + right.
    intro; apply H.
    rewrite Union_spec; right; apply H0.
Qed.

Lemma aux00: Same_set (Union _ PV1 (Complement _ PV1)) (Full_set _).
Proof.
  rewrite Same_set_spec; intro v.
  rewrite Union_spec; unfold Complement, Ensembles.In.
  clear.
  pose proof PV1_DEC.
  firstorder;
  constructor.
Qed.

Lemma aux01: Same_set PV3 (Union _ PV1 PV0).
Proof.
  clear PE1 PE3 PE0 H_PE1 H_PE3 H_PE0.
  intros.
  subst PV0 M_rec PV3.
  rewrite map_app; simpl map.
  rewrite reachable_by_through_app_strong' by (rewrite <- H_PV1; apply aux00).
  rewrite reachable_by_through_singleton'.
  subst PV1.
  rewrite Intersection_Complement.
  reflexivity.
Qed.

Lemma aux02: Same_set PE3 (Union _ PE1 PE0).
Proof.
  intros.
  rewrite H_PE0, H_PE3, H_PE1.
  rewrite aux01 by auto.
  rewrite weak_edge_prop_Union.
  rewrite Intersection_Union_distr_l.
  reflexivity.
Qed.

Lemma aux03: Same_set PE3_root (Union _ PE1_root (eq e0)).
Proof.
  intros.
  rewrite H_PE3r, H_PE1r.
  rewrite Same_set_spec; intro e.
  rewrite Union_spec, in_app_iff; simpl.
  tauto.
Qed.

Lemma aux04: forall e, PE1_root e -> src g e = root.
Proof.
  intros.
  assert (In e es) by (rewrite H_ES, in_app_iff; subst PE1_root; auto).
  rewrite H_OUT_EDGE in H0.
  destruct H0.
  auto.
Qed.

Lemma aux05: forall e, PE3_root e -> src g e = root.
Proof.
  intros.
  assert (In e es)
    by (rewrite H_ES; subst PE3_root; rewrite in_app_iff in H |- *; simpl in H |- *; tauto).
  rewrite H_OUT_EDGE in H0.
  destruct H0.
  auto.
Qed.

Lemma aux06: Disjoint _ PV1 PV0.
Proof.
  intros.
  rewrite H_PV0, H_Mrec, H_PV1.
  rewrite Disjoint_spec; intros.
  rewrite <- Intersection_Complement in H0.
  apply reachable_by_foot_prop in H0.
  rewrite Intersection_spec in H0; unfold Complement, Ensembles.In in H0.
  tauto.
Qed.

Lemma aux07: Disjoint _ PE1 PE0.
Proof.
  intros.
  rewrite H_PE1, H_PE0.
  rewrite Disjoint_spec; intros.
  rewrite Intersection_spec in H, H0.
  unfold weak_edge_prop in H, H0.
  generalize (src g x), (proj1 H), (proj1 H0).
  rewrite <- Disjoint_spec.
  apply aux06.
Qed.

Lemma aux08: Disjoint _ (eq root) PV0.
Proof.
  intros.
  rewrite H_PV0.
  rewrite Disjoint_spec.
  intros.
  subst x M_rec.
  rewrite <- Intersection_Complement in H0.
  apply reachable_by_foot_prop in H0.
  rewrite H_M0 in H0.
  rewrite !Intersection_spec in H0.
  apply (proj1 H0); right; reflexivity.
Qed.

Lemma aux09: Disjoint _ PE1_root PE0.
Proof.
  intros.
  rewrite H_PE0.
  rewrite Disjoint_spec.
  intros e ? ?.
  rewrite Intersection_spec in H0.
  unfold weak_edge_prop in H0.
  rewrite aux04 in H0 by auto.
  destruct H0.
  generalize (@eq_refl _ root) H0.
  generalize root at 2 3.
  rewrite <- Disjoint_spec.
  apply aux08.
Qed.

Lemma aux10: Disjoint _ PE3 (eq e0).
Proof.
  intros.
  rewrite Disjoint_spec.
  intros e ? ?.
  subst e.
  assert (In e0 es) by (rewrite H_ES; rewrite in_app_iff; simpl; tauto).
  rewrite H_OUT_EDGE in H0.
  unfold out_edges in H0.
  destruct H0.
  subst PE3.
  rewrite Intersection_spec in H.
  unfold weak_edge_prop in H.
  rewrite H1 in H.
  destruct H as [? _].
  subst PV3.
  apply reachable_by_through_set_foot_prop in H.
  subst M0.
  apply H; unfold Ensembles.In; rewrite Union_spec; right; auto.
Qed.

Lemma aux11: Disjoint _ PE1_root (eq e0).
Proof.
  rewrite Disjoint_spec.
  intros e ? ?.
  subst e.
  subst PE1_root.
  rewrite H_ES in H_NODUP.
  pose proof NoDup_app_not_in _ _ _ H_NODUP e0.
  simpl in H0.
  clear - H0 H.
  tauto.
Qed.

Lemma aux12: forall e, PE1 e -> PV0 (src g e) -> False.
Proof.
  intros.
  subst PE1.
  rewrite Intersection_spec in H.
  destruct H.
  unfold weak_edge_prop in H.
  generalize (src g e) H H0.
  rewrite <- Disjoint_spec.
  apply aux06.
Qed.

Lemma aux13: forall e, PE1 e -> PV0 (dst g e) -> False.
Proof.
  intros.
  subst PV0.
  pose proof reachable_by_foot_valid _ _ _ _ H0.
  apply reachable_by_foot_prop in H0.
  subst PE1 M_rec.
  unfold weak_edge_prop in H.
  rewrite Intersection_spec in H; destruct H.
  apply H0.
  unfold Ensembles.In.
  right.
  subst PV1.
  apply reachable_by_through_set_step with (src g e); auto.
  + intro; apply H0.
    unfold Ensembles.In.
    rewrite Union_spec; left; auto.
  + exists e; auto.
Qed.

Lemma aux14: forall e, PE0 e -> PV1 (src g e) -> False.
Proof.
  intros.
  subst PE0.
  rewrite Intersection_spec in H.
  destruct H.
  unfold weak_edge_prop in H.
  generalize (src g e) H0 H.
  rewrite <- Disjoint_spec.
  apply aux06.
Qed.

Lemma aux15: forall e, PE1_root e -> PV0 (src g e) -> False.
Proof.
  intros.
  apply aux04 in H.
  symmetry in H.
  generalize (src g e) H H0.
  rewrite <- Disjoint_spec.
  apply aux08.
Qed.

Lemma aux16: forall e, PE1_root e -> PV0 (dst g e) -> False.
Proof.
  intros.
  subst PV0.
  pose proof reachable_by_foot_valid _ _ _ _ H0.
  apply reachable_by_foot_prop in H0.
  subst M_rec.
  apply H0; unfold Ensembles.In; clear H0.
  rewrite Union_spec.
  destruct (M0_DEC (dst g e)); [left; auto | right].
  subst PV1 PE1_root; exists (dst g e).
  split; [apply in_map; auto |].
  apply reachable_by_refl; auto.
Qed.
  
Lemma aux17: forall e, PE0 e -> root = src g e -> False.
Proof.
  intros.
  subst PE0.
  rewrite Intersection_spec in H; destruct H.
  unfold weak_edge_prop in H.
  rewrite <- H0 in H.
  subst PV0.
  apply reachable_by_foot_prop in H.
  subst M_rec M0.
  apply H.
  unfold Ensembles.In.
  rewrite !Union_spec.
  left; right; auto.
Qed.

Lemma aux18: Same_set (Union _ PV3 (eq root)) (Union _ (Union _ PV1 (eq root)) PV0).
Proof.
  intros.
  rewrite aux01.
  rewrite Same_set_spec; intro v.
  rewrite !Union_spec; tauto.
Qed.

Lemma aux19: Same_set (Union _ PE3 PE1_root) (Union _ (Union _ PE1 PE1_root) PE0).
Proof.
  intros.
  rewrite aux02.
  rewrite Same_set_spec; intro e.
  rewrite !Union_spec; tauto.
Qed.

Lemma aux20: Same_set (Union _ PE3 PE3_root) (Union _ (Union _ PE3 PE1_root) (eq e0)).
Proof.
  intros.
  rewrite aux03.
  rewrite Same_set_spec; intro e.
  rewrite !Union_spec; tauto.
Qed.

Lemma aux21: forall e, PE1 e -> evalid g e.
Proof.
  intros.
  subst PE1.
  rewrite Intersection_spec in H; tauto.
Qed.

Lemma aux22: forall e, PE1_root e -> evalid g e.
Proof.
  intros.
  subst PE1_root.
  assert (In e es) by (rewrite H_ES, in_app_iff; tauto).
  rewrite H_OUT_EDGE in H0.
  destruct H0; auto.
Qed.

Lemma aux23: forall e, PE3 e -> evalid g e.
Proof.
  intros.
  subst PE3.
  rewrite Intersection_spec in H; tauto.
Qed.

End MARK_AUX.

Arguments aux01 {_} {_} {_} {_} {_} PV1 PV3 PV0 _ _ _ _ _.
Arguments aux02 {_} {_} {_} {_} {_} {_} {_} {_} PE1 PE3 PE0 _ _ _ _ _ _ _ _.
Arguments aux03 {_} {_} PE1_root PE3_root _ _.
Arguments aux06 {_} {_} {_} {_} {_} PV1 PV0 _ _ _.
Arguments aux07 {_} {_} {_} {_} {_} {_} {_} PE1 PE0 _ _ _ _ _.
Arguments aux08 {_} {_} {_} {_} root {_} {_} PV0 _ _ _ _.
Arguments aux09 {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} PE1_root PE0 _ _ _ _ _ _ _ _.
Arguments aux18 {_} {_} {_} root {_} {_} PV1 PV3 PV0 _ _ _ _ _.
Arguments aux19 {_} {_} {_} {_} {_} {_} {_} {_} PE1 PE1_root PE3 PE0 _ _ _ _ _ _ _ _.
Arguments aux20 e0 {_} PE1_root PE3 PE3_root _ _.

Lemma triple_aux4_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (M0: V -> Prop) es_done,
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  g ~=~ g1 ->
  forall son,
    extended_copy (Union _ M0 PV1) son (g1, g1') (g2, g2') ->
    forall e,
       Intersection E
         (weak_edge_prop
            (reachable_by g son (Complement _ (Union _ M0 PV1))) g) 
         (evalid g) e ->
       ~
       g |= son ~o~> dst g e satisfying (Complement _ (Union _ M0 PV1)) ->
       vmap g2 (dst g2 e) = dst g2' (emap g2 e).
Proof.
  intros.
  destruct H0 as [COPY_si [COPY_gprv [COPY_gpre [? [? COPY_bij]]]]].
  apply H3.
  + pose proof weak_edge_prop_si (reachable_by g1 son (Complement _ (Union _ M0 PV1))) _ _ H.
    rewrite <- H in H4 at 1.
    rewrite Same_set_spec in H4.
    rewrite <- (H4 e); auto.
  + rewrite <- H in COPY_si.
    rewrite Intersection_spec in H1; destruct H1.
    erewrite si_dst1 in H2 by eauto.
    rewrite <- H.
    auto.
Qed.

Lemma triple1_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (M: V -> Prop) root es es_done e0 es_later,
  let M0 := Union _ M (eq root) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) (Complement _ M0) in
  let PE3 := Intersection _ (weak_edge_prop PV3 g) (evalid g) in
  let M_rec := Union _ M0 PV1 in
  let PV0 := reachable_by g (dst g e0) (Complement _ M_rec) in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  guarded_bij (Union _ PV1 (eq root)) (Union _ PE1 PE1_root) (vmap g1) (emap g1) g1 g1' /\
  Same_set (vvalid g1') (image_set (Union _ PV1 (eq root)) (vmap g1)) /\
  Same_set (evalid g1') (image_set (Union _ PE1 PE1_root) (emap g1)) /\
  g ~=~ g1 ->
  extended_copy M_rec (dst g e0) (g1, g1') (g2, g2') ->
  (forall v, M v \/ ~ M v) -> (* From weak mark lemma *)
  guarded_bij (Union _ PV3 (eq root)) (Union _ PE3 PE1_root) (vmap g2) (emap g2) g2 g2'.
Proof.
  intros until es_later.
  intros ? ? ? ? ? ? ? ? ?.
  intros H_VVALID H_CM H_OUT_EDGES H_ES [PRE_bij [PRE_vvalid [PRE_evalid PRE_si]]] COPY M_DEC.
  erewrite (aux18 root PV1 PV3 PV0) by first [destruct COPY; tauto | reflexivity].
  erewrite (aux19 PE1 PE1_root PE3 PE0) by first [destruct COPY; tauto | reflexivity].

  assert (forall e,
       PE0 e ->
       ~ g |= dst g e0 ~o~> dst g e satisfying (Complement _ M_rec) ->
       vmap g2 (dst g2 e) = dst g2' (emap g2 e)) as COPY_consi
  by (eapply triple_aux4_copy; eauto).
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [COPY_pj [_ [COPY_DEC COPY_bij]]]]]].
  rewrite <- PRE_si in COPY_si.
  rewrite <- PRE_si in COPY_gprv at 1.
  rewrite <- PRE_si in COPY_gpre at 1.
  rewrite <- (weak_edge_prop_si _ _ _ PRE_si) in COPY_gpre.
  rewrite <- PRE_si in COPY_pj at 1 2.
  rewrite <- (weak_edge_prop_si _ _ _ PRE_si) in COPY_pj.
  rewrite <- PRE_si in COPY_bij at 1 2.
  rewrite <- (weak_edge_prop_si _ _ _ PRE_si) in COPY_bij.

  apply guarded_pointwise_relation_weaken with (P2 := Union V PV1 (eq root)) in COPY_gprv.
  Focus 2. {
    apply Included_Complement_Disjoint.
    apply Union_left_Disjoint.
    split; [eapply (aux06 PV1 PV0) | eapply (aux08 root PV0)];
    first [eassumption | reflexivity].
  } Unfocus.

  apply guarded_pointwise_relation_weaken with (P2 := Union E PE1 PE1_root) in COPY_gpre.
  Focus 2. {
    apply Included_Complement_Disjoint.
    apply Union_left_Disjoint.
    split; [eapply (aux07 PE1 PE0) | eapply (aux09 PE1_root PE0)];
    first [eassumption | reflexivity].
  } Unfocus.
  rewrite COPY_gprv in PRE_bij, PRE_vvalid.
  rewrite COPY_gpre in PRE_bij, PRE_evalid.

  assert (guarded_bij PV0 PE0 (vmap g2) (emap g2) g g2').
  Focus 1. {
    eapply guarded_bij_proper_aux1; [| reflexivity | exact COPY_bij].
    apply si_guarded_si; symmetry; auto.
  } Unfocus.

  assert (guarded_bij (Union _ PV1 (eq root)) (Union _ PE1 PE1_root) (vmap g2) (emap g2) g2 g2').
  Focus 1. {
    eapply guarded_bij_proper_aux1; [| | exact PRE_bij].
    1: apply si_guarded_si; rewrite <- COPY_si; symmetry; auto.
    pose proof pregraph_join_guarded_si _ _ _ _ COPY_pj.
    eapply guarded_si_weaken; [| | exact H0]; clear H0.
    + apply Included_Complement_Disjoint.
      destruct COPY_pj as [? _].
      apply Prop_join_Disjoint in H0.
      rewrite PRE_vvalid in H0; auto.
    + apply Included_Complement_Disjoint.
      destruct COPY_pj as [_ [? _]].
      apply Prop_join_Disjoint in H0.
      rewrite PRE_evalid in H0; auto.
  } Unfocus.

  apply guarded_bij_disjointed_union; auto.
  + destruct COPY_pj as [? [? _]].
    apply Prop_join_Disjoint in H1.
    apply Prop_join_Disjoint in H2.
    rewrite PRE_vvalid in H1.
    rewrite PRE_evalid in H2.
    split; auto.
  + split; split; intros.
    - erewrite <- si_src2 in H2 by eauto.
      rewrite Union_spec in H1; destruct H1; exfalso.
      * revert H1 H2; eapply aux12; reflexivity.
      * revert H1 H2; eapply aux15; eauto; reflexivity.
    - erewrite <- si_dst2 in H2 by eauto.
      rewrite Union_spec in H1; destruct H1; exfalso.
      * revert H1 H2; eapply aux13; eauto; reflexivity.
      * revert H1 H2; eapply aux16; eauto; reflexivity.
    - erewrite <- si_src2 in H2 by eauto.
      rewrite Union_spec in H2; destruct H2; exfalso.
      * revert H1 H2; eapply aux14; eauto; reflexivity.
      * revert H1 H2; eapply aux17; eauto; reflexivity.
    - erewrite <- si_dst2 in H2 by eauto.
      apply COPY_consi; auto.
      unfold not; generalize (dst g e) H2.
      rewrite <- Disjoint_spec.
      apply Union_left_Disjoint.
      split; [eapply (aux06 PV1 PV0) | eapply (aux08 root PV0)];
      first [eassumption | reflexivity].
Qed.

Lemma triple2_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (M: V -> Prop) root es es_done e0 es_later,
  vvalid g root ->
  ~ M root ->
  let M0 := Union _ M (eq root) in
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  g ~=~ g1 ->
  let M_rec := Union _ M0 PV1 in
  let PV0 := reachable_by g (dst g e0) (Complement _ M_rec) in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  extended_copy M_rec (dst g e0) (g1, g1') (g2, g2') ->
  g ~=~ g2.
Proof.
  intros.
  destruct H4 as [? [? [? [? [? [? [? ?]]]]]]].
  transitivity g1; auto.
Qed.

Lemma triple3_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (M: V -> Prop) root es es_done e0 es_later,
  let M0 := Union _ M (eq root) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) (Complement _ M0) in
  let PE3 := Intersection _ (weak_edge_prop PV3 g) (evalid g) in
  let M_rec := Union _ M0 PV1 in
  let PV0 := reachable_by g (dst g e0) (Complement _ M_rec) in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  guarded_bij (Union _ PV1 (eq root)) (Union _ PE1 PE1_root) (vmap g1) (emap g1) g1 g1' /\
  Same_set (vvalid g1') (image_set (Union _ PV1 (eq root)) (vmap g1)) /\
  Same_set (evalid g1') (image_set (Union _ PE1 PE1_root) (emap g1)) /\
  g ~=~ g1 /\
  (forall e, Union _ PE1 PE1_root e -> Complement _ (Union _ PV1 (eq root)) (dst g1 e) -> vmap g1 (dst g1 e) = dst g1' (emap g1 e)) ->
  extended_copy M_rec (dst g e0) (g1, g1') (g2, g2') ->
  (forall v, M v \/ ~ M v) -> (* From weak mark lemma *)
  (forall e, Union _ PE3 PE1_root e -> Complement _ (Union _ PV3 (eq root)) (dst g2 e) -> vmap g2 (dst g2 e) = dst g2' (emap g2 e)).
Proof.
  intros until es_later.
  intros ? ? ? ? ? ? ? ? ?.
  intros H_VVALID H_P H_OUT_EDGES H_ES [PRE_bij [PRE_vvalid [PRE_evalid [PRE_si PRE_consi]]]] COPY M_DEC.

  assert (forall e,
       PE0 e ->
       ~ g |= dst g e0 ~o~> dst g e satisfying (Complement _ M_rec) ->
       vmap g2 (dst g2 e) = dst g2' (emap g2 e)) as COPY_consi
  by (eapply triple_aux4_copy; eauto).
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [COPY_pj [_ [COPY_DEC COPY_bij]]]]]].

  rewrite <- PRE_si in COPY_gprv at 1.
  rewrite <- PRE_si in COPY_gpre at 1.
  rewrite <- (weak_edge_prop_si _ _ _ PRE_si) in COPY_gpre.
  rewrite <- PRE_si in COPY_pj at 1 2.
  rewrite <- (weak_edge_prop_si _ _ _ PRE_si) in COPY_pj.
  rewrite <- PRE_si in COPY_bij at 1 2.
  rewrite <- (weak_edge_prop_si _ _ _ PRE_si) in COPY_bij.

  intros.
  erewrite app_same_set in H by (eapply (aux19 PE1 PE1_root PE3 PE0); eauto; reflexivity).
  erewrite app_same_set in H0 by (erewrite (aux18 root PV1 PV3 PV0) by (eauto; reflexivity); reflexivity).
  erewrite app_same_set in H0 by (symmetry; apply Intersection_Complement).
  rewrite Intersection_spec in H0; destruct H0.
  rewrite Union_spec in H; destruct H.
  + assert (evalid g e).
    Focus 1. {
      rewrite Union_spec in H.
      destruct H; revert H; [eapply aux21 | eapply aux22]; eauto; reflexivity.
    } Unfocus.
    rewrite (proj1 (proj2 PRE_si)) in H2.
    erewrite <- si_dst1 in H0, H1 |- * by eauto.
    rewrite guarded_pointwise_relation_spec in COPY_gprv.
    rewrite <- COPY_gprv by auto.
    rewrite PRE_consi by auto.
    apply guarded_pointwise_relation_weaken with (P2 := Union E PE1 PE1_root) in COPY_gpre.
    Focus 2. {
      apply Included_Complement_Disjoint.
      apply Union_left_Disjoint; split.
      + eapply aux07; eauto; reflexivity.
      + eapply aux09; eauto; reflexivity.
    } Unfocus.
    rewrite guarded_pointwise_relation_spec in COPY_gpre.
    rewrite COPY_gpre by auto.
    pose proof pregraph_join_guarded_si _ _ _ _ COPY_pj.
    eapply guarded_si_weaken in H3; [| apply Included_refl |].
    Focus 2. {
      apply Included_Complement_Disjoint.
      destruct COPY_pj as [_ [? _]].
      eapply Prop_join_Disjoint; eauto.
    } Unfocus.
    assert (evalid g1' (emap g2 e)).
    Focus 1. {
      rewrite <- COPY_gpre by auto.
      apply (evalid_preserved PRE_bij); auto.
    } Unfocus.
    eapply guarded_si_dst1; eauto.
  + apply COPY_consi; auto.
    rewrite <- PRE_si in COPY_si.
    erewrite <- si_dst1 in H1; eauto.
    unfold PE0 in H.
    rewrite Intersection_spec in H; tauto.
Qed.

Lemma triple4_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (M: V -> Prop) root es es_done e0 es_later,
  let M0 := Union _ M (eq root) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let M_rec := Union _ M0 PV1 in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  g ~=~ g1 /\
  guarded_pointwise_relation (Complement V (reachable_by g root (Complement _ M))) eq (vmap g) (vmap g1) ->
  extended_copy M_rec (dst g e0) (g1, g1') (g2, g2') ->
  guarded_pointwise_relation (Complement V (reachable_by g root (Complement _ M))) eq (vmap g) (vmap g2).
Proof.
  intros until es_later.
  intros ? ? ?.
  intros H_VVALID H_M H_OUT_EDGES H_ES [PRE_si PRE_gpr] COPY.
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [? [? [COPY_DEC COPY_bij]]]]]].
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
    generalize x0, H2.
    apply Complement_Included_rev.
    eapply Included_trans; [| apply left_Included_Union].
    apply left_Included_Union.
Qed.

Lemma triple5_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (M: V -> Prop) root es es_done e0 es_later,
  let PV := reachable_by g root (Complement _ M) in
  let PE := Intersection E (weak_edge_prop PV g) (evalid g) in
  let M0 := Union _ M (eq root) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let M_rec := Union _ M0 PV1 in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  g ~=~ g1 /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g1) ->
  extended_copy M_rec (dst g e0) (g1, g1') (g2, g2') ->
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g2).
Proof.
  intros until es_later.
  intros ? ? ? ? ?.
  intros H_VVALID H_M H_OUT_EDGES H_ES [PRE_si PRE_gpr] COPY.
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [? [? [COPY_DEC COPY_bij]]]]]].
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
    generalize x0, H3.
    apply Complement_Included_rev.
    eapply Included_trans; [| apply left_Included_Union].
    apply left_Included_Union.
Qed.

Lemma triple6_copy: forall (g g1 g2: Graph) (g1' g2': Graph') (M: V -> Prop) root es es_done e0 es_later,
  let M0 := Union _ M (eq root) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) (Complement _ M0) in
  let PE3 := Intersection _ (weak_edge_prop PV3 g) (evalid g) in
  let M_rec := Union _ M0 PV1 in
  let PV0 := reachable_by g (dst g e0) (Complement _ M_rec) in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  Same_set (vvalid g1') (image_set (Union _ PV1 (eq root)) (vmap g1)) /\
  Same_set (evalid g1') (image_set (Union _ PE1 PE1_root) (emap g1)) /\
  g ~=~ g1 ->
  extended_copy M_rec (dst g e0) (g1, g1') (g2, g2') ->
  (forall v : V, M v \/ ~ M v) ->
  Same_set (vvalid g2') (image_set (Union _ PV3 (eq root)) (vmap g2)) /\
  Same_set (evalid g2') (image_set (Union _ PE3 PE1_root) (emap g2)).
Proof.
  intros until es_later.
  intros ? ? ? ? ?  ?  ? ? ?.
  intros H_VVALID H_P H_OUT_EDGES H_ES [PRE_vvalid [PRE_evalid PRE_si]] COPY M_DEC.
  destruct COPY as [COPY_si [COPY_gprv [COPY_gpre [COPY_pj [? [COPY_DEC COPY_bij]]]]]].
  erewrite (aux18 root PV1 PV3 PV0) by first [eassumption | reflexivity].
  erewrite (aux19 PE1 PE1_root PE3 PE0) by first [eassumption | reflexivity].

  rewrite <- PRE_si in COPY_si.
  rewrite <- PRE_si in COPY_gprv at 1.
  rewrite <- PRE_si in COPY_gpre at 1.
  rewrite <- (weak_edge_prop_si _ _ _ PRE_si) in COPY_gpre.
  rewrite <- PRE_si in COPY_pj at 1 2.
  rewrite <- (weak_edge_prop_si _ _ _ PRE_si) in COPY_pj.

  apply guarded_pointwise_relation_weaken with (P2 := Union V PV1 (eq root)) in COPY_gprv.
  Focus 2. {
    apply Included_Complement_Disjoint.
    apply Union_left_Disjoint.
    split; [eapply (aux06 PV1 PV0) | eapply (aux08 root PV0)];
    first [eassumption | reflexivity].
  } Unfocus.

  apply guarded_pointwise_relation_weaken with (P2 := Union E PE1 PE1_root) in COPY_gpre.
  Focus 2. {
    apply Included_Complement_Disjoint.
    apply Union_left_Disjoint.
    split; [eapply (aux07 PE1 PE0) | eapply (aux09 PE1_root PE0)];
    first [eassumption | reflexivity].
  } Unfocus.
  rewrite COPY_gprv in PRE_vvalid.
  rewrite COPY_gpre in PRE_evalid.

  split.
  + destruct COPY_pj as [? _].
    destruct H0.
    rewrite image_Union.
    rewrite Same_set_spec in PRE_vvalid |- *; intro v'; specialize (PRE_vvalid v').
    clear - H0 PRE_vvalid.
    unfold PV0.
    rewrite H0, PRE_vvalid, Union_spec.
    reflexivity.
  + destruct COPY_pj as [_ [? _]].
    destruct H0.
    rewrite image_Union.
    rewrite Same_set_spec in PRE_evalid |- *; intro v'; specialize (PRE_evalid v').
    clear - H0 PRE_evalid.
    unfold PE0.
    rewrite H0, PRE_evalid, Union_spec.
    reflexivity.
Qed.

(*
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
*)

Lemma triple1_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (M: V -> Prop) root es es_done e0 es_later,
  let M0 := Union _ M (eq root) in
  let PE1_root e := In e es_done in
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) (Complement _ M0) in
  let PE3 := Intersection _ (weak_edge_prop PV3 g) (evalid g) in
  let PE3_root e := In e (es_done ++ e0 :: nil) in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  guarded_bij (Union _ PV3 (eq root)) (Union _ PE3 PE1_root) (vmap g2) (emap g2) g2 g2' /\
  Same_set (vvalid g2') (image_set (Union _ PV3 (eq root)) (vmap g2)) /\
  Same_set (evalid g2') (image_set (Union _ PE3 PE1_root) (emap g2)) /\
  g ~=~ g2 ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  guarded_bij (Union _ PV3 (eq root)) (Union _ PE3 PE3_root) (vmap g3) (emap g3) g3 g3'.
Proof.
  intros until es_later.
  intros ? ? ? ? ?.
  intros H_VVALID H_P H_OUT_EDGES H_NODUP H_ES [PRE_bij [PRE_vvalid [PRE_evalid PRE_si]]] ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre [? [ECOPY_pj [? ?]]]]]].
  apply guarded_pointwise_relation_pointwise_relation with (P := Union V PV3 (eq root)) in ECOPY_prv.
  apply guarded_pointwise_relation_weaken with (P2 := Union E PE3 PE1_root) in ECOPY_gpre.
  Focus 2. {
    apply Included_Complement_Disjoint.
    apply Union_left_Disjoint; split.
    + eapply aux10; eauto; reflexivity.
    + eapply aux11; eauto; reflexivity.
  } Unfocus.
  rewrite ECOPY_prv in PRE_vvalid, PRE_bij.
  rewrite ECOPY_gpre in PRE_evalid, PRE_bij.
  rewrite <- Union_Empty_right.
  erewrite (aux20 e0 PE1_root PE3 PE3_root) by (eauto; reflexivity).
  apply guarded_bij_disjointed_union.
  + split.
    - rewrite image_Empty.
      apply Disjoint_Empty_set_right.
    - destruct ECOPY_pj as [_ [? _]].
      apply Prop_join_Disjoint in H2.
      rewrite PRE_evalid in H2.
      rewrite image_single; auto.
  + eapply guarded_bij_proper_aux1; [apply si_guarded_si, ECOPY_si | | exact PRE_bij].
    pose proof  pregraph_join_guarded_si _ _ _ _ ECOPY_pj.
    eapply guarded_si_weaken; [| | exact H2].
    1: rewrite Complement_Empty_set; apply Included_Full_set.
    apply Included_Complement_Disjoint.
    destruct ECOPY_pj as [_ [? _]].
    apply Prop_join_Disjoint in H3.
    rewrite PRE_evalid in H3.
    auto.
  + split; [.. | split]; intros.
    - apply is_guarded_inj_empty.
    - apply is_guarded_inj_single.
    - inversion H2.
    - subst e.
      assert (evalid g3 e0).
      Focus 1. {
        assert (In e0 es) by (rewrite H_ES, in_app_iff; simpl; tauto).
        rewrite H_OUT_EDGES in H2.
        destruct H2 as [? _].
        rewrite <- PRE_si in ECOPY_si.
        rewrite <- (proj1 (proj2 ECOPY_si)); auto.
      } Unfocus.
      assert (evalid g3' (emap g3 e0)).
      Focus 1. {
        destruct ECOPY_pj as [_ [[? _] _]].
        specialize (H3 (emap g3 e0)).
        tauto.
      } Unfocus.
      tauto.
    - inversion H3.
    - inversion H3.
  + split; split; intros.
    - inversion H3.
    - inversion H3.
    - subst e.
      auto.
    - subst e.
      auto.
Qed.

Lemma triple2_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (M: V -> Prop) root es es_done e0 es_later,
  let M0 := Union _ M (eq root) in
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) (Complement _ M0) in
  let PE3 := Intersection _ (weak_edge_prop PV3 g) (evalid g) in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  g ~=~ g2 ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  g ~=~ g3.
Proof.
  intros until es_later.
  intros ? ? ?.
  intros H_VVALID H_M H_OUT_EDGES H_ES PRE_si ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]].
  rewrite PRE_si; auto.
Qed.

Lemma triple3_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (M: V -> Prop) root es es_done e0 es_later,
  let M0 := Union _ M (eq root) in
  let PE1_root e := In e es_done in
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) (Complement _ M0) in
  let PE3 := Intersection _ (weak_edge_prop PV3 g) (evalid g) in
  let PE3_root e := In e (es_done ++ e0 :: nil) in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  guarded_bij (Union _ PV3 (eq root)) (Union _ PE3 PE1_root) (vmap g2) (emap g2) g2 g2' /\
  g ~=~ g2 /\
  (forall e, (Union _ PE3 PE1_root) e -> Complement _ (Union _ PV3 (eq root)) (dst g2 e) -> vmap g2 (dst g2 e) = dst g2' (emap g2 e)) ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  (forall e, (Union _ PE3 PE3_root) e -> Complement _ (Union _ PV3 (eq root)) (dst g3 e)  -> vmap g3 (dst g3 e) = dst g3' (emap g3 e)).
Proof.
  intros until es_later.
  intros ? ? ? ? ?.
  intros H_VVALID H_M H_OUT_EDGES H_NODUP H_ES [PRE_bij [PRE_si PRE_consi]] ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre
                     [? [ECOPY_pj [? ?]]]]]]. 

  intros.
  erewrite app_same_set in H2 by (eapply (aux20 e0 PE1_root PE3 PE3_root); eauto; reflexivity).
  rewrite Union_spec in H2; destruct H2.
  + assert (evalid g e).
    Focus 1. {
      rewrite Union_spec in H2; destruct H2;
      [eapply aux23 | eapply aux22]; eauto; reflexivity.
    } Unfocus.
    rewrite (proj1 (proj2 PRE_si)) in H4.
    erewrite <- si_dst1 in H3 |- * by eauto.
    rewrite <- ECOPY_prv.
    apply guarded_pointwise_relation_weaken with (P2 := Union E PE3 PE1_root) in ECOPY_gpre.
    Focus 2. {
      apply Included_Complement_Disjoint.
      apply Union_left_Disjoint; split;
      [eapply aux10 | eapply aux11]; eauto; reflexivity.
    } Unfocus.
    rewrite guarded_pointwise_relation_spec in ECOPY_gpre.
    rewrite <- ECOPY_gpre by auto.
    rewrite PRE_consi by auto.
    pose proof pregraph_join_guarded_si _ _ _ _ ECOPY_pj.
    eapply guarded_si_weaken in H5; [| apply Included_refl |].
    Focus 2. {
      apply Included_Complement_Disjoint.
      destruct ECOPY_pj as [_ [? _]].
      eapply Prop_join_Disjoint; eauto.
    } Unfocus.
    assert (evalid g2' (emap g2 e)) by (apply (evalid_preserved PRE_bij); auto).
    eapply guarded_si_dst1; eauto.
  + subst e.
    apply H1.
Qed.

Lemma triple4_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (M: V -> Prop) root es es_done e0 es_later,
  let M0 := Union _ M (eq root) in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  guarded_pointwise_relation (Complement V (reachable_by g root (Complement _ M))) eq (vmap g) (vmap g2) ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  guarded_pointwise_relation (Complement V (reachable_by g root (Complement _ M))) eq (vmap g) (vmap g3).
Proof.
  intros until es_later.
  intros H_VVALID H_P P0 H_OUT_EDGES H_ES PRE_gpr ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre
                     [? [? [? ?]]]]]].
  transitivity (vmap g2); auto.
  eapply guarded_pointwise_relation_pointwise_relation; auto.
Qed.

Lemma triple5_ecopy1: forall (g g2 g3: Graph) (g2' g3': Graph') (M: V -> Prop) root es es_done e0 es_later,
  let PV := reachable_by g root (Complement _ M) in
  let PE := Intersection E (weak_edge_prop PV g) (evalid g) in
  let M0 := Union _ M (eq root) in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  es = es_done ++ e0 :: es_later ->
  g ~=~ g2 /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g2) ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g3).
Proof.
  intros until es_later.
  intros PV PE M0 H_VVALID H_P H_OUT_EDGES H_ES [PRE_si PRE_gpr] ECOPY.
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

Lemma triple6_ecopy1: forall (g g2 g3: Graph) (g' g2' g3': Graph') (M: V -> Prop) root es es_done e0 es_later,
  let M0 := Union _ M (eq root) in
  let PE1_root e := In e es_done in
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) (Complement _ M0) in
  let PE3 := Intersection _ (weak_edge_prop PV3 g) (evalid g) in
  let PE3_root e := In e (es_done ++ e0 :: nil) in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  Same_set (vvalid g2') (image_set (Union _ PV3 (eq root)) (vmap g2)) /\
  Same_set (evalid g2') (image_set (Union _ PE3 PE1_root) (emap g2)) /\
  g ~=~ g2 ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  Same_set (vvalid g3') (image_set (Union _ PV3 (eq root)) (vmap g3)) /\
  Same_set (evalid g3') (image_set (Union _ PE3 PE3_root) (emap g3)).
Proof.
  intros until es_later.
  intros ? ? ? ? ?.
  intros H_VVALID H_P H_OUT_EDGES H_NODUP H_ES [PRE_vvalid [PRE_evalid PRE_si]] ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre [? [ECOPY_pj [? ?]]]]]].

  apply guarded_pointwise_relation_pointwise_relation with (P := Union V PV3 (eq root)) in ECOPY_prv.
  rewrite ECOPY_prv in PRE_vvalid.
  apply guarded_pointwise_relation_weaken with (P2 := Union E PE3 PE1_root) in ECOPY_gpre.
  Focus 2. {
    apply Included_Complement_Disjoint.
    apply Union_left_Disjoint; split.
    + eapply aux10; eauto; reflexivity.
    + eapply aux11; eauto; reflexivity.
  } Unfocus.
  rewrite ECOPY_gpre in PRE_evalid.
  
  split.
  + rewrite !Same_set_spec.
    intro v'.
    destruct ECOPY_pj as [[? _] _].
    rewrite H2.
    rewrite (PRE_vvalid v').
    tauto.
  + erewrite (aux20 e0 PE1_root PE3 PE3_root) by (eauto; reflexivity).
    rewrite image_Union, image_single.
    rewrite !Same_set_spec.
    intro e'.
    destruct ECOPY_pj as [_ [[? _] _]].
    rewrite H2.
    rewrite (PRE_evalid e').
    rewrite Union_spec.
    tauto.
Qed.

Lemma triple_loop: forall (g g1 g3: Graph) (g1' g3': Graph') (M: V -> Prop) root es es_done e0 es_later,
  let PV := reachable_by g root (Complement _ M) in
  let PE := Intersection E (weak_edge_prop PV g) (evalid g) in
  vvalid g root ->
  ~ M root ->
  let M0 := Union _ M (eq root) in
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  (forall v, M v \/ ~ M v) ->
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  guarded_bij (Union _ PV1 (eq root)) (Union _ PE1 PE1_root) (vmap g1) (emap g1) g1 g1' /\
  g ~=~ g1 /\
  (forall e, Union _ PE1 PE1_root e -> Complement _ (Union _ PV1 (eq root)) (dst g1 e) -> vmap g1 (dst g1 e) = dst g1' (emap g1 e)) /\
  guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g1) /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g1) /\
  Same_set (vvalid g1') (image_set (Union _ PV1 (eq root)) (vmap g1)) /\
  Same_set (evalid g1') (image_set (Union _ PE1 PE1_root) (emap g1)) ->
  let M_rec := Union _ M0 PV1 in
  let PV0 := reachable_by g (dst g e0) (Complement _ M_rec) in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  edge_copy g root M (es_done, e0) (g1, g1') (g3, g3') ->
  let PV3 := reachable_by_through_set g (map (dst g) (es_done ++ e0 :: nil)) (Complement _ M0) in
  let PE3 := Intersection _ (weak_edge_prop PV3 g) (evalid g) in
  let PE3_root e := In e (es_done ++ e0 :: nil) in
  guarded_bij (Union _ PV3 (eq root)) (Union _ PE3 PE3_root) (vmap g3) (emap g3) g3 g3' /\
  g ~=~ g3 /\
  (forall e, Union _ PE3 PE3_root e -> Complement _ (Union _ PV3 (eq root)) (dst g3 e) -> vmap g3 (dst g3 e) = dst g3' (emap g3 e)) /\
  guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g3) /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g3) /\
  Same_set (vvalid g3') (image_set (Union _ PV3 (eq root)) (vmap g3)) /\
  Same_set (evalid g3') (image_set (Union _ PE3 PE3_root) (emap g3)).
Proof.
  intros.
  unfold edge_copy in H6.
  destruct_relation_list p in H6; destruct p as [g2 g2'].
  rename H7 into COPY.
  rename H6 into ECOPY.

  assert
   (guarded_bij (Union _ PV3 (eq root)) (Union _ PE3 PE1_root) (vmap g2) (emap g2) g2 g2' /\
    g ~=~ g2 /\
    (forall e, Union _ PE3 PE1_root e -> Complement _ (Union _ PV3 (eq root)) (dst g2 e) -> vmap g2 (dst g2 e) = dst g2' (emap g2 e)) /\
    guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g2) /\
    guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g2) /\
    Same_set (vvalid g2') (image_set (Union _ PV3 (eq root)) (vmap g2)) /\
    Same_set (evalid g2') (image_set (Union _ PE3 PE1_root) (emap g2))) as PRE;
  [clear g3 g3' ECOPY; rename H5 into PRE | clear COPY H5].
  + split; [| split; [| split; [| split; [| split]]]].
    - eapply triple1_copy; eauto.
      tauto.
    - eapply triple2_copy; eauto.
      tauto.
    - eapply triple3_copy; eauto.
      tauto.
    - eapply triple4_copy; eauto.
      tauto.
    - eapply triple5_copy; eauto.
      tauto.
    - eapply triple6_copy; eauto.
      tauto.
  + split; [| split; [| split; [| split; [| split]]]].
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
Qed.

Lemma triple_final: forall (g g1: Graph) (g1': Graph') (M: V -> Prop) root es,
  let PV := reachable_by g root (Complement _ M) in
  let PE := Intersection E (weak_edge_prop PV g) (evalid g) in
  vvalid g root ->
  ~ M root ->
  let M0 := Union _ M (eq root) in
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  let PV1 := reachable_by_through_set g (map (dst g) es) (Complement _ M0) in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es in
  let g' := empty_pregraph (vmap g root) in
  guarded_bij (Union _ PV1 (eq root)) (Union _ PE1 PE1_root) (vmap g1) (emap g1) g1 g1' /\
  g ~=~ g1 /\
  (forall e, Union _ PE1 PE1_root e -> Complement _ (Union _ PV1 (eq root)) (dst g1 e) -> vmap g1 (dst g1 e) = dst g1' (emap g1 e)) /\
  guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g1) /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g1) /\
  Same_set (vvalid g1') (image_set (Union _ PV1 (eq root)) (vmap g1)) /\
  Same_set (evalid g1') (image_set (Union _ PE1 PE1_root) (emap g1)) ->
  copy M root g g1 g1'.
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
  destruct H3 as [?PRE [?PRE [?PRE [?PRE [?PRE ?PRE]]]]].
  assert (Same_set (reachable_by g root (Complement _ M)) (Union _ PV1 (eq root))).
  Focus 1. {
    rewrite Same_set_spec.
    intro v.
    erewrite reachable_by_ind_equiv by eauto.
    rewrite Union_spec, Intersection_Complement.
    tauto.
  } Unfocus.
  assert (Same_set (Intersection E (weak_edge_prop (reachable_by g root (Complement _ M)) g) (evalid g)) (Union _ PE1 PE1_root)).
  Focus 1. {
    rewrite Same_set_spec.
    intro e.
    rewrite Intersection_spec; unfold weak_edge_prop.
    erewrite reachable_by_ind_equiv by eauto.
    unfold PE1.
    rewrite Union_spec, Intersection_spec, Intersection_Complement.
    unfold weak_edge_prop, PV1, M0, PE1_root.
    rewrite H1.
    unfold out_edges.
    assert (root = src g e <-> src g e = root) by (split; intro; congruence).
    tauto.
  } Unfocus.
  unfold copy.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  + auto.
  + auto.
  + auto.
  + rewrite H3. tauto.
  + rewrite H5. tauto.
  + intros.
    rewrite (H5 e) in H6.
    apply PRE1; auto.
    generalize (dst g1 e), H7.
    apply Complement_Included_rev.
    rewrite <- H3.
    apply Included_refl.
  + rewrite H5, H3.
    auto.
Qed.

Lemma triple_vcopy1_edge_copy_list: forall (g g1 g2: Graph) g2' root es es_done es_later (M: V -> Prop),
  let g1' := single_vertex_pregraph (vmap g1 root) in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ es_later ->
  (forall v : V, M v \/ ~ M v) ->
  vcopy1 root g g1 ->
  edge_copy_list g root es_done M (g1, g1') (g2, g2') ->
  let PV := reachable_by g root (Complement _ M) in
  let PE := Intersection E (weak_edge_prop PV g) (evalid g) in
  let M0 := Union _ M (eq root) in
  let PV2 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  let PE2_root e := In e es_done in
  guarded_bij (Union _ PV2 (eq root)) (Union _ PE2 PE2_root) (vmap g2) (emap g2) g2 g2' /\
  g ~=~ g2 /\
  (forall e, Union _ PE2 PE2_root e -> Complement _ (Union _ PV2 (eq root)) (dst g2 e) -> vmap g2 (dst g2 e) = dst g2' (emap g2 e)) /\
  guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g2) /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g2) /\
  Same_set (vvalid g2') (image_set (Union _ PV2 (eq root)) (vmap g2)) /\
  Same_set (evalid g2') (image_set (Union _ PE2 PE2_root) (emap g2)).
Proof.
  intros.
  set (g' := empty_pregraph (vmap g root)).
  assert
   (let PV1 := reachable_by_through_set g (map (dst g) nil) (Complement _ M0) in
    let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
    let PE1_root e := In e nil in
    guarded_bij (Union _ PV1 (eq root)) (Union _ PE1 PE1_root) (vmap g1) (emap g1) g1 g1' /\
    g ~=~ g1 /\
    (forall e, Union _ PE1 PE1_root e -> Complement _ (Union _ PV1 (eq root)) (dst g1 e) -> vmap g1 (dst g1 e) = dst g1' (emap g1 e)) /\
    guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g1) /\
    guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g1) /\
    Same_set (vvalid g1') (image_set (Union _ PV1 (eq root)) (vmap g1)) /\
    Same_set (evalid g1') (image_set (Union _ PE1 PE1_root) (emap g1))).
  Focus 1. {
    pose proof triple_vcopy1 _ _ _ H H5.
    intros.
    assert (Same_set PV1 (Empty_set _)).
    Focus 1. {
      rewrite Same_set_spec; intro v.
      split; [intros [? [? ?]] | intros []].
      inv H8.
    } Unfocus.
    assert (Same_set PE1 (Empty_set _)).
    Focus 1. {
      rewrite Same_set_spec; intro v.
      split; [intro | intros []].
      unfold PE1 in H9; rewrite Intersection_spec in H9.
      destruct H9 as [[? [? ?]] ?].
      inv H9.
    } Unfocus.
    assert (Same_set PE1_root (Empty_set _)).
    Focus 1. {
      rewrite Same_set_spec; intro v.
      split; [intros [] | intros []].
    } Unfocus.
    split; [| split; [| split; [| split; [| split]]]].
    + rewrite H8, H9, H10.
      rewrite !Union_Empty_left.
      auto.
    + destruct H5; auto.
    + intros.
      rewrite Union_spec, (H9 e), (H10 e) in H11.
      inversion H11 as [[] | []].
    + destruct H5 as [_ [? _]].
      eapply guarded_pointwise_relation_weaken; [| exact H5].
      apply Complement_Included_rev.
      unfold Included, Ensembles.In; intros.
      subst x; unfold PV.
      apply reachable_by_refl; auto.
    + destruct H5 as [_ [_ ?]].
      eapply guarded_pointwise_relation_weaken; [| exact H5].
      apply Complement_Included_rev.
      unfold Included, Ensembles.In; intros.
      unfold PE; rewrite Intersection_spec in H11 |- *.
      split; [destruct H11 as [? _] | tauto].
      unfold weak_edge_prop in H11 |- *.
      rewrite <- H11.
      apply reachable_by_refl; auto.
    + split.
      - rewrite H8, Union_Empty_left, image_single.
        reflexivity.
      - rewrite H9, H10, Union_Empty_left, image_Empty.
        simpl.
        rewrite Same_set_spec; intro e.
        tauto.
  } Unfocus.
  clear H5.

  revert g2 g2' es_later H3 H6; rev_induction es_done; intros.
  + unfold edge_copy_list, relation_list in H6.
    simpl in H6.
    inversion H6; subst g2 g2'.
    auto.
  + clear H7.
    rewrite <- app_assoc in H5.
    unfold edge_copy_list in H6. rewrite combine_prefixes_app_1, map_app in H6; simpl in H6.
    apply (proj1 ((proj1 (same_relation_spec _ _) (relation_list_tail _ _)) _ _)) in H6.
    rename g2 into g3, g2' into g3'.
    apply compond_relation_spec in H6; destruct H6 as [[g2 g2'] [? ?]].

    eapply triple_loop; [auto | auto | eauto | auto | eauto | auto | ..].
    1: eapply H3; eauto.
    auto.
Qed.

Lemma vcopy1_edge_copy_list_copy: forall (g g1 g2: Graph) g2' root es (M: V -> Prop),
  let g1' := single_vertex_pregraph (vmap g1 root) in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  (forall v : V, M v \/ ~ M v) ->
  vcopy1 root g g1 ->
  edge_copy_list g root es M (g1, g1') (g2, g2') ->
  copy M root g g2 g2'.
Proof.
  intros.
  pose proof triple_vcopy1_edge_copy_list g g1 g2 g2' root es es nil M H H0 H1 H2 (eq_sym (app_nil_r _)) H3 H4 H5.
  apply triple_final with (es := es); auto.
Qed.

Lemma vcopy1_edge_copy_list_extend_copy: forall (g g1 g2 g3: Graph) g2' g' root es es_done e0 es_later (M: V -> Prop),
  let g1' := single_vertex_pregraph (vmap g1 root) in
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  (forall v : V, M v \/ ~ M v) ->
  vcopy1 root g g1 ->
  edge_copy_list g root es_done M (g1, g1') (g2, g2') ->
  let M0 := Union _ M (eq root) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  let M_rec := Union _ M0 PV1 in
  let PV0 := reachable_by g (dst g e0) (Complement _ M_rec) in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  copy M_rec (dst g e0) g2 g3 g' ->
  disjointed_guard
    (image_set (Union V PV1 (eq root))(vmap g2)) (image_set PV0 (vmap g3))
    (image_set (Union E PE1 PE1_root) (emap g2)) (image_set PE0 (emap g3)) ->
  (forall v, M_rec v \/ ~ M_rec v) ->
  exists g3': Graph',
  extended_copy M_rec (dst g e0) (g2, g2') (g3, g3') /\
  (predicate_partialgraph g2' (image_set PV1 (vmap g2))) ~=~
  (predicate_partialgraph g3' (image_set PV1 (vmap g3))) /\
  (predicate_partialgraph g' (image_set PV0 (vmap g3))) ~=~
  (predicate_partialgraph g3' (image_set PV0 (vmap g3))).
(*
  (gpredicate_subgraph (image_set PV1 (vmap g2)) (image_set PE1 (emap g2)) g2') ~=~
  (gpredicate_subgraph (image_set PV1 (vmap g3)) (image_set PE1 (emap g3)) g3') /\
  (gpredicate_subgraph (image_set PV0 (vmap g3)) (image_set PE0 (emap g3)) g') ~=~
  (gpredicate_subgraph (image_set PV0 (vmap g3)) (image_set PE0 (emap g3)) g3').
*)
Proof.
  intros.
  pose proof triple_vcopy1_edge_copy_list g g1 g2 g2' root es es_done (e0 :: es_later) M H H0 H1 H2 H3 H4 H5 H6.
  
  destruct H10 as [PRE_bij [PRE_si [PRE_consi [PRE_gprv [PRE_gpre [PRE_vvalid PRE_evalid]]]]]].
  destruct H7 as [COPY_si [COPY_gprv [COPY_gpre [COPY_vvalid [COPY_evalid [COPY_consi COPY_bij]]]]]].
  pose proof (fun H => guarded_pointwise_relation_weaken _ (Union _ PV1 (eq root)) eq H _ _ COPY_gprv) as COPY_gprv'.
  spec COPY_gprv'.
  Focus 1. {
    apply Included_Complement_Disjoint.
    rewrite <- PRE_si.
    apply Union_left_Disjoint; split.
    + eapply aux06; eauto; reflexivity.
    + eapply aux08; try reflexivity; eassumption.
  } Unfocus.
  pose proof (fun H => guarded_pointwise_relation_weaken _ (Union _ PE1 PE1_root) eq H _ _ COPY_gpre) as COPY_gpre'.
  spec COPY_gpre'.
  Focus 1. {
    apply Included_Complement_Disjoint.
    rewrite <- PRE_si at 1.
    rewrite <- weak_edge_prop_si by (exact PRE_si).
    apply Union_left_Disjoint; split.
    + eapply aux07; eauto; reflexivity.
    + eapply aux09; try eassumption; reflexivity.
  } Unfocus.
  assert
   (exists G',
      guarded_bij (Union V (Union V PV1 (eq root)) PV0)
        (Union E (Union E PE1 PE1_root) PE0) (vmap g3) 
        (emap g3) g3 G' /\
      pregraph_join (image_set PV0 (vmap g3)) (image_set PE0 (emap g3))
        g2' G' /\
      pregraph_join (image_set (Union V PV1 (eq root)) (vmap g3))
        (image_set (Union E PE1 PE1_root) (emap g3)) g' G').
  Focus 1. {
    apply (guarded_bij_pregraph_join (Union _ PV1 (eq root)) (Union _ PE1 PE1_root) PV0 PE0 (vmap g3) (emap g3) g3 g2' g').
    + destruct H8; split.
      - rewrite COPY_gprv' in H7; auto.
      - rewrite COPY_gpre' in H8; auto.
    + apply si_guarded_si with (PV := Union _ PV1 (eq root)) (PE := Union _ PE1 PE1_root) in COPY_si.
      rewrite <- COPY_si.
      rewrite <- COPY_gprv'.
      rewrite <- COPY_gpre'.
      auto.
    + rewrite <- PRE_si in COPY_bij at 1 2.
      rewrite <- weak_edge_prop_si in COPY_bij by (exact PRE_si).
      auto.
    + split; intros.
      - exfalso.
        rewrite COPY_si in PRE_si.
        rewrite <- si_src2 with (g4 := g) in H10 by auto.
        rewrite Union_spec in H7; destruct H7.
        * eapply aux12; eauto; reflexivity.
        * eapply aux15; [eassumption | reflexivity | reflexivity | reflexivity | reflexivity |  eassumption | eauto | eauto | eauto ]. 
      - exfalso.
        rewrite COPY_si in PRE_si.
        rewrite <- si_dst2 with (g4 := g) in H10 by auto.
        rewrite Union_spec in H7; destruct H7.
        * eapply aux13; eauto; reflexivity.
        * eapply aux16; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact H4 | eassumption | eauto | eauto].
    + split; intros.
      - exfalso.
        rewrite COPY_si in PRE_si.
        rewrite <- si_src2 with (g4 := g) in H10 by auto.
        rewrite Union_spec in H10; destruct H10.
        * eapply aux14; eauto; reflexivity.
        * eapply aux17; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | eauto | eauto | eauto].
      - apply COPY_consi.
        * eapply app_same_set; [| exact H7].
          rewrite <- PRE_si at 1.
          rewrite <- weak_edge_prop_si by (exact PRE_si).
          reflexivity.
        * generalize (dst g3 e), H10.
          unfold not; apply Disjoint_spec.
          rewrite <- PRE_si.
          apply Union_left_Disjoint; split.
          1: eapply aux06; eauto; reflexivity.
          1: eapply aux08; eauto; reflexivity.
    + rewrite <- COPY_gprv'.
      auto.
    + rewrite <- COPY_gpre'.
      auto.
    + rewrite <- PRE_si in COPY_vvalid.
      auto.
    + rewrite <- PRE_si in COPY_evalid at 1.
      rewrite <- weak_edge_prop_si in COPY_evalid by exact PRE_si.
      auto.
  } Unfocus.
  destruct H7 as [g3' [? [? ?]]].
  (* clear H7. pose proof I as H7. *)
  exists g3'.
  split; [split; [| split; [| split; [| split; [| split; [| split]]]]] | split]; auto.
  + rewrite <- PRE_si at 1 2.
    rewrite <- weak_edge_prop_si by exact PRE_si.
    auto.
  + intros.
    replace (dst g3' (emap g3 e)) with (dst g' (emap g3 e)).
    1: apply COPY_consi; auto.
    assert (evalid g' (emap g3 e)).
    Focus 1. {
      apply (evalid_preserved COPY_bij); auto.
      rewrite <- (proj1 (proj2 COPY_si)).
      rewrite Intersection_spec in H12; tauto.
    } Unfocus.
    assert (evalid g3' (emap g3 e)).
    Focus 1. {
      destruct H11 as [_ [[? _] _]].
      rewrite H11.
      tauto.
    } Unfocus.
    apply (proj2 (proj2 (proj2 H11))); auto.
  + rewrite <- PRE_si at 1 2.
    rewrite <- weak_edge_prop_si by exact PRE_si.
    fold PV0 PE0.
    apply pregraph_join_guarded_si in H11.
    apply guarded_si_weaken with (PV3 := image_set PV0 (vmap g3)) (PE3 := image_set PE0 (emap g3)) in H11.
    - rewrite <- H11.
      rewrite <- PRE_si in COPY_bij at 1 2.
      rewrite <- weak_edge_prop_si in COPY_bij by exact PRE_si.
      auto.
    - apply Included_Complement_Disjoint, Disjoint_comm.
      destruct H8; auto.
      rewrite <- COPY_gprv' at 1.
      auto.
    - apply Included_Complement_Disjoint, Disjoint_comm.
      destruct H8; auto.
      rewrite <- COPY_gpre' at 1.
      auto.
  + apply guarded_pointwise_relation_weaken with (P2 := PV1) in COPY_gprv';
      [| apply left_Included_Union].
    rewrite COPY_gprv' at 1.
    eapply pregraph_join_partial_si; [exact H10 | ..].
    - destruct H10 as [? _].
      rewrite PRE_vvalid in H10.
      destruct H10 as [_ ?].
      apply Disjoint_spec; intros v' ? ?; apply (H10 v'); auto.
      erewrite app_same_set; [| apply image_Union].
      erewrite app_same_set; [| fold M0 PV1; rewrite COPY_gprv' at 1; reflexivity].
      generalize v', H13.
      apply left_Included_Union.
    - intros e' ? ? ?.
      unfold PE0 in H12.
      rewrite COPY_si in PRE_si.
      erewrite app_same_set in H12 by 
      (erewrite weak_edge_prop_si by (exact PRE_si); reflexivity).
      eapply @guarded_bij_weak_edge_prop in H12; [| | | apply bij_is_morphism in H7; exact H7].
      * rewrite Intersection_spec in H12.
        destruct H12.
        destruct H8 as [? _].
        rewrite image_Union, Union_left_Disjoint in H8; destruct H8 as [? _].
        rewrite COPY_gprv' in H8.
        rewrite Disjoint_spec in H8.
        exact (H8 _ H14 H12).
      * apply right_Included_Union.
      * erewrite <- weak_edge_prop_si by (exact PRE_si).
        apply right_Included_Union.
  + eapply pregraph_join_partial_si; [exact H11 | ..].
    

End LocalGraphCopy.

End LocalGraphCopy.