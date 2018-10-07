Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Morphisms_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas. Import RamifyCoq.graph.path_lemmas.PathNotation.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_morphism.

Class GraphMorphismSetting (DV DE DG V' E' DV' DE' DG': Type): Type := {
  co_vertex: DV -> V';
  co_edge: DE -> E';
  default_DV': DV';
  default_DE': DE';
  default_DG': DG'
}.

Module LocalGraphCopy.

Section LocalGraphCopy.

Import GraphMorphism.

Context {V E V' E': Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {EV': EqDec V' eq}.
Context {EE': EqDec E' eq}.
Context {DV DE DG DV' DE' DG': Type}.

Context {GMS: GraphMorphismSetting DV DE DG V' E' DV' DE' DG'}.

Notation Graph := (LabeledGraph V E DV DE DG).
Notation Graph' := (LabeledGraph V' E' DV' DE' DG').
Local Coercion pg_lg : LabeledGraph >-> PreGraph.

Definition vmap (g: Graph): V -> V' := fun v => co_vertex (vlabel g v).

Definition emap (g: Graph): E -> E' := fun e => co_edge (elabel g e).

Definition vcopy1 root (g1 g2: Graph) (g2': Graph') :=
  let PV_root := eq root in
  let PE_root := Intersection _ (weak_edge_prop PV_root g1) (evalid g1) in
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ PV_root) eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ PE_root) eq (emap g1) (emap g2) /\
  g2' = single_vertex_labeledgraph (vmap g2 root) default_DV' default_DE' default_DG'.

Definition ecopy1 e (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  pointwise_relation V eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ (eq e)) eq (emap g1) (emap g2) /\
  pregraph_join (Empty_set _) (eq (emap g2 e)) g1' g2' /\
  (vvalid g1 (src g2 e) -> vmap g2 (src g2 e) = src g2' (emap g2 e)) /\
  (vvalid g1 (dst g2 e) -> vmap g2 (dst g2 e) = dst g2' (emap g2 e)).

Definition copy (M: V -> Prop) root (g1 g2: Graph) (g2': Graph') :=
  let PV := reachable_by g1 root (Complement _ M) in
  let PE := Intersection _ (weak_edge_prop PV g1) (evalid g1) in
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ PV) eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ PE) eq (emap g1) (emap g2) /\
  Same_set (vvalid g2') (image_set PV (vmap g2)) /\
  Same_set (evalid g2') (image_set PE (emap g2)) /\
  boundary_dst_consistent PE (Intersection _ (Complement _ PV) (vvalid g1)) (vmap g2) (emap g2) g2 g2' /\
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
  boundary_dst_consistent PE (Intersection _ (Complement _ PV) (vvalid g1)) (vmap g2) (emap g2) g2 g2' /\
  (forall v, M v \/ ~ M v) /\
  guarded_bij PV PE (vmap g2) (emap g2) g2 g2'.

Definition edge_copy (g: Graph) (root: V) (M: V -> Prop) (l: list E * E) :=
  let (es_done, e0) := l in
  let M0 := Union _ M (eq root) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let M_rec := Union _ M0 PV1 in
  relation_list (extended_copy M_rec (dst g e0) :: ecopy1 e0 :: nil).

Definition edge_copy_list (g: Graph) (root: V) es (P: V -> Prop) :=
  relation_list (map (edge_copy g root P) (cprefix es)).

Instance copy_proper: Proper (Same_set ==> eq ==> eq ==> eq ==> eq ==> iff) copy.
Proof.
  hnf; intros M1 M2 ?.
  hnf; intros root root' ?; subst root'.
  hnf; intros g1 g1_ ?; subst g1_.
  hnf; intros g2 g2_ ?; subst g2_.
  hnf; intros g2' g2'_ ?; subst g2'_.
  unfold copy.
  rewrite H.
  tauto.
Qed.
Global Existing Instance copy_proper.

Instance extended_copy_proper: Proper (Same_set ==> eq ==> eq ==> eq ==> iff) extended_copy.
Proof.
  hnf; intros M1 M2 ?.
  hnf; intros root root' ?; subst root'.
  intros [g1 g1'] ? ? [g2 g2'] ? ?; subst.
  unfold extended_copy.
  rewrite H.
  assert ((forall v : V, M1 v \/ ~ M1 v) <-> (forall v : V, M2 v \/ ~ M2 v)).
  1: {
    rewrite Same_set_spec in H.
    hnf in H; clear - H.
    firstorder.
  }
  tauto.
Qed.
Global Existing Instance extended_copy_proper.

Instance extended_copy_proper': Proper (Same_set ==> eq ==> same_relation (Graph * Graph')) extended_copy.
Proof.
  hnf; intros M1 M2 ?.
  hnf; intros root root' ?; subst root'.
  rewrite same_relation_spec.
  intros [g1 g1'] [g2 g2'].
  unfold extended_copy.
  rewrite H.
  assert ((forall v : V, M1 v \/ ~ M1 v) <-> (forall v : V, M2 v \/ ~ M2 v)).
  1: {
    rewrite Same_set_spec in H.
    hnf in H; clear - H.
    firstorder.
  }
  tauto.
Qed.
Global Existing Instance extended_copy_proper'.

Lemma vcopy1_copied_root_valid: forall (G G1: Graph) (G1': Graph') x x0,
  vcopy1 x G G1 G1' ->
  x0 = vmap G1 x ->
  vvalid G1' x0.
Proof.
  intros.
  destruct H as [? [? [? ?]]].
  subst.
  simpl.
  auto.
Qed.

Lemma extended_copy_vvalid_mono: forall (G1 G2: Graph) (G1' G2': Graph') M x x0,
  extended_copy M x (G1, G1') (G2, G2') ->
  vvalid G1' x0 ->
  vvalid G2' x0.
Proof.
  intros.
  destruct H as [_ [_ [_ [? _]]]].
  eapply pregraph_join_vvalid_mono; eauto.
Qed.

Lemma ecopy1_vvalid_mono: forall (G1 G2: Graph) (G1' G2': Graph') e x0,
  ecopy1 e (G1, G1') (G2, G2') ->
  vvalid G1' x0 ->
  vvalid G2' x0.
Proof.
  intros.
  destruct H as [_ [_ [_ [? _]]]].
  eapply pregraph_join_vvalid_mono; eauto.
Qed.

Lemma edge_copy_vvalid_mono: forall (G1 G2: Graph) (G1' G2': Graph') g root M es_done e0 x0,
  edge_copy g root M (es_done, e0) (G1, G1') (G2, G2') ->
  vvalid G1' x0 ->
  vvalid G2' x0.
Proof.
  intros.
  unfold edge_copy in H.
  destruct_relation_list GG0 in H; destruct GG0 as [G G'].
  eapply ecopy1_vvalid_mono; eauto.
  eapply extended_copy_vvalid_mono; eauto.
Qed.

Lemma edge_copy_list_vvalid_mono: forall (G1 G2: Graph) (G1' G2': Graph') g root es P x0,
  edge_copy_list g root es P (G1, G1') (G2, G2') ->
  vvalid G1' x0 ->
  vvalid G2' x0.
Proof.
  intros.
  revert G2 G2' H; rev_induction es.
  + unfold edge_copy_list, relation_list in H; simpl in H.
    inversion H; subst; auto.
  + unfold edge_copy_list in H1; rewrite combine_prefixes_app_1, map_app in H1; simpl in H1.
    apply (proj1 ((proj1 (same_relation_spec _ _) (relation_list_tail _ _)) _ _)) in H1.
    apply compond_relation_spec in H1. destruct H1 as [[G G'] [? ?]].
    eapply (edge_copy_vvalid_mono G G2 G' G2' g); [exact H2 |].
    eapply H; eauto.
Qed.

Lemma labeledgraph_vgen_vcopy1: forall (G: Graph) x x0,
  vcopy1 x G (labeledgraph_vgen G x x0) (single_vertex_labeledgraph (vmap (labeledgraph_vgen G x x0) x) default_DV' default_DE' default_DG') /\ co_vertex x0 = vmap (labeledgraph_vgen G x x0) x.
Proof.
  intros.
  split.
  + split; [| split; [| split]].
    - reflexivity.
    - apply guarded_pointwise_relation_spec; intros.
      simpl.
      unfold labeledgraph_vgen, update_vlabel, vmap; simpl.
      destruct_eq_dec x x1; [congruence | auto].
    - apply guarded_pointwise_relation_spec; intros.
      auto.
    - reflexivity.
  + simpl.
    unfold labeledgraph_vgen, update_vlabel, vmap; simpl.
    destruct_eq_dec x x; [auto | congruence].
Qed.

Lemma labeledgraph_egen_ecopy1: forall (g1: Graph) (g1': Graph') e e' src' dst',
  ~ evalid g1' (co_edge e') ->
  src' = vmap g1 (src g1 e) ->
  dst' = vmap g1 (dst g1 e) ->
  ecopy1 e (g1, g1') (labeledgraph_egen g1 e e', labeledgraph_add_edge g1' (co_edge e') src' dst' default_DE').
Proof.
  intros ? ? ? ? ? ? HH0 ? ?.
  subst src' dst'.
  split; [| split; [| split; [| split; [| split]]]].
  + reflexivity.
  + intros v; reflexivity.
  + rewrite guarded_pointwise_relation_spec; intros.
    unfold emap, labeledgraph_egen, update_elabel; simpl.
    destruct_eq_dec e x; auto.
    unfold Complement, Ensembles.In in H; congruence.
  + split; [| split; [| split]]; simpl.
    - apply Prop_join_Empty.
    - unfold emap, labeledgraph_egen, update_elabel, addValidFunc; simpl.
      destruct_eq_dec e e; [| congruence].
      apply Prop_join_x1; auto.
    - unfold emap, labeledgraph_egen, updateEdgeFunc, addValidFunc; simpl.
      intros.
      destruct_eq_dec (co_edge e') e0; auto.
      subst; exfalso; auto.
    - unfold emap, labeledgraph_egen, updateEdgeFunc, addValidFunc; simpl.
      intros.
      destruct_eq_dec (co_edge e') e0; auto.
      subst; exfalso; auto.
  + simpl.
    unfold vmap, emap, labeledgraph_egen, updateEdgeFunc, update_elabel; simpl.
    destruct_eq_dec e e; [| congruence].
    destruct_eq_dec (co_edge e') (co_edge e'); [| congruence].
    auto.
  + simpl.
    unfold vmap, emap, labeledgraph_egen, updateEdgeFunc, update_elabel; simpl.
    destruct_eq_dec e e; [| congruence].
    destruct_eq_dec (co_edge e') (co_edge e'); [| congruence].
    auto.
Qed.

Lemma labeledgraph_egen_ecopy1_not_vvalid: forall (g1: Graph) (g1': Graph') e e' src' dst',
  ~ evalid g1' (co_edge e') ->
  src' = vmap g1 (src g1 e) ->
  ~ vvalid g1' dst' ->
  ~ vvalid g1 (dst g1 e) ->
  ecopy1 e (g1, g1') (labeledgraph_egen g1 e e', labeledgraph_add_edge g1' (co_edge e') src' dst' default_DE').
Proof.
  intros ? ? ? ? ? ? HH0 HH1 HH2 HH3.
  subst src'.
  split; [| split; [| split; [| split; [| split]]]].
  + reflexivity.
  + intros v; reflexivity.
  + rewrite guarded_pointwise_relation_spec; intros.
    unfold emap, labeledgraph_egen, update_elabel; simpl.
    destruct_eq_dec e x; auto.
    unfold Complement, Ensembles.In in H; congruence.
  + split; [| split; [| split]]; simpl.
    - apply Prop_join_Empty.
    - unfold emap, labeledgraph_egen, update_elabel, addValidFunc; simpl.
      destruct_eq_dec e e; [| congruence].
      apply Prop_join_x1; auto.
    - unfold emap, labeledgraph_egen, updateEdgeFunc, addValidFunc; simpl.
      intros.
      destruct_eq_dec (co_edge e') e0; auto.
      subst; exfalso; auto.
    - unfold emap, labeledgraph_egen, updateEdgeFunc, addValidFunc; simpl.
      intros.
      destruct_eq_dec (co_edge e') e0; auto.
      subst; exfalso; auto.
  + simpl.
    unfold vmap, emap, labeledgraph_egen, updateEdgeFunc, update_elabel; simpl.
    destruct_eq_dec e e; [| congruence].
    destruct_eq_dec (co_edge e') (co_edge e'); [| congruence].
    auto.
  + simpl; intros.
    exfalso; auto.
Qed.

Lemma triple_vcopy1: forall (g1 g2: Graph) (g2': Graph') root,
  vvalid g1 root ->
  vcopy1 root g1 g2 g2' ->
  guarded_bij (eq root) (Empty_set _) (vmap g2) (emap g2) g2 g2'.
Proof.
  intros g1 g2 g2' root ? [VCOPY_si [VCOPY_gprv [VCOPY_gpre ?]]].
  subst g2'.
  split; [.. | split]; intros.
  + apply is_guarded_inj_single.
  + apply is_guarded_inj_empty.
  + subst v.
    unfold single_vertex_labeledgraph, single_vertex_pregraph; simpl.
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
  pose proof PV1_DEC.
  clear -H.
  firstorder;
  constructor.
Qed.

Lemma aux01: Same_set PV3 (Union _ PV1 PV0).
Proof.
  clear PE1 PE3 PE0 H_PE1 H_PE3 H_PE0.
  intros.
  rewrite H_PV0, H_Mrec, H_PV3.
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
  rewrite H_Mrec in *.
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

Lemma aux24: forall v, vvalid g root -> Union _ PV1 (eq root) v -> vvalid g v.
Proof.
  clear - H_PV1.
  intros.
  subst PV1; rewrite Union_spec in H0; destruct H0.
  + apply reachable_by_through_set_foot_valid in H0; eassumption.
  + subst; assumption.
Qed.

Lemma aux25: forall v, vvalid g root -> Union _ PV3 (eq root) v -> vvalid g v.
Proof.
  clear - H_PV3.
  intros.
  subst PV3; rewrite Union_spec in H0; destruct H0.
  + apply reachable_by_through_set_foot_valid in H0; eassumption.
  + subst; assumption.
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
       vvalid g (dst g2 e) ->
       vmap g2 (dst g2 e) = dst g2' (emap g2 e).
Proof.
  intros.
  destruct H0 as [COPY_si [COPY_gprv [COPY_gpre [? [? COPY_bij]]]]].
  apply H4.
  + pose proof weak_edge_prop_si (reachable_by g1 son (Complement _ (Union _ M0 PV1))) _ _ H.
    rewrite <- H in H5 at 1.
    rewrite Same_set_spec in H5.
    rewrite <- (H5 e); auto.
  + rewrite <- H in COPY_si.
    rewrite Intersection_spec in H1; destruct H1.
    erewrite si_dst1 in H2 by eauto.
    unfold Complement, Ensembles.In.
    rewrite Intersection_spec; split.
    - rewrite <- H.
      auto.
    - rewrite <- (proj1 H); auto.
  + rewrite <- H in COPY_si.
    destruct COPY_si as [_ [? _]].
    rewrite Intersection_spec in H1.
    destruct H1 as [_ ?].
    rewrite <- H5; auto.
Qed.

Lemma copy_invalid_refl: forall (g: Graph) M root (src0 dst0: E' -> V'),
  ~ vvalid g root ->
  copy M root g g (empty_labeledgraph src0 dst0 default_DV' default_DE' default_DG').
Proof.
  intros.
  unfold copy.
  assert (Same_set (reachable_by g root (Complement V M)) (Empty_set _)).
  1: {
    rewrite Same_set_spec; intros ?.
    rewrite Empty_set_spec.
    pose proof reachable_by_head_valid g root a (Complement V M); tauto.
  }
  rewrite H0.
  rewrite weak_edge_prop_Empty, Intersection_Empty_left.
  rewrite !image_Empty.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + simpl.
    rewrite Same_set_spec; intros ?.
    rewrite Empty_set_spec; tauto.
  + simpl.
    rewrite Same_set_spec; intros ?.
    rewrite Empty_set_spec; tauto.
  + simpl.
    intros ? ? ? ?.
    inversion H1.
  + simpl.
    apply guarded_bij_empty_empty.
Qed.

Lemma copy_marked_root_refl: forall (g: Graph) (M: V -> Prop) root (src0 dst0: E' -> V'),
  M root ->
  copy M root g g (empty_labeledgraph src0 dst0 default_DV' default_DE' default_DG').
Proof.
  intros.
  unfold copy.
  assert (Same_set (reachable_by g root (Complement V M)) (Empty_set _)).
  1: {
    rewrite Same_set_spec; intros ?.
    rewrite Empty_set_spec.
    pose proof reachable_by_head_prop g root a (Complement V M).
    unfold Complement at 2, Ensembles.In in H0.
    tauto.
  }
  rewrite H0.
  rewrite weak_edge_prop_Empty, Intersection_Empty_left.
  rewrite !image_Empty.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + simpl.
    rewrite Same_set_spec; intros ?.
    rewrite Empty_set_spec; tauto.
  + simpl.
    rewrite Same_set_spec; intros ?.
    rewrite Empty_set_spec; tauto.
  + simpl.
    intros ? ? ? ?.
    inversion H1.
  + simpl.
    apply guarded_bij_empty_empty.
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
       vvalid g (dst g2 e) ->
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
  2: {
    apply Included_Complement_Disjoint.
    apply Union_left_Disjoint.
    split; [eapply (aux06 PV1 PV0) | eapply (aux08 root PV0)];
    first [eassumption | reflexivity].
  }

  apply guarded_pointwise_relation_weaken with (P2 := Union E PE1 PE1_root) in COPY_gpre.
  2: {
    apply Included_Complement_Disjoint.
    apply Union_left_Disjoint.
    split; [eapply (aux07 PE1 PE0) | eapply (aux09 PE1_root PE0)];
    first [eassumption | reflexivity].
  }
  rewrite COPY_gprv in PRE_bij, PRE_vvalid.
  rewrite COPY_gpre in PRE_bij, PRE_evalid.

  assert (guarded_bij PV0 PE0 (vmap g2) (emap g2) g g2').
  1: {
    eapply guarded_bij_proper_aux1; [| reflexivity | exact COPY_bij].
    apply si_guarded_si; symmetry; auto.
  }

  assert (guarded_bij (Union _ PV1 (eq root)) (Union _ PE1 PE1_root) (vmap g2) (emap g2) g2 g2').
  1: {
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
  }

  apply guarded_bij_disjointed_union; auto.
  + destruct COPY_pj as [? [? _]].
    apply Prop_join_Disjoint in H1.
    apply Prop_join_Disjoint in H2.
    rewrite PRE_vvalid in H1.
    rewrite PRE_evalid in H2.
    split; auto.
  + split; split; hnf; intros.
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
    - apply COPY_consi; [auto | | eapply aux24; eauto].
      erewrite <- si_dst2 in H2 by eauto.
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
  (forall e, Union _ PE1 PE1_root e -> Complement _ (Union _ PV1 (eq root)) (dst g1 e) -> vvalid g (dst g1 e) -> vmap g1 (dst g1 e) = dst g1' (emap g1 e)) ->
  extended_copy M_rec (dst g e0) (g1, g1') (g2, g2') ->
  (forall v, M v \/ ~ M v) -> (* From weak mark lemma *)
  (forall e, Union _ PE3 PE1_root e -> Complement _ (Union _ PV3 (eq root)) (dst g2 e) -> vvalid g (dst g2 e) ->vmap g2 (dst g2 e) = dst g2' (emap g2 e)).
Proof.
  intros until es_later.
  intros ? ? ? ? ? ? ? ? ?.
  intros H_VVALID H_P H_OUT_EDGES H_ES [PRE_bij [PRE_vvalid [PRE_evalid [PRE_si PRE_consi]]]] COPY M_DEC.

  assert (forall e,
       PE0 e ->
       ~ g |= dst g e0 ~o~> dst g e satisfying (Complement _ M_rec) ->
       vvalid g (dst g2 e) ->
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

  intros ? ? ? H_EXTRA.
  erewrite app_same_set in H by (eapply (aux19 PE1 PE1_root PE3 PE0); eauto; reflexivity).
  erewrite app_same_set in H0 by (erewrite (aux18 root PV1 PV3 PV0) by (eauto; reflexivity); reflexivity).
  erewrite app_same_set in H0 by (symmetry; apply Intersection_Complement).
  rewrite Intersection_spec in H0; destruct H0.
  rewrite Union_spec in H; destruct H.
  + assert (evalid g e).
    1: {
      rewrite Union_spec in H.
      destruct H; revert H; [eapply aux21 | eapply aux22]; eauto; reflexivity.
    }
    assert (vvalid g (dst g1 e)) as H_EXTRA'.
    1: {
      rewrite (proj1 (proj2 PRE_si)) in H2.
      rewrite (si_dst1 _ _ _ COPY_si) by auto.
      auto.
    }
    rewrite (proj1 (proj2 PRE_si)) in H2.
    erewrite <- si_dst1 in H0, H1 |- * by eauto.
    rewrite guarded_pointwise_relation_spec in COPY_gprv.
    rewrite <- COPY_gprv by auto.
    rewrite PRE_consi by auto.
    apply guarded_pointwise_relation_weaken with (P2 := Union E PE1 PE1_root) in COPY_gpre.
    2: {
      apply Included_Complement_Disjoint.
      apply Union_left_Disjoint; split.
      + eapply aux07; eauto; reflexivity.
      + eapply aux09; eauto; reflexivity.
    }
    rewrite guarded_pointwise_relation_spec in COPY_gpre.
    rewrite COPY_gpre by auto.
    pose proof pregraph_join_guarded_si _ _ _ _ COPY_pj.
    eapply guarded_si_weaken in H3; [| apply Included_refl |].
    2: {
      apply Included_Complement_Disjoint.
      destruct COPY_pj as [_ [? _]].
      eapply Prop_join_Disjoint; eauto.
    }
    assert (evalid g1' (emap g2 e)).
    1: {
      rewrite <- COPY_gpre by auto.
      apply (evalid_preserved PRE_bij); auto.
    }
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
  2: {
    apply Included_Complement_Disjoint.
    apply Union_left_Disjoint.
    split; [eapply (aux06 PV1 PV0) | eapply (aux08 root PV0)];
    first [eassumption | reflexivity].
  }

  apply guarded_pointwise_relation_weaken with (P2 := Union E PE1 PE1_root) in COPY_gpre.
  2: {
    apply Included_Complement_Disjoint.
    apply Union_left_Disjoint.
    split; [eapply (aux07 PE1 PE0) | eapply (aux09 PE1_root PE0)];
    first [eassumption | reflexivity].
  }
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
  2: {
    assert (In e0 es) by (rewrite H0, in_app_iff; simpl; tauto).
    rewrite H in H2.
    destruct H2; congruence.
  }
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
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre [ECOPY_pj [? ?]]]]].
  apply guarded_pointwise_relation_pointwise_relation with (P := Union V PV3 (eq root)) in ECOPY_prv.
  apply guarded_pointwise_relation_weaken with (P2 := Union E PE3 PE1_root) in ECOPY_gpre.
  2: {
    apply Included_Complement_Disjoint.
    apply Union_left_Disjoint; split.
    + eapply aux10; eauto; reflexivity.
    + eapply aux11; eauto; reflexivity.
  }
  rewrite ECOPY_prv in PRE_vvalid, PRE_bij.
  rewrite ECOPY_gpre in PRE_evalid, PRE_bij.
  rewrite <- (Union_Empty_right (Union V PV3 (eq root))).
  erewrite (aux20 e0 PE1_root PE3 PE3_root) by (eauto; reflexivity).
  apply guarded_bij_disjointed_union.
  + split.
    - rewrite image_Empty.
      apply Disjoint_Empty_set_right.
    - destruct ECOPY_pj as [_ [? _]].
      apply Prop_join_Disjoint in H1.
      rewrite PRE_evalid in H1.
      rewrite image_single; auto.
  + eapply guarded_bij_proper_aux1; [apply si_guarded_si, ECOPY_si | | exact PRE_bij].
    pose proof  pregraph_join_guarded_si _ _ _ _ ECOPY_pj.
    eapply guarded_si_weaken; [| | exact H1].
    1: rewrite Complement_Empty_set; apply Included_Full_set.
    apply Included_Complement_Disjoint.
    destruct ECOPY_pj as [_ [? _]].
    apply Prop_join_Disjoint in H2.
    rewrite PRE_evalid in H2.
    auto.
  + split; [.. | split]; intros.
    - apply is_guarded_inj_empty.
    - apply is_guarded_inj_single.
    - inversion H1.
    - subst e.
      assert (evalid g3 e0).
      1: {
        assert (In e0 es) by (rewrite H_ES, in_app_iff; simpl; tauto).
        rewrite H_OUT_EDGES in H1.
        destruct H1 as [? _].
        rewrite <- PRE_si in ECOPY_si.
        rewrite <- (proj1 (proj2 ECOPY_si)); auto.
      }
      assert (evalid g3' (emap g3 e0)).
      1: {
        destruct ECOPY_pj as [_ [[? _] _]].
        specialize (H2 (emap g3 e0)).
        tauto.
      }
      tauto.
    - inversion H2.
    - inversion H2.
  + split; split; hnf; intros.
    - inversion H2.
    - inversion H2.
    - subst e.
      apply H.
      rewrite <- (proj1 PRE_si).
      eapply aux24; eauto.
    - subst e.
      apply H0.
      rewrite <- (proj1 PRE_si).
      eapply aux24; eauto.
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
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre [? [? ?]]]]].
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
  (forall e, (Union _ PE3 PE1_root) e -> Complement _ (Union _ PV3 (eq root)) (dst g2 e) -> vvalid g (dst g2 e) -> vmap g2 (dst g2 e) = dst g2' (emap g2 e)) ->
  ecopy1 e0 (g2, g2') (g3, g3') ->
  (forall e, (Union _ PE3 PE3_root) e -> Complement _ (Union _ PV3 (eq root)) (dst g3 e) -> vvalid g (dst g3 e) -> vmap g3 (dst g3 e) = dst g3' (emap g3 e)).
Proof.
  intros until es_later.
  intros ? ? ? ? ?.
  intros H_VVALID H_M H_OUT_EDGES H_NODUP H_ES [PRE_bij [PRE_si PRE_consi]] ECOPY.
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre [ECOPY_pj [? ?]]]]].

  intros ? ? ? H_EXTRA.
  erewrite app_same_set in H1 by (eapply (aux20 e0 PE1_root PE3 PE3_root); eauto; reflexivity).
  rewrite Union_spec in H1; destruct H1.
  + assert (evalid g e).
    1: {
      rewrite Union_spec in H1; destruct H1;
      [eapply aux23 | eapply aux22]; eauto; reflexivity.
    }
    assert (vvalid g (dst g2 e)) as H_EXTRA'.
    1: {
      rewrite (proj1 (proj2 PRE_si)) in H3.
      rewrite (si_dst1 _ _ _ ECOPY_si) by auto.
      auto.
    }
    rewrite (proj1 (proj2 PRE_si)) in H3.
    erewrite <- si_dst1 in H2 |- * by eauto.
    rewrite <- ECOPY_prv.
    apply guarded_pointwise_relation_weaken with (P2 := Union E PE3 PE1_root) in ECOPY_gpre.
    2: {
      apply Included_Complement_Disjoint.
      apply Union_left_Disjoint; split;
      [eapply aux10 | eapply aux11]; eauto; reflexivity.
    }
    rewrite guarded_pointwise_relation_spec in ECOPY_gpre.
    rewrite <- ECOPY_gpre by auto.
    rewrite PRE_consi by auto.
    pose proof pregraph_join_guarded_si _ _ _ _ ECOPY_pj.
    eapply guarded_si_weaken in H4; [| apply Included_refl |].
    2: {
      apply Included_Complement_Disjoint.
      destruct ECOPY_pj as [_ [? _]].
      eapply Prop_join_Disjoint; eauto.
    }
    assert (evalid g2' (emap g2 e)) by (apply (evalid_preserved PRE_bij); auto).
    eapply guarded_si_dst1; eauto.
  + subst e.
    apply H0.
    rewrite <- (proj1 PRE_si); auto.
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
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre [? [? ?]]]]].
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
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre [? [? ?]]]]].
  transitivity (emap g2); auto.
  eapply guarded_pointwise_relation_weaken; [| eauto].
  apply Complement_Included_rev.
  assert (In e0 es) by (rewrite H_ES, in_app_iff; simpl; tauto).
  rewrite H_OUT_EDGES in H2.
  destruct H2.
  unfold PE, Included, Ensembles.In; intros.
  subst x.
  rewrite Intersection_spec; split; [| auto].
  unfold weak_edge_prop, PV.
  rewrite H3.
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
  destruct ECOPY as [ECOPY_si [ECOPY_prv [ECOPY_gpre [ECOPY_pj [? ?]]]]].

  apply guarded_pointwise_relation_pointwise_relation with (P := Union V PV3 (eq root)) in ECOPY_prv.
  rewrite ECOPY_prv in PRE_vvalid.
  apply guarded_pointwise_relation_weaken with (P2 := Union E PE3 PE1_root) in ECOPY_gpre.
  2: {
    apply Included_Complement_Disjoint.
    apply Union_left_Disjoint; split.
    + eapply aux10; eauto; reflexivity.
    + eapply aux11; eauto; reflexivity.
  }
  rewrite ECOPY_gpre in PRE_evalid.
  
  split.
  + rewrite !Same_set_spec.
    intro v'.
    destruct ECOPY_pj as [[? _] _].
    rewrite H1.
    rewrite (PRE_vvalid v').
    tauto.
  + erewrite (aux20 e0 PE1_root PE3 PE3_root) by (eauto; reflexivity).
    rewrite image_Union, image_single.
    rewrite !Same_set_spec.
    intro e'.
    destruct ECOPY_pj as [_ [[? _] _]].
    rewrite H1.
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
  (forall e, Union _ PE1 PE1_root e -> Complement _ (Union _ PV1 (eq root)) (dst g1 e) -> vvalid g (dst g1 e) -> vmap g1 (dst g1 e) = dst g1' (emap g1 e)) /\
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
  (forall e, Union _ PE3 PE3_root e -> Complement _ (Union _ PV3 (eq root)) (dst g3 e) -> vvalid g (dst g3 e) -> vmap g3 (dst g3 e) = dst g3' (emap g3 e)) /\
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
    (forall e, Union _ PE3 PE1_root e -> Complement _ (Union _ PV3 (eq root)) (dst g2 e) -> vvalid g (dst g2 e) -> vmap g2 (dst g2 e) = dst g2' (emap g2 e)) /\
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
  guarded_bij (Union _ PV1 (eq root)) (Union _ PE1 PE1_root) (vmap g1) (emap g1) g1 g1' /\
  g ~=~ g1 /\
  (forall e, Union _ PE1 PE1_root e -> Complement _ (Union _ PV1 (eq root)) (dst g1 e) -> vvalid g (dst g1 e) -> vmap g1 (dst g1 e) = dst g1' (emap g1 e)) /\
  guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g1) /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g1) /\
  Same_set (vvalid g1') (image_set (Union _ PV1 (eq root)) (vmap g1)) /\
  Same_set (evalid g1') (image_set (Union _ PE1 PE1_root) (emap g1)) ->
  copy M root g g1 g1'.
Proof.
  intros.
  assert (step_list g root (map (dst g) es)).
  1: {
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
  }
  destruct H3 as [?PRE [?PRE [?PRE [?PRE [?PRE ?PRE]]]]].
  assert (Same_set (reachable_by g root (Complement _ M)) (Union _ PV1 (eq root))).
  1: {
    rewrite Same_set_spec.
    intro v.
    erewrite reachable_by_ind_equiv by eauto.
    rewrite Union_spec, Intersection_Complement.
    tauto.
  }
  assert (Same_set (Intersection E (weak_edge_prop (reachable_by g root (Complement _ M)) g) (evalid g)) (Union _ PE1 PE1_root)).
  1: {
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
  }
  unfold copy.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  + auto.
  + auto.
  + auto.
  + rewrite H3. tauto.
  + rewrite H5. tauto.
  + hnf; intros.
    rewrite (H5 e) in H6.
    rewrite Intersection_spec in H7; destruct H7.
    apply PRE1; auto.
    generalize (dst g1 e), H7.
    apply Complement_Included_rev.
    rewrite <- H3.
    apply Included_refl.
  + rewrite H5, H3.
    auto.
Qed.

Lemma triple_vcopy1_edge_copy_list: forall (g g1 g2: Graph) g1' g2' root es es_done es_later (M: V -> Prop),
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ es_later ->
  (forall v : V, M v \/ ~ M v) ->
  vcopy1 root g g1 g1' ->
  edge_copy_list g root es_done M (g1, g1') (g2, g2') ->
  let PV := reachable_by g root (Complement _ M) in
  let PE := Intersection E (weak_edge_prop PV g) (evalid g) in
  let M0 := Union _ M (eq root) in
  let PV2 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let PE2 := Intersection _ (weak_edge_prop PV2 g) (evalid g) in
  let PE2_root e := In e es_done in
  guarded_bij (Union _ PV2 (eq root)) (Union _ PE2 PE2_root) (vmap g2) (emap g2) g2 g2' /\
  g ~=~ g2 /\
  (forall e, Union _ PE2 PE2_root e -> Complement _ (Union _ PV2 (eq root)) (dst g2 e) -> vvalid g (dst g2 e) -> vmap g2 (dst g2 e) = dst g2' (emap g2 e)) /\
  guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g2) /\
  guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g2) /\
  Same_set (vvalid g2') (image_set (Union _ PV2 (eq root)) (vmap g2)) /\
  Same_set (evalid g2') (image_set (Union _ PE2 PE2_root) (emap g2)).
Proof.
  intros.
  assert
   (let PV1 := reachable_by_through_set g (map (dst g) nil) (Complement _ M0) in
    let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
    let PE1_root e := In e nil in
    guarded_bij (Union _ PV1 (eq root)) (Union _ PE1 PE1_root) (vmap g1) (emap g1) g1 g1' /\
    g ~=~ g1 /\
    (forall e, Union _ PE1 PE1_root e -> Complement _ (Union _ PV1 (eq root)) (dst g1 e) -> vvalid g (dst g1 e) -> vmap g1 (dst g1 e) = dst g1' (emap g1 e)) /\
    guarded_pointwise_relation (Complement V PV) eq (vmap g) (vmap g1) /\
    guarded_pointwise_relation (Complement E PE) eq (emap g) (emap g1) /\
    Same_set (vvalid g1') (image_set (Union _ PV1 (eq root)) (vmap g1)) /\
    Same_set (evalid g1') (image_set (Union _ PE1 PE1_root) (emap g1))).
  1: {
    pose proof triple_vcopy1 _ _ _ _ H H5.
    intros.
    assert (Same_set PV1 (Empty_set _)).
    1: {
      rewrite Same_set_spec; intro v.
      split; [intros [? [? ?]] | intros []].
      inv H8.
    }
    assert (Same_set PE1 (Empty_set _)).
    1: {
      rewrite Same_set_spec; intro v.
      split; [intro | intros []].
      unfold PE1 in H9; rewrite Intersection_spec in H9.
      destruct H9 as [[? [? ?]] ?].
      inv H9.
    }
    assert (Same_set PE1_root (Empty_set _)).
    1: {
      rewrite Same_set_spec; intro v.
      split; [intros [] | intros []].
    }
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
    + destruct H5 as [_ [_ [? _]]].
      eapply guarded_pointwise_relation_weaken; [| exact H5].
      apply Complement_Included_rev.
      unfold Included, Ensembles.In; intros.
      unfold PE; rewrite Intersection_spec in H11 |- *.
      split; [destruct H11 as [? _] | tauto].
      unfold weak_edge_prop in H11 |- *.
      rewrite <- H11.
      apply reachable_by_refl; auto.
    + destruct H5 as [_ [_ [_ ?]]]; subst g1'.
      split.
      - rewrite H8, Union_Empty_left, image_single.
        reflexivity.
      - rewrite H9, H10, Union_Empty_left, image_Empty.
        simpl.
        rewrite Same_set_spec; intro e.
        tauto.
  }
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

Lemma vcopy1_edge_copy_list_copy: forall (g g1 g2: Graph) g1' g2' root es (M: V -> Prop),
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  (forall v : V, M v \/ ~ M v) ->
  vcopy1 root g g1 g1' ->
  edge_copy_list g root es M (g1, g1') (g2, g2') ->
  copy M root g g2 g2'.
Proof.
  intros.
  pose proof triple_vcopy1_edge_copy_list g g1 g2 g1' g2' root es es nil M H H0 H1 H2 (eq_sym (app_nil_r _)) H3 H4 H5.
  apply triple_final with (es := es); auto.
Qed.

Lemma copy_vvalid_eq: forall (g1 g2: Graph) (g2'': Graph') (M: V -> Prop) x,
  copy M x g1 g2 g2'' ->
  Same_set (vvalid g2'') (reachable g2'' (vmap g2 x)).
Proof.
  intros.
  destruct H as [COPY_si [COPY_gprv [COPY_gpre [COPY_vvalid [COPY_evalid [COPY_consi COPY_bij]]]]]].
  rewrite Same_set_spec; intros v'.
  split; [intros | apply reachable_foot_valid].
  rewrite (app_same_set COPY_vvalid) in H.
  rewrite image_set_spec in H.
  destruct H as [v [? ?]]; subst v'.
  apply (guarded_morphism_reachable COPY_bij); [rewrite (weak_edge_prop_si _ _ _ COPY_si); apply Included_refl |].
  rewrite <- COPY_si.
  rewrite <- (reachable_by_reachable_by_equiv _ _ _ _); auto.
Qed.

Lemma copy_evalid_eq: forall (g1 g2: Graph) (g2'': Graph') (M: V -> Prop) x,
  copy M x g1 g2 g2'' ->
  Same_set (evalid g2'') (Intersection _ (weak_edge_prop (reachable g2'' (vmap g2 x)) g2'') (evalid g2'')).
Proof.
  intros.
  destruct H as [COPY_si [COPY_gprv [COPY_gpre [COPY_vvalid [COPY_evalid [COPY_consi COPY_bij]]]]]].
  rewrite Same_set_spec; intros e'.
  split; [intros | rewrite Intersection_spec; tauto].
  rewrite Intersection_spec; split; [| auto].
  rewrite (app_same_set COPY_evalid) in H.
  rewrite image_set_spec in H.
  destruct H as [e [? ?]]; subst e'.
  unfold weak_edge_prop.
  pose proof H.
  rewrite (app_same_set (weak_edge_prop_si _ _ _ COPY_si)) in H.
  rewrite Intersection_spec in H; destruct H.
  rewrite <- (src_preserved COPY_bij) by auto.
  apply (guarded_morphism_reachable COPY_bij); [rewrite (weak_edge_prop_si _ _ _ COPY_si); apply Included_refl |].
  rewrite <- COPY_si at 1.
  rewrite <- (reachable_by_reachable_by_equiv _ _ _ _); auto.
Qed.

Lemma copy_vvalid_weak_eq: forall (g1 g2: Graph) (g2'': Graph') (M: V -> Prop) x x0,
  ~ vvalid g1 x /\ ~ vvalid g2'' x0 \/ x0 = vmap g2 x ->
  copy M x g1 g2 g2'' ->
  Same_set (vvalid g2'') (reachable g2'' x0).
Proof.
  intros.
  destruct H; [| subst x0; eapply copy_vvalid_eq; eauto].
  destruct H0 as [COPY_si [COPY_gprv [COPY_gpre [COPY_vvalid [COPY_evalid [COPY_consi COPY_bij]]]]]].
  rewrite COPY_vvalid.
  destruct H.
  assert (Same_set (reachable_by g1 x (Complement V M)) (Empty_set _)).
  1: {
    rewrite Same_set_spec; intros v; rewrite Empty_set_spec.
    pose proof reachable_by_head_valid g1 x v (Complement V M); tauto.
  }
  assert (Same_set (reachable g2'' x0) (Empty_set _)).
  1: {
    rewrite Same_set_spec; intros v; rewrite Empty_set_spec.
    pose proof reachable_head_valid g2'' x0 v; tauto.
  }
  rewrite H1, H2.
  apply image_Empty.
Qed.

Lemma copy_evalid_weak_eq: forall (g1 g2: Graph) (g2'': Graph') (M: V -> Prop) x x0,
  ~ vvalid g1 x /\ ~ vvalid g2'' x0 \/ x0 = vmap g2 x ->
  copy M x g1 g2 g2'' ->
  Same_set (evalid g2'') (Intersection _ (weak_edge_prop (reachable g2'' x0) g2'') (evalid g2'')).
  intros.
  destruct H; [| subst x0; eapply copy_evalid_eq; eauto].
  destruct H0 as [COPY_si [COPY_gprv [COPY_gpre [COPY_vvalid [COPY_evalid [COPY_consi COPY_bij]]]]]].
  rewrite COPY_evalid.
  assert (Same_set (reachable_by g1 x (Complement V M)) (Empty_set _)).
  1: {
    rewrite Same_set_spec; intros v; rewrite Empty_set_spec.
    pose proof reachable_by_head_valid g1 x v (Complement V M); tauto.
  }
  assert (Same_set (reachable g2'' x0) (Empty_set _)).
  1: {
    rewrite Same_set_spec; intros v; rewrite Empty_set_spec.
    pose proof reachable_head_valid g2'' x0 v; tauto.
  }
  rewrite H0, H1, weak_edge_prop_Empty, !Intersection_Empty_left.
  rewrite image_Empty, Intersection_Empty_right.
  reflexivity.
Qed.

Lemma copy_extend_copy: forall (g g2 g3: Graph) (g2' g': Graph') root es es_done e0 es_later (M: V -> Prop),
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  (forall v : V, M v \/ ~ M v) ->
  let M0 := Union _ M (eq root) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  let M_rec := Union _ M0 PV1 in
  let PV0 := reachable_by g (dst g e0) (Complement _ M_rec) in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  copy M_rec (dst g e0) g2 g3 g' ->
  disjointed_guard (vvalid g') (vvalid g2') (evalid g') (evalid g2') ->
  (forall v, M_rec v \/ ~ M_rec v) ->
  exists g3': Graph',
  extended_copy M_rec (dst g e0) (g2, g2') (g3, g3') /\
  guarded_labeled_graph_equiv (vvalid g') (evalid g') g' g3' /\
  guarded_labeled_graph_equiv (vvalid g2') (evalid g2') g2' g3'.
Proof.
  intros.
  pose proof disjointed_union_labeledgraph_exists_ll g' g2' H6.
  destruct H5 as [COPY_si [COPY_gprv [COPY_gpre [COPY_vvalid [COPY_evalid [COPY_consi COPY_bij]]]]]].
  spec H8.
  1: {
    destruct (guarded_bij_vmap_image_dec _ _ _ _ _ _ COPY_bij) as [X _].
    refine (ex_intro _ _ I).
    intros v'; specialize (X v').
    destruct X; [left | right].
    + rewrite Same_set_spec in COPY_vvalid.
      rewrite (COPY_vvalid v'); auto.
    + rewrite Same_set_spec in COPY_vvalid.
      rewrite (COPY_vvalid v'); auto.
  }
  spec H8.
  1: {
    destruct (guarded_bij_emap_image_dec _ _ _ _ _ _ COPY_bij) as [X _].
    refine (ex_intro _ _ I).
    intros e'; specialize (X e').
    destruct X; [left | right].
    + rewrite Same_set_spec in COPY_evalid.
      rewrite (COPY_evalid e'); auto.
    + rewrite Same_set_spec in COPY_evalid.
      rewrite (COPY_evalid e'); auto.
  }
  destruct H8 as [g3' [? [? [? ?]]]]; exists g3'.
  split; [| split]; auto.
  split; [| split; [| split; [| split; [| split; [| split]]]]]; auto.
  + rewrite <- COPY_vvalid, <- COPY_evalid.
    rewrite pregraph_join_iff.
    rewrite @Prop_join_comm in H9, H10.
    apply guarded_lge_guarded_si in H8.
    tauto.
  + eapply boundary_dst_consistent_si with (G1' := g'); eauto.
    - apply COPY_bij.
    - apply (guarded_morphism_proper_aux1 _ _ _ _ g3 g3 g' g3').
      * reflexivity.
      * rewrite <- COPY_vvalid, <- COPY_evalid.
        apply guarded_lge_guarded_si; auto.
      * apply COPY_bij.
    - rewrite <- COPY_vvalid, <- COPY_evalid.
      apply guarded_lge_guarded_si; auto.
  + apply (guarded_bij_proper_aux1 _ _ _ _ g3 g3 g' g3').
    - reflexivity.
    - rewrite <- COPY_vvalid, <- COPY_evalid.
      apply guarded_lge_guarded_si; auto.
    - apply COPY_bij.
Qed.

Lemma vcopy1_edge_copy_list_copy_and_copy_extend: forall (g g1 g2 g3: Graph) (g1' g2' g3'' g3': Graph') root es es_done e0 es_later (M: V -> Prop),
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  (forall v : V, M v \/ ~ M v) ->
  vcopy1 root g g1 g1' ->
  edge_copy_list g root es_done M (g1, g1') (g2, g2') ->
  let M0 := Union _ M (eq root) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  let M_rec := Union _ M0 PV1 in
  let PV0 := reachable_by g (dst g e0) (Complement _ M_rec) in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  copy M_rec (dst g e0) g2 g3 g3'' ->
  disjointed_guard (vvalid g3'') (vvalid g2') (evalid g3'') (evalid g2') ->
  (forall v, M_rec v \/ ~ M_rec v) ->
  extended_copy M_rec (dst g e0) (g2, g2') (g3, g3') ->
  guarded_labeled_graph_equiv (vvalid g3'') (evalid g3'') g3'' g3' ->
  guarded_labeled_graph_equiv (vvalid g2') (evalid g2') g2' g3' ->
  Prop_join (vvalid g2') (vvalid g3'') (vvalid g3') /\
  Prop_join (evalid g2') (evalid g3'') (evalid g3') /\
  ((predicate_partial_labeledgraph g3'' (vvalid g3'')) ~=~ (predicate_partial_labeledgraph g3' (vvalid g3'')))%LabeledGraph /\
  ((predicate_partial_labeledgraph g2' (vvalid g2')) ~=~ (predicate_partial_labeledgraph g3' (vvalid g2')))%LabeledGraph.
Proof.
  intros.
  destruct H7 as [COPY_si [COPY_gprv [COPY_gpre [COPY_vvalid [COPY_evalid [COPY_consi COPY_bij]]]]]].
  assert (Prop_join (vvalid g2') (vvalid g3'') (vvalid g3') /\ Prop_join (evalid g2') (evalid g3'') (evalid g3') ) as [? ?].
  1: {
    destruct H10 as [_ [_ [_ [? _]]]].
    destruct H7 as [? [? _]].
    rewrite <- COPY_vvalid in H7.
    rewrite <- COPY_evalid in H10; auto.
  }
  split; [| split; [| split]]; auto.
  1: {
    rewrite !predicate_partial_labeledgraph_gpredicate_sub_labeledgraph.
    assert (Same_set (Intersection E' (weak_edge_prop (vvalid g3'') g3') (evalid g3')) (Intersection E' (weak_edge_prop (vvalid g3'') g3'') (evalid g3''))).
    + rewrite Same_set_spec; intros e.
      rewrite !Intersection_spec; unfold weak_edge_prop.
      rewrite (proj1 H13).
      split; [intros [? [? | ?]] | intros].
      - exfalso.
        assert (Included (evalid g2') (weak_edge_prop (vvalid g2') g2')) as HE_g2'.
        1: {
          pose proof triple_vcopy1_edge_copy_list _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5 H6.
          destruct H16 as [? [? [_ [_ [_ [? ?]]]]]].
          rewrite H18, H19.
          eapply guarded_morphism_weak_edge_prop; [apply H16 | |].
          + rewrite weak_edge_prop_si by exact H17.
            unfold Included, Ensembles.In, weak_edge_prop; intros.
            rewrite Union_spec in H20 |- *.
            destruct H20; [rewrite Intersection_spec in H20; tauto |].
            right.
            rewrite H3 in H1.
            specialize (H1 x); rewrite in_app_iff in H1.
            pose proof (proj1 H1 (or_introl H20)).
            destruct H21.
            rewrite (si_src1 _ _ _ H17) in H22 by auto; symmetry; auto.
          + rewrite weak_edge_prop_si by exact H17.
            unfold Included, Ensembles.In, weak_edge_prop; intros.
            rewrite Union_spec, Intersection_spec in H20.
            destruct H20; [tauto |].
            rewrite H3 in H1.
            specialize (H1 x); rewrite in_app_iff in H1.
            pose proof (proj1 H1 (or_introl H20)).
            destruct H21.
            rewrite (proj1 (proj2 H17)) in H21; auto.
        }
        assert (vvalid g2' (src g2' e)) by (apply HE_g2'; auto).
        unfold guarded_labeled_graph_equiv, respectful_relation in H12.
        rewrite gpredicate_sub_labeledgraph_self in H12.
        rewrite (si_src1 _ _ _ (proj1 H12)) in H16 by auto.
        simpl in H16.
        apply (proj2 H7 (src g3' e)); auto.
      - unfold guarded_labeled_graph_equiv, respectful_relation in H11.
        rewrite gpredicate_sub_labeledgraph_self in H11.
        rewrite (si_src1 _ _ _ (proj1 H11)) by auto.
        auto.
      - unfold guarded_labeled_graph_equiv, respectful_relation in H11.
        rewrite gpredicate_sub_labeledgraph_self in H11.
        rewrite (si_src1 _ _ _ (proj1 H11)) in H14 by tauto.
        tauto.
    + rewrite H14.
      eapply stronger_gpredicate_sub_labeledgraph_simple; [| | exact H11].
      - apply Included_refl.
      - apply Intersection2_Included, Included_refl.
  }
  1: {
    rewrite !predicate_partial_labeledgraph_gpredicate_sub_labeledgraph.
    assert (Same_set (Intersection E' (weak_edge_prop (vvalid g2') g3') (evalid g3')) (Intersection E' (weak_edge_prop (vvalid g2') g2') (evalid g2'))).
    + rewrite Same_set_spec; intros e.
      rewrite !Intersection_spec; unfold weak_edge_prop.
      rewrite (proj1 H13).
      split; [intros [? [? | ?]] | intros].
      - unfold guarded_labeled_graph_equiv, respectful_relation in H12.
        rewrite gpredicate_sub_labeledgraph_self in H12.
        rewrite (si_src1 _ _ _ (proj1 H12)) by auto.
        auto.
      - exfalso.
        assert (Included (evalid g3'') (weak_edge_prop (vvalid g3'') g3'')) as HE_g3''.
        1: {
          rewrite COPY_vvalid, COPY_evalid.
          eapply guarded_morphism_weak_edge_prop; [apply COPY_bij | |].
          + rewrite weak_edge_prop_si by exact COPY_si.
            apply Intersection1_Included, Included_refl.
          + rewrite weak_edge_prop_si by exact COPY_si.
            apply Intersection2_Included, Included_refl.
        }
        assert (vvalid g3'' (src g3'' e)) by (apply HE_g3''; auto).
        unfold guarded_labeled_graph_equiv, respectful_relation in H11.
        rewrite gpredicate_sub_labeledgraph_self in H11.
        rewrite (si_src1 _ _ _ (proj1 H11)) in H16 by auto.
        simpl in H16.
        apply (proj2 H7 (src g3' e)); auto.
      - unfold guarded_labeled_graph_equiv, respectful_relation in H12.
        rewrite gpredicate_sub_labeledgraph_self in H12.
        rewrite (si_src1 _ _ _ (proj1 H12)) in H14 by tauto.
        tauto.
    + rewrite H14.
      eapply stronger_gpredicate_sub_labeledgraph_simple; [| | exact H12].
      - apply Included_refl.
      - apply Intersection2_Included, Included_refl.
  }
Qed.

Lemma extend_copy_emap_root: forall (g g1 g2 g3: Graph) (g1' g2' g3': Graph') root es es_done e0 es_later (M: V -> Prop),
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  (forall v : V, M v \/ ~ M v) ->
  vcopy1 root g g1 g1' ->
  edge_copy_list g root es_done M (g1, g1') (g2, g2') ->
  let M0 := Union _ M (eq root) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  let M_rec := Union _ M0 PV1 in
  let PV0 := reachable_by g (dst g e0) (Complement _ M_rec) in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  (forall v, M_rec v \/ ~ M_rec v) ->
  extended_copy M_rec (dst g e0) (g2, g2') (g3, g3') ->
  map (emap g2) es_done = map (emap g3) es_done.
Proof.
  intros.
  destruct H8 as [_ [_ [? _]]].
  rewrite guarded_pointwise_relation_spec in H8.
  apply Coqlib.list_map_exten.
  intros e ?; symmetry.
  apply (H8 e).
  intro.
  pose proof triple_vcopy1_edge_copy_list g g1 g2 g1' g2' root es es_done _ M H H0 H1 H2 H3 H4 H5 H6.
  destruct H11 as [? [? [? [? [? [? ?]]]]]].
  
  unfold Ensembles.In in H10.
  rewrite Intersection_spec in H10; destruct H10.
  unfold weak_edge_prop in H10; apply reachable_by_foot_prop in H10.
  rewrite <- (si_src2 _ _ _ H12) in H10 by auto.
  assert (src g e = root).
  1: {
    rewrite H3 in H1.
    specialize (H1 e).
    rewrite in_app_iff in H1.
    pose proof (proj1 H1 (or_introl H9)).
    destruct H19; auto.
  }
  rewrite H19 in H10.
  apply H10.
  clear.
  unfold Ensembles.In.
  subst M_rec PV1 M0.
  rewrite !Union_spec.
  left; right; auto.
Qed.

Lemma extended_copy_vmap_root: forall (g1 g2: Graph) (g1' g2': Graph') x x0 (M: V -> Prop),
  M x0 ->
  extended_copy M x (g1, g1') (g2, g2') ->
  vmap g1 x0 = vmap g2 x0.
Proof.
  intros.
  destruct H0 as [_ [? _]].
  rewrite guarded_pointwise_relation_spec in H0.
  apply H0.
  clear - H; unfold Complement, Ensembles.In; intros ?.
  apply reachable_by_foot_prop in H0.
  auto.
Qed.

Lemma ecopy1_vmap_root: forall (g1 g2: Graph) (g1' g2': Graph') e x0,
  ecopy1 e (g1, g1') (g2, g2') ->
  vmap g1 x0 = vmap g2 x0.
Proof.
  intros.
  destruct H as [_ [? _]].
  apply H.
Qed.

(*
(* Maybe useful for non bigraph situation *)
Lemma vcopy1_edge_copy_list_vmap_root_aux: forall (g g1 g2: Graph) (g1' g2': Graph') root es es_done es_later (M: V -> Prop),
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ es_later ->
  vcopy1 root g g1 g1' ->
  edge_copy_list g root es_done M (g1, g1') (g2, g2') ->
  vmap g1 root = vmap g2 root /\
  (forall (g3: Graph) (g3': Graph') (M_rec: V -> Prop) (dst0: V), M_rec root -> extended_copy M_rec dst0 (g2, g2') (g3, g3') -> vmap g1 root = vmap g3 root).
Proof.
  intros.
  revert es_later g2 g2' H3 H5; rev_induction es_done.
  + hnf in H5.
    i
Lemma vcopy1_edge_copy_list_extended_vmap_root: forall (g g1 g2 g3: Graph) (g1' g2' g3': Graph') root es es_done e0 es_later (M: V -> Prop),
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ e0 :: es_later ->
  (forall v : V, M v \/ ~ M v) ->
  vcopy1 root g g1 g1' ->
  edge_copy_list g root es_done M (g1, g1') (g2, g2') ->
  let M0 := Union _ M (eq root) in
  let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
  let PE1 := Intersection _ (weak_edge_prop PV1 g) (evalid g) in
  let PE1_root e := In e es_done in
  let M_rec := Union _ M0 PV1 in
  let PV0 := reachable_by g (dst g e0) (Complement _ M_rec) in
  let PE0 := Intersection _ (weak_edge_prop PV0 g) (evalid g) in
  (forall v, M_rec v \/ ~ M_rec v) ->
  extended_copy M_rec (dst g e0) (g2, g2') (g3, g3') ->
  map (emap g1) es_done = map (emap g3) es_done.
*)
Lemma vcopy1_edge_copy_list_mapped_root_edge_evalid: forall (g g1 g2: Graph) (g1' g2': Graph') root es es_done es_later (M: V -> Prop),
  vvalid g root ->
  ~ M root ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  es = es_done ++ es_later ->
  (forall v : V, M v \/ ~ M v) ->
  vcopy1 root g g1 g1' ->
  edge_copy_list g root es_done M (g1, g1') (g2, g2') ->
  forall e',
  In e' (map (emap g2) es_done) ->
  evalid g2' e'.
Proof.
  intros.
  rewrite in_map_iff in H7.
  destruct H7 as [e [? ?]].
  pose proof triple_vcopy1_edge_copy_list g g1 g2 g1' g2' root es es_done _ M H H0 H1 H2 H3 H4 H5 H6.
  destruct H9 as [? [? _]].
  pose proof evalid_preserved H9 e.
  subst e'.
  rewrite <- H11.
  + rewrite <- (proj1 (proj2 H10)).
    clear - H1 H3 H8.
    rewrite H3 in H1.
    specialize (H1 e).
    rewrite in_app_iff in H1.
    pose proof (proj1 H1 (or_introl H8)).
    destruct H; auto.
  + rewrite Union_spec; right.
    auto.
Qed.

End LocalGraphCopy.

End LocalGraphCopy.