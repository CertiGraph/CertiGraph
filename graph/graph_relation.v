Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.Equivalence_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import VST.msl.Coqlib2.
Require Import Coq.Lists.List.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.graph_gen.

Section IS_PARTIAL_GRAPH.

  Context {V E: Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.

  Definition is_partial_graph (g1 g2: PreGraph V E) :=
    (forall v : V, vvalid g1 v -> vvalid g2 v) /\
    (forall e: E, evalid g1 e -> evalid g2 e) /\
    (forall e: E, evalid g1 e -> vvalid g1 (src g1 e) -> src g1 e = src g2 e) /\
    (forall e: E, evalid g1 e -> vvalid g1 (dst g1 e) -> dst g1 e = dst g2 e).

  Lemma is_partial_graph_refl: forall (g: PreGraph V E),
      is_partial_graph g g.
  Proof. intros. split; [|split; [|split]]; intros; auto. Qed.

  Lemma is_partial_graph_trans: forall (g1 g2 g3: PreGraph V E),
      is_partial_graph g1 g2 -> is_partial_graph g2 g3 -> is_partial_graph g1 g3.
  Proof.
    intros. unfold is_partial_graph in *.
    destruct H as [? [? [? ?]]], H0 as [? [? [? ?]]].
    split; [|split; [|split]]; intros.
    - apply H0, H; assumption.
    - apply H4, H1; assumption.
    - assert (src g1 e = src g2 e) by (apply H2; assumption). rewrite H9. apply H5.
      1: apply H1; assumption. rewrite <- H9; apply H; assumption.
    - assert (dst g1 e = dst g2 e) by (apply H3; assumption). rewrite H9. apply H6.
      1: apply H1; assumption. rewrite <- H9; apply H; assumption.
  Qed.

End IS_PARTIAL_GRAPH.

Section GuardedIdentical.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE DG: Type}.

Notation PGraph := (PreGraph V E).
Notation LGraph := (LabeledGraph V E DV DE DG).

Definition guarded_structurally_identical PV PE: relation PGraph := respectful_relation (gpredicate_subgraph PV PE) structurally_identical.

Definition guarded_labeled_graph_equiv PV PE: relation LGraph := respectful_relation (gpredicate_sub_labeledgraph PV PE) labeled_graph_equiv.

Instance guarded_si_Equivalence PV PE: Equivalence (guarded_structurally_identical PV PE).
Proof.
  apply resp_Equivalence.
  apply si_Equiv.
Qed.
Global Existing Instance guarded_si_Equivalence.

Instance guarded_lge_Equivalence PV PE: Equivalence (guarded_labeled_graph_equiv PV PE).
Proof.
  apply resp_Equivalence.
  apply lge_Equiv.
Qed.
Global Existing Instance guarded_lge_Equivalence.

Lemma guarded_si_spec: forall PV PE (G1 G2: PGraph),
  guarded_structurally_identical PV PE G1 G2 <->
  ((forall v, PV v -> (vvalid G1 v <-> vvalid G2 v)) /\
   (forall e, PE e -> (evalid G1 e <-> evalid G2 e)) /\
   (forall e, PE e -> evalid G1 e -> evalid G2 e -> src G1 e = src G2 e) /\
   (forall e, PE e -> evalid G1 e -> evalid G2 e -> dst G1 e = dst G2 e)).
Proof.
  intros.
  split; intros; (destruct H as [? [? [? ?]]]; split; [| split; [| split]]); intros.
  + specialize (H v); simpl in H.
    rewrite !Intersection_spec in H.
    tauto.
  + specialize (H0 e); simpl in H0.
    rewrite !Intersection_spec in H0.
    tauto.
  + apply H1; simpl; rewrite !Intersection_spec; auto.
  + apply H2; simpl; rewrite !Intersection_spec; auto.
  + specialize (H v); simpl.
    rewrite !Intersection_spec.
    tauto.
  + specialize (H0 e); simpl.
    rewrite !Intersection_spec.
    tauto.
  + apply H1; simpl in H3, H4; rewrite !Intersection_spec in H3, H4; tauto.
  + apply H2; simpl in H3, H4; rewrite !Intersection_spec in H3, H4; tauto.
Qed.

Lemma guarded_si_dst1: forall PV PE (G1 G2: PGraph),
  guarded_structurally_identical PV PE G1 G2 ->
  forall e, PE e -> evalid G1 e -> dst G1 e = dst G2 e.
Proof.
  intros.
  rewrite guarded_si_spec in H.
  apply (proj2 (proj2 (proj2 H))); auto.
  rewrite <- (proj1 (proj2 H)); auto.
Qed.

Instance guarded_si_proper: Proper (@Same_set V ==> @Same_set E ==> eq ==> eq ==> iff) guarded_structurally_identical.
Proof.
  intros.
  hnf; intros PV1 PV2 ?.
  hnf; intros PE1 PE2 ?.
  hnf; intros g1 g1' ?; subst g1'.
  hnf; intros g2 g2' ?; subst g2'.
  rewrite !guarded_si_spec.
  rewrite Same_set_spec in *.
  unfold pointwise_relation in *.
  firstorder.
Defined.
Global Existing Instance guarded_si_proper.

Lemma si_is_guarded_si:
  same_relation PGraph structurally_identical (guarded_structurally_identical (Full_set _) (Full_set _)).
Proof.
  intros.
  rewrite same_relation_spec.
  hnf; intros g1.
  hnf; intros g2.
  rewrite guarded_si_spec.
  unfold structurally_identical.
  pose proof Full_set_spec V.
  pose proof Full_set_spec E.
  firstorder.
Qed.

Lemma guarded_si_weaken: forall (PV1 PV2: V -> Prop) (PE1 PE2: E -> Prop),
  Included PV2 PV1 ->
  Included PE2 PE1 ->
  inclusion PGraph (guarded_structurally_identical PV1 PE1) (guarded_structurally_identical PV2 PE2).
Proof.
  intros.
  hnf; intros.
  rewrite guarded_si_spec in H1 |- *.
  unfold Included, Ensembles.In in H, H0.
  firstorder.
Qed.

Lemma si_guarded_si: forall PV PE,
  inclusion PGraph structurally_identical (guarded_structurally_identical PV PE).
Proof.
  intros.
  rewrite si_is_guarded_si.
  apply guarded_si_weaken; apply Included_Full_set.
Qed.

Lemma guarded_si_strong_trans: forall (PV1 PV2 PV: V -> Prop) (PE1 PE2 PE: E -> Prop) g1 g2 g3,
  Included PV PV1 ->
  Included PV PV2 ->
  Included PE PE1 ->
  Included PE PE2 ->
  guarded_structurally_identical PV1 PE1 g1 g2 ->
  guarded_structurally_identical PV2 PE2 g2 g3 ->
  guarded_structurally_identical PV PE g1 g3.
Proof.
  intros.
  transitivity g2.
  + eapply guarded_si_weaken; [| | eauto]; eauto.
  + eapply guarded_si_weaken; [| | eauto]; eauto.
Qed.

Lemma guarded_si_strong_trans': forall (PV1 PV2 PV: V -> Prop) (PE1 PE2 PE: E -> Prop) g1 g2 g3,
  Included PV1 PV ->
  Included PV2 PV ->
  Included PE1 PE ->
  Included PE2 PE ->
  guarded_structurally_identical (Complement _ PV1) (Complement _ PE1) g1 g2 ->
  guarded_structurally_identical (Complement _ PV2) (Complement _ PE2) g2 g3 ->
  guarded_structurally_identical (Complement _ PV ) (Complement _ PE ) g1 g3.
Proof.
  intros.
  eapply guarded_si_strong_trans.
  + apply Complement_Included_rev, H.
  + apply Complement_Included_rev, H0.
  + apply Complement_Included_rev, H1.
  + apply Complement_Included_rev, H2.
  + eauto.
  + eauto.
Qed.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Lemma guarded_lge_guarded_si: forall PV PE (G1 G2: LGraph),
  guarded_labeled_graph_equiv PV PE G1 G2 ->
  guarded_structurally_identical PV PE G1 G2.
Proof.
  intros.
  hnf in H |- *.
  destruct H as [? _].
  auto.
Qed.

Lemma guarded_lge_spec: forall PV PE (G1 G2: LGraph),
  guarded_labeled_graph_equiv PV PE G1 G2 <->
  (((forall v, PV v -> (vvalid G1 v <-> vvalid G2 v)) /\
    (forall e, PE e -> (evalid G1 e <-> evalid G2 e)) /\
    (forall e, PE e -> evalid G1 e -> evalid G2 e -> src G1 e = src G2 e) /\
    (forall e, PE e -> evalid G1 e -> evalid G2 e -> dst G1 e = dst G2 e)) /\
   (forall v, PV v -> vvalid G1 v -> vvalid G2 v -> vlabel G1 v = vlabel G2 v) /\
   (forall e, PE e -> evalid G1 e -> evalid G2 e -> elabel G1 e = elabel G2 e)).
Proof.
  split; intros; (destruct H as [[? [? [? ?]]] [? ?]]; split; [split; [| split; [| split]] | split]); intros.
  + specialize (H v); simpl in H.
    rewrite !Intersection_spec in H.
    tauto.
  + specialize (H0 e); simpl in H0.
    rewrite !Intersection_spec in H0.
    tauto.
  + apply H1; simpl; rewrite !Intersection_spec; auto.
  + apply H2; simpl; rewrite !Intersection_spec; auto.
  + apply H3; split; auto.
  + apply H4; split; auto.
  + simpl.
    rewrite !Intersection_spec.
    specialize (H v); tauto.
  + simpl.
    rewrite !Intersection_spec.
    specialize (H0 e); tauto.
  + apply H1; simpl in H5, H6; rewrite !Intersection_spec in H5, H6; tauto.
  + apply H2; simpl in H5, H6; rewrite !Intersection_spec in H5, H6; tauto.
  + apply H3; simpl in H5, H6; rewrite !Intersection_spec in H5, H6; tauto.
  + apply H4; simpl in H5, H6; rewrite !Intersection_spec in H5, H6; tauto.
Qed.

End GuardedIdentical.

Section ExpandPartialGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Notation Graph := (PreGraph V E).

Definition pregraph_join (PV: V -> Prop) (PE: E -> Prop) (G1 G2: Graph) : Prop :=
  Prop_join (vvalid G1) PV (vvalid G2) /\
  Prop_join (evalid G1) PE (evalid G2) /\
  (forall e : E, evalid G1 e -> evalid G2 e -> src G1 e = src G2 e) /\
  (forall e : E, evalid G1 e -> evalid G2 e -> dst G1 e = dst G2 e).

Lemma pregraph_join_proper_aux: forall (PV1 PV2: V -> Prop) (PE1 PE2: E -> Prop) (G11 G12 G21 G22: Graph),
  Same_set PV1 PV2 ->
  Same_set PE1 PE2 ->
  G11 ~=~ G12 ->
  G21 ~=~ G22 ->
  pregraph_join PV1 PE1 G11 G21 ->
  pregraph_join PV2 PE2 G12 G22.
Proof.
  intros.
  split; [| split; [| split]]; intros.
  + eapply Prop_join_proper; [.. | apply (proj1 H3)]; symmetry; auto.
    - rewrite Same_set_spec; destruct H1; auto.
    - rewrite Same_set_spec; destruct H2; auto.
  + eapply Prop_join_proper; [.. | apply (proj1 (proj2 H3))]; symmetry; auto.
    - rewrite Same_set_spec; destruct H1 as [_ [? _]]; auto.
    - rewrite Same_set_spec; destruct H2 as [_ [? _]]; auto.
  + assert (evalid G11 e) by (rewrite (proj1 (proj2 H1)); auto).
    assert (evalid G21 e) by (rewrite (proj1 (proj2 H2)); auto).
    rewrite <- (proj1 (proj2 (proj2 H1))) by auto.
    rewrite <- (proj1 (proj2 (proj2 H2))) by auto.
    apply (proj1 (proj2 (proj2 H3))); auto.
  + assert (evalid G11 e) by (rewrite (proj1 (proj2 H1)); auto).
    assert (evalid G21 e) by (rewrite (proj1 (proj2 H2)); auto).
    rewrite <- (proj2 (proj2 (proj2 H1))) by auto.
    rewrite <- (proj2 (proj2 (proj2 H2))) by auto.
    apply (proj2 (proj2 (proj2 H3))); auto.
Qed.

Instance pregraph_join_proper: Proper (Same_set ==> Same_set ==> structurally_identical ==> structurally_identical ==> iff) pregraph_join.
Proof.
  do 4 (hnf; intros).
  split; apply pregraph_join_proper_aux; auto; symmetry; auto.
Qed.
Global Existing Instance pregraph_join_proper.

Lemma pregraph_join_guarded_si: forall PV PE (G1 G2: Graph),
  pregraph_join PV PE G1 G2 ->
  guarded_structurally_identical (Complement _ PV) (Complement _ PE) G1 G2.
Proof.
  intros.
  rewrite guarded_si_spec.
  destruct H as [[? ?] [? [? ?]]].
  unfold Complement, Ensembles.In, weak_edge_prop.
  split; [| split; [| split]]; firstorder.
Qed.

Lemma pregraph_join_partial_si: forall PV PE (G1 G2: Graph) PV1,
  pregraph_join PV PE G1 G2 ->
  Disjoint _ PV PV1 ->
  (forall e, PE e -> evalid G2 e -> PV1 (src G2 e) -> False) ->
  (predicate_partialgraph G1 PV1) ~=~ (predicate_partialgraph G2 PV1).
Proof.
  intros.
  destruct H as [[? ?] [[? ?] [? ?]]].
  unfold Complement, Ensembles.In, weak_edge_prop.
  split; [| split; [| split]].
  + simpl; intros.
    unfold predicate_vvalid.
    rewrite H.
    rewrite Disjoint_spec in H0; specialize (H0 v).
    tauto.
  + simpl; intros.
    unfold predicate_weak_evalid.
    split; intros.
    - assert (evalid G2 e) by (rewrite H3; tauto).
      rewrite <- H5 by tauto.
      tauto.
    - pose proof proj1 H7.
      rewrite H3 in H8; destruct H8.
      * rewrite H5 by tauto.
        tauto.
      * exfalso; apply (H1 e); tauto.
  + simpl; unfold predicate_weak_evalid; intros.
    apply H5; tauto.
  + simpl; unfold predicate_weak_evalid; intros.
    apply H6; tauto.
Qed.

Lemma pregraph_join_Empty: forall (G: Graph),pregraph_join (Empty_set _) (Empty_set _) G G.
Proof.
  intros.
  split; [| split; [| split]]; auto.
  + pose proof Empty_set_iff V.
    split; firstorder.
  + pose proof Empty_set_iff E.
    split; firstorder.
Qed.

Lemma pregraph_join_pregraph_join: forall G1 G2 G3 PV PE PV' PE',
  pregraph_join PV PE G1 G2 ->
  pregraph_join PV' PE' G2 G3 ->
  pregraph_join (Union _ PV PV') (Union _ PE PE') G1 G3.
Proof.
  unfold pregraph_join.
  intros.
  destruct H as [? [? [? ?]]], H0 as [? [? [? ?]]].
  split; [| split; [| split]]; intros.
  + apply Prop_join_assoc with (P2 := vvalid G2); auto.
  + apply Prop_join_assoc with (P2 := evalid G2); auto.
  + assert (evalid G2 e) by (destruct H4; firstorder).
    rewrite H2, H5; auto.
  + assert (evalid G2 e) by (destruct H4; firstorder).
    rewrite H3, H6; auto.
Qed.

Lemma pregraph_join_empty_single: forall v0 src0 dst0,
  pregraph_join (eq v0) (Empty_set _) (empty_pregraph src0 dst0) (single_vertex_pregraph v0).
Proof.
  intros.
  unfold empty_pregraph, single_vertex_pregraph.
  split; [| split; [| split]]; simpl.
  + split; intros.
    - destruct_eq_dec v0 a; tauto.
    - auto.
  + split; intros.
    - tauto.
    - auto.
  + intros; tauto.
  + intros; tauto.
Qed.

Lemma pregraph_join_iff: forall PV PE G1 G2,
  pregraph_join PV PE G1 G2 <->
  (Prop_join (vvalid G1) PV (vvalid G2) /\
   Prop_join (evalid G1) PE (evalid G2) /\
   guarded_structurally_identical (vvalid G1) (evalid G1) G1 G2).
Proof.
  intros.
  unfold pregraph_join, Prop_join.
  rewrite guarded_si_spec.
  split; intros; repeat split; try tauto; auto; firstorder. (* slow *)
Qed.

Lemma pregraph_join_vvalid_mono: forall PV PE G1 G2,
  pregraph_join PV PE G1 G2 ->
  forall v: V,
  vvalid G1 v ->
  vvalid G2 v.
Proof.
  intros.
  rewrite pregraph_join_iff in H.
  destruct H as [? _].
  destruct H.
  rewrite H.
  auto.
Qed.

Lemma pregraph_join_vealid_mono: forall PV PE G1 G2,
  pregraph_join PV PE G1 G2 ->
  forall e: E,
  evalid G1 e ->
  evalid G2 e.
Proof.
  intros.
  rewrite pregraph_join_iff in H.
  destruct H as [_ [? _]].
  destruct H.
  rewrite H.
  auto.
Qed.

End ExpandPartialGraph.
