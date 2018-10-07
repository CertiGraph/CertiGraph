Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas. Import RamifyCoq.graph.path_lemmas.PathNotation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.

Section Dag.

Context {V : Type}.
Context {E : Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Notation Graph := (PreGraph V E).

Definition not_in_circle (g: Graph) (x: V) := forall y: V, edge g x y -> reachable g y x -> False.

Definition localDag (g: Graph) (x: V) := forall y, reachable g x y -> not_in_circle g y.

Definition Dag (g: Graph) := forall x, not_in_circle g x.

Lemma local_dag_step: forall (g: Graph) x y, localDag g x -> vvalid g x -> step g x y -> localDag g y.
Proof.
  intros.
  unfold localDag in *.
  intros z ?.
  apply (H z).
  apply step_reachable with y; auto.
Qed.

Lemma dag_local_dag: forall (g: Graph) x, Dag g -> localDag g x.
Proof.
  intros.
  intro; intros.
  apply H.
Qed.

Lemma si_local_dag: forall (g1 g2: Graph) x, g1 ~=~ g2 -> (localDag g1 x <-> localDag g2 x).
Proof.
  cut (forall (g1 g2: Graph) x, g1 ~=~ g2 -> localDag g1 x -> localDag g2 x).
  1: intros; split; apply H; [| symmetry]; auto.
  intros.
  hnf; intros.
  rewrite <- H in H1.
  specialize (H0 _ H1); clear H1.
  hnf; intros.
  pose proof edge_si _ _ y y0 H.
  rewrite <- H3 in H1.
  rewrite <- H in H2.
  specialize (H0 _ H1 H2).
  auto.
Qed.

Lemma si_dag: forall (g1 g2: Graph), g1 ~=~ g2 -> (Dag g1 <-> Dag g2).
Proof.
  cut (forall (g1 g2: Graph), g1 ~=~ g2 -> Dag g1 -> Dag g2).
  1: intros; split; apply H; [| symmetry]; auto.
  intros.
  hnf; intros.
  hnf; intros.
  pose proof edge_si _ _ x y H.
  rewrite <- H in H2.
  rewrite <- H3 in H1.
  specialize (H0 _ _ H1 H2).
  auto.
Qed.

Instance local_dag_proper: Proper (structurally_identical ==> eq ==> iff) localDag.
Proof.
  do 2 (hnf; intros).
  subst.
  apply si_local_dag; auto.
Defined.

Instance dag_proper: Proper (structurally_identical ==> iff) Dag.
Proof.
  hnf; intros.
  apply si_dag; auto.
Defined.

Lemma localDag_reachable_spec: forall g x S,
  vvalid g x ->
  localDag g x ->
  step_list g x S ->
  (forall y, reachable g x y <-> reachable_through_set g S y \/ y = x) /\
  (forall y, reachable_through_set g S y -> y <> x).
Proof.
  intros.
  split; intros.
  + rewrite (reachable_ind' g x S y H H1).
    assert (x = y <-> y = x) by (split; congruence).
    tauto.
  + destruct H2 as [x0 [? ?]].
    rewrite (H1 x0) in H2.
    specialize (H0 x).
    spec H0; [apply reachable_refl; auto |].
    specialize (H0 x0).
    assert (vvalid g x0) by (apply reachable_head_valid in H3; auto).
    assert (edge g x x0) by (split; [| split]; auto).
    spec H0; [auto |].
    intro; subst; tauto.
Qed.

Lemma localDag_reachable_spec': forall g x S,
  vvalid g x ->
  localDag g x ->
  step_list g x S ->
  Prop_join (reachable_through_set g S) (eq x) (reachable g x).
Proof.
  intros.
  destruct (localDag_reachable_spec _ _ _ H H0 H1).
  split.
  + intros y; specialize (H2 y).
    rewrite H2; clear.
    firstorder.
  + intros y; specialize (H3 y).
    firstorder.
Qed.

Lemma localDag_reachable_list_spec: forall g x S l,
  vvalid g x ->
  localDag g x ->
  step_list g x S ->
  reachable_list g x l ->
  reachable_set_list g S (remove equiv_dec x l).
Proof.
  intros.
  intro y.
  specialize (H2 y).
  rewrite remove_In_iff.
  rewrite H2.
  rewrite (reachable_ind' g x S y H H1).
  assert (x = y <-> y = x) by (split; intros; congruence).
  assert (reachable_through_set g S y -> y <> x); [| tauto].
  specialize (H0 x).
  spec H0; [apply reachable_refl; auto |].
  intros [z [? ?]] ?.
  subst.
  specialize (H0 z).
  rewrite (H1 z) in H4.
  apply H0; auto.
  split; [| split]; auto.
  apply reachable_head_valid in H5; auto.
Qed.

Lemma localDag_step_rev: forall g x S,
  vvalid g x ->
  step_list g x S ->
  ~ reachable_through_set g S x ->
  Forall (localDag g) S ->
  localDag g x.
Proof.
  intros.
  intros y ?; simpl.
  rewrite (reachable_ind' g x S y H H0) in H3.
  destruct H3.
  + subst y.
    intros y ? ?.
    apply H1; exists y; split; auto.
    rewrite (H0 y).
    destruct H3 as [? [? ?]]; auto.
  + destruct H3 as [s [? ?]].
    rewrite Forall_forall in H2; specialize (H2 s H3).
    apply H2; auto.
Qed.

End Dag.

Existing Instances local_dag_proper dag_proper.
