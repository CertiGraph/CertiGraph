Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import RamifyCoq.Coqlib.
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

Lemma local_dag_step: forall (g: Graph) x y `{@MathGraph _ _ _ _ g}, localDag g x -> step g x y -> localDag g y.
Proof.
  intros.
  unfold localDag in *.
  intros z ?.
  apply (H0 z).
  apply edge_reachable with y; auto.
  unfold edge.
  repeat split; auto.
  - rewrite step_spec in H1.
    destruct H1 as [e [? [? ?]]].
    destruct (valid_graph _ e H1).
    rewrite <- H3; auto.
  - apply reachable_head_valid in H2; auto.
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

End Dag.
