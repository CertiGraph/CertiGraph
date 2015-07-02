Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Lists.List.
Require Import RamifyCoq.Coqlib.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.find_not_in.
Require Import RamifyCoq.graph.path_lemmas.

Module ind.
Section ind.

Context {V : Type}.
Context {E : Type}.
Variable G : PreGraph V E.

Inductive reachable: V -> V -> Prop :=
  | reachable_nil: forall x, vvalid x -> reachable x x
  | reachable_cons: forall x y z, edge G x y -> reachable y z -> reachable x z.

End ind.
End ind.

Section ind_reachable.

Context {V : Type}.
Context {E : Type}.
Context {G : PreGraph V E}.

Lemma reachable_ind_reachable: forall x y, reachable G x y <-> ind.reachable G x y.
Proof.
  intros; split; intros.
  + destruct H as [p [? ?]].
    destruct p; [inversion H; inversion H1 |].
    inversion H; inversion H1; subst; clear H1.
    revert x H H0 H2; induction p; intros.
    - inversion H; inversion H1; inversion H2.
      subst; subst.
      apply ind.reachable_nil.
      destruct H0; simpl in H0; auto.
    - destruct H0.
      apply ind.reachable_cons with a.
      * simpl in H0. tauto.
      * apply IHp.
        1: split; auto.
        1: split; [exact (proj2 H0) | unfold path_prop; rewrite Forall_forall; intros; auto].
        1: simpl in H2; auto.
  + induction H.
    - exists (x :: nil).
      split; [split; auto |].
      split; [simpl; auto | unfold path_prop; rewrite Forall_forall; intros; auto].
    - destruct IHreachable as [p [? ?]].
      exists (x :: p).
      split.
      * destruct H1; split; auto.
        destruct p; simpl in H3 |- *; congruence.
      * destruct H2; split.
        1: destruct p; inversion H1; inversion H4; simpl in H2 |- *; subst; tauto.
        1: unfold path_prop; rewrite Forall_forall; intros; auto.
Qed.

Lemma reachable_edge:
  forall x y z, reachable G x y -> edge G y z -> reachable G x z.
Proof.
  intros.
  rewrite reachable_ind_reachable in *.
  induction H.
  + apply ind.reachable_cons with z; auto.
    apply ind.reachable_nil; unfold edge in H0; tauto.
  + apply ind.reachable_cons with y; auto.
Qed.
 
Lemma reachable_step:
  forall x y z, reachable G x y -> step G y z -> vvalid z -> reachable G x z.
Proof.
  intros.
  pose proof reachable_foot_valid V E G _ _ H.
  apply reachable_edge with y; auto.
  unfold edge. tauto.
Qed.
 
Lemma reachable_ind: forall x y, reachable G x y -> x = y \/ exists z, edge G x z /\ reachable G z y.
Proof.
  intros.
  rewrite reachable_ind_reachable in *.
  destruct H; [left | right]; auto.
  exists y. rewrite reachable_ind_reachable in *; auto.
Qed.

Lemma closed_edge_closed_reachable: forall l,
  (forall x y, In x l -> edge G x y -> In y l) ->
  (forall x y, In x l -> reachable G x y -> In y l).
Proof.
  intros.
  rewrite reachable_ind_reachable in H1.
  induction H1.
  + auto.
  + apply IHreachable.
    apply H with x; auto.
Qed.

Lemma reachable_refl: forall x, vvalid x -> reachable G x x.
Proof.
  intros.
  rewrite reachable_ind_reachable; apply ind.reachable_nil; auto.
Qed.

End ind_reachable.