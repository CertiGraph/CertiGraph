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
 
Lemma reachable_ind: forall x y, reachable G x y -> x = y \/ exists z, edge G x z /\ x <> z /\ reachable G z y.
Proof.
  intros.
  rewrite reachable_ind_reachable in H.
  induction H.
  + left; auto.
  + destruct (t_eq_dec x y).
    - subst y.
      apply IHreachable.
    - right.
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

Lemma reachable_list_bigraph_in:
  forall {l1 l2 x} l r,
    vvalid x ->
    reachable_list G l l1 ->
    reachable_list G r l2 ->
    (forall y, step G x y <-> y = l \/ y = r) ->
    forall y, reachable G x y <-> x = y \/ In y l1 \/ In y l2.
Proof.
  intros. specialize (H0 y). specialize (H1 y). split; intro.
  + apply reachable_ind in H3. destruct H3 as [? | [z [[? [? ?]] [? ?]]]]; auto.
    rewrite H2 in *. destruct H5.
    - subst. rewrite <- H0 in H7. auto.
    - subst. rewrite <- H1 in H7. auto.
  + destruct H3 as [? | [? | ?]].
    - subst. apply reachable_by_reflexive. split; auto.
    - rewrite H0 in H3. apply reachable_by_cons with l.
      * split; auto. split. apply reachable_head_valid in H3; auto. rewrite H2; auto.
      * auto.
      * apply H3.
    - rewrite H1 in H3. apply reachable_by_cons with r.
      * split; auto. split. apply reachable_head_valid in H3; auto. rewrite H2; auto.
      * hnf; auto.
      * apply H3.
Qed.

End ind_reachable.

Lemma edge_equiv_reachable_equiv: forall {V E} (g1 g2: PreGraph V E),
  (forall x, @vvalid _ _ g1 x <-> @vvalid _ _ g2 x) ->
  (forall x y, edge g1 x y <-> edge g2 x y) -> forall n, Same_set (reachable g1 n) (reachable g2 n).
Proof.
  intros V E.
  cut (forall (g1 g2 : PreGraph V E), (forall x, @vvalid _ _ g1 x <-> @vvalid _ _ g2 x) -> (forall x y, edge g1 x y <-> edge g2 x y) -> forall n, Included (reachable g1 n) (reachable g2 n)).
  1: intros; split; intros; apply H; [auto | auto | symmetry; auto | symmetry; auto].
  intros; intro; intros.
  unfold Ensembles.In in *.
  rewrite @reachable_ind_reachable in *.
  induction H1.
  + constructor. rewrite H in H1; auto.
  + rewrite H0 in H1.
    apply ind.reachable_cons with y; auto.
Qed.

Lemma si_reachable: forall {V E} (g1 g2: PreGraph V E) n,  g1 ~=~ g2 -> Same_set (reachable g1 n) (reachable g2 n).
Proof.
  intros.
  apply edge_equiv_reachable_equiv.
  + destruct H; auto.
  + intros; apply edge_si.
    auto.
Qed.

Lemma si_reachable_through_set: forall {V E} (g1 g2: PreGraph V E) S n, g1 ~=~ g2 -> (reachable_through_set g1 S n <-> reachable_through_set g2 S n).
Proof.
  intros V E.
  cut (forall (g1 g2 : PreGraph V E) (S : list V) (n : V), g1 ~=~ g2 ->
         (reachable_through_set g1 S n -> reachable_through_set g2 S n)).
  1: intros; split; apply H; [| symmetry]; auto.
  intros.
  unfold reachable_through_set in *.
  destruct H0 as [s [? ?]].
  exists s; split; auto.
  destruct (si_reachable g1 g2 s H).
  apply H2; auto.
Qed.
 
Lemma si_reachable_subgraph: forall {V E} (g1 g2: PreGraph V E) S, g1 ~=~ g2 -> (reachable_subgraph g1 S) ~=~ (reachable_subgraph g2 S).
Proof.
Arguments vvalid {_} {_} _ _.
  intros.
  pose proof (fun x => si_reachable_through_set g1 g2 S x H).
  destruct H as [? [? [? ?]]].
  split; [| split; [| split]]; auto.
  intros.
  simpl.
  unfold reachable_valid.
  rewrite (H0 v), H.
  tauto.
Arguments vvalid {_} {_} {_} _.
Qed.

