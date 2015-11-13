Require Import Coq.Logic.ProofIrrelevance.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.find_not_in.
Require Import RamifyCoq.graph.path_lemmas.

Module ind.
Section ind.

Context {V : Type}.
Context {E : Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Variable G : PreGraph V E.

Inductive reachable: V -> V -> Prop :=
  | reachable_nil: forall x, vvalid G x -> reachable x x
  | reachable_cons: forall x y z, edge G x y -> reachable y z -> reachable x z.

Lemma reachable_trans: forall x y z,
  reachable x y -> reachable y z -> reachable x z.
Proof.
  intros.
  induction H.
  + auto.
  + apply reachable_cons with y; auto.
Qed.
    
End ind.
End ind.

Module ind2.
Section ind2.

Context {V : Type}.
Context {E : Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Variable G : PreGraph V E.

Inductive reachable: V -> V -> Prop :=
  | reachable_nil: forall x, vvalid G x -> reachable x x
  | reachable_cons: forall x y z, reachable x y -> edge G y z -> reachable x z.

Lemma reachable_trans: forall x y z,
  reachable x y -> reachable y z -> reachable x z.
Proof.
  intros.
  induction H0.
  + auto.
  + apply reachable_cons with y; auto.
Qed.

End ind2.
End ind2.

Section ind_reachable.

Context {V : Type}.
Context {E : Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context (G : PreGraph V E).

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

Lemma reachable_ind2_reachable: forall x y, reachable G x y <-> ind2.reachable G x y.
Proof.
  intros.
  rewrite reachable_ind_reachable.
  split; intros.
  + induction H.
    - apply ind2.reachable_nil; auto.
    - apply ind2.reachable_trans with y; auto.
      apply ind2.reachable_cons with x; auto.
      apply ind2.reachable_nil.
      destruct H; tauto.
  + induction H.
    - apply ind.reachable_nil; auto.
    - apply ind.reachable_trans with y; auto.
      apply ind.reachable_cons with z; auto.
      apply ind.reachable_nil.
      destruct H0; tauto.
Qed.

Lemma reachable_edge:
  forall x y z, reachable G x y -> edge G y z -> reachable G x z.
Proof.
  intros.
  rewrite reachable_ind2_reachable in *.
  apply ind2.reachable_cons with y; auto.
Qed.

Lemma reachable_step:
  forall x y z, reachable G x y -> step G y z -> vvalid G z -> reachable G x z.
Proof.
  intros.
  pose proof reachable_foot_valid G _ _ H.
  apply reachable_edge with y; auto.
  unfold edge. tauto.
Qed.

Lemma edge_reachable:
  forall x y z, reachable G y z -> edge G x y -> reachable G x z.
Proof.
  intros.
  rewrite reachable_ind_reachable in *.
  apply ind.reachable_cons with y; auto.
Qed.

Lemma step_reachable:
  forall x y z, step G x y -> reachable G y z -> vvalid G x -> reachable G x z.
Proof.
  intros.
  pose proof reachable_head_valid G _ _ H0.
  apply edge_reachable with y; auto.
  unfold edge. tauto.
Qed.

Lemma reachable_ind: forall x y, reachable G x y -> x = y \/ exists z, edge G x z /\ x <> z /\ reachable G z y.
Proof.
  intros.
  rewrite reachable_ind_reachable in H.
  induction H.
  + left; auto.
  + destruct_eq_dec x y.
    - subst y.
      apply IHreachable.
    - right.
      exists y. rewrite reachable_ind_reachable in *; auto.
Qed.

Lemma reachable_ind': forall x S y, vvalid G x -> step_list G x S -> (reachable G x y <-> x = y \/ reachable_through_set G S y).
Proof.
  intros.
  unfold reachable_through_set.
  split; intros.
  + apply reachable_ind in H1.
    destruct H1; [left; auto | right].
    destruct H1 as [z ?]; exists z.
    split; [| tauto].
    rewrite (H0 z).
    destruct H1 as [[? [? ?]] ?].
    auto.
  + destruct H1 as [? | [? [? ?]]].
    - subst; apply reachable_refl; auto.
    - rewrite (H0 x0) in H1.
      apply edge_reachable with x0; auto.
      split; [| split]; auto.
      apply reachable_head_valid in H2; auto.
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

Lemma reachable_list_bigraph_in:
  forall {l1 l2 x} l r,
    vvalid G x ->
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
    - subst. apply reachable_by_refl; auto.
    - rewrite H0 in H3. apply edge_reachable_by with l.
      * auto.
      * split; auto. split. apply reachable_head_valid in H3; auto. rewrite H2; auto.
      * apply H3.
    - rewrite H1 in H3. apply edge_reachable_by with r.
      * hnf; auto.
      * split; auto. split. apply reachable_head_valid in H3; auto. rewrite H2; auto.
      * apply H3.
Qed.

Lemma edge_preserved_rev_foot: forall (P: V -> Prop),
  (forall x y, reachable G x y -> P x -> P y) ->
  forall x y, 
  reachable G x y ->
  ~ P y ->
  reachable_by G x (Complement _ P) y.
Proof.
  intros.
  rewrite reachable_ind_reachable in H0.
  induction H0.
  + apply reachable_by_refl; auto.
  + apply edge_reachable_by with y; auto.
    rewrite <- reachable_ind_reachable in H2.
    intro.
    apply (H x z) in H3; [auto |].
    apply edge_reachable with y; auto.
Qed.

Lemma edge_preserved_rev_foot0: forall (P: V -> Prop),
  (forall x y, reachable G x y -> P x -> P y) ->
  forall l y, 
  reachable_through_set G l y ->
  ~ P y ->
  reachable_by_through_set G l (Complement _ P) y.
Proof.
  intros.
  destruct H0 as [s [? ?]]; exists s; split; auto.
  apply edge_preserved_rev_foot; auto.
Qed.

End ind_reachable.

Section EQUIV.

Context {V : Type}.
Context {E : Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Lemma edge_equiv_reachable_equiv: forall (g1 g2: PreGraph V E),
  (forall x, vvalid g1 x <-> vvalid g2 x) ->
  (forall x y, edge g1 x y <-> edge g2 x y) -> forall n, Same_set (reachable g1 n) (reachable g2 n).
Proof.
  cut (forall (g1 g2 : PreGraph V E), (forall x, vvalid g1 x <-> vvalid g2 x) -> (forall x y, edge g1 x y <-> edge g2 x y) -> forall n, Included (reachable g1 n) (reachable g2 n)).
  1: intros; split; intros; apply H; [auto | auto | symmetry; auto | symmetry; auto].
  intros; intro; intros.
  unfold Ensembles.In in *.
  rewrite @reachable_ind_reachable in *.
  induction H1.
  + constructor. rewrite H in H1; auto.
  + rewrite H0 in H1.
    apply ind.reachable_cons with y; auto.
Qed.

Lemma si_reachable: forall (g1 g2: PreGraph V E) n,  g1 ~=~ g2 -> Same_set (reachable g1 n) (reachable g2 n).
Proof.
  intros.
  apply edge_equiv_reachable_equiv.
  + destruct H; auto.
  + intros; apply edge_si.
    auto.
Qed.

Lemma si_reachable_direct: forall (g1 g2: PreGraph V E) x y,  g1 ~=~ g2 -> (reachable g1 x y <-> reachable g2 x y).
Proof.
  intros. apply (si_reachable _ _ x) in H. destruct H. split; intros.
  + apply (H y); auto.
  + apply (H0 y); auto.
Qed.

Lemma si_eq_as_set_reachable_through_set: forall (g1 g2: PreGraph V E) S1 S2 n, g1 ~=~ g2 -> eq_as_set S1 S2 -> (reachable_through_set g1 S1 n <-> reachable_through_set g2 S2 n).
Proof.
  cut (forall (g1 g2 : PreGraph V E) S1 S2 (n : V), g1 ~=~ g2 -> eq_as_set S1 S2 ->
         (reachable_through_set g1 S1 n -> reachable_through_set g2 S2 n)).
  1: intros; split; apply H; [| | symmetry | symmetry]; auto.
  intros.
  intros.
  unfold reachable_through_set in *.
  destruct H1 as [s [? ?]].
  exists s; split.
  + pose proof proj1 H0 s.
    auto.
  + destruct (si_reachable g1 g2 s H).
    apply H3; auto.
Qed.

Lemma si_reachable_through_set: forall (g1 g2: PreGraph V E) S n, g1 ~=~ g2 -> (reachable_through_set g1 S n <-> reachable_through_set g2 S n).
Proof.
  intros.
  apply si_eq_as_set_reachable_through_set; auto.
  reflexivity.
Qed.

Instance reachable_proper: Proper (structurally_identical ==> (@eq V) ==> (@eq V) ==> iff) reachable.
Proof.
  do 3 (hnf; intros); subst.
  apply si_reachable_direct.
  auto.
Defined.

Instance reachable_proper': Proper (structurally_identical ==> (@eq V) ==> Same_set) reachable.
Proof.
  do 2 (hnf; intros); subst.
  rewrite Same_set_spec in *.
  hnf; intros.
  apply si_reachable_direct.
  auto.
Defined.

Instance reachable_through_set_proper: Proper (structurally_identical ==> eq_as_set ==> (@eq V) ==> iff) reachable_through_set.
Proof.
  do 3 (hnf; intros); subst.
  apply si_eq_as_set_reachable_through_set; auto.
Defined.

Instance reachable_through_set_proper': Proper (structurally_identical ==> eq_as_set ==> @Same_set V) reachable_through_set.
Proof.
  do 2 (hnf; intros); subst.
  rewrite Same_set_spec in *.
  hnf; intros.
  apply si_eq_as_set_reachable_through_set; auto.
Defined.

End EQUIV.

Global Existing Instances reachable_proper reachable_proper' reachable_through_set_proper reachable_through_set_proper'.
