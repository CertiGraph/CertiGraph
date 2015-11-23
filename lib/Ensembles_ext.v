Require Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import RamifyCoq.lib.Coqlib.

Lemma Full_set_spec: forall A (v: A), Full_set A v.
Proof.
  intros.
  constructor.
Qed.

Lemma Intersection_spec: forall A (v: A) P Q, Intersection _ P Q v <-> P v /\ Q v.
Proof.
  intros.
  split; intros.
  + inversion H; auto.
  + constructor; tauto.
Qed.

Lemma Union_spec: forall A (v: A) P Q, Union _ P Q v <-> P v \/ Q v.
Proof.
  intros.
  split; intros.
  + inversion H; auto.
  + destruct H; [apply Union_introl | apply Union_intror]; auto.
Qed.

Lemma Disjoint_spec: forall A P Q, Disjoint A P Q <-> (forall x, P x -> Q x -> False).
Proof.
  intros; split; intros.
  + inversion H.
    eapply H2.
    unfold In; rewrite Intersection_spec; split; eauto.
  + constructor.
    intros.
    unfold In; rewrite Intersection_spec.
    intro; apply H with x; tauto.
Qed.

Lemma Included_Full_set: forall A P, Included A P (Full_set A).
Proof.
  intros.
  hnf; unfold In; intros.
  apply Full_set_spec.
Qed.

Lemma Intersection_Complement: forall A (P Q: Ensemble A),
  Same_set A
  (Intersection A (Complement A P) (Complement A Q))
  (Complement A (Union A P Q)).
Proof.
  intros.
  unfold Same_set, Included, Complement, Ensembles.In.
  split; intros.
  + rewrite Union_spec.
    rewrite Intersection_spec in H.
    tauto.
  + rewrite Union_spec in H.
    rewrite Intersection_spec.
    tauto.
Qed.

Lemma Union_iff: forall U A B x, Ensembles.In U (Union U A B) x <-> Ensembles.In U A x \/ Ensembles.In U B x.
Proof.
  intros; split; intros.
  + apply Constructive_sets.Union_inv; auto.
  + destruct H; [apply Union_introl | apply Union_intror]; auto.
Qed.

Lemma Empty_set_iff: forall U x, Ensembles.In U (Empty_set U) x <-> False.
Proof.
  intros; split; intro; inversion H.
Qed.

Lemma Singleton_iff: forall U x y, Ensembles.In U (Singleton U x) y <-> x = y.
Proof.
  intros; split; intro.
  + inversion H; auto.
  + subst; constructor.
Qed.

Arguments Included {U} B C.
Arguments Same_set {U} B C.

Lemma Same_set_refl: forall A (S : Ensemble A), Same_set S S. Proof. intros; split; intro; tauto. Qed.

Lemma Same_set_sym: forall A (S1 S2 : Ensemble A), Same_set S1 S2 -> Same_set S2 S1. Proof. intros; destruct H; split; auto. Qed.

Lemma Same_set_trans: forall A (S1 S2 S3: Ensemble A), Same_set S1 S2 -> Same_set S2 S3 -> Same_set S1 S3.
Proof. intros; destruct H, H0; split; repeat intro; [apply H0, H, H3 | apply H1, H2, H3]. Qed.

Add Parametric Relation {A} : (Ensemble A) Same_set
    reflexivity proved by (Same_set_refl A)
    symmetry proved by (Same_set_sym A)
    transitivity proved by (Same_set_trans A) as Same_set_rel.

Lemma Same_set_spec: forall A P Q, Same_set P Q <-> (pointwise_relation A iff) P Q.
Proof.
  intros.
  unfold Same_set, Included, In, pointwise_relation.
  firstorder.
Qed.

Lemma Intersection_comm: forall A P Q, Same_set (Intersection A P Q) (Intersection A Q P).
Proof.
  intros.
  rewrite Same_set_spec; hnf; intros.
  rewrite !Intersection_spec.
  tauto.
Qed.

Lemma Intersection_assoc: forall A P Q R, Same_set (Intersection A (Intersection A P Q) R) (Intersection A P (Intersection A Q R)).
Proof.
  intros.
  rewrite Same_set_spec; hnf; intros.
  rewrite !Intersection_spec.
  tauto.
Qed.

Lemma Union_comm: forall A P Q, Same_set (Union A P Q) (Union A Q P).
Proof.
  intros.
  rewrite Same_set_spec; hnf; intros.
  rewrite !Union_spec.
  tauto.
Qed.

Lemma Union_assoc: forall A P Q R, Same_set (Union A (Union A P Q) R) (Union A P (Union A Q R)).
Proof.
  intros.
  rewrite Same_set_spec; hnf; intros.
  rewrite !Union_spec.
  tauto.
Qed.

Lemma Intersection_Union_distr_l: forall A P Q R,
  Same_set (Intersection A (Union A Q R) P)
   (Union A (Intersection A Q P) (Intersection A R P)).
Proof.
  intros.
  rewrite Same_set_spec; intro x.
  rewrite !Intersection_spec, !Union_spec, !Intersection_spec.
  tauto.
Qed.

Lemma Intersection_Union_distr_r: forall A P Q R,
  Same_set (Intersection A P (Union A Q R))
   (Union A (Intersection A P Q) (Intersection A P R)).
Proof.
  intros.
  rewrite Same_set_spec; intro x.
  rewrite !Intersection_spec, !Union_spec, !Intersection_spec.
  tauto.
Qed.

Instance Included_proper (V: Type): Proper (Same_set ==> Same_set ==> iff) (@Included V).
Proof.
  hnf; intros.
  hnf; intros.
  rewrite Same_set_spec in *.
  unfold pointwise_relation, Included, Ensembles.In in *.
  firstorder.
Defined.

Instance complement_proper (V: Type): Proper (Same_set ==> Same_set) (Complement V).
  hnf; intros.
  rewrite Same_set_spec in *.
  hnf; intros.
  unfold Complement, Ensembles.In.
  specialize (H a).
  tauto.
Defined.

Existing Instance complement_proper.

Instance Union_proper (V: Type): Proper (Same_set ==> Same_set ==> Same_set) (Union V).
  hnf; intros.
  hnf; intros.
  rewrite Same_set_spec in *.
  unfold pointwise_relation in *; intros.
  rewrite !Union_spec.
  firstorder.
Defined.

Existing Instance Union_proper.

Lemma left_Included_Union {A: Type}: forall P Q, Included P (Union A P Q).
Proof.
  intros.
  intros ? ?.
  rewrite Union_iff.
  tauto.
Qed.

Lemma right_Included_Union {A: Type}: forall P Q, Included Q (Union A P Q).
Proof.
  intros.
  intros ? ?.
  rewrite Union_iff.
  tauto.
Qed.

Lemma Union_Empty_set {A: Type}: forall P, Same_set (Union _ P (Empty_set A)) P.
Proof.
  intros.
  rewrite Same_set_spec.
  hnf; intros.
  rewrite Union_spec.
  pose proof Noone_in_empty A a.
  tauto.
Qed.

Lemma Complement_Included_rev: forall (U: Type) P Q, Included P Q -> Included (Complement U Q) (Complement U P).
Proof.
  unfold Included, Complement, Ensembles.In.
  intros.
  firstorder.
Qed.

Lemma Ensemble_join_Intersection_Complement: forall {A} P Q,
  Included Q P ->
  (forall x, Q x \/ ~ Q x) ->
  Prop_join Q (Intersection A P (Complement A Q)) P.
Proof.
  intros.
  unfold Prop_join.
  unfold Included, Ensembles.In in H.
  split; intros x; specialize (H0 x); specialize (H x);
  rewrite Intersection_spec; unfold Complement, Ensembles.In; try tauto.
Qed.

Instance Intersection_proper {A}: Proper (Same_set ==> Same_set ==> Same_set) (Intersection A).
Proof.
  do 2 (hnf; intros).
  rewrite Same_set_spec in *.
  intro a; specialize (H0 a); specialize (H a).
  rewrite !Intersection_spec.
  tauto.
Defined.

Instance Prop_join_proper {A}: Proper (@Same_set A ==> Same_set ==> Same_set ==> iff) Prop_join.
Proof.
  intros.
  do 3 (hnf; intros).
  rewrite Same_set_spec in *.
  unfold pointwise_relation in *.
  split; intros [? ?]; split; intro; firstorder.
Defined.

Lemma Included_Disjoint: forall A P Q P' Q',
  Included P P' ->
  Included Q Q' ->
  Disjoint A P' Q' ->
  Disjoint A P Q.
Proof.
  intros.
  rewrite Disjoint_spec in H1 |- *.
  intros; apply (H1 x).
  + apply H; auto.
  + apply H0; auto.
Qed.

Lemma Union_left_Disjoint: forall A P Q R,
  Disjoint A (Union A P Q) R <-> Disjoint A P R /\ Disjoint A Q R.
Proof.
  intros.
  rewrite !Disjoint_spec.
  pose proof (fun x => Union_spec A x P Q).
  firstorder.
Qed.

Lemma Included_Complement_Disjoint: forall A P Q,
  (Included P (Complement _ Q)) <-> Disjoint A P Q.
Proof.
  intros.
  unfold Included, Complement, In.
  rewrite Disjoint_spec.
  firstorder.
Qed.

Lemma Disjoint_comm: forall A P Q,
  Disjoint A P Q <-> Disjoint A Q P.
Proof.
  intros.
  rewrite !Disjoint_spec.
  firstorder.
Qed.

Lemma Disjoint_Empty_set_right: forall {A} (P: Ensemble A), Disjoint A P (Empty_set A).
Proof.
  intros.
  rewrite Disjoint_comm.
  apply Included_Complement_Disjoint.
  apply Constructive_sets.Included_Empty.
Qed.

Lemma Disjoint_Empty_set_left: forall {A} (P: Ensemble A), Disjoint A (Empty_set A) P.
Proof.
  intros.
  apply Included_Complement_Disjoint.
  apply Constructive_sets.Included_Empty.
Qed.

Lemma Included_trans: forall {A} (P Q R: Ensemble A), Included P Q -> Included Q R -> Included P R.
Proof.
  unfold Included, Ensembles.In.
  intros; firstorder.
Qed.

Lemma Intersection1_Included: forall {A} P Q R, Included P R -> Included (Intersection A P Q) R.
Proof.
  unfold Included, Ensembles.In.
  intros.
  rewrite Intersection_spec in H0.
  firstorder.
Qed.

Lemma Intersection2_Included: forall {A} P Q R, Included Q R -> Included (Intersection A P Q) R.
Proof.
  unfold Included, Ensembles.In.
  intros.
  rewrite Intersection_spec in H0.
  firstorder.
Qed.

Lemma Included_refl: forall A P, @Included A P P.
Proof.
  intros; hnf; auto.
Qed.

Definition app_same_set {A: Type} {P Q: Ensemble A} (H: Same_set P Q) (x: A): P x <-> Q x := proj1 (Same_set_spec A P Q) H x.

Coercion app_same_set : Same_set >-> Funclass.

(*

Lemma Finite_spec: forall A U, Finite A U <-> exists l, NoDup l /\ forall x, In x l <-> Ensembles.In A U x.
Proof.
  intros.
  split; intros.
  + induction H.
    - exists nil.
      split; [constructor |].
      intros.
      rewrite Empty_set_iff; simpl; tauto.
    - destruct IHFinite as [l [? ?]].
      exists (x :: l).
      split; [constructor; auto; rewrite H2; auto |]. 
      intros x0; specialize (H2 x0).
      simpl.
      unfold Add.
      rewrite Union_iff, Singleton_iff.
      tauto.
  + destruct H as [l [? ?]].
    revert U H0; induction l; intros.
    - replace U with (Empty_set A); [apply Empty_is_finite |].
      apply Extensionality_Ensembles.
      split; intros x ?; specialize (H0 x); simpl in *; repeat rewrite Empty_set_iff in *; tauto.
    - replace U with (Add A (Subtract A U a) a);
      [apply Union_is_finite | apply Extensionality_Ensembles].
      * inversion H; subst.
        apply IHl; [auto |].
        intros x; specialize (H0 x).
        unfold Subtract, Setminus; unfold Ensembles.In at 1.
        simpl in H0.
        rewrite Singleton_iff.
        assert (a = x -> ~ In x l) by (intro; subst; auto).
        tauto.
      * unfold Subtract, Setminus; unfold Ensembles.In at 1.
        rewrite Singleton_iff.
        tauto.
      * unfold Add, Subtract, Setminus.
        split; intros ?; rewrite Union_iff;
          [unfold Ensembles.In at 1 | unfold Ensembles.In at 2];
          rewrite  Singleton_iff; intro;
          specialize (H0 x); simpl in H0; [tauto |].
        inversion H; subst.
        assert (a = x -> ~ In x l) by (intro; subst; auto).
        tauto.
Qed.

*)
