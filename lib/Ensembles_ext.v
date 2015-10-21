Require Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import RamifyCoq.lib.Coqlib.

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

Lemma Intersection_Complement': forall A (P Q: Ensemble A),
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

Lemma Intersection_comm: forall A P Q, (pointwise_relation A iff) (Intersection A P Q) (Intersection A Q P).
Proof.
  repeat (hnf; intros).
  rewrite !Intersection_spec.
  tauto.
Qed.

Instance complement_proper (V: Type): Proper ((pointwise_relation V iff) ==> (pointwise_relation V iff)) (Complement V).
  hnf; intros.
  hnf; intros.
  unfold Complement, Ensembles.In.
  specialize (H a).
  tauto.
Defined.

Existing Instance complement_proper.

Lemma Intersection_Complement: forall A (P Q: Ensemble A),
  (pointwise_relation A iff)
  (Intersection A (Complement A P) (Complement A Q))
  (Complement A (Union A P Q)).
Proof.
  intros.
  intro x.
  rewrite Intersection_spec.
  unfold Complement, Ensembles.In.
  rewrite Union_spec.
  tauto.
Qed.

Instance Included_proper (V: Type): Proper ((pointwise_relation V iff) ==> (pointwise_relation V iff) ==> iff) (@Included V).
Proof.
  hnf; intros.
  hnf; intros.
  unfold pointwise_relation, Included, Ensembles.In in *.
  firstorder.
Defined.

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

Instance Intersection_proper {A}: Proper ((pointwise_relation A iff) ==> (pointwise_relation A iff) ==> (pointwise_relation A iff)) (Intersection A).
Proof.
  do 2 (hnf; intros).
  intro a; specialize (H0 a); specialize (H a).
  rewrite !Intersection_spec.
  tauto.
Defined.

Instance Prop_join_proper {A}: Proper ((pointwise_relation A iff) ==> (pointwise_relation A iff) ==> (pointwise_relation A iff) ==> iff) Prop_join.
Proof.
  intros.
  do 3 (hnf; intros).
  unfold pointwise_relation in *.
  split; intros [? ?]; split; intro; firstorder.
Defined.

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
