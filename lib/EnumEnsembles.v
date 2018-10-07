Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.EquivDec.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.List_ext.
Require Export RamifyCoq.lib.Ensembles_ext.
Require Import Coq.Lists.List.

Definition Enumerable U (A: Ensemble U) := {l: list U | NoDup l /\ forall x, In x l <-> Ensembles.In U A x}.

Definition EnumCovered U (A: Ensemble U) := {l: list U | NoDup l /\ forall x, Ensembles.In U A x -> In x l}.

Definition sizeOfEnum {U} {A: Ensemble U} (H: Enumerable U A) : nat := length (proj1_sig H).

Lemma Enumerable_Same_set: forall {U} (A B: Ensemble U), Same_set A B -> Enumerable U A -> Enumerable U B.
Proof.
  intros.
  destruct X.
  exists x.
  destruct a; split; auto.
  unfold Ensembles.In in *; firstorder.
Qed.

Lemma EnumCovered_strengthen: forall U A B,
  Included A B -> EnumCovered U B -> EnumCovered U A.
Proof.
  intros.
  destruct X as [x ?H].
  exists x.
  split; [tauto |].
  intros.
  apply H in H1.
  firstorder.
Qed.

Lemma EnumStrengthen: forall U (P Q: Ensemble U),
  (forall x, P x -> Decidable (Q x)) ->
  Included Q P ->
  Enumerable U P -> 
  Enumerable U Q.
Proof.
  intros.
  destruct X0 as [l [? ?]].
  unfold Included, Ensembles.In in H, H1.
  assert (forall x : U, In x l -> Decidable (Q x)) by firstorder.
  assert (forall x : U, Q x -> In x l) by firstorder.
  clear X H H1 P.
  assert ({l' | NoDup l' /\ (forall x, In x l' <-> Q x /\ In x l)}).
  + clear H2.
    induction l; intros.
    - exists nil.
      split; [constructor |].
      intros x; simpl; tauto.
    - spec IHl; [inversion H0; auto |].
      spec IHl; [intros; apply X0; simpl; auto |].
      destruct IHl as [l0 [? ?]].
      destruct (X0 a (or_introl eq_refl)) as [?H | ?H]; [exists (a :: l0) | exists l0]; split.
      * constructor; auto.
        specialize (H1 a).
        inversion H0; tauto.
      * intros.
        simpl.
        specialize (H1 x).
        assert (a = x -> Q x) by (intros; subst; auto).
        tauto.
      * auto.
      * intros; simpl.
        specialize (H1 x).
        assert (a = x -> ~ Q x) by (intros; subst; auto).
        tauto.
  + destruct X as [l' [? ?]]; exists l'.
    split; [auto |].
    intros; unfold Ensembles.In; specialize (H1 x); specialize (H2 x).
    tauto.
Qed.

Lemma EnumSplit: forall U (P Q R: Ensemble U),
  (forall x, P x -> {Q x} + {R x}) ->
  Prop_join Q R P ->
  Enumerable U P -> 
  Enumerable U Q * Enumerable U R.
Proof.
  intros U P Q R ? [? ?] ?.
  split.
  + apply EnumStrengthen with P; auto.
    - intros x HH; specialize (X x HH); specialize (H x); specialize (H0 x).
      apply sumbool_weaken_right with (R x); auto.
    - intros x; simpl; specialize (H x); tauto.
  + apply EnumStrengthen with P; auto.
    - intros x HH; specialize (X x HH); specialize (H x); specialize (H0 x).
      apply swap_sumbool.
      apply sumbool_weaken_left with (Q x); auto.
    - intros x; simpl; specialize (H x); tauto.
Qed.

Lemma Enumerable_is_EnumCovered: forall U A, Enumerable U A -> EnumCovered U A.
Proof. intros. destruct X as [l [? ?]]. exists l. firstorder. Qed.
