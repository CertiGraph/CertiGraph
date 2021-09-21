Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.

Lemma ex_iff: forall {A: Type} P Q, (forall x: A, P x <-> Q x) -> (ex P <-> ex Q).
Proof.
  intros.
  split; intros [x ?]; exists x; firstorder.
Qed.

Lemma forall_iff: forall {A: Type} P Q, (forall x: A, P x <-> Q x) -> ((forall x, P x) <-> (forall x, Q x)).
Proof. intros. firstorder. Qed.

Lemma and_iff_split: forall A B C D : Prop, (A <-> B) -> (C <-> D) -> (A /\ C <-> B /\ D).
Proof. intros. tauto. Qed.

Lemma and_iff_compat_l_weak: forall A B C : Prop, (A -> (B <-> C)) -> (A /\ B <-> A /\ C).
Proof. intros. tauto. Qed.

Lemma and_iff_compat_r_weak: forall A B C : Prop, (A -> (B <-> C)) -> (B /\ A <-> C /\ A).
Proof. intros. tauto. Qed.

Lemma and_or_distr_r: forall P Q R, P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
  intros.
  tauto.
Qed.

Lemma demorgan_weak: forall P Q: Prop, P \/ ~ P -> (~ (P /\ Q) <-> ~ P \/ ~ Q).
Proof.
  intros.
  destruct H; tauto.
Qed.

Lemma demorgan_weak': forall P Q: Prop, P \/ ~ P -> (~ (~ P /\ Q) <-> P \/ ~ Q).
Proof.
  intros.
  destruct H; tauto.
Qed.

Lemma eq_sym_iff: forall {A} (x y: A), x = y <-> y = x.
Proof.
  intros.
  split; intro; congruence.
Qed.

Lemma sumbool_weaken_right: forall P Q Q': Prop, (Q -> Q') -> ({P} + {Q}) -> ({P} + {Q'}).
Proof.
  intros.
  destruct H0; [left | right]; auto.
Qed.

Lemma sumbool_weaken_left: forall P P' Q: Prop, (P -> P') -> ({P} + {Q}) -> ({P'} + {Q}).
Proof.
  intros.
  destruct H0; [left | right]; auto.
Qed.

Definition Prop_join {A} (X Y Z: A -> Prop): Prop :=
  (forall a, Z a <-> X a \/ Y a) /\ (forall a, X a -> Y a -> False).

Definition Decidable (P: Prop) := {P} + {~ P}.

Lemma decidable_prop_decidable: forall P: Prop, Decidable P -> P \/ ~ P.
Proof.
  intros.
  destruct H; [left | right]; auto.
Qed.

Definition DecidablePred (A: Type): Type := {P : A -> Prop & forall a, {P a} + {~ P a}}.

Definition app_DecidablePred {A: Type} (P: DecidablePred A) (a: A) := projT1 P a.

Coercion app_DecidablePred: DecidablePred >-> Funclass.

Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ =>
    let H1 := fresh in (assert (H1: a); [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "disc" := (try discriminate).
Tactic Notation "contr" := (try contradiction).
Tactic Notation "congr" := (try congruence).
Tactic Notation "inv" hyp(H) := inversion H; clear H; subst.
Tactic Notation  "icase" constr(v) := (destruct v; disc; contr; auto).
Tactic Notation "copy" hyp(H) := (generalize H; intro).

(* TODO: This tactic is now duplicated here and in VST.msl.Coqlib2. *)
Ltac super_pattern t x :=
  let t0 := fresh "t" in
  set (t0 := t);
  pattern x in t0;
  cbv beta in (type of t0);
  subst t0.

Record bijective {A B} (f: A -> B) (invf: B -> A) : Prop :=
  {
    injective: forall x y, f x = f y -> x = y;
    surjective: forall x, f (invf x) = x;
  }.

Lemma bijective_refl: forall {A: Type}, @bijective A A id id.
Proof. intros. split; auto. Qed.

Lemma bijective_sym: forall {A B} (f: A -> B) (invf: B -> A),
    bijective f invf -> bijective invf f.
Proof.
  intros. destruct H as [?H ?H]. split; intros.
  - rewrite <- (H0 x), <- (H0 y), H1, H0. reflexivity.
  - apply H, H0.
Qed.

Lemma bijective_trans:
  forall {A B C} (f: A -> B) (g: B -> C) (invf: B -> A) (invg: C -> B),
    bijective f invf -> bijective g invg ->
    bijective (compose g f) (compose invf invg).
Proof.
  intros. destruct H, H0. split; intros; unfold compose in *.
  - apply injective0, injective1. assumption.
  - rewrite surjective0. apply surjective1.
Qed.

Lemma bijective_map: forall {A B} (f: A -> B) (g: B -> A),
    bijective f g -> bijective (map f) (map g).
Proof.
  intros. destruct H. split; intros.
  - revert y H. induction x; intros; destruct y; simpl in H; [|inversion H..]; auto.
    f_equal. 1: apply injective0; auto. apply IHx; assumption.
  - induction x; simpl; auto. rewrite IHx. f_equal. apply surjective0.
Qed.

Definition idempotent {A} (f: A -> A): Prop := forall x, f (f x) = f x.
