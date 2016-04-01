Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.Equivalence_ext.
Require Import RamifyCoq.lib.EquivDec_ext.

Definition app_sig {A B: Type} (P: A -> Prop) (f: A -> B): sig P -> B := fun a => f (proj1_sig a).

Definition guarded_pointwise_relation {A B : Type} (P: A -> Prop) (R : relation B) : relation (A -> B) :=
  respectful_relation (app_sig P) (pointwise_relation (sig P) R).

Definition is_rev_fun {A B: Type} (P: A -> Prop) (f: A -> B) (g: B -> option A) :=
  forall b,
  match g b with
  | Some a0 => P a0 /\ forall a, P a -> (f a = b <-> a = a0)
  | None => forall a, P a -> f a <> b
  end.
  
Definition is_guarded_inj {A B: Type} (P: A -> Prop) (f: A -> B) :=
  exists g: B -> option A, is_rev_fun P f g.
(* forall a1 a2: A, P a1 -> P a2 -> f a1 = f a2 -> a1 = a2. *)
(* This commented definition is weaker. *)

Instance guarded_pointwise_equivalence {A B : Type} (P: A -> Prop) {R : relation B} {EqR: Equivalence R}: Equivalence (guarded_pointwise_relation P R).
Proof.
  apply resp_Equivalence.
  apply pointwise_equivalence.
  auto.
Defined.

Definition guarded_pointwise_relation_spec: forall {A B : Type} (P: A -> Prop) (R : relation B) f g, guarded_pointwise_relation P R f g <-> (forall x: A, P x -> R (f x) (g x)).
Proof.
  intros.
  unfold guarded_pointwise_relation, respectful_relation, app_sig, pointwise_relation.
  split; intros.
  + specialize (H (exist P x H0)).
    exact H.
  + destruct a.
    specialize (H x p).
    exact H.
Qed.

Lemma guarded_pointwise_relation_weaken: forall {A B : Type} (P1 P2: A -> Prop) (R : relation B), Included P2 P1 -> inclusion _ (guarded_pointwise_relation P1 R) (guarded_pointwise_relation P2 R).
Proof.
  intros.
  hnf; intros.
  rewrite guarded_pointwise_relation_spec in H0 |- *.
  unfold Included, In in H.
  firstorder.
Qed.

Lemma guarded_pointwise_relation_pointwise_relation: forall {A B : Type} (P: A -> Prop) (R : relation B), inclusion _ (pointwise_relation A R) (guarded_pointwise_relation P R).
Proof.
  intros.
  hnf; intros.
  rewrite guarded_pointwise_relation_spec.
  intros.
  apply H.
Qed.

Lemma pointwise_relation_is_guarded_pointwise_relation: forall {A B : Type} (R : relation B), same_relation _ (pointwise_relation A R) (guarded_pointwise_relation (fun _ => True) R).
Proof.
  intros.
  rewrite same_relation_spec.
  hnf; intros.
  hnf; intros.
  rewrite guarded_pointwise_relation_spec.
  unfold pointwise_relation.
  firstorder.
Qed.

Instance guarded_pointwise_relation_Proper {A B : Type}: Proper (Same_set ==> eq ==> eq ==> eq ==> iff) (@guarded_pointwise_relation A B).
Proof.
  do 4 (hnf; intros); subst.
  destruct H.
  split; apply guarded_pointwise_relation_weaken; auto.
Defined.

(* surjection properties are not used now. *)
Lemma guarded_surj_Included: forall {X Y} (f: X -> Y) (PX: X -> Prop) (PY PY0: Y -> Prop),
  (forall y, PY y -> exists x, PX x /\ f x = y) ->
  (forall x, PX x -> PY0 (f x)) ->
  Included PY PY0.
Proof.
  intros.
  unfold Included, Ensembles.In.
  intros y ?.
  destruct (H _ H1) as [x [? ?]].
  subst y.
  apply (H0 x); auto.
Qed.

Lemma guarded_surj_Disjoint: forall {X Y} (f: X -> Y) (PX: X -> Prop) (PY PY0: Y -> Prop),
  (forall y, PY y -> exists x, PX x /\ f x = y) ->
  (forall x, PX x -> ~ PY0 (f x)) ->
  Disjoint Y PY PY0.
Proof.
  intros.
  rewrite Disjoint_spec.
  intros y ? ?.
  destruct (H _ H1) as [x [? ?]].
  subst y.
  apply (H0 x); auto.
Qed.

Lemma is_guarded_inj_empty {A B: Type} (f: A -> B):
  is_guarded_inj (Empty_set _) f.
Proof.
  intros.
  exists (fun v => None).
  intro b.
  intros.
  inv H.
Qed.

Lemma is_guarded_inj_single {A B: Type} {EqB: EqDec B eq} (f: A -> B) (a: A):
  is_guarded_inj (eq a) f.
Proof.
  intros.
  exists (fun b => if equiv_dec (f a) b then Some a else None).
  intro b.
  destruct_eq_dec (f a) b.
  + split; auto.
    intros; subst.
    tauto.
  + intros; subst.
    auto.
Qed.

Lemma is_guarded_inj_rev_aux {A B: Type} (P: A -> Prop) (f: A -> B) (g: B -> option A) (a: A):
  P a ->
  is_rev_fun P f g ->
  g (f a) = Some a.
Proof.
  intros.
  specialize (H0 (f a)).
  destruct (g (f a)).
  + destruct H0.
    specialize (H1 a H).
    rewrite (proj1 H1) by auto.
    auto.
  + specialize (H0 a H).
    congruence.
Qed.

Lemma is_guarded_inj_rev_aux' {A B: Type} (P1 P2: A -> Prop) (f: A -> B) (g1: B -> option A) (a: A):
  Disjoint B (image_set P1 f) (image_set P2 f) ->
  P2 a ->
  is_rev_fun P1 f g1 ->
  g1 (f a) = None.
Proof.
  intros.
  specialize (H1 (f a)).
  destruct (g1 (f a)); auto.
  destruct H1.
  specialize (H2 a0 H1).
  pose proof proj2 H2 eq_refl.

  exfalso.
  rewrite Disjoint_spec in H.
  apply (H (f a0)).
  + constructor; auto.
  + rewrite H3; constructor; auto.
Qed.

Lemma is_guarded_inj_spec {A B: Type} (P: A -> Prop) (f: A -> B):
  is_guarded_inj P f ->
  forall a1 a2: A, P a1 -> P a2 -> f a1 = f a2 -> a1 = a2.
Proof.
  intros.
  destruct H as [g ?].
  pose proof H (f a2).
  rewrite (is_guarded_inj_rev_aux P f g a2) in H3 by auto.
  destruct H3 as [_ ?].
  specialize (H3 a1 H0).
  tauto.
Qed.

Lemma is_guarded_inj_spec' {A B: Type} (P: A -> Prop) (f: A -> B):
  is_guarded_inj P f ->
  forall a1 a2: A, P a1 -> P a2 -> a1 <> a2 -> f a1 <> f a2.
Proof.
  intros.
  specialize (is_guarded_inj_spec _ _ H a1 a2 H0 H1).
  intros ? ?.
  apply H2.
  apply H3; auto.
Qed.

Lemma is_guarded_inj_disjoint_union_aux {A B: Type} (P1 P2 P: A -> Prop) (f: A -> B) (g1 g2: B -> option A):
  Prop_join P1 P2 P ->
  is_rev_fun P1 f g1 ->
  is_rev_fun P2 f g2 ->
  (forall a1 a2, P1 a1 -> P2 a2 -> f a1 <> f a2) ->
  let g := fun b => match g1 b with Some a => Some a | _ => g2 b end in
  is_rev_fun P f g.
Proof.
  intros.
  destruct H.
  intro b.
  specialize (H0 b); specialize (H1 b).
  subst g; cbv beta.
  destruct (g1 b); [| destruct (g2 b)].
  + split; [firstorder |].
    intros.
    rewrite H in H4; destruct H4.
    - apply (proj2 H0); auto.
    - pose proof proj2 (proj2 H0 a (proj1 H0)) eq_refl.
      split; intros.
      * exfalso.
        apply (H2 a a0 (proj1 H0) H4).
        congruence.
      * subst a; auto.
  + split; [firstorder |].
    intros.
    rewrite H in H4; destruct H4.
    - pose proof proj2 (proj2 H1 a (proj1 H1)) eq_refl.
      split; intros.
      * exfalso.
        apply (H2 a0 a H4 (proj1 H1)).
        congruence.
      * subst a; auto.
    - apply (proj2 H1); auto.
  + intros.
    rewrite H in H4; firstorder.
Qed.

Lemma is_guarded_inj_disjoint_union {A B: Type} (P1 P2 P: A -> Prop) (f: A -> B):
  Prop_join P1 P2 P ->
  is_guarded_inj P1 f ->
  is_guarded_inj P2 f ->
  (forall a1 a2, P1 a1 -> P2 a2 -> f a1 <> f a2) ->
  is_guarded_inj P f.
Proof.
  intros.
  destruct H0 as [g1 ?], H1 as [g2 ?].
  exists (fun b => match g1 b with Some a => Some a | _ => g2 b end).
  eapply is_guarded_inj_disjoint_union_aux; eauto.
Qed.

Lemma is_guarded_inj_proper_aux1 {A B: Type} (P: A -> Prop) (f1 f2: A -> B):
  guarded_pointwise_relation P eq f1 f2 ->
  is_guarded_inj P f1 ->
  is_guarded_inj P f2.
Proof.
  intros.
  destruct H0 as [g ?].
  exists g.
  intro b; specialize (H0 b); destruct (g b).
  + destruct H0; split; auto.
    intros; specialize (H1 a0 H2).
    rewrite guarded_pointwise_relation_spec in H.
    rewrite H in H1 by auto; auto.
  + intros; specialize (H0 a H1).
    rewrite guarded_pointwise_relation_spec in H.
    rewrite H in H0 by auto; auto.
Qed.

Instance is_guarded_inj_proper1 {A B: Type} (P: A -> Prop): Proper (guarded_pointwise_relation P eq ==> iff) (@is_guarded_inj A B P).
Proof.
  hnf; intros.
  split; apply is_guarded_inj_proper_aux1; auto.
  symmetry; auto.
Qed.

Lemma is_guarded_inj_proper_aux2 {A B: Type} (P1 P2: A -> Prop) (f: A -> B):
  Same_set P1 P2 ->
  is_guarded_inj P1 f ->
  is_guarded_inj P2 f.
Proof.
  intros.
  destruct H0 as [g ?].
  exists g.
  rewrite Same_set_spec in H.
  intro b; specialize (H0 b); destruct (g b).
  + rewrite H in H0.
    destruct H0; split; auto.
    intros; rewrite <- H in H2; auto.
  + intros; rewrite <- H in H1; auto.
Qed.

Instance is_guarded_inj_proper2 {A B: Type}: Proper (Same_set ==> eq ==> iff) (@is_guarded_inj A B).
Proof.
  do 2 (hnf; intros); subst.
  split; apply is_guarded_inj_proper_aux2; auto.
  symmetry; auto.
Qed.

Instance image_set_proper1 {A B: Type} (P: A -> Prop) : Proper (guarded_pointwise_relation P (@eq B) ==> Same_set) (image_set P).
Proof.
  hnf; intros.
  rewrite Same_set_spec.
  rewrite guarded_pointwise_relation_spec in H.
  intro z.
  rewrite !image_set_spec.
  firstorder; subst; firstorder.
Qed.
