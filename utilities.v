Require Import List.
Require Import Omega.

Definition Sublist {A} (L1 L2 : list A) : Prop := forall a, In a L1 -> In a L2.

Lemma Sublist_refl: forall A (L : list A), Sublist L L. Proof. repeat intro; auto. Qed.

Lemma Sublist_trans: forall A (L1 L2 L3 : list A), Sublist L1 L2 -> Sublist L2 L3 -> Sublist L1 L3.
Proof. repeat intro; apply H0; apply H; trivial. Qed.

Add Parametric Relation {A} : (list A) Sublist
    reflexivity proved by (@Sublist_refl A)
    transitivity proved by (@Sublist_trans A) as Sublist_rel.

Lemma Sublist_nil: forall A (L : list A), Sublist nil L. Proof. repeat intro; inversion H. Qed.

Lemma Sublist_cons: forall A (a : A) L, Sublist L (a :: L). Proof. repeat intro; simpl; auto. Qed.

Lemma Sublist_app: forall A (L1 L2 L3 L4: list A), Sublist L1 L2 -> Sublist L3 L4 -> Sublist (L1 ++ L3) (L2 ++ L4).
Proof. repeat intro; apply in_app_or in H1; apply in_or_app; destruct H1; [left; apply H | right; apply H0]; trivial. Qed.

Lemma Sublist_app_2: forall A (l1 l2 l3 : list A), Sublist l1 l3 -> Sublist l2 l3 -> Sublist (l1 ++ l2) l3.
Proof. repeat intro; apply in_app_or in H1; destruct H1; [apply H | apply H0]; trivial. Qed.

Lemma In_tail: forall A (a : A) L, In a (tl L) -> In a L.
Proof. induction L; simpl; auto. Qed.

Definition eq_as_set {A} (L1 L2 : list A) : Prop := Sublist L1 L2 /\ Sublist L2 L1.

Notation "a '~=' b" := (eq_as_set a b) (at level 1).

Lemma eq_as_set_refl: forall A (L : list A), L ~= L. Proof. intros; split; apply Sublist_refl. Qed.

Lemma eq_as_set_sym: forall A (L1 L2 : list A), L1 ~= L2 -> L2 ~= L1. Proof. intros; hnf in *; firstorder. Qed.

Lemma eq_as_set_trans: forall A (L1 L2 L3 : list A), L1 ~= L2 -> L2 ~= L3 -> L1 ~= L3.
Proof. intros; hnf in *; intuition; transitivity L2; trivial. Qed.

Add Parametric Relation {A} : (list A) eq_as_set
    reflexivity proved by (eq_as_set_refl A)
    symmetry proved by (eq_as_set_sym A)
    transitivity proved by (eq_as_set_trans A) as eq_as_set_rel.

Lemma eq_as_set_app: forall A (L1 L2 L3 L4: list A), L1 ~= L2 -> L3 ~= L4 -> (L1 ++ L3) ~= (L2 ++ L4).
Proof. intros; hnf in *; intuition; apply Sublist_app; trivial. Qed.

Lemma Forall_tl: forall {A : Type} (P : A -> Prop) (x : A) (l : list A), Forall P (x :: l) -> Forall P l.
Proof. intros; rewrite Forall_forall in *; intros. apply H, in_cons; auto. Qed.

Lemma Forall_app: forall {A : Type} (P : A -> Prop) (l1 l2 : list A), Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1; intros. rewrite app_nil_l; auto. generalize (Forall_inv H); intros.
  rewrite <- app_comm_cons. apply Forall_cons; auto. apply IHl1; auto. apply Forall_tl with a; auto.
Qed.

Lemma Forall_sublist: forall {A : Type} (P : A -> Prop) (l1 l2 : list A), Sublist l1 l2 -> Forall P l2 -> Forall P l1.
Proof. intros; hnf in *. rewrite Forall_forall in *; intro y; intros. apply H0, H; auto. Qed.

Lemma map_sublist: forall (A B : Type) (f : A -> B) (l1 l2 : list A), Sublist l1 l2 -> Sublist (map f l1) (map f l2).
Proof. intros; hnf in *; intros. rewrite in_map_iff in *. destruct H0 as [y [? ?]]. exists y; split; auto. Qed.


Lemma sublist_reverse: forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A),
                         NoDup l1 -> length l1 = length l2 -> Sublist l1 l2 -> Sublist l2 l1.
Proof.
  induction l1; intros. destruct l2; auto. simpl in H0; inversion H0.
  generalize (H1 a); intros. assert (In a (a :: l1)) as S by apply in_eq; specialize (H2 S); clear S.
  generalize (in_split a l2 H2); intro S; clear H2; destruct S as [l3 [l4 ?]].
  intro y; intros. destruct (eq_dec y a). subst. apply in_eq. apply in_cons. subst. apply in_app_or in H3.
  assert (In y l3 \/ In y l4). destruct H3; [left; auto | right]. apply in_inv in H2. destruct H2; [exfalso | ]; auto.
  clear H3. apply in_or_app in H2. unfold Sublist in IHl1 at 2. apply IHl1 with (l3 ++ l4).
  rewrite <- app_nil_l in H. apply NoDup_remove_1 in H. rewrite app_nil_l in H. apply H.
  rewrite app_length in *. simpl in H0. omega. intro z; intros. clear H2 n y H0. specialize (H1 z).
  generalize (in_cons a z l1 H3); intro S; specialize (H1 S); clear S. apply in_app_or in H1. apply in_or_app.
  destruct H1. left; auto. apply in_inv in H0. right; destruct H0. subst. rewrite <- app_nil_l in H.
  apply NoDup_remove_2 in H. rewrite app_nil_l in H. exfalso; intuition. auto. auto.
Qed.

Lemma NoDup_cons_1 : forall (A : Type) (x : A) (l : list A), NoDup (x :: l) -> NoDup l.
Proof. intros. rewrite <- (app_nil_l (x :: l)) in H. apply NoDup_remove_1 in H. rewrite app_nil_l in H. auto. Qed.

Lemma NoDup_cons_2 : forall (A : Type) (x : A) (l : list A), NoDup (x :: l) -> ~ In x l.
Proof. intros. rewrite <- (app_nil_l (x :: l)) in H. apply NoDup_remove_2 in H. rewrite app_nil_l in H. auto. Qed.

Lemma NoDup_app_r: forall (A : Type) (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l2.
Proof. induction l1; simpl; intros; auto. apply NoDup_cons_1 in H. apply IHl1. auto. Qed.

Lemma NoDup_app_l: forall (A : Type) (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  intros A l1 l2. revert l1. induction l2; intros. rewrite app_nil_r in H. apply H.
  apply NoDup_remove_1 in H. apply IHl2. apply H.
Qed.

Lemma NoDup_app_not_in: forall (A : Type) (l1 l2 : list A), NoDup (l1 ++ l2) -> forall y, In y l1 -> ~ In y l2.
Proof.
  induction l1; intros. inversion H0. rewrite <- app_comm_cons in H. 
  apply in_inv in H0. destruct H0. subst. apply NoDup_cons_2 in H. intro. apply H.
  apply in_or_app. right. apply H0. apply NoDup_cons_1 in H. apply IHl1; auto.
Qed.

Lemma NoDup_app_inv: forall (A : Type) (l1 l2 : list A),
                       NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1; intros. rewrite app_nil_l. auto. rewrite <- app_comm_cons. apply NoDup_cons.
  intro. apply in_app_or in H2. destruct H2. apply NoDup_cons_2 in H. auto.
  apply (H1 a). apply in_eq. auto. apply IHl1. apply NoDup_cons_1 in H. auto.
  auto. intro y; intros. apply H1. apply in_cons. auto.
Qed.

Lemma NoDup_app_eq: forall (A : Type) (l1 l2 : list A),
                      NoDup (l1 ++ l2) <-> NoDup l1 /\ NoDup l2 /\ (forall x, In x l1 -> ~ In x l2).
Proof.
  intros. split; intros. split. apply NoDup_app_l with l2. auto. split. apply NoDup_app_r with l1; auto.
  apply NoDup_app_not_in; auto. destruct H as [? [? ?]]. apply NoDup_app_inv; auto.
Qed.

Lemma Sublist_cons_in: forall (A : Type) (a : A) (l1 l2 : list A), In a l2 -> Sublist l1 l2 -> Sublist (a :: l1) l2.
Proof. intros. intro y; intros. apply in_inv in H1. destruct H1. subst; auto. specialize (H0 y). apply H0; auto. Qed.

Lemma Sublist_cons_2: forall (A : Type) (a : A) (l1 l2 : list A), Sublist l1 l2 -> Sublist l1 (a :: l2).
Proof. repeat intro. apply in_cons. apply (H a0); auto. Qed.

Lemma remove_sublist: forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x : A),
                        Sublist (remove eq_dec x l) l.
Proof.
  induction l; intros; simpl in *. apply Sublist_nil. destruct (eq_dec x a). subst. apply Sublist_cons_2. apply IHl.
  apply Sublist_cons_in. apply in_eq. apply Sublist_cons_2. auto.
Qed.

Lemma remove_in_2: forall  (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x y : A),
                     In x l -> x = y \/ In x (remove eq_dec y l).
Proof.
  induction l; intros; simpl in *. right; auto. destruct (eq_dec y a); destruct H. subst. left; auto.
  apply IHl; auto. subst. right; apply in_eq. specialize (IHl x y H). destruct IHl. left; auto.
  right; apply in_cons. auto.
Qed.
