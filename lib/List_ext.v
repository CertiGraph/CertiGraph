Require Export Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Export Coq.Sorting.Permutation.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.

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

Lemma eq_as_set_nil: forall {A} (l : list A), nil ~= l -> l = nil.
Proof. intros; destruct l; auto. destruct H. assert (In a (a :: l)) by apply in_eq. specialize (H0 a H1). inversion H0. Qed.

Lemma Forall_tl: forall {A : Type} (P : A -> Prop) (x : A) (l : list A), Forall P (x :: l) -> Forall P l.
Proof. intros; rewrite Forall_forall in *; intros. apply H, in_cons; auto. Qed.

Lemma Forall_app: forall {A : Type} (P : A -> Prop) (l1 l2 : list A), Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1; intros. rewrite app_nil_l; auto. generalize (Forall_inv H); intros.
  rewrite <- app_comm_cons. apply Forall_cons; auto. apply IHl1; auto. apply Forall_tl with a; auto.
Qed.

Lemma Forall_app_iff: forall {A : Type} (P : A -> Prop) (l1 l2 : list A), Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  intros; induction l1; intros.
  + simpl.
    assert (Forall P nil) by constructor; tauto.
  + simpl; split; intros.
    - inversion H; subst; split; try tauto.
      constructor; auto; tauto.
    - destruct H.
      inversion H; subst.
      constructor; auto; tauto.
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

Lemma In_remove_length: forall {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l: list A) x,
  In x l -> length (remove eq_dec x l) < length l.
Proof.
  intros ? ? l x.
  apply (@proj1 _ (length (remove eq_dec x l) <= length l)).
  induction l.
  + split; [intro H; inversion H | reflexivity].
  + simpl.
    destruct (eq_dec x a).
    - split; [intros; omega | omega].
    - split.
      * intros. simpl.
        destruct IHl.
        destruct H; [congruence | apply H0 in H].
        omega.
      * simpl; omega.
Qed.

Lemma not_in_app: forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) x a (l : list A),
                    (~ In x (a :: l)) -> x <> a /\ ~ In x l.
Proof.
  intros; split. destruct (eq_dec x a); auto. subst; intro; apply H. apply in_eq. intro. apply H; apply in_cons; auto.
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

Lemma remove_in_3: forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x y : A),
                     In x (remove eq_dec y l) <-> In x l /\ x <> y.
Proof.
  induction l; intros; simpl in *.
  + tauto.
  + destruct (eq_dec y a).
    - specialize (IHl x y).
      assert (a = x <-> x = y) by (split; congruence).
      tauto.
    - simpl.
      specialize (IHl x y).
      assert (a = x -> x <> y) by (intros; congruence).
      tauto.
Qed.

Lemma NoDup_Sublist_length: forall {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A),
  Sublist l1 l2 -> NoDup l1 -> length l1 <= length l2.
Proof.
  intros.
  revert l2 H; induction H0; intros.
  + simpl; omega.
  + simpl.
    specialize (IHNoDup (remove eq_dec x l2)).
    assert (Sublist l (remove eq_dec x l2)).
    Focus 1. {
      unfold Sublist in *; intros y; specialize (H1 y).
      rewrite remove_in_3.
      destruct (eq_dec x y); [subst; tauto |].
      simpl in H1.
      assert (y = x <-> x = y) by (split; congruence).
      tauto.
    } Unfocus.
    apply IHNoDup in H2.
    specialize (H1 x (or_introl eq_refl)).
    pose proof In_remove_length eq_dec l2 x H1.
    omega.
Qed.

Lemma remove_len_le: forall  (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x : A),
                       length (remove eq_dec x l) <= length l.
Proof. induction l; intros; simpl in *. auto. destruct (eq_dec x a). intuition. simpl. intuition. Qed.

Definition dupOrder {A} (i1 i2 : list A) := length i1 < length i2.

Lemma dupOrder_wf' A : forall len (i: list A), length i <= len -> Acc dupOrder i.
Proof.
  induction len; intros; constructor; intros; unfold dupOrder in * |-; [exfalso | apply IHlen]; intuition.
Qed.

Lemma dupOrder_wf A : well_founded (@dupOrder A).
Proof. red; intro; eapply dupOrder_wf'; eauto. Defined.

(* This definition is not necessary. *)
(* Change to the following definition some time. *)
(*
Fixpoint remove_dup {A} {EA: EqDec A eq} (l: list A) : list A :=
  match l with
  | nil => nil
  | x :: l0 => remove equiv_dec x (remove_dup l0)
  end.
*)
Definition remove_dup {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) : list A -> list A.
  refine (
      Fix (dupOrder_wf A) (fun _ => list A)
          (fun (inp : list A) =>
             match inp return ((forall inp2 : list A, dupOrder inp2 inp -> list A) -> list A) with
               | nil => fun _ => nil
               | x :: l => fun f => x :: (f (remove eq_dec x l) _)
             end)).
  apply le_lt_trans with (length l). apply remove_len_le. simpl; apply lt_n_Sn.
Defined.

Lemma remove_dup_unfold:
  forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (i : list A),
    remove_dup eq_dec i = match i with
                            | nil => nil
                            | x :: l => x :: remove_dup eq_dec (remove eq_dec x l)
                          end.
Proof.
  intros. unfold remove_dup at 1; rewrite Fix_eq. destruct i; auto. intros.
  assert (f = g) by (extensionality y; extensionality p; auto); subst; auto.
Qed.

Lemma remove_dup_len_le: forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A),
                           length (remove_dup eq_dec l) <= length l.
Proof.
  intros. remember (length l). assert (length l <= n) by omega. clear Heqn. revert H. revert l.
  induction n; intros; rewrite remove_dup_unfold; destruct l; auto. inversion H. simpl. apply le_n_S. apply IHn.
  simpl in H; apply le_S_n in H. apply le_trans with (length l). apply remove_len_le. auto.
Qed.

Lemma remove_dup_in_inv: forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) l,
                           In x l <-> In x (remove_dup eq_dec l).
Proof.
  intros. remember (length l). assert (length l <= n) by omega. clear Heqn. revert l H.
  induction n; intros; rewrite remove_dup_unfold; destruct l; auto. split; auto. simpl in H. omega. split; auto.
  destruct (eq_dec a x). subst. split; intro; apply in_eq. assert (length (remove eq_dec a l) <= n).
  apply le_trans with (length l). apply remove_len_le. simpl in H. omega. specialize (IHn _ H0). clear H0.
  split; intro; simpl in H0; destruct H0. exfalso; intuition. right. rewrite <- IHn. destruct (remove_in_2 A eq_dec l x a H0).
  exfalso; intuition. auto. exfalso; intuition. right. rewrite <- IHn in H0. generalize (remove_sublist A eq_dec l a x H0).
  intro; auto.
Qed.

Lemma remove_dup_nodup: forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) l, NoDup (remove_dup eq_dec l).
Proof.
  intros. remember (length l). assert (length l <= n) by omega. clear Heqn. revert H. revert l.
  induction n; intros; rewrite remove_dup_unfold; destruct l; simpl. apply NoDup_nil. inversion H. apply NoDup_nil.
  apply NoDup_cons. generalize (remove_In eq_dec l a); intro. intro; apply H0; clear H0. rewrite <- remove_dup_in_inv in H1.
  apply H1. apply IHn. simpl in H. apply le_trans with (length l). apply remove_len_le. apply le_S_n. apply H.
Qed.

Lemma eq_as_set_permutation: forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A),
                               NoDup l1 -> NoDup l2 -> l1 ~= l2 -> Permutation l1 l2.
Proof.
  induction l1; intros. destruct l2. constructor. destruct H1. assert (In a (a :: l2)) by apply in_eq. specialize (H2 a H3).
  inversion H2. destruct H1. assert (In a l2). apply H1, in_eq. apply in_split in H3. destruct H3 as [ll1 [ll2 ?]]. subst.
  generalize (NoDup_remove_1 _ _ _ H0); intro. generalize (NoDup_remove_2 _ _ _ H0); intro.
  assert (Permutation l1 (ll1 ++ ll2)). apply IHl1. apply NoDup_cons_1 in H; auto. auto. split; intro x; intros.
  destruct (eq_dec x a). subst. apply NoDup_cons_2 in H. exfalso; intuition. assert (In x (a :: l1)). apply in_cons; auto.
  specialize (H1 x H6). apply in_app_or in H1. apply in_or_app. destruct H1; [left | right]. auto. apply in_inv in H1.
  destruct H1. exfalso; intuition. auto. destruct (eq_dec x a). subst. intuition. assert (In x (a :: l1)). apply H2.
  apply in_app_or in H5. apply in_or_app. destruct H5; [left | right]. auto. apply in_cons. auto. apply in_inv in H6.
  destruct H6. exfalso; intuition. auto. assert (Permutation l1 (ll2 ++ ll1)). apply Permutation_trans with (ll1 ++ ll2).
  auto. apply Permutation_app_comm. apply (Permutation_cons a) in H6. apply Permutation_trans with (a :: ll2 ++ ll1). auto.
  rewrite app_comm_cons. apply Permutation_app_comm.
Qed.

Fixpoint intersect {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) : list A :=
  match l1 with
    | nil => nil
    | e :: l => if (in_dec eq_dec e l2)
                then e :: intersect eq_dec l l2
                else intersect eq_dec l l2
  end.

Lemma intersect_property {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}):
  forall l1 l2 x, (In x l1 /\ In x l2) <-> In x (intersect eq_dec l1 l2).
Proof.
  induction l1; intros; simpl. intuition. destruct (in_dec eq_dec a l2). split; intros. destruct H as [[? | ?] ?]. subst.
  apply in_eq. apply in_cons. rewrite <- IHl1. split; auto. split. apply in_inv in H. destruct H; [left | right]; auto.
  rewrite <- IHl1 in H. destruct H; auto. apply in_inv in H; destruct H. subst; auto. rewrite <- IHl1 in H; destruct H; auto.
  rewrite <- IHl1. intuition. subst; intuition.
Qed.

Lemma intersect_nodup {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}):
  forall (l1 l2 : list A), NoDup l1 -> NoDup (intersect eq_dec l1 l2).
Proof.
  induction l1; intros; simpl; auto. destruct (in_dec eq_dec a l2). apply NoDup_cons. apply NoDup_cons_2 in H. intro; apply H.
  rewrite <- intersect_property in H0. destruct H0; auto. apply IHl1. apply NoDup_cons_1 in H; auto. apply IHl1.
  apply NoDup_cons_1 in H. auto.
Qed.

Fixpoint subtract {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) : list A :=
  match l2 with
    | nil => l1
    | e :: l => subtract eq_dec (remove eq_dec e l1) l
  end.

Lemma remove_app {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}):
  forall l1 l2 a, remove eq_dec a (l1 ++ l2) = remove eq_dec a l1 ++ remove eq_dec a l2.
Proof.
  induction l1; intros; simpl; auto. destruct (eq_dec a0 a). subst. apply IHl1. rewrite <- app_comm_cons. f_equal. apply IHl1.
Qed.

Lemma remove_not_in {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}): forall l x, ~ In x l -> remove eq_dec x l = l.
Proof.
  induction l; intros; simpl; auto. destruct (eq_dec x a). subst. exfalso; apply H, in_eq. f_equal. apply IHl. intro; apply H.
  apply in_cons. auto.
Qed.

Lemma remove_middle {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}):
  forall l1 l2 a, NoDup (l1 ++ a :: l2) -> remove eq_dec a (l1 ++ a :: l2) = l1 ++ l2.
Proof.
  intros. rewrite (remove_app eq_dec). f_equal. apply NoDup_remove_2 in H. apply remove_not_in. intro; apply H, in_or_app; left.
  auto. simpl. destruct (eq_dec a a). apply remove_not_in. apply NoDup_remove_2 in H. intro; apply H, in_or_app; right; auto.
  exfalso; apply n; auto.
Qed.

Lemma subtract_permutation {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}):
  forall (l1 l2 : list A), NoDup l1 -> NoDup l2 -> Sublist l2 l1 -> Permutation l1 (subtract eq_dec l1 l2 ++ l2).
Proof.
  intros l1 l2; revert l1; induction l2; intros; simpl. rewrite app_nil_r. apply Permutation_refl.
  assert (In a (a :: l2)) by apply in_eq. generalize (H1 a H2); intros. apply in_split in H3. destruct H3 as [ll1 [ll2 ?]].
  subst. assert (Sublist l2 (ll1 ++ ll2)). intro y; intros. apply in_or_app. assert (In y (a :: l2)) by (apply in_cons; auto).
  specialize (H1 y H4). apply in_app_or in H1. destruct H1; [left | right]; auto. apply in_inv in H1. destruct H1. subst.
  apply NoDup_cons_2 in H0. intuition. auto. apply Permutation_trans with (a :: ll1 ++ ll2). apply Permutation_sym.
  apply Permutation_middle. apply Permutation_cons_app. rewrite (remove_middle eq_dec); auto. apply IHl2.
  apply NoDup_remove_1 in H. auto. apply NoDup_remove_1 in H. apply NoDup_cons_1 in H0. auto. auto.
Qed.

Lemma subtract_nodup {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}):
  forall (l1 l2 : list A), NoDup l1 -> NoDup (subtract eq_dec l1 l2).
Proof.
  intros l1 l2; revert l1; induction l2; intros; simpl; auto. apply IHl2. destruct (in_dec eq_dec a l1). apply in_split in i.
  destruct i as [ll1 [ll2 ?]]. subst. rewrite remove_app. assert (~ In a ll1 /\ ~ In a ll2). apply NoDup_remove_2 in H.
  split; intro; apply H, in_or_app; [left | right] ; auto. destruct H0. rewrite (remove_not_in eq_dec _ _ H0). simpl.
  destruct (eq_dec a a). rewrite (remove_not_in eq_dec _ _ H1). apply NoDup_remove_1 in H. auto. exfalso; intuition.
  rewrite (remove_not_in eq_dec _ _ n). auto.
Qed.

Lemma subtract_property {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}):
  forall l1 l2 x, (In x l1 /\ ~ In x l2) <-> In x (subtract eq_dec l1 l2).
Proof.
  intros l1 l2; revert l1; induction l2; intros. simpl; auto; intuition. split; intros. destruct H.
  apply (not_in_app eq_dec) in H0. destruct H0. simpl. rewrite <- IHl2. split; auto. apply (remove_in_2 _ eq_dec _ _ a) in H.
  destruct H; intuition. simpl in H. rewrite <- IHl2 in H. destruct H. split. apply (remove_sublist _ eq_dec l1 a x); auto.
  intro. apply in_inv in H1. destruct H1. subst. apply remove_In in H. auto. apply H0; auto.
Qed.

Lemma tri_list_split {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}):
  forall (l l1 l2 : list A), NoDup l -> NoDup l1 -> NoDup l2 -> l ~= (l1 ++ l2) ->
                             exists i1 i2 i3, Permutation l1 (i1 ++ i2) /\ Permutation l2 (i2 ++ i3) /\
                                              Permutation l (i1 ++ i2 ++ i3).
Proof.
  intros. remember (intersect eq_dec l1 l2) as j2. remember (subtract eq_dec l1 j2) as j1.
  remember (subtract eq_dec l2 j2) as j3. exists j1, j2, j3. assert (Permutation l1 (j1 ++ j2)). rewrite Heqj1.
  apply subtract_permutation. auto. rewrite Heqj2. apply intersect_nodup. auto. intro y; intros. rewrite Heqj2 in H3.
  rewrite <- intersect_property in H3. intuition. split. auto. assert (Permutation l2 (j2 ++ j3)). rewrite Heqj3.
  apply Permutation_trans with (subtract eq_dec l2 j2 ++ j2). apply subtract_permutation. auto. rewrite Heqj2.
  apply intersect_nodup. auto. intro y; intros. rewrite Heqj2 in H4. rewrite <- intersect_property in H4.
  intuition. apply Permutation_app_comm. split; auto. remember (subtract eq_dec l l2) as j4.
  apply Permutation_trans with (j4 ++ l2). rewrite Heqj4. apply subtract_permutation; auto. destruct H2. repeat intro.
  apply (H5 a). apply in_or_app; right; auto. apply Permutation_app. apply (eq_as_set_permutation eq_dec). rewrite Heqj4.
  apply subtract_nodup; auto. rewrite Heqj1. apply subtract_nodup; auto. rewrite Heqj1, Heqj4. destruct H2. hnf in H2, H5.
  split; intro x; intros; rewrite <- subtract_property in H6; destruct H6; rewrite <- subtract_property; split. apply H2 in H6.
  apply in_app_or in H6. destruct H6; intuition. rewrite Heqj2. intro; apply H7. rewrite <- intersect_property in H8.
  destruct H8; auto. apply H5. apply in_or_app; left; auto. intro; apply H7. rewrite Heqj2. rewrite <- intersect_property.
  split; auto. auto.
Qed.

Arguments tri_list_split [A] _ [l] [l1] [l2] _ _ _ _.

Lemma Permutation_NoDup (A : Type) : forall (l1 l2 : list A), Permutation l1 l2 -> NoDup l1 -> NoDup l2.
Proof.
  induction l1; intros. apply Permutation_nil in H. subst; auto. assert (In a l2). apply (Permutation_in _ H). apply in_eq.
  apply in_split in H1. destruct H1 as [ll1 [ll2 ?]]. subst. generalize H; intro. apply Permutation_cons_app_inv in H.
  generalize (NoDup_cons_1 _ _ _ H0); intro. specialize (IHl1 _ H H2). assert (In a l1 <-> In a (ll1 ++ ll2)).
  split; apply (Permutation_in a); auto. apply Permutation_sym; auto. apply NoDup_app_inv. apply NoDup_app_l with ll2; auto.
  apply NoDup_cons. apply NoDup_cons_2 in H0. intro. apply H0. rewrite H3. apply in_or_app. right; auto.
  apply NoDup_app_r in IHl1. auto. intros. intro. apply in_inv in H5. destruct H5. subst. assert (In x (ll1 ++ ll2)).
  apply in_or_app. left; auto. rewrite <- H3 in H5. apply NoDup_cons_2 in H0. auto.
  apply NoDup_app_not_in with (y := x) in IHl1. apply IHl1. auto. auto.
Qed.

Arguments Permutation_NoDup [A] [l1] [l2] _ _.

Lemma double_list_split {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}):
  forall (l1 l2 : list A), NoDup l1 -> NoDup l2 -> exists i1 i2 i3, Permutation l1 (i1 ++ i2) /\ Permutation l2 (i2 ++ i3) /\
                                                                    NoDup (i1 ++ i2 ++ i3).
Proof.
  intros. remember (intersect eq_dec l1 l2) as j2. remember (subtract eq_dec l1 j2) as j1.
  remember (subtract eq_dec l2 j2) as j3. exists j1, j2, j3. assert (Permutation l1 (j1 ++ j2)). rewrite Heqj1.
  apply subtract_permutation. auto. rewrite Heqj2. apply intersect_nodup. auto. intro y; intros. rewrite Heqj2 in H1.
  rewrite <- intersect_property in H1. intuition. split. auto. assert (Permutation l2 (j2 ++ j3)). rewrite Heqj3.
  apply Permutation_trans with (subtract eq_dec l2 j2 ++ j2). apply subtract_permutation. auto. rewrite Heqj2.
  apply intersect_nodup. auto. intro y; intros. rewrite Heqj2 in H2. rewrite <- intersect_property in H2. intuition.
  apply Permutation_app_comm. split; auto. apply NoDup_app_inv. rewrite Heqj1. apply subtract_nodup; auto. apply NoDup_app_inv.
  rewrite Heqj2. apply intersect_nodup; auto. rewrite Heqj3. apply subtract_nodup; auto. intros. rewrite Heqj3. intro.
  rewrite <- subtract_property in H4. destruct H4. auto. intros. rewrite Heqj1 in H3. rewrite <- subtract_property in H3.
  destruct H3. intro. apply in_app_or in H5. destruct H5. auto. apply H4; clear H4. rewrite Heqj3 in H5.
  rewrite <- subtract_property in H5. destruct H5 as [? _]. assert (In x l1 /\ In x l2) by intuition.
  rewrite intersect_property in H5. rewrite Heqj2. apply H5.
Qed.

Arguments double_list_split [A] _ [l1] [l2] _ _.

Lemma eq_as_set_spec: forall {A} (l1 l2: list A),
  (forall x, In x l1 <-> In x l2) ->
  l1 ~= l2.
Proof.
  intros.
  split; intro x; intros; specialize (H x); tauto.
Qed.

Notation "a '+::' b" := (a ++ (b :: nil)) (at level 19).

Lemma app_cons_assoc: forall {A} (l1 l2 : list A) x, l1 ++ x :: l2 = l1 +:: x ++ l2.
Proof. intros. induction l1. simpl. auto. rewrite <- app_comm_cons. rewrite IHl1. do 2 rewrite <- app_comm_cons. auto. Qed.

Fixpoint judgeNoDup {A} {EA : EqDec A eq} (l : list A) : bool :=
  match l with
    | nil => true
    | s :: ls => if in_dec equiv_dec s ls then false else judgeNoDup ls
  end.

Lemma judgeNoDup_ok {A} {EA : EqDec A eq}: forall (l : list A), judgeNoDup l = true <-> NoDup l.
Proof.
  induction l; intros; split; intros. apply NoDup_nil. simpl; auto.
  simpl in H; destruct (in_dec equiv_dec a l); [discriminate H | apply NoDup_cons; auto; rewrite <- IHl; auto].
  simpl; destruct (in_dec equiv_dec a l).
  change (a :: l) with (nil ++ a :: l) in H; apply NoDup_remove_2 in H; simpl in H; contradiction.
  change (a :: l) with (nil ++ a :: l) in H; apply NoDup_remove_1 in H; simpl in H; rewrite IHl; auto.
Qed.

Lemma nodup_dec {A} {EA : EqDec A eq}: forall (l : list A), {NoDup l} + {~ NoDup l}.
Proof.
  intros; destruct (judgeNoDup l) eqn : Hnodup;
  [left; rewrite judgeNoDup_ok in Hnodup; assumption |
   right; intro H; rewrite <- judgeNoDup_ok in H; rewrite Hnodup in H; discriminate H].
Qed.

Definition Dup {A} (L : list A) : Prop := ~ NoDup L.

Lemma Dup_unfold {A} {EA : EqDec A eq}: forall (a : A) (L : list A), Dup (a :: L) -> In a L \/ Dup L.
Proof.
  intros; destruct (in_dec equiv_dec a L);
  [left; trivial | right; intro; apply H; constructor; auto].
Qed.

Lemma Dup_cyclic {A} {EA : EqDec A eq} : forall (L : list A), Dup L -> exists a L1 L2 L3, L = L1 ++ (a :: L2) ++ (a :: L3).
Proof.
  induction L. destruct 1. constructor. intros. apply Dup_unfold in H. destruct H. apply in_split in H.
  destruct H as [L1 [L2 ?]]. exists a. exists nil. exists L1. exists L2. rewrite H. simpl. trivial.
  destruct (IHL H) as [a' [L1 [L2 [L3 ?]]]]. rewrite H0. exists a'. exists (a :: L1). exists L2. exists L3. trivial.
Qed.

Fixpoint foot {A} (L : list A) : option A :=
  match L with
    | nil => None
    | a :: nil => Some a
    | a :: L' => foot L'
  end.

Lemma foot_simpl: forall A (a1 a2 : A) (L : list A), foot (a1 :: a2 :: L) = foot (a2 :: L).
Proof. intros. simpl. destruct L; auto. Qed.

Lemma foot_last: forall A (L : list A) (a : A), foot (L +:: a) = Some a.
Proof.
  induction L; auto; intros; destruct L; auto; rewrite <- (IHL a0); simpl; destruct (L +:: a0); simpl; auto.
Qed.

Lemma foot_app: forall A (L1 L2 : list A), L2 <> nil -> foot (L1 ++ L2) = foot L2.
Proof.
  induction L1. auto. intros. rewrite <- app_comm_cons. simpl. case_eq (L1 ++ L2).
  intro. apply app_eq_nil in H0. destruct H0. contradiction. intros. rewrite <- H0. apply IHL1. trivial.
Qed.

Lemma foot_explicit {A}: forall L (a : A), foot L = Some a -> exists L', L = L' +:: a.
Proof.
  induction L. inversion 1. intros. simpl in H. icase L. inv H. exists nil. trivial.
  specialize (IHL a0 H). destruct IHL. exists (a :: x). rewrite <- app_comm_cons. congr.
Qed.

Lemma foot_in {A}: forall (a : A) L, foot L = Some a -> In a L.
Proof. induction L. inversion 1. icase L. simpl. inversion 1. auto. rewrite foot_simpl. right. auto. Qed.

Lemma foot_none_nil {A}: forall (l : list A), foot l = None -> l = nil.
Proof. induction l; intros; auto. simpl in H. destruct l. inversion H. specialize (IHl H). inversion IHl. Qed.

Lemma filter_sublist: forall A f (l: list A), Sublist (filter f l) l.
Proof.
  unfold Sublist; intros.
  induction l; simpl; auto.
  simpl in H.
  destruct (f a0); auto.
  simpl in H; tauto.
Qed.

Lemma NoDup_filter: forall A f (l: list A), NoDup l -> NoDup (filter f l).
Proof.
  intros.
  induction l.
  + simpl; constructor.
  + inversion H; subst.
    simpl; destruct (f a) eqn:?; [constructor |]; auto.
    rewrite filter_In.
    tauto.
Qed.

Lemma exists_list_dec: forall A (l: list A) P,
  (forall x, {P x} + {~ P x}) ->
  ({exists x, In x l /\ P x} + {~ exists x, In x l /\ P x}).
Proof.
  intros.
  induction l.
  + right; intros [x [? ?]].
    inversion H.
  + destruct (X a); [| destruct IHl]; [left | left | right].
    - exists a; split; auto.
      left; auto.
    - destruct e as [? [? ?]].
      exists x; split; auto.
      right; auto.
    - intros [? [? ?]].
      destruct H; [subst; tauto |].
      apply n0; exists x.
      tauto.
Qed.

Lemma exists_list_weak_dec: forall A (l: list A) P
  (X: forall x, (P x) \/ (~ P x)),
  (exists x, In x l /\ P x) \/ (~ exists x, In x l /\ P x).
Proof.
  intros.
  induction l.
  + right; intros [x [? ?]].
    inversion H.
  + destruct (X a); [| destruct IHl]; [left | left | right].
    - exists a; split; auto.
      left; auto.
    - destruct H0 as [? [? ?]].
      exists x; split; auto.
      right; auto.
    - intros [? [? ?]].
      destruct H1; [subst; tauto |].
      apply H0; exists x.
      tauto.
Qed.

(* TODO: As this lemma is proved. many other lemmas about remove can be
replaced by similar existential lemmas. *)
Lemma In_Permutation_cons: forall {A : Type} (l : list A) (x : A),
  In x l ->
  exists l', Permutation l (x :: l').
Proof.
  intros.
  induction l.
  + inversion H.
  + destruct H.
    - exists l; subst; reflexivity.
    - destruct (IHl H) as [l' ?].
      exists (a :: l').
      rewrite H0.
      constructor.
Qed.

Lemma perm_spec_minus_1: forall {A : Type} (l : list A) (P: A -> Prop) (x : A),
  P x ->
  (forall y : A, In y l <-> P y) /\ NoDup l ->
  (exists l', Permutation l (x :: l') /\
    (forall y : A, In y l' <-> P y /\ x <> y) /\ NoDup l').
Proof.
  intros.
  destruct H0.
  rewrite <- H0 in H.
  destruct (In_Permutation_cons _ _ H) as [l' ?].
  exists l'.
  split; auto.
  eapply Permutation_NoDup in H1; eauto.
  pose proof NoDup_cons_1 _ _ _ H1.
  pose proof NoDup_cons_2 _ _ _ H1.
  split; [| auto].
  intro y; rewrite <- H0.
  assert (x = y -> ~ In y l') by (intro; subst; auto).
  pose proof @Permutation_in _ _ _ y H2.
  pose proof @Permutation_in _ _ _ y (Permutation_sym H2).
  simpl in H6, H7.
  tauto.
Qed.

Lemma Permutation_spec_Prop_join: forall {A : Type} (l : list A) (P Pf: A -> Prop) (x : A),
  Prop_join (eq x) Pf P ->
  (forall y : A, In y l <-> P y) /\ NoDup l ->
  (exists l', Permutation l (x :: l') /\
    (forall y : A, In y l' <-> Pf y) /\ NoDup l').
Proof.
  intros.
  destruct H, H0.
  assert (In x l) by (rewrite H0, H; auto).
  destruct (In_Permutation_cons _ _ H3) as [l' ?].
  exists l'.
  split; auto.
  pose proof Permutation_NoDup H4 H2.
  pose proof NoDup_cons_1 _ _ _ H5.
  pose proof NoDup_cons_2 _ _ _ H5.
  split; auto.
  intros.
  pose proof @Permutation_in _ _ _ y H4.
  pose proof @Permutation_in _ _ _ y (Permutation_sym H4).
  simpl in H8, H9.
  clear H6 H2 H3 H4 H5.
  specialize (H y).
  specialize (H0 y).
  specialize (H1 y).
  assert (x = y -> ~ In y l') by (intros; subst; auto).
  tauto.
Qed.

Lemma nodup_remove_perm: forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x : A),
                           NoDup l -> In x l -> Permutation l (x :: remove eq_dec x l).
Proof.
  intros. apply in_split in H0. destruct H0 as [l1 [l2 ?]]. subst.
  rewrite (remove_middle eq_dec _ _ _ H). rewrite app_cons_assoc. 
  apply (@Permutation_app_tail _ _ (x :: l1) l2), Permutation_sym, Permutation_cons_append.
Qed.

Lemma filter_perm: forall {A: Type} (f g: A -> bool) l,
  (forall x, In x l -> f x = negb (g x)) ->
  Permutation l (filter f l ++ filter g l).
Proof.
  intros.
  induction l.
  + reflexivity.
  + simpl.
    pose proof (H a (or_introl eq_refl)).
    spec IHl; [intros; apply H; simpl; auto |].
    destruct (g a) eqn:?H; simpl in H0; rewrite H0.
    - apply Permutation_cons_app; auto.
    - apply Permutation_cons; auto.
Qed.

Lemma map_nodup: forall {A} {B} (f : A -> B) (l : list A), (forall x y : A, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros. induction l; simpl. apply NoDup_nil. apply NoDup_cons.
  + apply NoDup_cons_2 in H0. intro. apply H0. rewrite in_map_iff in H1.
    destruct H1 as [x [? ?]]. specialize (H _ _ H1). subst. auto.
  + apply NoDup_cons_1 in H0. apply IHl. auto.
Qed.

Existing Instance Permutation_app'_Proper.

Ltac split5 := split; [| split; [| split; [| split]]].

Lemma spec_or_list_split: forall {A} (l: list A) P Q,
    NoDup l -> (forall x, In x l <-> P x \/ Q x) ->
    exists lp lq,
      NoDup lp /\
      NoDup lq /\     
      (forall x, In x lp -> P x) /\
      (forall x, In x lq -> Q x) /\
      (forall x, In x l <-> In x lp \/ In x lq).
Proof.
  intros. pose proof (fun x => proj1 (H0 x)). clear H0. induction l.
  + exists nil, nil.
    split5; [constructor | constructor |..]; intro x; simpl; tauto.
  + spec IHl; [inversion H; auto |].
    spec IHl; [intros; apply H1; simpl; auto |].
    destruct IHl as [lp [lq [? [? [? [? ?]]]]]].
    destruct (H1 a (or_introl eq_refl)); [exists (a :: lp), lq | exists lp, (a :: lq)];
    split5; intros; auto.
    - constructor; auto. inversion H; subst. firstorder.
    - destruct H7; [subst |]; auto.
    - simpl; specialize (H5 x); tauto.
    - constructor; auto. inversion H; subst. firstorder.
    - destruct H7; [subst |]; auto.
    - simpl; specialize (H5 x); tauto.
Qed.

Lemma spec_list_split: forall {A} (l: list A) P Q R,
  NoDup l ->
  (forall x, In x l <-> R x) ->
  Prop_join P Q R ->
  exists lp lq,
    NoDup lp /\
    NoDup lq /\
    (forall x, In x lp <-> P x) /\
    (forall x, In x lq <-> Q x) /\
    Permutation l (lp ++ lq).
Proof.
  intros A l P Q R ? EQUIV [? ?].
  assert (forall a, In a l <-> P a \/ Q a) by firstorder.
  clear EQUIV H0 R; rename H2 into H0.
  pose proof (spec_or_list_split l P Q H H0).
  destruct H2 as [lp [lq [? [? [? [? ?]]]]]].
  exists lp, lq. split5; auto.
  + firstorder.
  + firstorder.
  + apply NoDup_Permutation; auto.
    - apply NoDup_app_inv; auto. firstorder.
    - intro; rewrite in_app_iff. firstorder.
Qed.

Fixpoint select {A: Type} {P: A -> Prop} (dec_p: forall x, Decidable (P x)) (l: list A) : list A :=
  match l with
  | nil => nil
  | x :: lx => if dec_p x then x :: select dec_p lx else select dec_p lx
  end.

Lemma select_In {A: Type} {P: A -> Prop} (dec_p: forall x, Decidable (P x)): forall x l,
    In x (select dec_p l) <-> In x l /\ P x.
Proof.
  intros; induction l; simpl; [intuition | destruct (dec_p a)]; split; intro.
  + simpl in H. destruct H; [subst|]; intuition.
  + destruct H. simpl. destruct H; [left | right]; intuition.
  + rewrite IHl in H. intuition.
  + rewrite IHl. destruct H. split; auto. destruct H; [subst; exfalso|]; intuition.
Qed.

Lemma NoDup_select {A: Type} {P: A -> Prop} (dec_p: forall x, Decidable (P x)): forall l,
    NoDup l -> NoDup (select dec_p l).
Proof.
  intro. induction l; intros; simpl; auto. specialize (IHl (NoDup_cons_1 _ _ _ H)).
  apply NoDup_cons_2 in H. destruct (dec_p a); auto. constructor; auto. intro. apply H.
  rewrite select_In in H0. intuition.
Qed.

Lemma or_dec_prop_list_split: forall {A} (l: list A) P Q,
    NoDup l -> (forall x, Decidable (P x)) -> (forall x, Decidable (Q x)) ->
    (forall x, In x l <-> P x \/ Q x) ->
    exists lp lq,
      NoDup lp /\
      NoDup lq /\     
      (forall x, In x lp <-> P x) /\
      (forall x, In x lq <-> Q x) /\
      (forall x, In x l <-> In x lp \/ In x lq).
Proof.
  intros. exists (select X l), (select X0 l). split5; intros.
  + apply NoDup_select; auto.
  + apply NoDup_select; auto.
  + rewrite select_In. firstorder.
  + rewrite select_In. firstorder.
  + do 2 rewrite select_In. firstorder.
Qed.

Fixpoint prefixes {A: Type} (l: list A): list (list A) :=
  match l with
  | nil => nil
  | a :: l0 => nil :: map (cons a) (prefixes l0)
  end.

Definition cprefix {A: Type} (l: list A) := combine (prefixes l) l.

Lemma map_id: forall {A: Type} (l: list A),
  map id l = l.
Proof.
  intros.
  induction l; auto.
  simpl.
  rewrite IHl; auto.
Qed.

Lemma length_prefixes: forall {A: Type} (l: list A),
  length (prefixes l) = length l.
Proof.
  intros.
  induction l; auto.
  simpl.
  f_equal.
  rewrite map_length.
  auto.
Qed.

Lemma prefixes_app_1: forall {A: Type} (l: list A) (a: A),
  prefixes (l +:: a) = prefixes l +:: l.
Proof.
  intros.
  induction l; auto.
  simpl.
  rewrite IHl.
  rewrite map_app.
  auto.
Qed.

Lemma combine_app: forall {A B: Type} (la1 la2: list A) (lb1 lb2: list B),
  length la1 = length lb1 ->
  combine (la1 ++ la2) (lb1 ++ lb2) = combine la1 lb1 ++ combine la2 lb2.
Proof.
  intros.
  revert lb1 H; induction la1; intros; destruct lb1; try now inversion H.
  inv H.
  simpl.
  f_equal.
  apply IHla1; auto.
Qed.

Lemma combine_prefixes_app_1: forall {A: Type} (l: list A) (a: A),
  cprefix (l +:: a) = cprefix l +:: (l, a).
Proof.
  intros.
  unfold cprefix.
  rewrite prefixes_app_1.
  rewrite combine_app by (apply length_prefixes).
  auto.
Qed.

Lemma map_fst_combine: forall {A B: Type} (a: list A) (b: list B),
  length a = length b ->
  map fst (combine a b) = a.
Proof.
  intros.
  revert b H; induction a; intros; destruct b; try solve [inversion H].
  + reflexivity.
  + simpl.
    f_equal.
    apply IHa.
    inv H.
    auto.
Qed.

Lemma map_snd_combine: forall {A B: Type} (a: list A) (b: list B),
  length a = length b ->
  map snd (combine a b) = b.
Proof.
  intros.
  revert b H; induction a; intros; destruct b; try solve [inversion H].
  + reflexivity.
  + simpl.
    f_equal.
    apply IHa.
    inv H.
    auto.
Qed.

Lemma map_snd_cprefix: forall {A: Type} (l: list A),
  map snd (cprefix l) = l.
Proof.
  intros.
  apply map_snd_combine.
  apply length_prefixes.
Qed.

Lemma map_snd_cprefix': forall {A B: Type} (l: list A) (f: A -> B),
  map f l = map (fun p => f (snd p)) (cprefix l).
Proof.
  intros.
  unfold cprefix.
  rewrite <- (map_map snd f).
  rewrite map_snd_combine; auto.
  apply length_prefixes.
Qed.

Lemma rev_list_ind: forall {A} (P: list A -> Prop),
  P nil ->
  (forall l a, P l -> P (l +:: a)) ->
  (forall l, P l).
Proof.
  intros.
  rewrite <- rev_involutive.
  set (P' l' := P (rev l')).
  assert (forall l' a, P' l' -> P' (a :: l')).
  Focus 1. {
    unfold P'.
    intros.
    specialize (H0 (rev l') a).
    change (a :: l') with ((a :: nil) ++ l').
    rewrite rev_app_distr.
    simpl (rev (a :: nil)).
    apply H0; auto.
  } Unfocus.
  set (l' := rev l).
  change (P (rev l')) with (P' l').
  assert (P' nil) by auto.
  clearbody l' P'.
  clear H0 P l H.
  induction l'; auto.
Qed.

Ltac rev_induction l :=
  revert dependent l;
  refine (rev_list_ind _ _ _); intros.

Lemma in_cprefix: forall {A: Type} (xs: list A) xs0 x0,
  In (xs0, x0) (cprefix xs) ->
  In x0 xs.
Proof.
  intros.
  rev_induction xs.
  + inversion H.
  + rewrite combine_prefixes_app_1 in H0.
    rewrite in_app_iff in H0 |- *.
    destruct H0.
    - auto.
    - destruct H0 as [| []].
      inversion H0; subst.
      simpl; auto.
Qed.

Lemma in_cprefix': forall {A: Type} (xs: list A) xs_done x0,
  In (xs_done, x0) (cprefix xs) ->
  exists xs_later, xs = xs_done ++ x0 :: xs_later.
Proof.
  intros.
  rev_induction xs.
  + inversion H.
  + rewrite combine_prefixes_app_1 in H0.
    rewrite in_app_iff in H0.
    destruct H0.
    - destruct (H H0) as [xs_later ?].
      exists (xs_later +:: a).
      change (x0 :: xs_later +:: a) with ((x0 :: xs_later) +:: a).
      rewrite app_assoc.
      f_equal; auto.
    - destruct H0 as [| []].
      inversion H0; subst.
      exists nil; auto.
Qed.

Lemma in_cprefix_cprefix: forall {A: Type} (xs: list A) xs0 xss0,
  In (xss0, xs0) (cprefix (cprefix xs)) ->
  xss0 = cprefix (fst xs0).
Proof.
  intros.
  rev_induction xs.
  + inversion H.
  + rewrite !combine_prefixes_app_1 in H0.
    rewrite in_app_iff in H0.
    destruct H0; [auto |].
    destruct H0 as [| []].
    inversion H0; subst.
    reflexivity.
Qed.

Lemma in_cprefix_cprefix': forall {A: Type} (xs: list A) xs0 xss0,
  In (xss0, xs0) (cprefix (cprefix xs)) ->
  map snd xss0 = fst xs0.
Proof.
  intros.
  rev_induction xs.
  + inversion H.
  + rewrite !combine_prefixes_app_1 in H0.
    rewrite in_app_iff in H0.
    destruct H0; [auto |].
    destruct H0 as [| []].
    inversion H0; subst.
    rewrite map_snd_cprefix.
    reflexivity.
Qed.

