Require Import List.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import Permutation.

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
