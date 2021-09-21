Require Export Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Export Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith_base.
Require Import Coq.ZArith.Zcomplements.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import VST.floyd.sublist.
Require Import VST.floyd.list_solver.


Lemma list_prop_reduced_list: forall {A : Type} (Q : A -> Prop) (Q_lem : forall a, Q a \/ ~Q a) (l : list A),
  exists l', forall a, In a l' <-> (In a l /\ Q a).
Proof.
  induction l. exists nil. split; inversion 1. trivial.
  destruct IHl as [l' ?]. simpl.
  destruct (Q_lem a).
  exists (a :: l'). simpl. split; intros.
  destruct H1. subst a0. split; auto.
  rewrite H in H1. tauto. destruct H1. destruct H1. auto.
  right. rewrite H. tauto.
  exists l'. split; intros.
  rewrite H in H1. tauto.
  destruct H1. destruct H1. subst. contradiction.
  rewrite H. tauto.
Qed.

Lemma list_decidable_prop_reduced_list: forall {A : Type} (P Q : A -> Prop) (l: list A),
  (forall a, Q a \/ ~Q a) ->
  (forall a, In a l <-> P a) -> 
  (exists l', (forall a, In a l' <-> P a /\ Q a)).
Proof.
  intros.
  destruct (list_prop_reduced_list Q H l) as [l' ?]. exists l'.
  intuition. apply H1 in H2. destruct H2. apply H0. trivial.
  apply H1 in H2. tauto.
  apply H0 in H3. apply H1. tauto.
Qed.

Lemma list_not_forall_exists:
  forall {A: Type} {A': Inhabitant A} (l: list A) (P: A -> Prop), l <> nil -> (forall a, P a \/ ~ P a) -> ~ (forall a, In a l -> P a) -> (exists a, In a l /\ ~ P a).
Proof.
induction l; intros.
contradiction.
destruct (H0 a).
assert (exists a0 : A, In a0 l /\ ~ P a0). apply IHl.
(*if l is nil, then (forall a, ... P a) holds*)
unfold not; intros. subst l. assert (forall a0, In a0 (a::nil) -> P a0). intros. destruct H3. subst a0. auto. contradiction. contradiction.
auto.
unfold not; intros.
assert (forall a0, In a0 (a::l) -> P a0). intros. destruct H4. subst a0. auto. apply H3. auto. contradiction.
destruct H3 as [a0 [? ?]]. exists a0. split. right; auto. auto.
exists a. split. left; auto. auto.
Qed.

Lemma Permutation_incl:
forall {A:Type} (l1 l2: list A), Permutation l1 l2 -> incl l1 l2.
Proof.
unfold incl; intros. apply (Permutation_in (l:=l1)); auto.
Qed.

Lemma Permutation_cons_In: forall {A} (l1 l2: list A) a,
    Permutation l1 (a :: l2) -> In a l1.
Proof.
  intros.
  pose proof (in_eq a l2).
  apply Permutation_sym in H.
  apply (Permutation_in _ H); trivial.
Qed.

Lemma In_tail: forall A (a : A) L, In a (tl L) -> In a L.
Proof. induction L; simpl; auto. Qed.

Definition eq_as_set {A} (L1 L2 : list A) : Prop := incl L1 L2 /\ incl L2 L1.

Notation "a '~=' b" := (eq_as_set a b) (at level 1).

Lemma eq_as_set_refl: forall A (L : list A), L ~= L.
Proof. intros; split; apply incl_refl. Qed.

Lemma eq_as_set_sym: forall A (L1 L2 : list A), L1 ~= L2 -> L2 ~= L1.
Proof. intros; hnf in *; firstorder. Qed.

Lemma eq_as_set_trans: forall A (L1 L2 L3 : list A), L1 ~= L2 -> L2 ~= L3 -> L1 ~= L3.
Proof. intros; hnf in *; intuition; apply incl_tran with L2; trivial. Qed.

Add Parametric Relation {A} : (list A) eq_as_set
    reflexivity proved by (eq_as_set_refl A)
    symmetry proved by (eq_as_set_sym A)
    transitivity proved by (eq_as_set_trans A) as eq_as_set_rel.

Lemma eq_as_set_app: forall A (L1 L2 L3 L4: list A),
    L1 ~= L2 -> L3 ~= L4 -> (L1 ++ L3) ~= (L2 ++ L4).
Proof. intros; hnf in *; intuition. Qed.

Lemma eq_as_set_nil: forall {A} (l : list A), nil ~= l -> l = nil.
Proof.
  intros; destruct l; auto. destruct H. assert (In a (a :: l)) by apply in_eq.
  specialize (H0 a H1). inversion H0.
Qed.

(***************FORALL***************)

Lemma Forall_tl: forall {A : Type} (P : A -> Prop) (x : A) (l : list A),
    Forall P (x :: l) -> Forall P l.
Proof. intros; rewrite Forall_forall in *; intros. apply H, in_cons; auto. Qed.

Lemma Forall_app: forall {A : Type} (P : A -> Prop) (l1 l2 : list A),
    Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1; intros. rewrite app_nil_l; auto. generalize (Forall_inv H); intros.
  rewrite <- app_comm_cons. apply Forall_cons; auto. apply IHl1; auto.
  apply Forall_tl with a; auto.
Qed.

Lemma Forall_app_iff: forall {A : Type} (P : A -> Prop) (l1 l2 : list A),
    Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
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

Lemma Forall_incl: forall {A : Type} (P : A -> Prop) (l1 l2 : list A), incl l1 l2 -> Forall P l2 -> Forall P l1.
Proof. intros; hnf in *. rewrite Forall_forall in *; intro y; intros. apply H0, H; auto. Qed.

Lemma Forall_permutation: forall {A: Type} (al bl: list A) f, Forall f al -> Permutation al bl -> Forall f bl.
Proof.
intros. rewrite Forall_forall in *; intros.
apply H. apply (Permutation_in (l:=bl) (l':=al) x). apply Permutation_sym. apply H0. apply H1.
Qed.

Lemma Forall_upd_Znth: forall (l: list Z) (i: Z) new F,
    (0 <= i < Zlength l)%Z ->
    Forall F l -> F new ->
    Forall F (upd_Znth i l new).
Proof.
  intros. rewrite Forall_forall in *. intros.
  destruct (Z.eq_dec x new); [rewrite e; trivial|].
  rewrite upd_Znth_unfold in H2; auto.
  apply in_app_or in H2; destruct H2.
  - apply sublist_In in H2. apply (H0 x H2).
  - simpl in H2. destruct H2; [lia|].
    apply sublist_In in H2. apply (H0 x H2).
Qed.

Lemma repeat1:
  forall {A} (a: A),
    repeat a (Z.to_nat 1) = a :: nil.
Proof. trivial. Qed.

Lemma upd_Znth_repeat:
  forall {A} (i:Z) size (a b : A),
    (0 <= i < size)%Z ->
    upd_Znth i (repeat a (Z.to_nat i) ++
                            repeat b (Z.to_nat (size - i))) a =
    repeat a (Z.to_nat (i + 1)) ++
                repeat b (Z.to_nat (size - (i + 1))).
Proof.
  intros.
  rewrite upd_Znth_app2.
  2: repeat rewrite Zlength_repeat; lia. 
  rewrite Zlength_repeat by lia.
  replace (i-i)%Z with 0%Z by lia.
  rewrite <- repeat_app' by lia.
  rewrite app_assoc_reverse; f_equal.
  rewrite upd_Znth0_old.
  2: rewrite Zlength_repeat; lia.
  rewrite Zlength_repeat, sublist_repeat by lia.
  rewrite repeat1, Z.sub_add_distr. easy.
Qed.

Lemma map_incl: forall {A B : Type} (f : A -> B) (l1 l2 : list A), incl l1 l2 -> incl (map f l1) (map f l2).
Proof. intros; hnf in *; intros. rewrite in_map_iff in *. destruct H0 as [y [? ?]]. exists y; split; auto. Qed.

(*****NODUP******)

Lemma NoDup_cons_1 : forall (A : Type) (x : A) (l : list A), NoDup (x :: l) -> NoDup l. Proof. intros. rewrite NoDup_cons_iff in H. destruct H; auto. Qed.

Lemma NoDup_cons_2 : forall (A : Type) (x : A) (l : list A), NoDup (x :: l) -> ~ In x l. Proof. intros. rewrite NoDup_cons_iff in H. destruct H; auto. Qed.

Lemma NoDup_app_r: forall (A : Type) (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l2. Proof. induction l1; simpl; intros; auto. apply NoDup_cons_1 in H. apply IHl1. auto. Qed.

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

Lemma NoDup_app_iff: forall (A : Type) (l1 l2 : list A),
    NoDup (l1 ++ l2) <->
    NoDup l1 /\ NoDup l2 /\ (forall x, In x l1 -> ~ In x l2).
Proof.
  intros. split; intros. split. apply NoDup_app_l with l2. auto. split. apply NoDup_app_r with l1; auto.
  apply NoDup_app_not_in; auto. destruct H as [? [? ?]]. apply NoDup_app_inv; auto.
Qed.

Lemma NoDup_one: forall A (n: A), NoDup (n :: nil).
Proof.
  intros. apply NoDup_cons. 
  inversion 1. apply NoDup_nil.
Qed.

Lemma NoDup_all_bounded_Zlength:
  forall (size : Z),
    (0 <= size)%Z ->
    forall L,
      NoDup L ->
      (forall j, In j L -> 0 <= j < size)%Z ->
      (Zlength L <= size)%Z.
Proof.
  intros ? ?.
  rename H into Ha.
  rewrite <- (Z2Nat.id size) in *; trivial.
  remember (Z.to_nat size) as size_n.
  clear Heqsize_n Ha.
  induction size_n; intros.
  - destruct L.
    + rewrite Zlength_nil. apply Nat2Z.is_nonneg.
    + exfalso. specialize (H0 z (in_eq _ _)). lia.
  - destruct (in_dec Z.eq_dec (Z.of_nat size_n) L);
      [rename i into H1 | rename n into H1].
    + apply in_split in H1. destruct H1 as [l1 [l2 ?]]. subst L.
      apply NoDup_remove in H. destruct H.
      assert (forall j : Z, In j (l1 ++ l2) ->
                            0 <= j < Z.of_nat size_n)%Z. {
        intros.
        assert (In j (l1 ++ Z.of_nat size_n :: l2)). {
          apply in_or_app. apply in_app_or in H2.
          destruct H2; auto. right. right. trivial.
        }
        specialize (H0 _ H3).
        rewrite Nat2Z.inj_succ in H0.
        assert (0 <= j < Z.of_nat size_n \/ j = Z.of_nat size_n)%Z by lia.
        destruct H4; auto.
        subst j. contradiction.
      }
      specialize (IHsize_n (l1 ++ l2) H H2).
      rewrite Zlength_app in *. rewrite Zlength_cons. simpl. lia.
    + rewrite Nat2Z.inj_succ.
      assert (forall j, In j L -> 0 <= j < Z.of_nat size_n)%Z. {
        intros. specialize (H0 _ H2).
        rewrite Nat2Z.inj_succ in H0.
        assert (0 <= j < (Z.of_nat size_n) \/ j = (Z.of_nat size_n))%Z by lia.
        destruct H3; auto. subst. contradiction.
      }
      specialize (IHsize_n _ H H2). lia.
Qed.

Lemma NoDup_all_bounded_Zlength':
  forall i size,
    (0 <= i < size)%Z ->
    forall L,
      NoDup L ->
      (forall j, In j L -> 0 <= j < size /\ j <> i)%Z ->
      (Zlength L <= size - 1)%Z.
Proof.
  intros ? ? ?.
  rewrite <- (Z2Nat.id size) in *; try lia.
  remember (Z.to_nat size) as size_n.
  clear Heqsize_n.
  induction size_n; intros.
  1: lia.
  replace (Z.of_nat (S size_n) - 1)%Z with (Z.of_nat size_n) by lia.
  assert (i = Z.of_nat size_n \/ 0 <= i < Z.of_nat size_n)%Z by lia.
  destruct H2. subst i.
  apply NoDup_all_bounded_Zlength. lia. apply H0. intros. specialize (H1 _ H2). lia.
  destruct (in_dec Z.eq_dec (Z.of_nat size_n) L);
    [rename i0 into H3 | rename n into H3].
  - apply in_split in H3. destruct H3 as [l1 [l2 ?]]. subst L.
    apply NoDup_remove in H0. destruct H0.
    assert (forall j, In j (l1 ++ l2) -> 0 <= j < Z.of_nat size_n /\ j <> i)%Z. {
      intros.
      assert (In j (l1 ++ Z.of_nat size_n :: l2)). {
        apply in_or_app. apply in_app_or in H4.
        destruct H4; auto. right. right. trivial.
      }
      specialize (H1 _ H5).
      assert (0 <= j < Z.of_nat size_n \/ j = Z.of_nat size_n)%Z by lia.
      destruct H6. lia.
      subst j. contradiction.
    }
    specialize (IHsize_n H2 (l1 ++ l2) H0 H4).
    rewrite Zlength_app in *. rewrite Zlength_cons. lia.
  - assert (forall j, In j L -> 0 <= j < Z.of_nat size_n /\ j <> i)%Z. {
      intros. specialize (H1 _ H4).
      assert (0 <= j < Z.of_nat size_n \/ j = Z.of_nat size_n)%Z by lia.
      destruct H5. lia. subst. contradiction.
    }
    specialize (IHsize_n H2 _ H0 H4). lia.
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
    - split; [intros; lia | lia].
    - split.
      * intros. simpl.
        destruct IHl.
        destruct H; [congruence | apply H0 in H].
        lia.
      * simpl; lia.
Qed.

Lemma not_in_app: forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) x a (l : list A), (~ In x (a :: l)) -> x <> a /\ ~ In x l.
Proof. intros; split. destruct (eq_dec x a); auto. subst; intro; apply H. apply in_eq. intro. apply H; apply in_cons; auto. Qed.

Lemma remove_In_iff: forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x y : A), In x (remove eq_dec y l) <-> In x l /\ x <> y.
Proof. intros. induction l; simpl. 1: tauto. destruct (eq_dec y a); [subst | simpl ]; rewrite IHl; intuition. apply n. subst; auto. Qed.

Lemma remove_incl: forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x : A), incl (remove eq_dec x l) l.
Proof. intros. hnf. intros. rewrite remove_In_iff in H. destruct H; auto. Qed.

Lemma remove_in_2: forall  (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x y : A),
                     In x l -> x = y \/ In x (remove eq_dec y l).
Proof.
  intros. destruct (eq_dec x y).
  - left; auto.
  - right. rewrite remove_In_iff. split; auto.
Qed.

Lemma remove_len_le: forall  (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x : A), length (remove eq_dec x l) <= length l.
Proof. induction l; intros; simpl in *. auto. destruct (eq_dec x a). intuition. simpl. intuition. Qed.

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
  forall (l1 l2 : list A), NoDup l1 -> NoDup l2 -> incl l2 l1 -> Permutation l1 (subtract eq_dec l1 l2 ++ l2).
Proof.
  intros l1 l2; revert l1; induction l2; intros; simpl. rewrite app_nil_r. apply Permutation_refl.
  assert (In a (a :: l2)) by apply in_eq. generalize (H1 a H2); intros. apply in_split in H3. destruct H3 as [ll1 [ll2 ?]].
  subst. assert (incl l2 (ll1 ++ ll2)). intro y; intros. apply in_or_app. assert (In y (a :: l2)) by (apply in_cons; auto).
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
  destruct H; intuition. simpl in H. rewrite <- IHl2 in H. destruct H. split. rewrite remove_In_iff in H. destruct H; auto.
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
  apply (H5 a). apply in_or_app; right; auto. apply Permutation_app. apply NoDup_Permutation. rewrite Heqj4.
  apply subtract_nodup; auto. rewrite Heqj1. apply subtract_nodup; auto. rewrite Heqj1, Heqj4. destruct H2. hnf in H2, H5.
  intro x; split; intros; rewrite <- subtract_property in H6; destruct H6; rewrite <- subtract_property; split. apply H2 in H6.
  apply in_app_or in H6. destruct H6; intuition. rewrite Heqj2. intro; apply H7. rewrite <- intersect_property in H8.
  destruct H8; auto. apply H5. apply in_or_app; left; auto. intro; apply H7. rewrite Heqj2. rewrite <- intersect_property.
  split; auto. auto.
Qed.

Arguments tri_list_split [A] _ [l] [l1] [l2] _ _ _ _.

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

Lemma cons_tail_dec {A}: forall (l: list A), (l = nil) + {l0: list A & {a: A | l = l0 +:: a}}.
Proof.
  intros.
  destruct l.
  1: left; auto.
  right.
  revert a; induction l; intros.
  + exists nil, a; auto.
  + destruct (IHl a) as [? [? ?]].
    exists (a0 :: x), x0.
    rewrite e.
    simpl; auto.
Qed.

Lemma filter_incl: forall A f (l: list A), incl (filter f l) l. Proof. intros. hnf. intros. rewrite filter_In in H. destruct H; auto. Qed.

Lemma NoDup_filter: forall A f (l: list A), NoDup l -> NoDup (filter f l).
Proof.
  intros.
  induction l.
  - simpl; constructor.
  - inversion H; subst.
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

Lemma incl_Permutation {A: Type}: forall (l1 l2: list A), NoDup l2 -> incl l2 l1 -> exists l', Permutation l1 (l2 ++ l').
Proof.
  intros l1 l2. revert l1. induction l2; intros.
  - exists l1. simpl. auto.
  - rewrite NoDup_cons_iff in H. destruct H. hnf in H0. assert (In a l1) by (apply H0; simpl; auto). assert (incl l2 l1) by (hnf; intros; apply H0; simpl; auto).
    specialize (IHl2 l1 H1 H3). destruct IHl2 as [l3 ?]. assert (In a l3) by (rewrite H4 in H2; apply in_app_or in H2; destruct H2; [exfalso|]; auto).
    apply In_Permutation_cons in H5. destruct H5 as [l4 ?]. rewrite H5 in H4. exists l4. rewrite H4. rewrite <- app_comm_cons. symmetry. apply Permutation_middle.
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

Existing Instance Permutation_app'.

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
    cut (P x \/ Q x).
    2: left; trivial.
    intros. rewrite <- H0, H6 in H8.
    destruct H8; [trivial | exfalso].
    apply (H1 x); trivial. apply H5; trivial.
  + firstorder.
    cut (P x \/ Q x).
    2: right; trivial.
    intros. rewrite <- H0, H6 in H8.
    destruct H8; [exfalso | trivial].
    apply (H1 x); trivial. apply H4; trivial.
  + apply NoDup_Permutation; auto.
    - apply NoDup_app_inv; auto. firstorder.
    - intro; rewrite in_app_iff. apply H6. 
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

Ltac rev_induction l :=
  revert dependent l;
  refine (rev_ind _ _ _); intros.

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
      exists (xs_later +:: x).
      change (x0 :: xs_later +:: x) with ((x0 :: xs_later) +:: x).
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

Lemma nodup_remove_nodup: forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x : A), NoDup l -> NoDup (remove eq_dec x l).
Proof.
  intros. destruct (in_dec eq_dec x l). 2: rewrite remove_not_in; auto.
  pose proof (nodup_remove_perm eq_dec _ _ H i). apply (Permutation_NoDup H0) in H. apply NoDup_cons_1 in H; auto.
Qed.

Lemma filter_cons: forall {A: Type} (f: A -> bool) l x xl, filter f l = x :: xl -> exists l1 l2, l = l1 ++ x :: l2 /\ filter f l1 = nil /\ filter f l2 = xl /\ f x = true.
Proof.
  intros. induction l. 1: simpl in H; inversion H. simpl in H. destruct (f a) eqn:? .
  + inversion H. subst a. exists nil, l. split; [|split; [|split]]; auto.
  + specialize (IHl H). destruct IHl as [l1 [l2 [? [? [? ?]]]]]. exists (a :: l1), l2. split; [|split; [|split]]; auto.
    - rewrite <- app_comm_cons. subst l. auto.
    - simpl. destruct (f a) eqn:? . inversion Heqb. auto.
Qed.

Lemma filter_2_cons: forall {A: Type} (f: A -> bool) l x1 x2 xl,
    filter f l = x1 :: x2 :: xl -> exists l1 l2 l3, l = l1 ++ x1 :: l2 ++ x2 :: l3 /\ filter f l1 = nil /\ filter f l2 = nil /\ filter f l3 = xl /\ f x1 = true /\ f x2 = true.
Proof.
  intros. apply filter_cons in H. destruct H as [l1 [l4 [? [? [? ?]]]]]. apply filter_cons in H1. destruct H1 as [l2 [l3 [? [? [? ?]]]]]. subst l4.
  exists l1, l2, l3. split; auto.
Qed.

Lemma map_mid: forall {A B: Type} (f: A -> B) l x xl1 xl2, map f l = xl1 ++ x :: xl2 -> exists y yl1 yl2, l = yl1 ++ y :: yl2 /\ f y = x /\ map f yl1 = xl1 /\ map f yl2 = xl2.
Proof.
  intros. revert xl1 H. induction l; intros. 1: simpl in H; destruct xl1; inversion H. destruct xl1.
  + clear IHl. simpl in H. exists a, nil, l. inversion H. split; auto.
  + simpl in H. inversion H. specialize (IHl _ H2). destruct IHl as [y [yl1 [yl2 [? [? [? ?]]]]]]. exists y, (a :: yl1), yl2. simpl. subst l. rewrite H4. split; auto.
Qed.

Lemma map_2_mid: forall {A B: Type} (f: A -> B) l x1 x2 l1 l2 l3,
    map f l = l1 ++ x1 :: l2 ++ x2 :: l3 -> exists y1 y2 m1 m2 m3, l = m1 ++ y1 :: m2 ++ y2 :: m3 /\ map f m1 = l1 /\ map f m2 = l2 /\ map f m3 = l3 /\ f y1 = x1 /\ f y2 = x2.
Proof.
  intros. apply map_mid in H. destruct H as [y1 [m1 [m4 [? [? [? ?]]]]]]. apply map_mid in H2. destruct H2 as [y2 [m2 [m3 [? [? [? ?]]]]]]. subst m4.
  exists y1, y2, m1, m2, m3. split; auto.
Qed.

Lemma nth_error_None_iff: forall {A} (l: list A) n, nth_error l n = None <-> n >= length l.
Proof.
  intros.
  revert n; induction l; intros; destruct n; simpl.
  + split; [intros _; lia | auto].
  + split; [intros _; lia | auto].
  + split; [intros; inversion H | lia].
  + rewrite IHl.
    lia.
Qed.

(* TODO: These three lemmas are copied from VST.veric.assert_lemmas and VST.veric.initial_world *)
Lemma nth_error_in_bounds: forall {A} (l: list A) i, (O <= i < length l)%nat
  -> exists x, nth_error l i = value x.
Proof.
intros until i; intros H.
revert i l H.
induction i; destruct l; intros; simpl in *;
  try solve [eauto | lia].
apply IHi; lia.
Qed.

Lemma nth_error_app: forall {T} (al bl : list T) (j: nat),
     nth_error (al++bl) (length al + j) = nth_error bl j.
Proof.
 intros. induction al; simpl; auto.
Qed.

Lemma nth_error_app1: forall {T} (al bl : list T) (j: nat),
     (j < length al)%nat ->
     nth_error (al++bl) j = nth_error al j.
Proof.
  intros. revert al H; induction j; destruct al; simpl; intros; auto; try lia.
   apply IHj. lia.
Qed.

Lemma in_split_not_in_first: forall {A} (eq_dec: forall x y : A, {x = y} + {x <> y}) (x: A) (l: list A), In x l -> exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l1.
Proof.
  intros ? ? ?. induction l; intros.
  - inversion H.
  - simpl in H. destruct (eq_dec a x).
    + exists nil, l. rewrite app_nil_l. subst a. split; auto.
    + destruct H. 1: exfalso; auto. specialize (IHl H). destruct IHl as [l1 [l2 [? ?]]]. exists (a :: l1), l2. simpl. rewrite H0. split; auto.
      intro. destruct H2; auto.
Qed.

Lemma in_split_not_in_last: forall {A} (eq_dec: forall x y : A, {x = y} + {x <> y}) (x: A) (l: list A), In x l -> exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l2.
Proof.
  intros ? ? ? ?. rev_induction l. 1: inversion H. destruct (eq_dec x0 x).
  - exists l, nil. subst x0. split; auto.
  - rewrite in_app_iff in H0. destruct H0.
    + specialize (H H0). destruct H as [l1 [l2 [? ?]]]. exists l1, (l2 +:: x0). rewrite H. rewrite <- app_assoc. simpl. split; auto.
      intro. rewrite in_app_iff in H2. destruct H2; auto. simpl in H2. destruct H2; auto.
    + simpl in H0. destruct H0; exfalso; auto.
Qed.

Fixpoint filter_sum_left {A B} (l: list (A + B)) : list A :=
  match l with
  | nil => nil
  | inl x :: l' => x :: filter_sum_left l'
  | inr _ :: l' => filter_sum_left l'
  end.

Fixpoint filter_sum_right {A B} (l: list (A + B)) : list B :=
  match l with
  | nil => nil
  | inl _ :: l' => filter_sum_right l'
  | inr x :: l' => x :: filter_sum_right l'
  end.

Fixpoint filter_option {A} (l: list (option A)) : list A :=
  match l with
  | nil => nil
  | Some x :: l' => x :: filter_option l'
  | None :: l' => filter_option l'
  end.

Lemma filter_sum_right_In_iff {A B}: forall e (l: list (A + B)),
    In (inr e) l <-> In e (filter_sum_right l).
Proof.
  intros. induction l; simpl; intuition.
  - inversion H2.
  - inversion H2. simpl. left; reflexivity.
  - simpl in H1. destruct H1.
    + subst b. left; reflexivity.
    + right. apply H0. assumption.
Qed.

Lemma filter_sum_left_In_iff {A B}: forall e (l: list (A + B)),
    In (inl e) l <-> In e (filter_sum_left l).
Proof.
  intros. induction l; simpl; intuition.
  - inversion H2. simpl. left; reflexivity.
  - simpl in H1. destruct H1.
    + subst a0. left; reflexivity.
    + right. apply H0. assumption.
  - inversion H2.
Qed.

Lemma filter_option_In_iff {A}: forall e (l: list (option A)),
    In (Some e) l <-> In e (filter_option l).
Proof.
  intros. induction l; simpl; try reflexivity. destruct a; intuition.
  - inversion H2. simpl. left; reflexivity.
  - simpl in H1. destruct H1.
    + subst a. left; reflexivity.
    + right. apply H0. assumption.
  - inversion H2.
Qed.

Lemma combine_nth_lt {A B}: forall (l1: list A) (l2: list B) n x y,
    n < length l1 -> n < length l2 ->
    nth n (combine l1 l2) (x, y) = (nth n l1 x, nth n l2 y).
Proof.
  induction l1; intros.
  - simpl in *. exfalso. lia.
  - destruct l2.
    + simpl in H0. exfalso. lia.
    + simpl. destruct n; [|simpl in *; rewrite IHl1 by lia]; reflexivity.
Qed.

Lemma map_tl {A B: Type}: forall (f: A -> B) (l: list A), map f (tl l) = tl (map f l).
Proof. intros; destruct l; simpl; reflexivity. Qed.

Lemma fold_left_comm: forall {A B} (f: A -> B -> A) l1 l2 init,
    (forall a b1 b2, f (f a b1) b2  = f (f a b2) b1) ->
    Permutation l1 l2 -> fold_left f l1 init = fold_left f l2 init.
Proof.
  intros. remember (length l1). assert (length l1 <= n) by lia. clear Heqn.
  revert init l1 l2 H1 H0. induction n; intros; destruct l1.
  - apply Permutation_nil in H0. subst l2. simpl. reflexivity.
  - simpl in H1; exfalso; lia.
  - apply Permutation_nil in H0. subst l2. simpl. reflexivity.
  - simpl in H1. assert (length l1 <= n) by lia. clear H1.
    assert (In b l2) by
        (apply Permutation_in with (x := b) in H0; [assumption | left; reflexivity]).
    apply in_split in H1. destruct H1 as [l3 [l4 ?]]. subst l2.
    apply Permutation_cons_app_inv in H0. simpl.
    rewrite IHn with (l2 := l3 ++ l4) by assumption. rewrite !fold_left_app. simpl.
    f_equal. clear -H. revert b init. rev_induction l3; simpl. 1: reflexivity.
    rewrite !fold_left_app. simpl. rewrite H. f_equal. apply H0.
Qed.

Local Open Scope Z_scope.

Lemma exists_element_list:
  forall {A B: Type} {A': Inhabitant A} {B': Inhabitant B} (P: A -> B -> Prop) (la: list A),
    (forall a, In a la -> exists b, P a b) ->
    (exists lb, Zlength lb = Zlength la /\ forall i, 0 <= i < Zlength la -> P (Znth i la) (Znth i lb)).
Proof.
induction la; intros. exists nil. split. auto. intros. rewrite Zlength_nil in H0; lia.
assert (forall a : A, In a la -> exists b : B, P a b). intros. apply H. right; auto.
apply IHla in H0. destruct H0 as [lb ?].
assert (exists b : B, P a b). apply H. left; auto. destruct H1 as [b ?].
exists (b::lb). split. do 2 rewrite Zlength_cons; lia.
intros. rewrite Zlength_cons in H2.
destruct (Z.lt_trichotomy 0 i).
do 2 rewrite Znth_pos_cons by lia. apply H0. lia.
destruct H3. subst i. do 2 rewrite Znth_0_cons. auto. lia.
Qed.

Lemma fold_left_Z_mono_strict: forall {A} (f: Z -> A -> Z) (l1 l2 l3: list A) s,
    (forall a b, a < f a b) -> (forall a b1 b2, f (f a b1) b2  = f (f a b2) b1) ->
    l2 <> nil -> Permutation (l1 ++ l2) l3 -> fold_left f l1 s < fold_left f l3 s.
Proof.
  intros. rewrite <- (fold_left_comm _ _ _ _ H0 H2). rewrite fold_left_app.
  remember (fold_left f l1 s). clear -H H1. rev_induction l2. 1: contradiction.
  rewrite fold_left_app. simpl. destruct l. 1: simpl; apply H.
  transitivity (fold_left f (a :: l) z); [apply H0; intro; inversion H2 | apply H].
Qed.

Lemma fold_left_Z_mono: forall {A} (f: Z -> A -> Z) (l1 l2 l3: list A) s,
    (forall a b, a <= f a b) -> (forall a b1 b2, f (f a b1) b2  = f (f a b2) b1) ->
    Permutation (l1 ++ l2) l3 -> fold_left f l1 s <= fold_left f l3 s.
Proof.
  intros. rewrite <- (fold_left_comm _ _ _ _ H0 H1). rewrite fold_left_app.
  remember (fold_left f l1 s). clear -H. rev_induction l2. 1: simpl; intuition.
  rewrite fold_left_app. simpl. transitivity (fold_left f l z); [apply H0 | apply H].
Qed.

Lemma fold_left_mono_filter: forall {A} (f: Z -> A -> Z) (l: list A) (h: A -> bool) s,
    (forall a b, a <= f a b) -> (forall a b1 b2, f (f a b1) b2  = f (f a b2) b1) ->
    fold_left f (filter h l) s <= fold_left f l s.
Proof.
  intros. remember (fun x: A => negb (h x)) as g.
  assert (Permutation (filter h l ++ filter g l) l) by
      (symmetry; apply filter_perm; intros; subst; apply Bool.negb_involutive_reverse).
  apply (fold_left_Z_mono f _ _ _ s H H0 H1).
Qed.

Lemma fold_left_ext: forall {A B} (f g: A -> B -> A) l init,
    (forall x y, In y l -> f x y = g x y) -> fold_left f l init = fold_left g l init.
Proof.
  intros. revert init. rev_induction l; intros; simpl. 1: reflexivity.
  rewrite !fold_left_app. simpl.
  rewrite H; intros; apply H0; rewrite in_app_iff; intuition.
Qed.

Lemma fold_left_Zadd_diff_accum:
forall (l: list Z) (x y: Z), x <= y -> fold_left Z.add l x <= fold_left Z.add l y.
Proof.
induction l; intros. simpl; auto.
apply IHl. lia.
Qed.

Lemma fold_left_accum_Zadd:
forall (l: list Z) (x y: Z), fold_left Z.add l (x+y) = (fold_left Z.add l x) + y.
Proof.
induction l; intros. simpl; auto.
simpl. replace (x + y + a) with ((x+a) + y) by lia. apply (IHl (x+a) y).
Qed.

Lemma fold_left_Zadd_comp:
forall (l1 l2: list Z), Zlength l1 = Zlength l2 -> (forall i, 0<=i<Zlength l1 -> Znth i l1 <= Znth i l2)
  -> (forall s, fold_left Z.add l1 s <= fold_left Z.add l2 s).
Proof.
induction l1; intros.
rewrite Zlength_nil in H. symmetry in H. apply Zlength_nil_inv in H. subst l2. lia.
destruct l2. rewrite Zlength_cons in H. rewrite Zlength_nil in H. pose proof (Zlength_nonneg l1). lia.
simpl. assert (a <= z). replace a with (Znth 0 (a::l1)). replace z with (Znth 0 (z::l2)).
apply H0. split. lia. rewrite Zlength_cons. pose proof (Zlength_nonneg l1). lia.
auto. auto.
apply (Z.le_trans _ (fold_left Z.add l1 (s + z)) _).
apply fold_left_Zadd_diff_accum. lia.
apply IHl1. do 2 rewrite Zlength_cons in H. lia.
intros. replace (Znth i l1) with (Znth (i+1) (a::l1)).
 replace (Znth i l2) with (Znth (i+1) (z::l2)). apply H0. rewrite Zlength_cons. lia.
all: rewrite (Znth_pos_cons (i+1)) by lia; rewrite Z.add_simpl_r; auto.
Qed.

Lemma exists_Zmin:
  forall {A:Type} (l: list A) (f: A -> Z), l <> nil -> exists a, In a l /\ (forall b, In b l -> f a <= f b).
Proof.
induction l; intros. contradiction.
destruct l. exists a. split. left; auto. intros. destruct H0. subst b. lia. contradiction.
assert (exists a : A, In a (a0 :: l) /\ (forall b : A, In b (a0 :: l) -> f a <= f b)). apply IHl. unfold not; intros. inversion H0.
destruct H0 as [a' [? ?]].
destruct (Z.le_ge_cases (f a) (f a')).
exists a. split. left; auto. intros. destruct H3. subst a; lia. apply H1 in H3. lia.
exists a'. split. right; auto. intros. destruct H3. subst b; lia. apply H1 in H3; lia.
Qed.

Lemma fold_left_Zadd_map_remove:
forall {A: Type} {EA: EquivDec.EqDec A eq} l f b,
  In b l -> NoDup l ->
  fold_left Z.add (map f (remove EA b l)) 0 = (fold_left Z.add (map f l) 0) - f b.
Proof.
induction l; intros. contradiction.
simpl. replace (f a) with (0 + f a) by lia. rewrite fold_left_accum_Zadd.
replace (fold_left Z.add (map f l) 0 + f a - f b) with
  (fold_left Z.add (map f l) 0 - f b + f a) by lia.
destruct H; destruct (EA b a). 
++hnf in e. subst a. assert (~ In b l). apply NoDup_cons_2 in H0; auto.
rewrite remove_not_in by auto. rewrite Z.sub_add. auto.
++unfold RelationClasses.complement, Equivalence.equiv in c. subst a. contradiction.
++hnf in e; subst a. apply NoDup_cons_2 in H0. contradiction.
++simpl. replace (f a) with (0 + f a) by lia. rewrite fold_left_accum_Zadd. apply NoDup_cons_1 in H0. rewrite IHl; auto.
Qed.

Lemma sublist_of_nil:
forall {A:Type} lo hi, sublist lo hi (nil (A:=A)) = nil.
Proof.
intros. unfold sublist. rewrite firstn_nil. rewrite skipn_nil. auto.
Qed.

Lemma sublist_overshoot:
forall {A:Type} (l: list A) lo hi, Zlength l <= lo -> sublist lo hi l = nil.
Proof.
intros. unfold sublist.
rewrite skipn_short; auto.
rewrite <- ZtoNat_Zlength.
rewrite Zlength_firstn.
destruct (Z.lt_trichotomy 0 hi). rewrite Z.max_r by lia.
destruct (Z.lt_trichotomy hi (Zlength l)). rewrite Z.min_l. lia. lia. destruct H1. 
subst hi. rewrite Z.min_id. lia. rewrite Z.min_r by lia. lia.
destruct H0. subst hi. rewrite Z.max_id. rewrite Z.min_l. lia. pose proof (Zlength_nonneg l); lia.
rewrite Z.max_l by lia. rewrite Z.min_l. lia. pose proof (Zlength_nonneg l); lia.
Qed.

Lemma sublist_same_overshoot:
forall {A:Type} (l: list A) hi, Zlength l <= hi -> sublist 0 hi l = l.
Proof.
intros. unfold sublist. rewrite skipn_0. rewrite firstn_same. auto.
rewrite <- ZtoNat_Zlength. lia.
Qed.

Lemma list_eq_Znth:
  forall {A:Type} {d: Inhabitant A} (l l': list A), Zlength l = Zlength l' ->
    (forall i, 0 <= i < Zlength l -> Znth i l = Znth i l') ->
    l = l'.
Proof.
induction l; intros. symmetry; apply Zlength_nil_inv. rewrite Zlength_nil in H; auto.
destruct l'. rewrite Zlength_cons, Zlength_nil in H.
pose proof (Zlength_nonneg (A:=A) l).
assert (Zlength l < Z.succ (Zlength l)) by lia. lia.
replace a with (Znth 0 (a::l)). 2: rewrite Znth_0_cons; auto.
replace a0 with (Znth 0 (a0::l)). 2: rewrite Znth_0_cons; auto.
rewrite (H0 0). 2: rewrite Zlength_cons; pose proof (Zlength_nonneg (A:=A) l); lia.
rewrite (IHl l'); auto.
apply Z.succ_inj. do 2 rewrite Zlength_cons in H. auto.
intros. replace (Znth i l) with (Znth (i+1) (a::l)).
replace (Znth i l') with (Znth (i+1) (a0::l')). apply H0. rewrite Zlength_cons. lia.
replace (Znth i l') with (Znth (i+1 - 1) l'). apply Znth_pos_cons. lia. rewrite Z.add_simpl_r; auto.
replace (Znth i l) with (Znth (i+1 - 1) l). apply Znth_pos_cons. lia. rewrite Z.add_simpl_r; auto.
Qed.

Lemma Permutation_Zlength:
  forall {A: Type} (l l': list A), Permutation l l' -> Zlength l = Zlength l'.
Proof.
intros. assert (length l = length l'). apply Permutation_length. apply H.
repeat rewrite Zlength_correct. rewrite H0. auto.
Qed.

Lemma NoDup_combine_r: forall {A B} (l1: list A) (l2: list B),
    NoDup l2 -> NoDup (combine l1 l2).
Proof.
  intros. revert l2 H. induction l1; intros; simpl. 1: constructor.
  destruct l2; constructor.
  - intro. apply in_combine_r in H0. apply NoDup_cons_2 in H. contradiction.
  - apply IHl1. apply NoDup_cons_1 in H. assumption.
Qed.

Lemma filter_ext: forall {A} (f g: A -> bool) l,
    (forall i, In i l -> f i = g i) -> filter f l = filter g l.
Proof.
  intros. induction l; simpl. 1: reflexivity.
  assert (f a = g a) by (apply H; left; reflexivity).
  assert (forall i : A, In i l -> f i = g i) by (intros; apply H; right; assumption).
  destruct (f a), (g a); [|inversion H0.. |]; rewrite IHl by assumption; reflexivity.
Qed.

Lemma filter_singular_perm: forall {A} (f g: A -> bool) l x,
    (forall i, In i l -> i <> x -> f i = g i) -> In x l ->
    g x = false -> f x = true -> NoDup l ->
    Permutation (filter f l) (x :: filter g l).
Proof.
  intros. induction l. 1: inversion H0. simpl. simpl in H0. destruct H0.
  - subst a. rewrite H1. rewrite H2. constructor. cut (filter f l = filter g l).
    + intros. rewrite H0. reflexivity.
    + apply filter_ext. intros. apply H.
      * simpl; right; assumption.
      * apply NoDup_cons_2 in H3. intro. subst i. contradiction.
  - assert (a <> x) by (apply NoDup_cons_2 in H3; intro; subst a; contradiction).
    assert (f a = g a) by (apply H; [left; reflexivity | assumption]).
    assert (Permutation (filter f l) (x :: filter g l)). {
      apply IHl; [intros; apply H; [right|] | |apply NoDup_cons_1 in H3]; assumption. }
    destruct (f a); destruct (g a); try discriminate; clear H5;
      [transitivity (a :: x :: filter g l); constructor|]; assumption.
Qed.

Lemma app_not_nil: forall {A} (l: list A) (a: A), l ++ (a :: nil) <> nil.
Proof. intros. destruct l; intro; simpl in H; inversion H. Qed.

Lemma combine_repeat_eq_map: forall {A B} (a: A) (l: list B),
    combine (repeat a (length l)) l = map (fun b : B => (a, b)) l.
Proof. intros. induction l; simpl; auto. rewrite IHl. reflexivity. Qed.

Lemma combine_map_join: forall {A B C} (f: A -> B) (g: A -> C) (l: list A),
    combine (map f l) (map g l) = map (fun x => (f x, g x)) l.
Proof. intros. induction l; simpl; auto. rewrite IHl. reflexivity. Qed.

Lemma map_fst_split: forall {A B} (l: list (A * B)), map fst l = fst (split l).
Proof.
  intros. pose proof (split_length_l l). pose proof (split_length_r l).
  pose proof (split_combine l). destruct (split l). simpl in *. rewrite <- H0 in H.
  now rewrite <- H1, map_fst_combine.
Qed.

Lemma map_snd_split: forall {A B} (l: list (A * B)), map snd l = snd (split l).
Proof.
  intros. pose proof (split_length_l l). pose proof (split_length_r l).
  pose proof (split_combine l). destruct (split l). simpl in *. rewrite <- H0 in H.
  now rewrite <- H1, map_snd_combine.
Qed.

Lemma In_map_fst_iff: forall {A B} a (l: list (A * B)),
    In a (map fst l) <-> exists b : B, In (a, b) l.
Proof.
  intros. induction l; simpl. 1: intuition; now destruct H.
  destruct a0 as [a0 b0]. simpl in *. split; intros.
  - destruct H. 1: subst; exists b0; now left. rewrite IHl in H. destruct H as [b ?].
    exists b. now right.
  - destruct H as [b ?]. destruct H. 1: inversion H; now left. rewrite IHl.
    right. now exists b.
Qed.

Lemma In_map_snd_iff: forall {A B} b (l: list (A * B)),
    In b (map snd l) <-> exists a : A, In (a, b) l.
Proof.
  intros. induction l; simpl. 1: intuition; now destruct H.
  destruct a as [a0 b0]. simpl in *. split; intros.
  - destruct H. 1: subst; exists a0; now left. rewrite IHl in H. destruct H as [a ?].
    exists a. now right.
  - destruct H as [a ?]. destruct H. 1: inversion H; now left. rewrite IHl.
    right. now exists a.
Qed.

Lemma In_map_fst: forall {A B} a b (l: list (A * B)),
    In (a, b) l -> In a (map fst l).
Proof.
  intros. assert (exists y, In (a, y) l) by (now exists b).
  now rewrite <- In_map_fst_iff in H0.
Qed.

Lemma In_map_snd: forall {A B} a b (l: list (A * B)),
    In (a, b) l -> In b (map snd l).
Proof.
  intros. assert (exists x, In (x, b) l) by (now exists a).
  now rewrite <- In_map_snd_iff in H0.
Qed.

Section LIST_DERIVED_BIJECTION.

  Context {A: Type}.
  Context {AE: EqDec A eq}.

  Fixpoint bi_look_up (l: list (A * A)) (key: A): option A :=
    match l with
    | nil => None
    | (k, v) :: l' => if equiv_dec k key then Some v
                      else if equiv_dec v key then Some k
                           else bi_look_up l' key
    end.

  Definition list_bi_map (l: list (A * A)) (r: A): A :=
    match (bi_look_up l r) with
    | Some v => v
    | None => r
    end.

  Definition DoubleNoDup (l: list (A * A)): Prop :=
    let (left_l, right_l) := split l in NoDup (left_l ++ right_l).

  Lemma DoubleNoDup_cons_tl: forall x l, DoubleNoDup (x :: l) -> DoubleNoDup l.
  Proof.
    intros. destruct x as [x y]. unfold DoubleNoDup in *. simpl in H.
    destruct (split l) as [l1 l2]. simpl in H. apply NoDup_cons_1, NoDup_remove_1 in H.
    assumption.
  Qed.

  Lemma DoubleNoDup_cons_hd: forall k v l, DoubleNoDup ((k, v) :: l) -> k <> v.
  Proof.
    intros. unfold DoubleNoDup in H. simpl in H.
    destruct (split l) as [l1 l2]. simpl in H. apply NoDup_cons_2 in H. intro. subst.
    apply H. rewrite in_app_iff. right. left. reflexivity.
  Qed.

  Definition InEither (v: A) (l: list (A * A)): Prop :=
    let (left_l, right_l) := split l in In v (left_l ++ right_l).

  Definition IsEither (v: A) (a: A * A): Prop := v = fst a \/ v = snd a.

  Lemma InEither_cons_iff: forall v a l,
      InEither v (a :: l) <-> IsEither v a \/ InEither v l.
  Proof.
    do 3 intro. revert v a. induction l; intros.
    - destruct a. unfold InEither at 1. simpl. unfold IsEither. simpl. intuition.
    - rewrite IHl. unfold InEither. simpl. destruct (split l) as [l1 l2].
      destruct a. destruct a0. unfold IsEither. simpl. rewrite !in_app_iff. simpl.
      clear. firstorder.
  Qed.

  Lemma InEither_dec: forall v l, {InEither v l} + {~ InEither v l}.
  Proof.
    intros. induction l. 1: right; intro; inversion H. destruct a as [v1 v2].
    destruct (equiv_dec v v1); unfold equiv in *.
    - left. rewrite InEither_cons_iff. left. red. simpl. left. assumption.
    - destruct (equiv_dec v v2); unfold equiv in *.
      + left. rewrite InEither_cons_iff. left. red. simpl. right. assumption.
      + destruct IHl; [left | right].
        * rewrite InEither_cons_iff. right. assumption.
        * intro. apply n. clear n. rewrite InEither_cons_iff in H. destruct H; auto.
          red in H. simpl in H. exfalso. unfold complement in *. destruct H; auto.
  Defined.

  Lemma list_bi_map_cons_1: forall a l x,
      ~ IsEither x a -> list_bi_map (a :: l) x = list_bi_map l x.
  Proof.
    intros. unfold list_bi_map. simpl. destruct a. unfold IsEither in H. simpl in H.
    apply Decidable.not_or in H. destruct H. destruct (equiv_dec a x).
    1: exfalso; intuition. destruct (equiv_dec a0 x). 1: exfalso; intuition.
    reflexivity.
  Qed.

  Lemma list_bi_map_not_In: forall l x, ~ InEither x l -> list_bi_map l x = x.
  Proof.
    induction l; intros. 1: unfold list_bi_map; simpl; reflexivity.
    rewrite InEither_cons_iff in H. apply Decidable.not_or in H. destruct H.
    rewrite list_bi_map_cons_1; auto.
  Qed.

  Lemma IsEither_dec: forall v a, {IsEither v a} + {~ IsEither v a}.
  Proof.
    intros. destruct a. destruct (equiv_dec v a).
    - left. red. left. simpl. assumption.
    - destruct (equiv_dec v a0).
      + left. red. right; simpl; assumption.
      + right. unfold IsEither. simpl. unfold equiv, complement in *. intuition.
  Defined.

  Lemma list_bi_map_In: forall l x,
      InEither x l -> exists k v, In (k, v) l /\
                                  ((x = k /\ list_bi_map l x = v) \/
                                   (x = v /\ list_bi_map l x = k)).
  Proof.
    induction l; intros. 1: inversion H. destruct (IsEither_dec x a).
    - destruct a. exists a, a0. simpl. split. 1: left; reflexivity. red in i.
      simpl in i. destruct i; subst; [left | right]; split; try reflexivity;
                    unfold list_bi_map; simpl.
      + destruct (equiv_dec a a); [| exfalso; apply c]; reflexivity.
      + destruct (equiv_dec a a0). 1: intuition.
        destruct (equiv_dec a0 a0); [| exfalso; apply c0]; reflexivity.
    - rewrite InEither_cons_iff in H. destruct H. 1: contradiction.
      specialize (IHl _ H). destruct IHl as [k [v [? ?]]]. exists k, v. split.
      + simpl. right; assumption.
      + destruct a. unfold IsEither in n. simpl in n. apply Decidable.not_or in n.
        destruct n. unfold list_bi_map in *. simpl.
        destruct (equiv_dec a x); unfold equiv in *. 1: exfalso; intuition.
        destruct (equiv_dec a0 x); unfold equiv in *. 1: exfalso; intuition.
        assumption.
  Qed.

  Lemma DoubleNoDup_cons_neq: forall v1 v2 l,
      DoubleNoDup ((v1, v2) :: l) -> ~ InEither v1 l /\ ~ InEither v2 l.
  Proof.
    do 3 intro. revert v1 v2. induction l; intros. 1: intuition. destruct a.
    specialize (IHl _ _ (DoubleNoDup_cons_tl _ _ H)). destruct IHl.
    unfold DoubleNoDup in H. simpl in H. unfold InEither in *. simpl.
    destruct (split l) as [l1 l2]. split.
    - simpl in H. apply NoDup_cons_2 in H. simpl in *. intro. apply H.
      destruct H2; auto. right. rewrite in_app_iff in H2 |-* . destruct H2; intuition.
    - apply NoDup_remove_2 in H. intro. apply H. rewrite in_app_iff in H2 |-* .
      destruct H2; auto. left. right. assumption.
  Qed.

  Lemma In_InEither: forall v1 v2 l, In (v1, v2) l -> InEither v1 l /\ InEither v2 l.
  Proof.
    do 3 intro. revert v1 v2. induction l; intros. 1: inversion H. simpl in H.
    destruct H.
    - subst. rewrite !InEither_cons_iff. unfold IsEither. simpl. intuition.
    - apply IHl in H. destruct H. rewrite !InEither_cons_iff. intuition.
  Qed.

  Lemma DoubleNoDup_In_fst_eq: forall l k v1 v2,
      DoubleNoDup l -> In (k, v1) l -> In (k, v2) l -> v1 = v2.
  Proof.
    induction l; intros. 1: inversion H0. simpl in H0, H1. destruct H0, H1.
    - rewrite H0 in H1. inversion H1. reflexivity.
    - apply In_InEither in H1. destruct H1. subst a. apply DoubleNoDup_cons_neq in H.
      destruct H. contradiction.
    - apply In_InEither in H0. destruct H0. subst a. apply DoubleNoDup_cons_neq in H.
      destruct H. contradiction.
    - eapply IHl; eauto. eapply DoubleNoDup_cons_tl; eauto.
  Qed.

  Lemma DoubleNoDup_In_snd_eq: forall l k1 k2 v,
      DoubleNoDup l -> In (k1, v) l -> In (k2, v) l -> k1 = k2.
  Proof.
    induction l; intros. 1: inversion H0. simpl in H0, H1. destruct H0, H1.
    - rewrite H0 in H1. inversion H1. reflexivity.
    - apply In_InEither in H1. destruct H1. subst a. apply DoubleNoDup_cons_neq in H.
      destruct H. contradiction.
    - apply In_InEither in H0. destruct H0. subst a. apply DoubleNoDup_cons_neq in H.
      destruct H. contradiction.
    - eapply IHl; eauto. eapply DoubleNoDup_cons_tl; eauto.
  Qed.

  Lemma DoubleNoDup_In_fst_snd_impsb: forall l v1 v2 v,
      DoubleNoDup l -> In (v1, v) l -> In (v, v2) l -> False.
  Proof.
    induction l; intros. 1: inversion H0. simpl in H0, H1. destruct H0, H1.
    - rewrite H0 in H1. inversion H1. subst.
      apply DoubleNoDup_cons_hd in H. contradiction.
    - apply In_InEither in H1. destruct H1. subst a. apply DoubleNoDup_cons_neq in H.
      destruct H. contradiction.
    - apply In_InEither in H0. destruct H0. subst a. apply DoubleNoDup_cons_neq in H.
      destruct H. contradiction.
    - apply (IHl v1 v2 v); auto. eapply DoubleNoDup_cons_tl; eauto.
  Qed.

  Lemma DoubleNoDup_bi_look_up: forall k v l,
      DoubleNoDup l -> In (k, v) l ->
      bi_look_up l k = Some v /\ bi_look_up l v = Some k.
  Proof.
    do 3 intro. induction l; intros. 1: inversion H0.
    assert (a = (k, v) \/ a <> (k, v)). {
      destruct a; destruct (equiv_dec a k); destruct (equiv_dec a0 v);
        unfold equiv in *; unfold complement in *; simpl in *; subst;
          [left; reflexivity | right; intro; apply c; inversion H1; reflexivity..]. }
    destruct H1.
    - subst. simpl. apply DoubleNoDup_cons_hd in H.
      destruct (equiv_dec k k); intuition. destruct (equiv_dec k v); intuition.
      destruct (equiv_dec v v); intuition.
    - destruct a. simpl. destruct (equiv_dec a k); unfold equiv in *.
      + exfalso. subst a. apply H1. f_equal. eapply DoubleNoDup_In_fst_eq; eauto.
        simpl. left; reflexivity.
      + destruct (equiv_dec a0 k); unfold equiv in *.
        * exfalso. subst a0. eapply (DoubleNoDup_In_fst_snd_impsb _ a); eauto.
          simpl. left; reflexivity.
        * destruct (equiv_dec a v); unfold equiv in *.
          -- exfalso. subst a. eapply (DoubleNoDup_In_fst_snd_impsb _ k a0 v); eauto.
             simpl. left; reflexivity.
          -- destruct (equiv_dec a0 v); unfold equiv in *.
             ++ exfalso. subst. apply H1. f_equal. eapply DoubleNoDup_In_snd_eq; eauto.
                simpl. left; reflexivity.
             ++ apply IHl. 1: eapply DoubleNoDup_cons_tl; eauto. simpl in H0.
                destruct H0; auto. contradiction.
  Qed.

  Lemma bijective_list_bi_map: forall l,
      DoubleNoDup l -> bijective (list_bi_map l) (list_bi_map l).
  Proof.
    intros. constructor; intros.
    - destruct (InEither_dec x l).
      + apply list_bi_map_In in i. destruct i as [kx [vx [? ?]]].
        destruct (InEither_dec y l).
        * apply list_bi_map_In in i. destruct i as [ky [vy [? ?]]].
          destruct H2 as [[? ?] | [? ?]]; destruct H4 as [[? ?] | [? ?]];
            rewrite H5, H6 in H0; subst.
          -- eapply DoubleNoDup_In_snd_eq; eauto.
          -- exfalso; eapply (DoubleNoDup_In_fst_snd_impsb _ kx); eauto.
          -- exfalso; eapply (DoubleNoDup_In_fst_snd_impsb _ ky); eauto.
          -- eapply DoubleNoDup_In_fst_eq; eauto.
        * pose proof n. apply list_bi_map_not_In in n. rewrite <- H0 in n.
          destruct H2 as [[? ?] | [? ?]]; rewrite H4 in n; rewrite n in H1;
            exfalso; apply H3; apply In_InEither in H1; destruct H1; assumption.
      + pose proof n. apply list_bi_map_not_In in n. rewrite H0 in n.
        destruct (InEither_dec y l).
        * apply list_bi_map_In in i. destruct i as [ky [vy [? ?]]].
          destruct H3 as [[? ?] | [? ?]]; rewrite H4 in n; rewrite n in H2;
            exfalso; apply H1; apply In_InEither in H2; destruct H2; assumption.
        * apply list_bi_map_not_In in H1. apply list_bi_map_not_In in n0.
          rewrite H1, n0 in H0. assumption.
    - destruct (InEither_dec x l).
      + apply list_bi_map_In in i. destruct i as [k [v [? ?]]].
        destruct (DoubleNoDup_bi_look_up _ _ _ H H0).
        destruct H1 as [[? ?] | [? ?]]; subst x; rewrite H4; unfold list_bi_map.
        * rewrite H3. reflexivity.
        * rewrite H2. reflexivity.
      + apply list_bi_map_not_In in n. rewrite n. assumption.
  Qed.

  Lemma DoubleNoDup_cons_iff: forall a b l,
      DoubleNoDup ((a, b) :: l) <->
      DoubleNoDup l /\ a <> b /\ ~ InEither a l /\ ~ InEither b l.
  Proof.
    intros. unfold DoubleNoDup, InEither. simpl. destruct (split l) as [l1 l2].
    rewrite !NoDup_app_iff, !NoDup_cons_iff, !in_app_iff. simpl. split; intros.
    - destruct H as [[? ?] [[? ?] ?]]. intuition.
      + apply (H3 x); right; assumption.
      + apply (H3 b); left; auto.
      + apply (H3 a); [left | right]; auto.
      + apply (H3 b); [right | left]; auto.
    - destruct H as [[? [? ?]] [? [? ?]]]. apply Decidable.not_or in H3.
      apply Decidable.not_or in H4. destruct H3, H4.
      intuition; [subst; contradiction..| apply (H1 x); assumption].
  Qed.

  Lemma InEither_app_iff: forall a l1 l2,
      InEither a (l1 ++ l2) <-> InEither a l1 \/ InEither a l2.
  Proof.
    intros a l1. revert a. induction l1; simpl; intros. 1: intuition.
    rewrite !InEither_cons_iff, IHl1. intuition.
  Qed.

  Lemma DoubleNoDup_app_iff: forall l1 l2,
      DoubleNoDup (l1 ++ l2) <->
      DoubleNoDup l1 /\ DoubleNoDup l2 /\ (forall x, InEither x l1 -> ~ InEither x l2).
  Proof.
    induction l1; simpl; intros. 1: intuition; constructor. destruct a as [a b].
    rewrite !DoubleNoDup_cons_iff, !InEither_app_iff, IHl1. clear IHl1. intuition.
    - apply (H4 x); auto. rewrite InEither_cons_iff in H5. destruct H5; auto.
      unfold IsEither in H5. simpl in H5. exfalso. destruct H5; subst; contradiction.
    - apply (H3 x); auto. rewrite InEither_cons_iff. right; assumption.
    - apply (H3 a); auto. rewrite InEither_cons_iff. left. left. simpl; reflexivity.
    - apply (H3 b); auto. rewrite InEither_cons_iff. left. right. simpl; reflexivity.
  Qed.

  Lemma DoubleNoDup_list_bi_map: forall k v l,
      DoubleNoDup l -> In (k, v) l -> list_bi_map l k = v /\ list_bi_map l v = k.
  Proof.
    intros. destruct (DoubleNoDup_bi_look_up _ _ _ H H0). unfold list_bi_map.
    rewrite H1, H2. split; reflexivity.
  Qed.

  Lemma DoubleNoDup_cons_InEither: forall l a b,
      DoubleNoDup (a :: l) -> InEither b l -> ~ IsEither b a.
  Proof.
    intros. destruct a as [x y]. rewrite DoubleNoDup_cons_iff in H.
    destruct H as [? [? [? ?]]]. intro. red in H4. simpl in H4. destruct H4; now subst.
  Qed.

  Lemma list_bi_map_nil: list_bi_map nil = id.
  Proof. extensionality x. unfold list_bi_map. now simpl. Qed.

  Lemma DoubleNoDup_fst: forall l, DoubleNoDup l -> NoDup (map fst l).
  Proof.
    intros. red in H. destruct (split l) eqn:? . rewrite map_fst_split, Heqp. simpl.
    now apply NoDup_app_l in H.
  Qed.

  Lemma DoubleNoDup_snd: forall l, DoubleNoDup l -> NoDup (map snd l).
  Proof.
    intros. red in H. destruct (split l) eqn:? . rewrite map_snd_split, Heqp. simpl.
    now apply NoDup_app_r in H.
  Qed.

End LIST_DERIVED_BIJECTION.

Section LIST_DERIVED_MAPPING.

  Context {A: Type}.
  Context {AE: EqDec A eq}.

  Fixpoint look_up (l: list (A * A)) (key: A): option A :=
    match l with
    | nil => None
    | (k, v) :: l' => if equiv_dec k key then Some v else look_up l' key
    end.

  Definition list_map (l: list (A * A)) (r: A): A :=
    match (look_up l r) with
    | Some v => v
    | None => r
    end.

  Lemma list_map_cons_1: forall a l x,
      x <> fst a -> list_map (a :: l) x = list_map l x.
  Proof.
    intros. unfold list_map. simpl. destruct a. simpl in *. destruct (equiv_dec a x).
    1: unfold equiv in e; exfalso; apply H; subst; easy. reflexivity.
  Qed.

  Lemma list_map_not_In: forall l x, ~ In x (map fst l) -> list_map l x = x.
  Proof.
    induction l; intros. 1: unfold list_map; simpl; reflexivity. simpl in H.
    apply Decidable.not_or in H. destruct H. rewrite list_map_cons_1. 2: intuition.
    now apply IHl.
  Qed.

  Lemma NoDup_look_up: forall k v l,
      NoDup (map fst l) -> In (k, v) l -> look_up l k = Some v.
  Proof.
    do 3 intro. induction l; intros. 1: inversion H0. simpl in *.
    destruct a as [k0 v0]. destruct H0.
    - inversion H0. subst. destruct (equiv_dec k k). reflexivity. exfalso. intuition.
    - simpl in H. destruct (equiv_dec k0 k); unfold equiv in *.
      + apply NoDup_cons_2 in H. exfalso. apply H. subst. now apply (in_map fst) in H0.
      + apply NoDup_cons_1 in H. now apply IHl.
  Qed.

  Lemma list_map_In: forall l k v,
      NoDup (map fst l) -> In (k, v) l -> list_map l k = v.
  Proof. intros. unfold list_map. now rewrite (NoDup_look_up k v). Qed.

  Lemma list_map_NoDup_app_eq: forall l1 l2 v,
      NoDup (map fst (l2 ++ l1)) ->
      (~ In v (map fst l1) -> In (v, v) l2) -> list_map l1 v = list_map (l2 ++ l1) v.
  Proof.
    intros. destruct (in_dec equiv_dec v (map fst (l2 ++ l1))).
    - destruct (in_dec equiv_dec v (map fst l1)).
      + rewrite In_map_fst_iff in i0. destruct i0 as [b ?].
        erewrite !list_map_In; eauto. 1: rewrite in_app_iff; now right.
        rewrite map_app in H. now apply NoDup_app_r in H.
      + rewrite list_map_not_In; auto. apply H0 in n. erewrite list_map_In; eauto.
        rewrite in_app_iff. now left.
    - rewrite !list_map_not_In; auto. intro. apply n. rewrite map_app, in_app_iff.
      now right.
  Qed.

  Lemma list_map_DoubleNoDup_incl_eq: forall l1 l2 v,
      DoubleNoDup (l2 ++ l1) -> (In v (map fst (l2 ++ l1)) -> In v (map fst l1)) ->
      list_map l1 v = list_map (l2 ++ l1) v.
  Proof.
    intros. destruct (in_dec equiv_dec v (map fst (l2 ++ l1))).
    - destruct (in_dec equiv_dec v (map fst l1)). 2: now apply H0 in i.
      rewrite In_map_fst_iff in i0. destruct i0 as [b ?].
      rewrite !(list_map_In _ _ b); auto.
      + now apply DoubleNoDup_fst in H.
      + rewrite in_app_iff. now right.
      + rewrite DoubleNoDup_app_iff in H. destruct H as [? [? ?]].
        now apply DoubleNoDup_fst in H2.
    - rewrite !list_map_not_In; auto. intro. apply n. rewrite map_app, in_app_iff.
      now right.
  Qed.

  Lemma look_up_not_In: forall l v, ~ In v (map fst l) <-> look_up l v = None.
  Proof.
    induction l; intros; simpl. 1: intuition. destruct a as [k v']. simpl.
    split; intros.
    - apply Decidable.not_or in H. destruct H.
      destruct (equiv_dec k v); unfold equiv in *; [contradiction | now apply IHl].
    - destruct (equiv_dec k v). 1: inversion H. rewrite <- IHl in H. intro.
      unfold equiv, complement in c. destruct H0; contradiction.
  Qed.

  Lemma In_look_up: forall l v a, look_up l v = Some a ->
                                  In v (map fst l) /\ In a (map snd l).
  Proof.
    induction l; intros; simpl in *. 1: inversion H. destruct a as [k v']. simpl.
    destruct (equiv_dec k v); unfold equiv in *.
    - inversion H. subst. intuition.
    - apply IHl in H. destruct H. split; now right.
  Qed.

  Lemma InEither_map_iff: forall v (l: list (A * A)),
      InEither v l <-> In v (map fst l) \/ In v (map snd l).
  Proof.
    intros. unfold InEither. destruct (split l) eqn:? .
    rewrite in_app_iff, map_fst_split, map_snd_split, Heqp. now simpl.
  Qed.

  Lemma In_look_up': forall l k v, look_up l k = Some v -> In (k, v) l.
  Proof.
    induction l; intros; simpl in *. 1: inversion H. destruct a as [k' v'].
    destruct (equiv_dec k' k); unfold equiv in *.
    - inversion H. subst. now left.
    - apply IHl in H. now right.
  Qed.

  Lemma list_map_idempotent: forall l, DoubleNoDup l -> idempotent (list_map l).
  Proof.
    destruct l; intros; red; intros.
    - unfold list_map. now simpl.
    - destruct p as [k v]. rewrite DoubleNoDup_cons_iff in H.
      destruct H as [? [? [? ?]]]. unfold list_map. simpl.
      destruct (equiv_dec k x); unfold equiv in *.
      + subst x. destruct (equiv_dec k v); auto.
        destruct (look_up l v) eqn:? ; auto. apply In_look_up in Heqo. exfalso.
        apply H2. rewrite InEither_map_iff. now left.
      + unfold complement in c. destruct (look_up l x) eqn:? .
        * apply In_look_up in Heqo. destruct Heqo.
          destruct (equiv_dec k a); unfold equiv in *.
          -- subst a. exfalso. apply H1. rewrite InEither_map_iff. now right.
          -- destruct (look_up l a) eqn:? ; auto. apply In_look_up in Heqo.
             destruct Heqo as [? _]. red in H. destruct (split l) eqn:? .
             rewrite map_fst_split, Heqp in H5. rewrite map_snd_split, Heqp in H4.
             simpl in H4, H5. rewrite NoDup_app_iff in H. destruct H as [_ [_ ?]].
             exfalso. now apply (H a).
        * destruct (equiv_dec k x); unfold equiv in *; [easy | now rewrite Heqo].
  Qed.

  Lemma list_map_bi_map: forall l x,
      ~ In x (map snd l) -> list_map l x = list_bi_map l x.
  Proof.
    induction l; intros; unfold list_map, list_bi_map; simpl; auto.
    destruct a as [k v]. simpl in *. apply Decidable.not_or in H. destruct H.
    destruct (equiv_dec k x); auto. destruct (equiv_dec v x); unfold equiv in *.
    1: easy. fold (list_map l x) (list_bi_map l x). now apply IHl.
  Qed.

End LIST_DERIVED_MAPPING.

(************CUSTOM LIST OPERATIONS************)
(*Since it makes sense for us to deal with l+::a a lot*)

(*curious this doesn't exist in the list library*)
Fixpoint last_error {A: Type} (l : list A): option A :=
match l with
| nil => None
| a::nil => Some a
| _::l' => last_error l'
end.

Lemma last_error_cons: (*for convenience*)
  forall {A:Type} (l: list A) (a: A), l <> nil -> last_error (a::l) = last_error l.
Proof.
intros. destruct l. contradiction. simpl. reflexivity.
Qed.

Lemma last_err_appcons:
  forall {A:Type} (l: list A) (a: A), last_error (l+::a) = Some a.
Proof.
induction l. auto. intros. rewrite <- app_comm_cons. rewrite <- (IHl a0). simpl.
destruct (l+::a0) eqn:H. assert (l+::a0 <> nil) by (apply app_not_nil). contradiction.
reflexivity.
Qed.

Lemma last_err_app':
  forall {A:Type} (l2 l1: list A) (a: A), last_error l2 = Some a -> last_error (l1++l2) = Some a.
Proof.
induction l2; intros. inversion H.
destruct l2. simpl in H. inversion H. apply last_err_appcons.
assert (last_error (a::a1::l2) = last_error (a1::l2)). simpl. reflexivity. rewrite H0 in H.
assert (l1++a::a1::l2 = (l1+::a) ++ (a1::l2)).
assert (a:: a1 :: l2 = (a::nil)++a1::l2) by reflexivity. rewrite H1.
rewrite app_assoc. reflexivity. rewrite H1.
apply (IHl2 (l1+::a)). apply H.
Qed.

Lemma last_err_app:
  forall {A:Type} (l1 l2: list A) (a: A), last_error l2 = Some a -> last_error (l1++l2) = Some a.
Proof.
intros. apply (last_err_app' l2 l1 a H).
Qed.

Lemma last_err_split2:
forall {A: Type} (l1 l2: list A) (a: A),
last_error (l1++a::l2) = last_error (a::l2).
induction l1; intros. rewrite app_nil_l; auto.
replace (last_error ((a :: l1) ++ a0 :: l2)) with (last_error (l1 ++ a0 :: l2)).
2: { simpl. destruct (l1++a0::l2) eqn:Htmp.
  apply app_eq_nil in Htmp. destruct Htmp. inversion H0. auto. }
apply IHl1.
Qed.

Lemma hd_error_app:
  forall {A:Type} (l2 l1: list A) (a: A), hd_error l1 = Some a -> hd_error (l1++l2) = Some a.
Proof.
induction l1; intros. inversion H. simpl. simpl in H. auto.
Qed.

Lemma rev_hd_last:
  forall {A:Type} (l: list A), hd_error l = last_error (rev l).
Proof.
induction l. auto.
simpl. rewrite (last_err_appcons (rev l) a). reflexivity.
Qed.

Lemma hd_error_In:
  forall {A:Type} (l: list A) a, hd_error l = Some a -> In a l.
Proof.
intros. destruct l; simpl in H; inversion H. left; auto.
Qed.

Lemma last_error_In:
  forall {A:Type} (l: list A) a, last_error l = Some a -> In a l.
Proof.
induction l; intros. inversion H.
destruct l. inversion H. left; auto.
right. apply IHl. rewrite last_error_cons in H. apply H.
unfold not; intros. inversion H0.
Qed.

(*NoDup is probably unnecessary, but convenient*)
Lemma list_same_diff:
forall {A: Type} {EA: EqDec A eq} (l1 l2: list A), NoDup l1 -> NoDup l2 ->
      exists lsame ldiff, NoDup lsame /\ NoDup ldiff /\ Permutation (lsame++ldiff) l1 /\
      incl lsame l2 /\ (forall e, In e ldiff -> ~ In e l2).
Proof.
induction l1; intros.
+exists nil. exists nil. repeat split.
  apply NoDup_nil. apply NoDup_nil. rewrite app_nil_l. apply perm_nil.
  unfold incl; intros; contradiction. unfold not; intros; contradiction.
+
(*By NoDup, a can't already be in l1*)
assert (NoDup l1). apply NoDup_cons_1 in H; auto.
apply (IHl1 l2 H1) in H0. destruct H0 as [lsame [ldiff [? [? [? [? ?]]]]]].
destruct (in_dec EA a l2).
(*yes, then a is in lsame*)
exists (a::lsame). exists ldiff. repeat split.
  simpl. apply NoDup_cons. unfold not; intros.
  assert (In a l1). apply (Permutation_in (l:=(lsame++ldiff))); auto. apply in_or_app. left; auto.
  apply NoDup_cons_2 in H; auto. auto.
  auto.
  simpl; apply perm_skip; auto.
  unfold incl; intros. destruct H6. subst a; auto. auto.
  auto.
(*no, then a is in ldiff*)
exists lsame. exists (a::ldiff). repeat split.
  auto.
  apply NoDup_cons. unfold not; intros. assert (In a l1).
  apply (Permutation_in (l:=(lsame++ldiff))); auto. apply in_or_app. right; auto.
  apply NoDup_cons_2 in H. contradiction.
  auto.
  apply (Permutation_trans (l:=lsame ++ a :: ldiff) (l':=a::ldiff++lsame)).
  apply Permutation_app_comm. apply perm_skip.
  apply (Permutation_trans (l':=lsame ++ ldiff) (l:=ldiff++lsame)).
  apply Permutation_app_comm. apply H3.
  auto.
  intros. destruct H6. subst a. auto. auto.
Qed.

Lemma app_eq_single_inv:
  forall
    A l (a b: A),
    l ++ (a::nil) = b::nil ->
    l = nil /\ a = b.
Proof.
  intros.
  induction l.
  - inversion H. split; trivial.
  - simpl in H. inversion H. exfalso.
    apply (app_not_nil l a); trivial.
Qed.

Lemma Zlength_cons_sub_1:
  forall A (a: A) l,
    Zlength (a :: l) - 1 = Zlength l.
Proof.
  intros. rewrite Zlength_cons.
  pose proof (Zlength_nonneg l). lia.
Qed.

Lemma backwards_list_ind: forall A (P : list A -> Prop),
  P nil ->
  (forall (a : A) (l : list A), P l -> P (l +:: a )) ->
     forall l : list A, P l.
Proof.
  intros.
  remember (length l).
  assert (Datatypes.length l <= n)%nat by lia. clear Heqn. revert l H1. induction n; intros.
  destruct l. apply H. simpl in H1. lia.
  remember (foot l). symmetry in Heqo.
  destruct o.
  2: apply foot_none_nil in Heqo; subst l; apply H.
  apply foot_explicit in Heqo. destruct Heqo as [l' ?]. subst l.
  apply H0. apply IHn. rewrite app_length in H1. simpl in H1. lia.
Qed.

(***** NAT_INC_LIST ******)

Fixpoint nat_inc_list (n: nat) : list Z :=
  match n with
  | O => nil
  | S n' => nat_inc_list n' ++ (Z.of_nat n' :: nil)
  end.

Lemma nat_inc_list_in_iff: forall n v, List.In v (nat_inc_list n) <-> 0 <= v < Z.of_nat n.
Proof.
  induction n; intros; [simpl; lia|]. rewrite Nat2Z.inj_succ. unfold Z.succ. simpl. rewrite in_app_iff.
  assert (0 <= v < Z.of_nat n + 1 <-> 0 <= v < Z.of_nat n \/ v = Z.of_nat n) by lia. rewrite H. clear H. rewrite IHn. simpl. intuition.
Qed.

Lemma nat_inc_list_NoDup: forall n, NoDup (nat_inc_list n).
Proof.
  induction n; simpl; [constructor|]. apply NoDup_app_inv; auto.
  - constructor; auto. constructor.
  - intros. rewrite nat_inc_list_in_iff in H. simpl. lia.
Qed.

Lemma nat_inc_list_length: forall n, length (nat_inc_list n) = n. Proof. induction n; simpl; auto. rewrite app_length. simpl. rewrite IHn. lia. Qed.

Lemma nat_inc_list_Zlength:
  forall n, Zlength (nat_inc_list n) = Z.of_nat n.
Proof.
  intros. now rewrite Zlength_correct, nat_inc_list_length. Qed.

Lemma nat_inc_list_i: forall i n,
    0 <= i < Z.of_nat n ->
    Znth i (nat_inc_list n) = i.
Proof.
  intros. generalize dependent i. induction n.
  1: intros; exfalso; destruct H; rewrite Nat2Z.inj_0 in H0; lia.
  intros. simpl. rewrite Nat2Z.inj_succ in H. destruct H.
  apply Zlt_succ_le in H0. apply Zle_lt_or_eq in H0. destruct H0.
  - rewrite app_Znth1. apply IHn. lia.
    now rewrite nat_inc_list_Zlength.
  - rewrite app_Znth2 by (rewrite nat_inc_list_Zlength; lia). 
    rewrite H0. rewrite nat_inc_list_Zlength. simpl. 
    replace (Z.of_nat n - Z.of_nat n) with 0 by lia.
    rewrite Znth_0_cons; trivial.
Qed.

Lemma nat_inc_list_app:
  forall n m p i,
    0 <= i < m ->
    0 <= n ->
    n + m <= p ->
    Znth i (nat_inc_list (Z.to_nat m)) =
    Znth i (sublist n (n + m)
                    (nat_inc_list (Z.to_nat p))) - n.
Proof.
  symmetry. rewrite Znth_sublist by lia.
  repeat rewrite nat_inc_list_i by lia. lia.
Qed.

Lemma nat_inc_list_sublist:
  forall n m,
    0 <= n ->
    n <= m ->
    sublist 0 n (nat_inc_list (Z.to_nat m)) =
    nat_inc_list (Z.to_nat n).
Proof.
  intros.
  apply Zle_lt_or_eq in H0. destruct H0.
  2: { subst. rewrite sublist_same; trivial.
       rewrite nat_inc_list_Zlength; lia.
  }
  apply Znth_eq_ext.
  1: { rewrite Zlength_sublist;
       try rewrite nat_inc_list_Zlength; lia.
  }
  intros. rewrite nat_inc_list_i.
  2: { rewrite Zlength_sublist in H1; 
       try rewrite nat_inc_list_Zlength; lia.
  }
  rewrite <- Z.sub_0_r at 1.
  replace n with (0 + n) by lia.
  rewrite Zlength_sublist in H1.
  rewrite <- nat_inc_list_app.
  rewrite nat_inc_list_i.
  all: try rewrite nat_inc_list_Zlength; lia.
Qed.

Lemma nat_inc_list_hd:
  forall n,
    0 < n ->
    Znth 0 (nat_inc_list (Z.to_nat n)) = 0.
Proof.
  intros. induction (Z.to_nat n); trivial.
  simpl. destruct n0; trivial.
  rewrite app_Znth1; [lia|].
  rewrite nat_inc_list_Zlength.
  rewrite <- Nat2Z.inj_0.
  apply inj_lt; lia.
Qed.

Lemma tl_app:
  forall (l1 l2: list Z),
    0 < Zlength l1 ->
    tl (l1 ++ l2) = tl l1 ++ l2.
Proof.
  intros. destruct l1; trivial. inversion H.
Qed.

Lemma in_tl_nat_inc_list:
  forall i n,
    In i (tl (nat_inc_list n)) -> 1 <= i.
Proof.
  destruct n. inversion 1.
  induction n. inversion 1.
  intros. simpl in H.
  rewrite Zpos_P_of_succ_nat in H.
  rewrite tl_app in H.
  2: { rewrite Zlength_app.
       replace (Zlength (Z.of_nat n :: nil)) with 1 by reflexivity.
       pose proof (Zlength_nonneg (nat_inc_list n)). lia.
  }
  apply in_app_or in H; destruct H.
  - apply IHn. simpl. assumption.
  - simpl in H. destruct H; lia.
Qed.
