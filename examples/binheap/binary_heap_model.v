Require Import Psatz.
Require Import List.
Require Import Arith.Div2.
Require Import Even.
Require Import Relations.
Require Import RelationClasses.
Require Import PeanoNat.
Require Import Peano_dec.
Require Import Recdef.
Require Import Sorting.
Require Import Permutation.
Require Import Multiset.

(* List-related items... *)

Lemma nth_error_le {A}: forall L x (a : A),
  nth_error L x = Some a ->
  forall y, y <= x -> exists b, nth_error L y = Some b.
Proof.
  induction L; intros. destruct x; inversion H.
  destruct x. assert (y = 0) by lia. subst y. inversion H. subst a0. exists a. apply H.
  simpl in H. specialize (IHL _ _ H).
  destruct y. exists a. trivial.
  simpl. apply IHL. lia.
Qed.

Lemma nth_error_eq: forall A (L1 L2 : list A),
  (forall i, nth_error L1 i = nth_error L2 i) ->
  L1 = L2.
Proof.
  induction L1. destruct L2; auto; intros. specialize (H 0%nat); discriminate.
  destruct L2. intro. specialize (H 0%nat); discriminate. intros.
  f_equal. specialize (H 0%nat). inversion H. trivial.
  apply IHL1. intro. specialize (H (S i)). apply H.
Qed.

Lemma forall_permutation: forall A P (L : list A),
  Forall P L ->
    forall L', Permutation L L' ->
      Forall P L'.
Proof.
  intros. revert H. induction H0; intros; auto.
  inversion H; subst. constructor; auto.
  inversion H. inversion H3. subst.
  repeat (constructor; auto).
Qed.

Fixpoint update {A} (L : list A) (i : nat) (x : A) : list A :=
  match L, i with
   | _ :: L', 0 => x :: L'
   | h :: L', S i' => h :: (update L' i' x)
   | nil, _ => L
  end.

Lemma update_length: forall A (L : list A) i x,
  length (update L i x) = length L.
Proof.
  induction L; auto; destruct i; simpl; auto.
Qed.

Lemma nth_error_update: forall A (L : list A) i x, i < length L ->
  nth_error (update L i x) i = Some x.
Proof.
  induction L; intros. inversion H.
  destruct i. reflexivity.
  simpl. apply IHL. simpl in H. lia.
Qed.

Lemma nth_error_update': forall A (L : list A) i x j, i <> j ->
  nth_error (update L i x) j = nth_error L j.
Proof.
  induction L; intros. destruct j; reflexivity.
  destruct j; destruct i. contradiction. reflexivity. reflexivity.
  apply IHL. lia.
Qed.

Lemma nth_error_update_oob: forall A (L : list A) i x, i >= length L ->
  nth_error (update L i x) i = None.
Proof.
  induction L; intros. destruct i; reflexivity.
  destruct i. simpl in H. lia.
  apply IHL. simpl in H. lia.
Qed.

Lemma update_idem: forall A (L : list A) i x,
  nth_error L i = Some x ->
  update L i x = L.
Proof.
  induction L; intros. reflexivity.
  destruct i. inversion H. subst. reflexivity.
  simpl. f_equal. apply IHL. apply H.
Qed.

Lemma update_update: forall A (L : list A) i x y,
  update (update L i x) i y = update L i y.
Proof.
  induction L; intros. reflexivity.
  destruct i. reflexivity.
  simpl. f_equal. apply IHL.
Qed.

Lemma update_update': forall A (L : list A) i x j y,
  i <> j ->
  update (update L i x) j y = update (update L j y) i x.
Proof.
  induction L; intros. reflexivity.
  destruct i, j. contradiction. reflexivity. reflexivity.
  simpl. rewrite IHL; trivial. lia.
Qed.

Definition exchange {A} (L : list A) (i j : nat) : list A :=
  match nth_error L i, nth_error L j with
   | Some a, Some b => update (update L j a) i b
   | _, _ => L
  end.

Lemma exchange_length: forall A (L : list A) i j,
  length (exchange L i j) = length L.
Proof.
  unfold exchange. intros. case nth_error; trivial. case nth_error; trivial.
  intros. do 2 rewrite update_length. trivial.
Qed.

Lemma exchange_eq_nil: forall A (L : list A) i j,
  exchange L i j = nil ->
  L = nil.
Proof. unfold exchange. intros A L i j. case nth_error; auto. case nth_error; auto.
  destruct L. trivial. destruct j, i; simpl; discriminate.
Qed.

Lemma exchange_eq: forall A (L : list A) i,
  exchange L i i = L.
Proof.
  unfold exchange. intros. case_eq (nth_error L i); auto.
  intros. rewrite update_update. rewrite update_idem; auto.
Qed.

Lemma exchange_eq': forall A (L : list A) i j a,
  nth_error L i = a ->
  nth_error L j = a ->
  exchange L i j = L.
Proof.
  unfold exchange. intros. rewrite H, H0. destruct a; trivial.
  replace (update L j a) with L. apply update_idem; trivial.
  symmetry. apply update_idem; trivial.
Qed.

Lemma nth_error_exchange: forall A (L : list A) i j,
  i < length L -> j < length L ->
  nth_error (exchange L i j) i = nth_error L j.
Proof.
  unfold exchange. intros. case_eq (nth_error L j).
  intros. case_eq (nth_error L i); intros.
  rewrite nth_error_update; auto.
  rewrite update_length.
  apply nth_error_Some. rewrite H2. discriminate.
  apply nth_error_Some in H. contradiction.
  intro. apply nth_error_None in H1. lia.
Qed.

Lemma nth_error_exchange': forall A (L : list A) i j,
  i < length L -> j < length L ->
  nth_error (exchange L i j) j = nth_error L i.
Proof.
  unfold exchange. intros. case_eq (nth_error L i).
  intros. case_eq (nth_error L j); intros.
  case (eq_nat_dec i j); intro. subst. rewrite update_update.
  rewrite nth_error_update; auto. rewrite H1 in H2. auto.
  rewrite nth_error_update'; auto. rewrite nth_error_update; auto.
  apply nth_error_None in H2. lia.
  intro. apply nth_error_None in H1. lia.
Qed.

Lemma nth_error_exchange'': forall A (L : list A) i j k,
  i <> k -> j <> k ->
  nth_error (exchange L i j) k = nth_error L k.
Proof.
  unfold exchange. intros.
  case_eq (nth_error L i);
  case_eq (nth_error L j);
  case_eq (nth_error L k); intros; auto;
  rewrite nth_error_update'; auto;
  rewrite nth_error_update'; auto.
Qed.

Lemma nth_error_exchange_oob: forall A (L : list A) i j k,
  k >= length L ->
  nth_error (exchange L i j) k = None.
Proof. 
  intros.
  apply nth_error_None. 
  rewrite exchange_length. lia.
Qed.

Lemma exchange_Permutation: forall A (L : list A) i j,
  Permutation (exchange L i j) L.
Proof.
  unfold exchange. intros.
  case_eq (nth_error L i); auto.
  case_eq (nth_error L j); auto.
  intros. rewrite Permutation_nth_error.
  do 2 rewrite update_length. split; trivial.
  exists (fun x => if eq_nat_dec x i then j else
                   if eq_nat_dec x j then i else x).
  split.
  do 2 intro.
  case (eq_nat_dec x i); case (eq_nat_dec y i); case (eq_nat_dec x j); case (eq_nat_dec y j); congruence.
  intro n.
  case (eq_nat_dec n i); intro. subst i.
  case (eq_nat_dec n j); intro. subst j.
  rewrite H in H0. inversion H0. subst a0.
  repeat rewrite nth_error_update; auto.
  rewrite update_length. apply nth_error_Some; congruence.
  rewrite nth_error_update'; auto.
  rewrite nth_error_update; auto.
  apply nth_error_Some; congruence.
  case (eq_nat_dec n j); intro.
  subst j.
  rewrite nth_error_update; auto.
  rewrite update_length.
  apply nth_error_Some; congruence.
  do 2 (rewrite nth_error_update'; auto).
Qed.

Lemma exchange_head_foot: forall A (head : A) body foot,
  exchange ((head :: body) ++ (foot :: nil)) 0 (length (head :: body)) = ((foot :: body) ++ (head :: nil)).
Proof.
  intros.
  apply nth_error_eq. intro i. case (eq_nat_dec i 0); intro.
  + subst i. 
    rewrite nth_error_exchange; simpl. 2: lia.
    rewrite nth_error_app2. simpl. rewrite Nat.sub_diag. trivial. trivial.
    rewrite app_length. simpl. lia.
  + case (eq_nat_dec i (length (head :: body))); intro.
    - subst i.
      rewrite nth_error_exchange'; simpl. 2: lia.
      rewrite nth_error_app2. rewrite Nat.sub_diag. trivial. trivial.
      rewrite app_length. simpl. lia.
    - rewrite nth_error_exchange''; auto.
      destruct i. contradiction. simpl. simpl in n0.
      assert (i < (length body) \/ i >= length (body ++ (foot :: nil))). { rewrite app_length. simpl. lia. }
      destruct H. repeat rewrite nth_error_app1; auto.
      assert (i >= length (body ++ (head :: nil))). { rewrite app_length in *. simpl in *. trivial. }
      apply nth_error_None in H. apply nth_error_None in H0. congruence.
Qed.

Lemma exchange_symm : forall A (L : list A) i j,
  (i < length L) -> (j < length L) ->
  exchange L i j = exchange L j i.
Proof.
  intros.
  apply nth_error_eq. intro k.
  case (eq_nat_dec i k); intro. subst k.
  rewrite nth_error_exchange; auto.
  rewrite nth_error_exchange'; auto.
  case (eq_nat_dec j k); intro. subst k.
  rewrite nth_error_exchange'; auto.
  rewrite nth_error_exchange; auto.
  rewrite nth_error_exchange''; auto.
  rewrite nth_error_exchange''; auto.
Qed.

Lemma exchange_update : forall A k j x y (L : list A),
  k < length L ->
  j < length L ->
  nth_error L k = Some x ->
  nth_error L j = Some y ->
  update (update L j x) k y = exchange L j k.
Proof.
  intros. apply nth_error_eq. intros.
  case (eq_nat_dec k i); intro. subst k.
  rewrite nth_error_exchange'; auto.
  rewrite nth_error_update; auto. rewrite update_length; auto.
  rewrite nth_error_update'; auto.
  case (eq_nat_dec j i); intro. subst j.
  rewrite nth_error_exchange; auto.
  rewrite nth_error_update; auto.
  rewrite nth_error_exchange''; auto.
  rewrite nth_error_update'; auto.
Qed.

Fixpoint foot_split {A} (L : list A) : (list A) * (option A) :=
  match L with 
   | nil => (nil, None)
   | h :: nil => (nil, Some h)
   | h :: L' => match foot_split L' with (L'', o) => (h :: L'', o) end
  end.

Lemma foot_split_spec: forall A (L : list A),
  match foot_split L with
   | (L', None) => L = L' /\ L' = nil
   | (L', Some a) => L = L' ++ a :: nil
  end.
Proof.
  induction L; simpl. auto.
  destruct L. reflexivity.
  remember (foot_split (a0 :: L)). destruct p. destruct o.
  rewrite IHL.
  rewrite app_comm_cons. trivial. destruct IHL. congruence.
Qed.

Lemma foot_split_length: forall A (L : list A),
  match foot_split L with
   | (L', None) => length L' = length L
   | (L', Some _) => 1 + length L' = length L
  end.
Proof. 
  intros. generalize (foot_split_spec _ L). destruct (foot_split L).
  destruct o; intros; subst; auto. rewrite app_length. simpl. lia. destruct H. congruence. 
Qed.

Lemma sorted_glue {A : Type}: forall (A_rel : A -> A -> Prop) (L1 L2 : list A) (a1 a2 : A),
  Sorted A_rel (L1 ++ (a1 :: nil)) ->
  Sorted A_rel (a2 :: L2) ->
  A_rel a1 a2 ->
  Sorted A_rel ((L1 ++ (a1 :: nil)) ++ (a2 :: L2)).
Proof.
  induction L1; simpl. constructor; auto.
  intros. apply Sorted_inv in H. destruct H.
  constructor. apply IHL1; auto.
  destruct L1; apply HdRel_inv in H2; constructor; auto.
Qed.

Lemma sorted_rev {A : Type}: forall (A_rel : A -> A -> Prop) (L : list A),
  Sorted A_rel L -> Sorted (Basics.flip A_rel) (rev L).
Proof.
  intros. induction H. apply Sorted_nil.
  destruct l; simpl in *. repeat constructor.
  apply sorted_glue; auto.
  apply HdRel_inv in H0. apply H0.
Qed.

Lemma sorted_rev' {A : Type}: forall (A_rel : A -> A -> Prop) (L : list A),
  Sorted A_rel (rev L) -> Sorted (Basics.flip A_rel) L.
Proof. intros. apply sorted_rev in H. rewrite rev_involutive in H. trivial. Qed.

Section Heap.

Variable A : Type.
Variable Aleq : relation A.
Variable Aleq_dec : forall a a', {Aleq a a'} + {~Aleq a a'}.
Variable Apo : PreOrder Aleq. (* Reflexive, transitive *)
Variable Aleq_linear : forall a b, Aleq a b \/ Aleq b a.

Instance A_Apo : PreOrder Aleq := Apo.

Declare Scope heap_scope.
Notation "A <<= B" := (Aleq A B) (at level 50) : heap_scope.
Notation "A <<=? B" := (Aleq_dec A B) (at level 50) : heap_scope.
Local Open Scope heap_scope.

(* Unlike in [Segwick], we use the root at zero and adjust the left/right/parent
   calculations.  This has the advantage of simpler theorem statements, but 
   somewhat messier arithmetic.  In the end our indicies will be 1 less than his, 
   but other than that, no divergence. *)
Definition root_idx : nat := 0.
Definition left_child (idx : nat) : nat := 1 + idx + idx. (* 2 * (idx + 1) - 1 *) 
Definition right_child (idx : nat) : nat := (left_child idx) + 1. (* 2 + idx + idx. *) (* 2 * (idx + 1) + 1 - 1 *)
Definition parent (idx : nat) : nat := div2 (idx - 1). (* ((idx + 1) / 2) - 1 *)

Lemma parent_le: forall i,
  parent i <= i.
Proof. intro. apply Nat.div2_decr. lia. Qed.

Lemma parent_root: parent root_idx = root_idx.
Proof. reflexivity. Qed.

Lemma parent_dec: forall i,
  i > root_idx ->
  parent i < i.
Proof.
  intros.
  destruct i. inversion H. destruct i. constructor.
  etransitivity.
  apply lt_div2; lia.
  lia.
Qed.

Lemma left_child_inc: forall i,
  i < left_child i.
Proof. unfold left_child. lia. Qed.

Lemma right_child_inc: forall i,
  i < right_child i.
Proof. unfold right_child, left_child. lia. Qed.

Lemma left_child_lt_right_child: forall j,
  left_child j < right_child j.
Proof. unfold right_child, left_child. lia. Qed.

Lemma parent_left_child: forall i,
  parent (left_child i) = i.
Proof. unfold parent, left_child. intro. replace (1 + i + i - 1) with (2 * i) by lia. apply div2_double. Qed.

Lemma parent_right_child: forall i,
  parent (right_child i) = i.
Proof. unfold parent, right_child, left_child. intro. replace (1 + i + i + 1 - 1) with (S (2 * i)) by lia. apply div2_double_plus_one. Qed.

Lemma left_child_parent_odd: forall i,
  odd i ->
  left_child (parent i) = i.
Proof. 
  unfold left_child, parent. intros.
  inversion H.
  replace (S n - 1) with n by lia.
  simpl. f_equal. rewrite even_double; auto.
Qed.

Lemma right_child_parent_even: forall i,
  i > root_idx -> even i ->
  right_child (parent i) = i.
Proof. 
  unfold right_child, left_child, parent, root_idx. intros.
  inversion H0. lia.
  replace (S n - 1) with n by lia. simpl. f_equal.
  rewrite (odd_double n) at 3; auto. unfold double. lia.
Qed.

Lemma left_child_monotone: forall i j,
  i < j ->
  left_child i < left_child j.
Proof. unfold left_child. lia. Qed.

Lemma right_child_monotone: forall i j,
  i < j ->
  right_child i < right_child j.
Proof. unfold right_child, left_child. lia. Qed.

(*
Lemma left_child_wmonotone: forall i j,
  i <= j ->
  left_child i <= left_child j.
Proof. unfold left_child. lia. Qed.

Lemma right_child_wmonotone: forall i j,
  i <= j ->
  right_child i <= right_child j.
Proof. unfold right_child, left_child. lia. Qed.
*)

(* Might be nice to see if this can be made more abstract. *)
Lemma left_child_S_right_child: forall i,
  S (left_child i) = right_child i.
Proof. unfold right_child. lia. Qed.

(*
Lemma left_child_nonroot: forall i,
  left_child i > root_idx.
Proof. unfold root_idx, left_child. intro i; lia. Qed.

Lemma right_child_nonroot: forall i,
  right_child i > root_idx.
Proof. unfold root_idx, right_child, left_child. intro i; lia. Qed.
*)

Lemma left_child_inj: forall i j,
  left_child i = left_child j -> i = j.
Proof. unfold left_child; intros; lia. Qed.

Lemma right_child_inj: forall i j,
  right_child i = right_child j -> i = j.
Proof. unfold right_child, left_child; intros; lia. Qed.

Lemma left_child_root: forall i,
  left_child i > root_idx.
Proof. unfold left_child, root_idx. lia. Qed.

Lemma right_child_root: forall i,
  right_child i > root_idx.
Proof. unfold right_child, root_idx. lia. Qed.

Lemma left_child_neq_right_child: forall i j,
  left_child i <> right_child j.
Proof. unfold right_child, left_child. lia. Qed.

Opaque left_child. Opaque right_child. Opaque parent.

Definition heapOrdered (L : list A) : Prop :=
  forall i a,
    nth_error L i = Some a ->
    (forall b, nth_error L (left_child i) = Some b -> a <<= b) /\
    (forall c, nth_error L (right_child i) = Some c -> a <<= c).

Lemma heapOrdered_empty: 
  heapOrdered nil.
Proof.
  repeat intro. destruct i; discriminate.
Qed.

Lemma heapOrdered_cutfoot: forall L a,
  heapOrdered (L ++ (a :: nil)) ->
  heapOrdered L.
Proof.
  repeat intro. specialize (H i a0). 
  rewrite nth_error_app1 in H.
  specialize (H H0). destruct H.
  split; intros. apply H.
  rewrite nth_error_app1. trivial.
  apply nth_error_Some; congruence.
  apply H1.
  rewrite nth_error_app1. trivial.
  apply nth_error_Some; congruence.
  apply nth_error_Some; congruence.
Qed.

(* Sometimes, it's more convenient to reason bottom-up rather than top-down. *)
Definition heapOrdered2 (L : list A) : Prop :=
  forall i b,
    nth_error L i = Some b ->
      forall a, nth_error L (parent i) = Some a ->
        a <<= b.

Lemma hOhO2: forall L, heapOrdered L <-> heapOrdered2 L.
Proof.
  split; repeat intro.
  * destruct i. simpl in H1. destruct L. discriminate. inversion H1.
    simpl in H0. inversion H0. subst. reflexivity.
    specialize (H _ _ H1). destruct H.
    destruct (even_or_odd (S i)).
    apply H2. rewrite right_child_parent_even; auto. unfold root_idx; lia.
    apply H. rewrite left_child_parent_odd; auto.
  * split; intros; eapply H; try apply H1.
    rewrite parent_left_child. trivial.
    rewrite parent_right_child. trivial.
Qed.

Lemma root_minimal: 
  forall L, heapOrdered L -> 
    forall r, nth_error L root_idx = Some r ->
      Forall (fun x => r <<= x) L.
Proof.
  unfold root_idx.
  do 4 intro.
  rewrite Forall_forall. intros. apply In_nth_error in H1. destruct H1 as [i H1].
  remember i as j. assert (j <= i) by (subst j; constructor). clear Heqj.
  revert j x H2 H1.
  induction i. destruct j. intros. rewrite H0 in H1. inversion H1. reflexivity.
  inversion 1.
  intros. assert (j <= i \/ j = S i) by lia. destruct H3.
  eapply IHi; eauto.
  subst j.
  destruct (nth_error_le _ _ _ H1 (parent (S i))).
  generalize (parent_dec (S i)). unfold root_idx. lia.
  transitivity x0. eapply IHi. 2: apply H3. generalize (parent_dec (S i)). unfold root_idx. lia.
  rewrite hOhO2 in H.
  eapply H; eauto.
Qed.

(* subtle invariant for transitivity of grandparents/children, when parent is delinquient.
   Used in both weak invariants. *)

(* rt: the highest location in the heap (that is, the lowest index) that is known to be ok,
   except for p itself *)
Definition grandsOk (L : list A) (p : nat) (rt : nat) : Prop :=
  p <> root_idx -> parent p >= rt ->
    forall gs bb, parent gs = p -> nth_error L gs = Some bb ->
      forall a, nth_error L (parent p) = Some a -> a <<= bb.

Lemma grandsOk_root: forall L j,
  grandsOk L j root_idx <-> (j <> root_idx ->
    forall jj bb, parent jj = j -> nth_error L jj = Some bb ->
      forall a, nth_error L (parent j) = Some a -> a <<= bb).
Proof.
  split; repeat intro; eapply H; eauto. unfold root_idx. lia.
Qed.

Lemma hO_grandsOk: forall L j,
  heapOrdered L ->
  grandsOk L j root_idx.
Proof.
  repeat intro.
  generalize (nth_error_le _ _ _ H3 j); intro. rewrite <- H2 in H5.
  destruct (H5 (parent_le gs)). apply hOhO2 in H.
  transitivity x; eapply H; eauto. congruence.
Qed.

(* insertion, via swimming upwards *)

Definition swim1 (L : list A) (j : nat) : (list A) * (option nat) :=
  if j <=? root_idx then (L, None) else 
  match nth_error L j, nth_error L (parent j) with
   | None, _ | _, None => (L, None)
   | Some child, Some root => if child <<=? root then (exchange L j (parent j), Some (parent j)) else (L, None)
  end.

Lemma swim1_dec: forall L j L' j',
  swim1 L j = (L', Some j') ->
  j' < j.
Proof.
  unfold swim1. intros L j L' j'. case_eq (j <=? root_idx). discriminate.
  case_eq (nth_error L j). 2: discriminate.
  case_eq (nth_error L (parent j)). 2: discriminate.
  intros a a0 ?. case (a1 <<=? a). 2: discriminate.
  intros. inversion H1.
  apply parent_dec.
  apply Nat.leb_nle in H0. lia.
Qed.

Function swim (L : list A) (j : nat) {measure id j} : list A :=
  match swim1 L j with
   | (L, None) => L
   | (L', Some j') => swim L' j'
  end.
Proof. intros. unfold id. eapply swim1_dec. apply teq. Defined.

Definition insert (L : list A) (x : A) : list A :=
  swim (L ++ (x :: nil)) (length L).

(* Simple facts about swim *)

Lemma swim_0: forall L,
  swim L 0 = L.
Proof. reflexivity. Qed.

Lemma swim_done: forall L i a b,
  nth_error L i = Some b ->
  nth_error L (parent i) = Some a ->
  ~ b <<= a ->
  swim L i = L.
Proof.
  intros. rewrite swim_equation. unfold swim1. rewrite H, H0. case (i <=? root_idx); auto.
  case (b <<=? a); intro; trivial. contradiction.
Qed.

Lemma swim_step: forall L i a b,
  0 < i < length L ->
  nth_error L i = Some b ->
  nth_error L (parent i) = Some a ->
  b <<= a ->
  swim (exchange L i (parent i)) (parent i) = swim L i.
Proof.
  intros. assert (parent i < i) by (apply parent_dec; unfold root_idx; lia).
  rewrite (swim_equation L i). unfold swim1.
  rewrite H0, H1.
  case_eq (i <=? root_idx); intro. { apply Nat.leb_le in H4. unfold root_idx in H4. lia. }
  case (b <<=? a); intro. 2: contradiction. trivial.
Qed.

(* insertion preserves heap order *)

Definition weak_heapOrdered2 (L : list A) (j : nat) : Prop :=
  (forall i b, i <> j -> nth_error L i = Some b ->
     forall a, nth_error L (parent i) = Some a -> a <<= b) /\
  grandsOk L j root_idx.

Lemma hOwhO2: forall L j,
  heapOrdered L ->
  weak_heapOrdered2 L j.
Proof.
  split. 2: apply hO_grandsOk; auto. rewrite hOhO2 in H. intros ? ? ?. apply H.
Qed.

Lemma weak_heapOrdered2_root: forall (L : list A),
  weak_heapOrdered2 L root_idx -> heapOrdered L.
Proof.
  intros. rewrite hOhO2.
  repeat intro.
  destruct H.
  case (eq_nat_dec i root_idx); intro.
  subst i. rewrite parent_root in H1. rewrite H0 in H1. inversion H1. reflexivity.
  eapply H; eauto.
Qed.

Lemma weak_heapOrdered2_postpend: forall (L : list A) x,
  heapOrdered L <->
  weak_heapOrdered2 (L ++ (x :: nil)) (length L).
Proof.
  intros L x. rewrite hOhO2. split.
* split; repeat intro.
  + assert (i < length (L ++ (x :: nil))) by (apply nth_error_Some; congruence).
    rewrite app_length in H3. simpl in H3.
    assert (i < length L) by lia.
    generalize (parent_le i); intro.
    rewrite nth_error_app1 in H1; try lia.
    rewrite nth_error_app1 in H2; try lia.
    eapply H; eauto.
  + (* grands *)
    assert (gs < length (L ++ x :: nil)) by (apply nth_error_Some; congruence).
    rewrite app_length in H5. simpl in H5.
    destruct gs. destruct L. simpl in *. inversion H3. inversion H4. subst. reflexivity. discriminate.
    assert (parent (S gs) < S gs). apply parent_dec. unfold root_idx. lia.
    lia.
* repeat intro.
  assert (i < length L) by (apply nth_error_Some; congruence).
  destruct H. apply H with i; auto.
  lia. 
  rewrite nth_error_app1; trivial.
  rewrite nth_error_app1; trivial.
  apply nth_error_Some; congruence.
Qed.

Lemma weak_heapOrdered2_oob: forall i L,
  i >= length L ->
  weak_heapOrdered2 L i ->
  heapOrdered L.
Proof.
  intros. apply hOhO2.
  repeat intro. destruct H0. eapply H0. 2: apply H1. 2: apply H2.
  intro. subst i0. assert (i < length L) by (apply nth_error_Some; congruence). lia.
Qed.

Lemma heapOrdered_lower_priority_weak_heapOrdered2: forall H,
  heapOrdered H ->
  forall t old, 
  nth_error H t = Some old ->
  forall new, new <<= old ->
  weak_heapOrdered2 (update H t new) t.
Proof.
  intros. apply hOhO2 in H0. split. intros. rewrite nth_error_update' in H4; auto.
  case (dec_eq_nat t (parent i)); intro.
  subst t. rewrite nth_error_update in H5. inversion H5. subst a. clear H5.
  transitivity old; auto. eapply H0; eauto.
  eapply nth_error_Some. intro. rewrite H6 in H1. discriminate.
  rewrite nth_error_update' in H5; auto.
  eapply H0; eauto.
  repeat intro.
  assert (t > root_idx) by (unfold root_idx in *; lia).
  generalize (parent_dec _ H8); intro.
  rewrite nth_error_update' in H7. 2: lia.
  rewrite nth_error_update' in H6.
  transitivity old; eapply H0; eauto. rewrite H5; trivial.
  intro. subst gs. lia.
Qed.

Lemma swim1_hO: forall L j,
  weak_heapOrdered2 L j ->
  match swim1 L j with
   | (L', None) => heapOrdered L'
   | (L', Some j') => weak_heapOrdered2 L' j'
  end.
Proof.
  intros. unfold swim1. case_eq (j <=? root_idx); intro.
  rewrite Nat.leb_le in H0. destruct j. apply weak_heapOrdered2_root. trivial. inversion H0.
  rename H0 into Hx.
  case_eq (nth_error L j); case_eq (nth_error L (parent j)); intros.
  + case (a0 <<=? a).
    - split; repeat intro. 
      * rename j into child. remember (parent child) as root. rename a into rootval. rename a0 into childval.
        case (eq_nat_dec i child); intro. 
        ++ subst i. rewrite nth_error_exchange in H3; try (apply nth_error_Some; congruence).
           rewrite H0 in H3.  inversion H3. subst b. clear H3.
           rewrite <- Heqroot in H4. rewrite nth_error_exchange' in H4; try (apply nth_error_Some; congruence).
           rewrite H1 in H4. inversion H4. subst a2. trivial.
        ++ rewrite nth_error_exchange'' in H3; auto.
           destruct (eq_nat_dec (parent i) root).
           -- rename i into sibling.
              rewrite e in H4.
              rewrite nth_error_exchange' in H4; try (apply nth_error_Some; congruence).
              rewrite H1 in H4. inversion H4. subst a2. clear H4.
              destruct H.
              specialize (H sibling b n H3 rootval). rewrite e in H. specialize (H H0).
              transitivity rootval; auto.
           -- destruct (eq_nat_dec (parent i) child).
              rename i into grandchild.
              2: destruct H; specialize (H i b n H3); rewrite nth_error_exchange'' in H4; auto.
              rewrite e in H4. rewrite nth_error_exchange in H4; try (apply nth_error_Some; congruence).
              rewrite H0 in H4. inversion H4. subst a2. clear H4.
              destruct H.
              rewrite Heqroot in H0.
              rewrite grandsOk_root in H4.
              eapply H4; eauto.
              apply Nat.leb_nle in Hx. lia. 
      * (* establish grands *)
        apply Nat.leb_nle in Hx. assert (j > root_idx) by lia.
        assert (parent j < j) by (apply parent_dec; lia).
        assert (parent (parent j) < parent j) by (apply parent_dec; unfold root_idx in *; lia).
        rewrite nth_error_exchange'' in H6; try lia.
        case (eq_nat_dec j gs); intro.
        -- subst gs.
           rewrite nth_error_exchange in H5; try (apply nth_error_Some; congruence).
           destruct H. eapply H. 3: eapply H6. lia. trivial.
        -- assert (gs <> parent j). { intro. subst gs. lia. }
              rewrite nth_error_exchange'' in H5; auto.
              rewrite <- H4 in *. destruct H. transitivity a; eapply H.
              2: apply H0. lia. trivial. 2: apply H5. lia. trivial.
    - rewrite hOhO2. repeat intro. destruct (eq_nat_dec i j).
      subst j. rewrite H1 in H3. rewrite H0 in H4. inversion H3. inversion H4. subst a0 a1. clear H3 H4.
      destruct (Aleq_linear a b); auto. contradiction.
      destruct H.
      apply H with i; auto.
  + assert (parent j <= j) by apply parent_le.
    destruct (nth_error_le _ _ _ H1 _ H2). congruence.
  + rewrite hOhO2. repeat intro. destruct H. apply H with i; auto.
    congruence.
  + rewrite hOhO2. repeat intro. destruct H. apply H with i; auto.
    congruence.
Qed.

Lemma swim_hO: forall L j,
  weak_heapOrdered2 L j ->
  heapOrdered (swim L j).
Proof.
  intros L j.
  apply swim_ind; intros.
  generalize (swim1_hO L0 j0 H).
  rewrite e. trivial.
  generalize (swim1_hO L0 j0 H0).
  rewrite e.
  apply H.
Qed.

Lemma insert_hO: forall L x,
  heapOrdered L ->
  heapOrdered (insert L x).
Proof.
  intros. unfold insert. apply swim_hO.
  apply weak_heapOrdered2_postpend. trivial.
Qed.

(* insertion yields permutation *)

Lemma swim1_permutation: forall L j,
  match swim1 L j with
   | (L', _) => Permutation L L'
  end.
Proof.
  unfold swim1. intros. case (j <=? root_idx); auto.
  case (nth_error L j); auto.
  case (nth_error L (parent j)); auto.
  intros. case (a0 <<=? a); auto.
  intro. symmetry. apply exchange_Permutation.
Qed.

Lemma swim_permutation: forall L j,
  Permutation L (swim L j).
Proof.
  intros. apply swim_ind; clear; intros.
  generalize (swim1_permutation L j); intro. rewrite e in H. trivial.
  generalize (swim1_permutation L j); intro. rewrite e in H0. transitivity L'; trivial.
Qed.

Lemma insert_permutation: forall L x,
  Permutation (x :: L) (insert L x).
Proof.
  intros. unfold insert.
  transitivity (L ++ (x :: nil)).
  change (x :: L) with ((x :: nil) ++ L).
  apply Permutation_app_comm.
  apply swim_permutation.
Qed.

(* remove min, via sinking downwards *)

Definition sink1 (L : list A) (j : nat) : (list A) * (option nat) :=
  match nth_error L j, nth_error L (left_child j), nth_error L (right_child j) with
   | None, _, _ | Some _, None, _ => (L, None)
   | Some root, Some Left, None => if root <<=? Left then (L, None) else (exchange L j (left_child j), Some (left_child j)) (* corner case *)
   | Some root, Some Left, Some Right => 
     if Right <<=? Left then if root <<=? Right then (L, None) else (exchange L j (right_child j), Some (right_child j)) 
     else if root <<=? Left then (L, None) else (exchange L j (left_child j), Some (left_child j))
  end.

Lemma sink1_length: forall L j,
  match sink1 L j with
   | (L', None) | (L', Some _) => length L = length L'
  end.
Proof.
  unfold sink1. intros. case (nth_error L j); trivial. case (nth_error L (left_child j)); trivial.
  case (nth_error L (right_child j)); intros. case (a <<=? a0). case (a1 <<=? a); trivial.
  rewrite exchange_length. trivial.
  case (a1 <<=? a0); trivial. rewrite exchange_length; trivial.
  case (a0 <<=? a); trivial. rewrite exchange_length; trivial.
Qed.

Lemma sink1_inc: forall L j L' j',
  sink1 L j = (L', Some j') ->
  j < j' < length L'.
Proof.
  unfold sink1. intros L j L' j'.
  case_eq (nth_error L j). 2: discriminate.
  case_eq (nth_error L (left_child j)). 2: discriminate.
  case_eq (nth_error L (right_child j)).
  do 6 intro. case (a <<=? a0). case (a1 <<=? a).
  discriminate.
  intros. inversion H2. rewrite exchange_length.
  split. apply right_child_inc. apply nth_error_Some; congruence.
  case (a1 <<=? a0). discriminate.
  inversion 3. rewrite exchange_length.
  split. apply left_child_inc. apply nth_error_Some; congruence.
  do 5 intro. case (a0 <<=? a). discriminate. 
  inversion 2.
  rewrite exchange_length.
  split. apply left_child_inc. apply nth_error_Some. congruence.
Qed.

Definition sink_measure (Lj : (list A) * nat) : nat := 
  match Lj with (L, j) => length L - j end.

Function sink (Lj : (list A) * nat) {measure sink_measure Lj} : list A :=
  match Lj with (L, j) => 
  match sink1 L j with
   | (L, None) => L
   | (L', Some j') => sink (L', j')
  end end.
Proof. intros. unfold sink_measure. generalize (sink1_length L j). generalize (sink1_inc L j). rewrite teq0. intros.
  specialize (H L' j'). assert (j < j' < length L') by auto. lia. Defined.

Definition remove_min (L : list A) : (list A) * (option A) :=
  match L with
   | nil => (L, None)
   | r :: L'' => (match foot_split L'' with (_, None) => nil | (L''', Some f) => sink (f :: L''', root_idx) end
                 , Some r)
  end.

(* Simple facts about sink *)

Lemma sink_large: forall L i,
  length L <= i ->
  sink (L,i) = L.
Proof.
  intros. rewrite sink_equation. unfold sink1.
  case_eq (nth_error L i); auto. intros.
  assert (i < length L) by (apply nth_error_Some; congruence).
  lia.
Qed.

Lemma sink_done: forall L i a,
  nth_error L i = Some a ->
  (forall b, nth_error L (left_child i)  = Some b -> a <<= b) -> 
  (forall b, nth_error L (right_child i) = Some b -> a <<= b) ->
  sink (L, i) = L.
Proof.
  intros. rewrite sink_equation. unfold sink1. rewrite H.
  case_eq (nth_error L (left_child i)); auto.
  intros. specialize (H0 _ H2).
  case_eq (nth_error L (right_child i)); intros.
  specialize (H1 _ H3). case (a1 <<=? a0); intro.
  case (a <<=? a1); auto. contradiction.
  case (a <<=? a0); auto. contradiction.
  case (a <<=? a0); auto. contradiction.
Qed.

Lemma sink_step: forall L i p lc,
  nth_error L i = Some p ->
  nth_error L (left_child i) = Some lc ->
  forall j, (match nth_error L (right_child i) with 
              | None => j = left_child i /\ ~(p <<= lc) 
              | Some rc => (j = left_child i /\ ~(rc <<= lc) /\ ~(p <<= lc)) \/ 
                           (j = right_child i /\ rc <<= lc /\ (~p <<= rc)) 
             end) ->
  sink (exchange L i j, j) = sink (L, i).
Proof.
  intros. rewrite (sink_equation (L, i)). unfold sink1.
  rewrite H, H0. revert H1. case nth_error; intros. case (a <<=? lc); intros.
  destruct H1 as [[? [? ?]] | [? [? ?]]]; subst j.
  case (p <<=? a); auto. contradiction. contradiction.
  case (p <<=? a); auto. contradiction.
  destruct H1 as [[? [? ?]] | [? [? ?]]]; subst j.
  case (p <<=? lc). contradiction. auto.
  contradiction.
  destruct H1. subst.
  case (p <<=? lc). contradiction. auto.
Qed.

(* removal preserves heap order *)

Definition weak_heapOrdered (L : list A) (j : nat) : Prop :=
  (forall i a, i <> j -> 
    nth_error L i = Some a ->
    (forall b, nth_error L (left_child i) = Some b -> a <<= b) /\
    (forall c, nth_error L (right_child i) = Some c -> a <<= c)) /\
  grandsOk L j root_idx.

(* The following two versions are to support bottom-up heapify *)
Definition heapOrdered_bounded (L : list A) (k : nat) : Prop :=
  forall i a, i >= k ->
    nth_error L i = Some a ->
    (forall b, nth_error L (left_child i) = Some b -> a <<= b) /\
    (forall c, nth_error L (right_child i) = Some c -> a <<= c).

Definition weak_heapOrdered_bounded (L : list A) (k : nat) (j : nat) : Prop :=
  (forall i a, i >= k -> i <> j -> 
    nth_error L i = Some a ->
    (forall b, nth_error L (left_child i) = Some b -> a <<= b) /\
    (forall c, nth_error L (right_child i) = Some c -> a <<= c)) /\
  (grandsOk L j k).

Lemma heapOrdered_bounded_root_heapOrdered: forall L,
  heapOrdered_bounded L root_idx <-> heapOrdered L.
Proof.
  split. split; intros; assert (i >= root_idx) by (unfold root_idx; lia); destruct (H i a H2 H0); auto.
  repeat intro. apply H. trivial.
Qed.

Lemma weak_heapOrdered_bounded_root_weak_heapOrdered: forall L j,
  weak_heapOrdered_bounded L root_idx j <-> weak_heapOrdered L j.
Proof.
  split; intros [? ?]; split; auto.
  intros. apply H; auto. unfold root_idx; lia.
Qed.

Lemma hOwhO: forall L j,
  heapOrdered L ->
  weak_heapOrdered L j.
Proof.
  split. 2: apply hO_grandsOk; auto. intros ? ? ?. apply H.
Qed.

Lemma weak_heapOrdered_bounded_root: forall r1 L b,
  heapOrdered_bounded (r1 :: L) b ->
  forall r2, weak_heapOrdered_bounded (r2 :: L) b root_idx.
Proof.
  repeat intro. split; intros.
  specialize (H i a H0).
  destruct i. contradiction.
  specialize (H H2). apply H. intro. lia.
Qed.

Lemma weak_heapOrdered_bounded_oob: forall i L b,
  i >= length L ->
  weak_heapOrdered_bounded L b i ->
  heapOrdered_bounded L b.
Proof.
  repeat intro. destruct H0. apply H0; auto. 
  intro. subst i0. assert (i < length L) by (apply nth_error_Some; congruence). lia.
Qed.

Lemma weak_heapOrdered_root: forall r1 L,
  heapOrdered (r1 :: L) ->
  forall r2, weak_heapOrdered (r2 :: L) root_idx.
Proof.
  intros. apply weak_heapOrdered_bounded_root_weak_heapOrdered.
  apply heapOrdered_bounded_root_heapOrdered in H.
  apply weak_heapOrdered_bounded_root with r1. trivial.
Qed.

Lemma weak_heapOrdered_oob: forall i L,
  i >= length L ->
  weak_heapOrdered L i ->
  heapOrdered L.
Proof.
  intros. apply weak_heapOrdered_bounded_root_weak_heapOrdered in H0.
  apply heapOrdered_bounded_root_heapOrdered. apply weak_heapOrdered_bounded_oob in H0; auto.
Qed.

Lemma heapOrdered_raise_priority_weak_heapOrdered: forall H,
  heapOrdered H ->
  forall t old,
  nth_error H t = Some old ->
  forall new, old <<= new ->
  weak_heapOrdered (update H t new) t.
Proof.
  split; intros. rewrite nth_error_update' in H4; auto.
  specialize (H0 _ _ H4). destruct H0.
  case (eq_nat_dec t (left_child i)); intro. subst t.
  rewrite nth_error_update. 2: apply nth_error_Some; intro Hx; rewrite Hx in H1; discriminate.
  rewrite nth_error_update'. 2: apply left_child_neq_right_child.
  split; intros; auto. inversion H6. subst b. transitivity old; auto.
  case (eq_nat_dec t (right_child i)); intro. subst t.
  rewrite nth_error_update. 2: apply nth_error_Some; intro Hx; rewrite Hx in H1; discriminate.
  rewrite nth_error_update'. 2: { intro. symmetry in H6. apply left_child_neq_right_child in H6; trivial. }
  split; intros; auto. inversion H6. subst c. transitivity old; auto.
  rewrite nth_error_update'; auto. rewrite nth_error_update'; auto.
  repeat intro.
  rewrite nth_error_update' in H7. 2: generalize (parent_dec t); lia.
  rewrite nth_error_update' in H6. 2: intro; subst gs; generalize (parent_dec t); lia.
  apply hOhO2 in H0.
  transitivity old; eapply H0; eauto. rewrite H5; trivial.
Qed.

(* facts about sink relative to bottom-up heapify *)

Lemma heapOrdered_bounded_half: forall L,
  heapOrdered_bounded L (1 + parent (length L)).
Proof.
  intro. assert (length L = 0 \/ length L > 0) by lia. destruct H. destruct L.
  repeat intro. destruct i; inversion H1. inversion H. rename H into Hx.
  split; repeat intro.
  *  assert (left_child i < length L) by (apply nth_error_Some; congruence).
     destruct (even_or_odd (length L)).
     + apply right_child_monotone in H.
       rewrite right_child_parent_even in H; auto.
       clear -H H2.
       generalize (left_child_S_right_child i); intro. lia.
     + apply left_child_monotone in H.
       rewrite left_child_parent_odd in H; auto. lia.
  * assert (right_child i < length L) by (apply nth_error_Some; congruence).
    destruct (even_or_odd (length L)).
    + apply right_child_monotone in H.
      rewrite right_child_parent_even in H; auto.
      lia.
    + apply left_child_monotone in H.
      rewrite left_child_parent_odd in H; auto.
      assert (Hw : left_child i < right_child i) by apply left_child_lt_right_child.
      lia.
Qed.

Lemma hObU_whObU_pred: forall L k,
  heapOrdered_bounded L (1 + k) <->
  weak_heapOrdered_bounded L k k.
Proof.
  split; intros.
  * split; intros. apply H. lia. auto.
    repeat intro. assert (k > root_idx) by (unfold root_idx in *; lia).
    generalize (parent_dec k H5). lia.
  * repeat intro. destruct H. apply H; auto; lia.
Qed.

Lemma weak_heapOrdered_bounded_half: forall L,
  weak_heapOrdered_bounded L (parent (length L)) (parent (length L)).
Proof.
  intros. rewrite <- hObU_whObU_pred. apply heapOrdered_bounded_half.
Qed.

(* This proof is rather maddening... *)
Lemma sink1_hObU: forall L k j,
  weak_heapOrdered_bounded L k j ->
  match sink1 L j with
   | (L', None) => heapOrdered_bounded L' k
   | (L', Some j') => weak_heapOrdered_bounded L' k j'
  end.
Proof.
  intros. unfold sink1.
  assert (Hy : j < left_child j) by apply left_child_inc.
  assert (Hw : left_child j < right_child j) by apply left_child_lt_right_child.
  case_eq (nth_error L j).
  * case_eq (nth_error L (left_child j)).
    + intros. assert (Hl : left_child j < length L) by (apply nth_error_Some; congruence).
      case_eq (nth_error L (right_child j)); intros.
      - assert (Hr: right_child j < length L) by (apply nth_error_Some; congruence).
        case (a1 <<=? a). 2: (destruct (Aleq_linear a1 a); try contradiction; intros _).
        ** case (a0 <<=? a1). 2: (destruct (Aleq_linear a0 a1); try contradiction; intros _).
           ++ repeat intro. case (eq_nat_dec i j).
              -- intro. subst j. rewrite H0, H2. rewrite H1 in H4. inversion H4. subst a4. clear H4.
                 split; inversion 1; subst; auto.
                 transitivity a1; auto.
              -- intro. destruct H. apply H; auto.
           ++ split; intros.
              -- case (eq_nat_dec i j); intro.
                 *** subst j.
                     rewrite nth_error_exchange in H6; try lia.
                     rewrite nth_error_exchange'; try lia.
                     rewrite nth_error_exchange''; try lia.
                     rewrite H1, H0.
                     rewrite H2 in H6. inversion H6. subst a3. clear H6.
                     split; inversion 1; subst; auto.
                 *** rewrite nth_error_exchange'' in H6; auto.
                     assert (right_child i <> right_child j) by (intro Hq; apply right_child_inj in Hq; auto).
                     destruct H. case (eq_nat_dec j (right_child i)); intro.
                     +++ subst j. rewrite nth_error_exchange; try lia.
                         rewrite H2. split.
                         --- intro. rewrite nth_error_exchange''.
                             intro. specialize (H i a3 H4 n H6). apply H in H9. trivial.
                             generalize (left_child_lt_right_child i). lia.
                             intro. eapply left_child_neq_right_child; eauto.
                         --- inversion 1. subst c. clear H9.
                             apply H8 with (right_child (right_child i)); auto.
                             generalize (right_child_root i). unfold root_idx. lia.
                             rewrite parent_right_child. unfold root_idx. lia.
                             rewrite parent_right_child; auto.
                             rewrite parent_right_child; auto.
                     +++ split. 2: rewrite nth_error_exchange''; auto; apply H; auto.
                         case (eq_nat_dec j (left_child i)); intro.
                         --- subst j. rewrite nth_error_exchange; try lia.
                             rewrite H2. inversion 1. subst b. clear H9.
                             eapply H8. 4: apply H2.
                             generalize (left_child_root i); unfold root_idx; lia.
                             rewrite parent_left_child. trivial.
                             rewrite parent_right_child. trivial.
                             rewrite parent_left_child. trivial.
                         --- rewrite nth_error_exchange''; auto.
                             apply H; auto.
                             generalize (left_child_neq_right_child i j). lia.
              -- repeat intro.
                 rewrite parent_right_child in H8. rewrite nth_error_exchange in H8; try lia.
                 rewrite H2 in H8. inversion H8. subst a3. clear H8.
                 assert (parent gs < gs). { apply parent_dec. unfold root_idx. assert (gs = 0 \/ gs > 0) by lia. 
                   destruct H8; trivial. subst gs. change 0 with root_idx in H6. rewrite parent_root in H6.
                   generalize (right_child_root j). lia. }
                 rewrite nth_error_exchange'' in H7; try lia.
                 destruct H.
                 assert (right_child j <> j) by lia.
                 rewrite parent_right_child in H5.
                 assert (right_child j >= k) by (generalize (right_child_inc j); lia).
                 specialize (H _ _ H11 H10 H2). destruct H.
                 rewrite <- H6 in *.
                 destruct (even_or_odd gs).
                 apply H12. rewrite right_child_parent_even; auto. generalize (left_child_root j); intro. lia.
                 apply H. rewrite left_child_parent_odd; auto.
        ** case (a0 <<=? a). 2: (destruct (Aleq_linear a0 a); try contradiction; intros _).
           ++ repeat intro. case (eq_nat_dec i j).
              -- intro. subst j. rewrite H0, H2. rewrite H1 in H5. inversion H5. subst a3. clear H5.
                 split; inversion 1; subst; auto.
                 transitivity a; auto.
              -- intro. destruct H. apply H; auto.
           ++ intros. split; intros.
              -- case (eq_nat_dec i j); intro.
                 *** subst j.
                     rewrite nth_error_exchange in H7; try lia.
                     rewrite nth_error_exchange'; try lia.
                     rewrite nth_error_exchange''; try lia.
                     rewrite H1, H2.
                     rewrite H0 in H7. inversion H7. subst a2. clear H7.
                     split; inversion 1; subst; auto.
                 *** rewrite nth_error_exchange'' in H7; auto.
                     assert (left_child i <> left_child j) by (intro Hq; apply left_child_inj in Hq; auto).
                     destruct H. case (eq_nat_dec j (left_child i)); intro.
                     +++ subst j. rewrite nth_error_exchange; try lia.
                         rewrite H0. split.
                         --- inversion 1. subst b. clear H10.
                             apply H9 with (left_child (left_child i)); auto.
                             generalize (left_child_root i). lia.
                             1,2,3: rewrite parent_left_child; auto.
                         --- intro. rewrite nth_error_exchange''.
                             intro. eapply H; eauto.
                             generalize (left_child_lt_right_child i). lia.
                             apply left_child_neq_right_child.
                     +++ rewrite nth_error_exchange''; auto. split.
                         apply H; auto.
                         case (eq_nat_dec j (right_child i)); intro.
                         --- subst j. rewrite nth_error_exchange; try lia.
                             rewrite H0. inversion 1. subst c. clear H10.
                             eapply H9. 4: apply H0.
                             generalize (right_child_root i); lia.
                             1,3: rewrite parent_right_child; auto.
                             rewrite parent_left_child. trivial.
                         --- rewrite nth_error_exchange''; auto.
                             apply H; auto.
                             apply left_child_neq_right_child.
              -- repeat intro.
                 rewrite parent_left_child in H9. rewrite nth_error_exchange in H9; try lia.
                 rewrite H0 in H9. inversion H9. subst a2. clear H9.
                 assert (parent gs < gs). { apply parent_dec. unfold root_idx. assert (gs = 0 \/ gs > 0) by lia. 
                   destruct H9; trivial. subst gs. change 0 with root_idx in H7. rewrite parent_root in H7.
                   generalize (left_child_root j). lia. }
                 rewrite nth_error_exchange'' in H8; try lia.
                 destruct H.
                 assert (left_child j <> j) by lia.
                 rewrite parent_left_child in H6.
                 assert (left_child j >= k) by (generalize (left_child_inc j); lia).
                 specialize (H _ _ H12 H11 H0). destruct H.
                 rewrite <- H7 in *.
                 destruct (even_or_odd gs).
                 apply H13. rewrite right_child_parent_even; auto. generalize (left_child_root j); intro. lia.
                 apply H. rewrite left_child_parent_odd; auto.
      - assert (Hr: right_child j >= length L) by (apply nth_error_None in H2; auto).
        case (a0 <<=? a); repeat intro.
        ** case (eq_nat_dec i j); intro.
           ++ subst j. rewrite H1 in H4. inversion H4. subst a2. clear H4.
              rewrite H0, H2.
              split; inversion 1. subst b. trivial.
           ++ destruct H. apply H; auto.
        ** split; intros. case (eq_nat_dec i j); intro.
           ++ subst j.
              rewrite nth_error_exchange in H5; try lia.
              rewrite nth_error_exchange'; try lia.
              rewrite nth_error_exchange_oob; try lia.
              rewrite H1. rewrite H0 in H5. inversion H5. subst a1. clear H5.
              split; intros; inversion H5. subst a0. destruct (Aleq_linear a b); trivial.
              contradiction.
           ++ rewrite nth_error_exchange'' in H5; auto.
              assert (left_child i <> left_child j) by (intro Hq; apply left_child_inj in Hq; auto).
              assert (left_child j <> right_child i) by apply left_child_neq_right_child.
              destruct H. specialize (H _ _ H3 n0 H5).
              split.
              -- case (eq_nat_dec j (left_child i)); intro.
                 *** subst j. rewrite nth_error_exchange; try lia. rewrite H0. inversion 1. subst b. clear H9.
                     assert (left_child i <> root_idx) by (generalize (left_child_root i); lia).
                     assert (parent (left_child i) >= k) by (rewrite parent_left_child; auto).
                     apply (H8 H9 H10 (left_child (left_child i))); try rewrite parent_left_child; auto.
                 *** rewrite nth_error_exchange''; auto. destruct H. apply H.
              -- case (eq_nat_dec j (right_child i)); intro.
                 *** subst j. rewrite nth_error_exchange; try lia. rewrite H0. inversion 1. subst c. clear H9.
                     assert (right_child i <> root_idx) by (generalize (right_child_root i); lia).
                     assert (parent (right_child i) >= k) by (rewrite parent_right_child; auto). 
                     eapply (H8 H9 H10 (left_child (right_child i))).
                     rewrite parent_left_child. trivial. trivial. rewrite parent_right_child. trivial.
                 *** rewrite nth_error_exchange''; auto. destruct H. apply H9.
           ++ repeat intro.
              rewrite parent_left_child in H7. rewrite nth_error_exchange in H7; try lia.
              rewrite H0 in H7. inversion H7. subst a1. clear H7.
              assert (parent gs < gs). { apply parent_dec. unfold root_idx. assert (gs = 0 \/ gs > 0) by lia.
                   destruct H7; trivial. subst gs. change 0 with root_idx in H5. rewrite parent_root in H5.
                   generalize (left_child_root j). lia. }
              rewrite nth_error_exchange'' in H6; try lia.
              assert (left_child j <> j) by lia.
              rewrite parent_left_child in H4.
              assert (left_child j >= k) by (generalize (left_child_inc j); lia).
              destruct H. specialize (H _ _ H9 H8 H0). destruct H.
              rewrite <- H5 in *.
              destruct (even_or_odd gs).
              apply H11. rewrite right_child_parent_even; auto. generalize (left_child_root j); intro. lia.
              apply H. rewrite left_child_parent_odd; auto.
    + repeat intro. case (eq_nat_dec i j); intro. 2: eapply H; auto.
      subst j. rewrite H1 in H3; inversion H3. subst a0. clear H3.
      split; intros. rewrite H0 in H3; inversion H3.
      apply nth_error_None in H0.
      assert (right_child i < length L) by (apply nth_error_Some; congruence).
      lia.
  * repeat intro. assert (i <> j). intro. subst. rewrite H0 in H2. discriminate. destruct H. eapply H; trivial.
Qed.

Lemma sink_hO_bounded: forall L k j,
  weak_heapOrdered_bounded L k j ->
  heapOrdered_bounded (sink (L, j)) k.
Proof.
  intros L k j whO. remember (L, j) as Lj. assert (match Lj with (L, j) => weak_heapOrdered_bounded L k j end). rewrite HeqLj. trivial. revert H. clear -Apo Aleq_linear.
  apply sink_ind; intros.
  generalize (sink1_hObU L k j H).
  rewrite e0. trivial.
  generalize (sink1_hObU L k j H0).
  rewrite e0.
  apply H.
Qed.

Lemma sink_hO: forall L j,
  weak_heapOrdered L j ->
  heapOrdered (sink (L, j)).
Proof.
  intros. rewrite <- heapOrdered_bounded_root_heapOrdered. apply sink_hO_bounded.
  rewrite weak_heapOrdered_bounded_root_weak_heapOrdered. trivial.
Qed.

Lemma remove_min_hO: forall L,
  heapOrdered L ->
  match remove_min L with
   | (L', _) => heapOrdered L'
  end.
Proof.
  intros. unfold remove_min.
  destruct L. apply heapOrdered_empty.
  generalize (foot_split_spec _ L).
  destruct (foot_split L). destruct o; intros; subst.
  rewrite app_comm_cons in H.
  apply heapOrdered_cutfoot in H.
  apply sink_hO.
  apply weak_heapOrdered_root with a. trivial.
  apply heapOrdered_empty.
Qed.


Lemma sink_downwards_crawl: forall L k,
  weak_heapOrdered_bounded L (1 + k) (1 + k) ->
  weak_heapOrdered_bounded (sink (L,1 + k)) k k.
Proof.
  intros.
  apply sink_hO_bounded in H.
  rewrite hObU_whObU_pred in H.
  apply H.
Qed.

(* Bottom-up heapify *)
Fixpoint build_heap_helper (L : list A) (n : nat) :=
  let L' := sink (L, n) in
  match n with 
  | 0 => L'
  | S n' => build_heap_helper L' n'
  end.

Lemma build_heap_helper_downwards: forall L n,
  weak_heapOrdered_bounded L n n ->
  heapOrdered (build_heap_helper L n).
Proof.
  intros L n. revert L. induction n; intros.
  apply heapOrdered_bounded_root_heapOrdered. simpl.
  apply sink_hO_bounded. apply H.
  simpl. apply IHn, sink_downwards_crawl, H.
Qed.

Definition heapify (L : list A) :=
  build_heap_helper L (parent (length L)).

Lemma heapify_builds_heap: forall L,
  heapOrdered (heapify L).
Proof.
  unfold heapify. intros. apply build_heap_helper_downwards.
  apply hObU_whObU_pred, heapOrdered_bounded_half.
Qed.

(* sink preserves permutations *)

Lemma sink1_permutation: forall L j,
  match sink1 L j with
   | (L', _) => Permutation L L'
  end.
Proof.
  unfold sink1. intros.
  case (nth_error L j); auto.
  case (nth_error L (left_child j)); auto.
  case (nth_error L (right_child j)); intros.
  case (a <<=? a0). case (a1 <<=? a); auto.
  intros. symmetry. apply exchange_Permutation.
  case (a1 <<=? a0); auto.
  intros. symmetry. apply exchange_Permutation.
  case (a0 <<=? a); auto.
  intros. symmetry. apply exchange_Permutation.
Qed.

Lemma sink_permutation: forall L j,
  Permutation L (sink (L,j)).
Proof.
  intros. remember (L, j) as Lj. replace L with (match Lj with (L, _) => L end) by (subst; trivial). clear.
  apply sink_ind; intros.
  generalize (sink1_permutation L j); intro. rewrite e0 in H. trivial.
  generalize (sink1_permutation L j); intro. rewrite e0 in H0. transitivity L'; trivial.
Qed.

Lemma build_heap_permutation: forall L n,
  Permutation L (build_heap_helper L n).
Proof.
  intros L n. revert L. induction n; intros. simpl. apply sink_permutation.
  simpl. eapply Permutation_trans. 2: apply IHn. apply sink_permutation.
Qed.

Lemma heapify_permutation: forall L,
  Permutation L (heapify L).
Proof. intros. apply build_heap_permutation. Qed.

(* remove_min yields permutation *)

Lemma remove_min_permutation: forall L,
  match remove_min L with
   | (L', None) => L = L' /\ L' = nil
   | (L', Some m) => Permutation L (m :: L')
  end.
Proof.
  intros. unfold remove_min.
  destruct L. auto.
  constructor. clear a.
  generalize (foot_split_spec _ L).
  case_eq (foot_split L). intros. destruct o; intros; subst.
  transitivity (a :: l).
  rewrite Permutation_app_comm. trivial.
  apply sink_permutation.
  destruct H0. subst. constructor.
Qed.

(* remove_min removes a minimum *)

Lemma remove_min_root: forall L,
  match remove_min L with
   | (L', None) => L = L' /\ L' = nil
   | (L', Some a) => nth_error L root_idx = Some a
  end.
Proof. unfold remove_min. destruct L; auto. Qed.

Lemma remove_min_min: forall L,
  heapOrdered L ->
  match remove_min L with
   | (L', None) => L = L' /\ L' = nil
   | (L', Some a) => Forall (fun x => a <<= x) L'
  end.
Proof.
  intro. generalize (remove_min_permutation L). generalize (remove_min_root L).
  case remove_min. destruct o; auto.
  intros. generalize (root_minimal _ H1 a H); intro. clear H H1.
  eapply forall_permutation in H2. 2: apply H0.
  apply Forall_inv_tail with a. trivial.
Qed.

(* all-in-one specs *)

Lemma insert_spec: forall L x,
  heapOrdered L ->
  Permutation (x :: L) (insert L x) /\ heapOrdered (insert L x).
Proof.
  split. apply insert_permutation. apply insert_hO; trivial.
Qed.

Lemma remove_min_spec: forall L,
  heapOrdered L ->
  match remove_min L with
   | (L', None) => L = L' /\ L' = nil
   | (L', Some a) => Permutation L (a :: L') /\ Forall (fun x => a <<= x) L' /\ heapOrdered L'
  end.
Proof.
  intros. generalize (remove_min_hO L H), (remove_min_permutation L), (remove_min_min L H).
  case (remove_min L). destruct o; tauto.
Qed.

(* heapsort *)

Lemma remove_min_dec: forall L,
  match remove_min L with
  | (L', None) => L = L' /\ L' = nil
  | (L', Some a) => 1 + length L' = length L
  end.
Proof.
  intros. generalize (remove_min_permutation L). case (remove_min L). destruct o; auto.
  intro. apply Permutation_length in H. simpl in H. lia.
Qed.

Function heapsort_core (L : list A) {measure length L} : list A :=
  match remove_min L with
   | (L', None) => L'
   | (L', Some a) => a :: (heapsort_core L')
  end.
Proof.
  intros. clear o teq0. generalize (remove_min_dec L). revert teq.
  case remove_min. intros. inversion teq. subst l o. lia.
Defined.

Lemma heapsort_core_nil: heapsort_core nil = nil.
Proof.
  rewrite heapsort_core_equation. reflexivity.
Qed.

Lemma heapsort_core_sorts: forall L,
  heapOrdered L ->
  Sorted Aleq (heapsort_core L).
Proof.
  intro L. apply heapsort_core_ind; clear L; intros.
  generalize (remove_min_spec _ H). rewrite e. intros [? ?]. subst. apply Sorted_nil.
  generalize (remove_min_spec _ H0). rewrite e. intros [? [? ?]].
  constructor. apply H. trivial.
  destruct L'. rewrite heapsort_core_nil. apply HdRel_nil.
  rewrite heapsort_core_equation. generalize (remove_min_permutation (a0 :: L')).
  case remove_min. destruct o. 2: intros [? ?]; subst; discriminate.
  intros. apply HdRel_cons.
  rewrite Forall_forall in H2. apply H2.
  symmetry in H4.
  apply (Permutation_in _ H4). left. trivial.
Qed.

Lemma heapsort_core_permutation: forall L,
  Permutation L (heapsort_core L).
Proof.
  intro L. apply heapsort_core_ind; clear L; intros.
  generalize (remove_min_permutation L). rewrite e. intros [? ?]. subst. constructor.
  generalize (remove_min_permutation L). rewrite e.
  intros. eapply Permutation_trans. apply H0.
  constructor. trivial.
Qed.

Definition heapsort (L : list A) : list A :=
  heapsort_core (heapify L).

Lemma heapsort_sorts: forall L,
  Permutation L (heapsort L) /\ Sorted Aleq (heapsort L).
Proof.
  split.
  * intros. unfold heapsort. eapply Permutation_trans.
    apply heapify_permutation.
    apply heapsort_core_permutation.
  * apply heapsort_core_sorts. apply heapify_builds_heap.
Qed.

End Heap.

(* Just to test it out... *)
(* Compute (heapsort nat le Coq.Arith.Compare_dec.le_dec (3::1::4::1::5::9::2::6::5::3::nil)). *)

(*
(* multiset, currently under experimentation... *)

(* Need a few more things... *)
Require Coq.Logic.FunctionalExtensionality.
Variable As : Antisymmetric A eq Aleq. (* a <<= b -> b <<= a -> a = b *)
Instance A_As : Antisymmetric A eq Aleq := As.

Definition Aeq_dec : forall x y : A, {x = y} + {~ x = y}.
Proof.
  intros.
  case (x <<=? y). case (y <<=? x). left.
  apply As; trivial.
  right; intro. subst y. auto.
  right; intro. subst y. apply n. reflexivity.
Qed.

Definition empty : multiset A := EmptyBag _.
Definition singleton (a : A) : multiset A := SingletonBag eq Aeq_dec a.

Definition heap2multiset : list A -> multiset A := fun L =>
  fold_right (fun a ms => munion ms (singleton a)) empty L.

Notation h2ms := heap2multiset.

Lemma multiset_meq_eq: forall A (M1 : multiset A) M2,
  meq M1 M2 <->
  M1 = M2.
Proof.
  split; intros. destruct M1. destruct M2. f_equal.
  apply FunctionalExtensionality.functional_extensionality.
  intro x. apply H. subst. apply meq_refl.
Qed.

Lemma multiset_permutation:
  forall L L',
  Permutation L L' ->
  h2ms L = h2ms L'.
Proof.
  induction 1; auto. simpl. congruence.
  simpl. apply multiset_meq_eq.
  eapply meq_trans. apply munion_ass.
  apply meq_sym.
  eapply meq_trans. apply munion_ass.
  apply meq_right.
  apply munion_comm.
  congruence.
Qed.

Lemma insert_ms: forall L x,
  munion (h2ms L) (singleton x) = h2ms (insert L x).
Proof.
  intros.
  generalize (insert_permutation L x); intro.
  apply multiset_permutation in H.
  rewrite <- H. trivial.
Qed.

Lemma remove_ms: forall L,
  match remove_min L with
   | (L', None) => L = L' /\ h2ms L' = empty
   | (L', Some m) => munion (h2ms L') (singleton m) = h2ms L
  end.
Proof.
  intros.
  generalize (remove_min_permutation L). destruct remove_min, o; intros.
  apply multiset_permutation in H. rewrite H. trivial.
  destruct H. subst. tauto.
Qed.
*)