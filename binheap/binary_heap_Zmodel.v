Require Import VST.floyd.proofauto.
Require Import CertiGraph.binheap.binary_heap_model.

(* Versions in Z... *)

Definition Zexchange {A : Type} (L : list A) (i j : Z) : list A :=
  exchange L (Z.to_nat i) (Z.to_nat j).

Lemma Zlength_Zexchange {A : Type} : forall (L : list A) i j,
  Zlength (Zexchange L i j) = Zlength L.
Proof.
  intros. unfold Zexchange. do 2 rewrite Zlength_correct. rewrite exchange_length. trivial.
Qed.

Lemma Zlength_one: forall A (a : A),
  Zlength [a] = 1.
Proof. reflexivity. Qed.

Lemma Znth_nth_error {A} `{Ia : Inhabitant A} : forall (L : list A) (i : Z),
  0 <= i < Zlength L ->
  nth_error L (Z.to_nat i) = Some (Znth i L).
Proof.
  intros. rewrite <- nth_Znth; trivial.
  apply nth_error_nth.
  rewrite <- ZtoNat_Zlength. lia.
Qed.

Lemma nth_error_Znth {A} `{Ia : Inhabitant A}: forall (L1 L2 : list A) i j,
  0 <= i < Zlength L1 ->
  0 <= j < Zlength L2 ->
  nth_error L1 (Z.to_nat i) = nth_error L2 (Z.to_nat j) <->
  Znth i L1 = Znth j L2.
Proof.
  intros.
  assert (Z.to_nat i < length L1 /\ Z.to_nat j < length L2)%nat. {
    generalize (Zlength_length _ L1 (Zlength L1)); intro.
    generalize (Zlength_length _ L2 (Zlength L2)); intro.
    destruct H1. apply Zlength_nonneg.
    destruct H2. apply Zlength_nonneg.
    rewrite (H1 eq_refl). rewrite (H2 eq_refl). lia. }
  repeat rewrite <- nth_Znth; trivial.
  generalize (nth_error_nth A Ia); intros.
  split; intros. do 2 (rewrite H2 in H3; try lia). inversion H3. congruence.
  rewrite H2. rewrite H2. congruence. lia. lia.
Qed.

Lemma Znth_Zexchange : forall {A} `{Ia : Inhabitant A} (L : list A) i j,
  0 <= i < Zlength L ->
  0 <= j < Zlength L ->
  Znth i (Zexchange L i j) = Znth j L.
Proof.
  intros.
  apply nth_error_Znth; auto. rewrite Zlength_Zexchange. trivial.
  generalize (Zlength_length _ L (Zlength L)). intro.
  apply nth_error_exchange; lia.
Qed.

Lemma Znth_Zexchange' : forall {A} `{Ia : Inhabitant A} (L : list A) i j,
  0 <= i < Zlength L ->
  0 <= j < Zlength L ->
  Znth j (Zexchange L i j) = Znth i L.
Proof.
  intros.
  apply nth_error_Znth; auto. rewrite Zlength_Zexchange. trivial.
  generalize (Zlength_length _ L (Zlength L)). intro.
  apply nth_error_exchange'; lia.
Qed.

Lemma Znth_Zexchange'' : forall {A} `{Ia : Inhabitant A} (L : list A) k i j,
  0 <= i < Zlength L ->
  0 <= j < Zlength L ->
  k <> i -> k <> j ->
  Znth k (Zexchange L i j) = Znth k L.
Proof.
  intros.
  assert (k < 0 \/ 0 <= k < Zlength L \/ Zlength L <= k) by lia.
  destruct H3 as [? | [? | ?]].
  repeat rewrite Znth_underflow; trivial.
  2: repeat rewrite Znth_overflow; try rewrite Zlength_Zexchange; trivial; lia.
  apply nth_error_Znth; auto. rewrite Zlength_Zexchange. trivial.
  apply nth_error_exchange''.
  intro. apply H1. apply Z2Nat.inj; lia.
  intro. apply H2. apply Z2Nat.inj; lia.
Qed.

Lemma Zexchange_eq: forall A (L : list A) i,
  Zexchange L i i = L.
Proof. unfold Zexchange. intros. apply exchange_eq. Qed.

Lemma upd_Znth_overwrite:
  forall {A} (l : list A) i a b,
    0 <= i < Zlength l ->
    upd_Znth i (upd_Znth i l a) b = upd_Znth i l b.
Proof.
  intros.
  rewrite upd_Znth_unfold by now rewrite upd_Znth_Zlength.
  rewrite upd_Znth_Zlength; trivial.
  repeat rewrite upd_Znth_unfold by trivial.
  rewrite sublist0_app1.
  2: rewrite Zlength_sublist; lia.
  rewrite sublist_sublist00 by lia.
  f_equal. f_equal.
  rewrite app_assoc.
  rewrite sublist_app2.
  2: { rewrite Zlength_app, Zlength_sublist by lia.
       unfold Zlength. simpl. lia.
  }
  rewrite Zlength_app, Zlength_sublist by lia.
  unfold Zlength at 1; simpl.
  rewrite sublist_same; trivial.
  - lia.
  - unfold Zlength at 2; simpl.
    rewrite Zlength_sublist by lia. lia.
Qed.

Lemma upd_Znth_same_Znth:
  forall {A} `{Ia : Inhabitant A} (l: list A) i,
    0 <= i < Zlength l ->
    upd_Znth i l (Znth i l) = l.
Proof.
  intros. rewrite upd_Znth_unfold by trivial.
  rewrite <- sublist_len_1 by trivial.
  repeat rewrite <- sublist_split.
  apply sublist_same; trivial.
  all: lia.
Qed.

Lemma Zexchange_head_foot: forall A (head : A) body foot,
  Zexchange ((head :: body) ++ [foot]) 0 (Zlength (head :: body)) = ((foot :: body) ++ [head]).
Proof.
  intros.
  unfold Zexchange. simpl.  rewrite Zlength_correct. rewrite Nat2Z.id.
  do 2 rewrite app_comm_cons. apply exchange_head_foot.
Qed.

Lemma Permutation_Zlength: forall A (L1 : list A) L2,
  Permutation L1 L2 ->
  Zlength L1 = Zlength L2.
Proof.
  intros. apply Permutation_length in H. do 2 rewrite Zlength_correct. congruence.
Qed.

Lemma Zexchange_Permutation: forall A (L : list A) i j,
  Permutation L (Zexchange L i j).
Proof.
  intros. unfold Zexchange. symmetry. apply exchange_Permutation.
Qed.

Lemma Permutation_Znth {A : Type} `{iA: Inhabitant A}: forall (l l' : list A) (d : A),
       Permutation l l' <->
       (let n := Zlength l in
        Zlength l' = n /\
        (exists f : nat -> nat,
           FinFun.bFun (Z.to_nat n) f /\
           FinFun.bInjective (Z.to_nat n) f /\ 
           (forall z : Z, (0 <= z < n) -> Znth z l' = Znth (Z.of_nat (f (Z.to_nat z))) l))).
Proof.
  intros. rewrite Permutation_nth. instantiate (1 := iA). do 2 rewrite Zlength_correct. split; intros; subst n; destruct H as [? [? [? [? ?]]]]; rename x into f.
  * split. congruence. 
    exists f. rewrite Nat2Z.id. split; trivial. split; trivial. intros.
    repeat rewrite <- nth_Znth. 3: rewrite Zlength_correct; lia.
    rewrite H2. 2: rep_lia.
    rewrite Nat2Z.id. trivial.
    rewrite Zlength_correct. specialize (H0 (Z.to_nat z)).  rep_lia.
  * split. rep_lia.
    exists f. rewrite Nat2Z.id in *. split; trivial. split; trivial. intros.
    specialize (H2 (Z.of_nat x)).
    do 2 rewrite <- nth_Znth in H2. repeat rewrite Nat2Z.id in *.
    apply H2. lia.
    1,2,3: rewrite Zlength_correct. 2,3: lia.
    specialize (H0 x). rewrite Nat2Z.id. lia.
Qed.

Lemma Zexchange_symm {A}: forall (L : list A) i j,
  0 <= i < Zlength L -> 0 <= j < Zlength L ->
  Zexchange L i j = Zexchange L j i.
Proof.
  intros.
  rewrite Zlength_correct in H, H0.
  apply exchange_symm; lia.
Qed.

Definition Zleft_child i  := Z.of_nat (binary_heap_model.left_child  (Z.to_nat i)).
Lemma Zleft_child_unfold: forall i,
  0 <= i ->
  Zleft_child i = (2 * i) + 1.
Proof.
  unfold Zleft_child, binary_heap_model.left_child. intros.
  do 2 rewrite Nat2Z.inj_add. rewrite Z2Nat.id; lia.
Qed.

Lemma Zleft_child_repr: forall i,
  0 <= i ->
  Int.repr (Zleft_child i) = Int.add (Int.mul (Int.repr 2) (Int.repr i)) Int.one.
Proof.
  intros. rewrite Zleft_child_unfold; trivial.
  unfold Int.one.
  rewrite mul_repr, add_repr. trivial.
Qed.

Definition Zright_child i := Z.of_nat (binary_heap_model.right_child (Z.to_nat i)).
Lemma Zright_child_unfold: forall i,
  Zright_child i = Zleft_child i + 1.
Proof.
  unfold Zright_child, Zleft_child, binary_heap_model.right_child. intros.
  rewrite Nat2Z.inj_add. trivial.
Qed.

Lemma Zright_child_repr: forall i,
  0 <= i ->
  Int.repr (Zright_child i) = Int.mul (Int.repr 2) (Int.add (Int.repr i) Int.one).
Proof.
  intros. rewrite Zright_child_unfold.
  rewrite <- add_repr.
  rewrite Zleft_child_repr; trivial.
  rewrite Int.add_assoc.
  change (Int.add Int.one (Int.repr 1)) with (Int.repr 2).
  rewrite Int.mul_add_distr_r.
  reflexivity.
Qed.

Definition Zparent (i : Z) : Z := Z.of_nat (parent (Z.to_nat i)).
Lemma Zparent_unfold: forall i,
  0 < i ->
  Zparent i = (i - 1) / 2.
Proof.
  unfold Zparent, parent. intros.
  rewrite Nat.div2_div, div_Zdiv; auto.
  rewrite Nat2Z.inj_sub. rewrite Z2Nat.id; lia.
  lia.
Qed.
Lemma Zparent_0:
  Zparent 0 = 0.
Proof. reflexivity. Qed.

Lemma Zparent_repr: forall i,
  0 < i <= Int.max_unsigned ->
  Int.repr (Zparent i) = Int.divu (Int.repr (i - 1)) (Int.repr 2).
Proof.
  intros. unfold Int.divu. repeat rewrite Int.unsigned_repr.
  2,3: rep_lia. rewrite Zparent_unfold. trivial. lia.
Qed.

(*
Lemma heapOrdered_lower_priority_weak_heapOrdered2: forall H,
  heapOrdered H ->
  forall t old, 
  nth_error H t = Some old ->
  forall new, new <<= old ->
  weak_heapOrdered2 (update H t new) t.

Lemma heapOrdered_raise_priority_weak_heapOrdered: forall H,
  heapOrdered H ->
  forall t old,
  nth_error H t = Some old ->
  forall new, old <<= new ->
  weak_heapOrdered (update H t new) t.
*)

