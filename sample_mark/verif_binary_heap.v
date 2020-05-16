Require Import VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.binary_heap_model.
Require Import RamifyCoq.sample_mark.binary_heap.
Require Import RelationClasses.
(* Require Import VST.floyd.sublist. *)

Set Nested Proofs Allowed.

Definition Zexchange {A : Type} (L : list A) (i j : Z) : list A :=
  exchange L (Z.to_nat i) (Z.to_nat j).

Lemma Zlength_Zexchange {A : Type} : forall (L : list A) i j,
  Zlength (Zexchange L i j) = Zlength L.
Proof.
  intros. unfold Zexchange. do 2 rewrite Zlength_correct. rewrite exchange_length. trivial.
Qed.

Lemma Znth_nth_error {A} `{Ia : Inhabitant A} : forall (L : list A) (i : Z),
  0 <= i < Zlength L ->
  nth_error L (Z.to_nat i) = Some (Znth i L).
Proof.
  intros. rewrite <- nth_Znth; trivial.
  apply nth_error_nth.
  rewrite <- ZtoNat_Zlength. lia.
Qed.

Lemma Zlength_one: forall A (a : A),
  Zlength [a] = 1.
Proof. reflexivity. Qed.

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

Lemma exchange_eq_nil: forall A (L : list A) i j,
  exchange L i j = [] ->
  L = [].
Proof. unfold exchange. intros A L i j. case nth_error; auto. case nth_error; auto.
  destruct L. trivial. destruct j, i; simpl; discriminate.
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

Lemma Zexchange_head_foot: forall A (head : A) body foot,
  Zexchange ((head :: body) ++ [foot]) 0 (Zlength (head :: body)) = ((foot :: body) ++ [head]).
Proof.
  intros.
  apply nth_error_eq. intro i'. unfold Zexchange. simpl Z.to_nat. case (eq_nat_dec i' 0); intro.
  + subst i'. 
    rewrite nth_error_exchange; simpl. 2: lia.
    rewrite app_comm_cons. rewrite ZtoNat_Zlength.
    rewrite nth_error_app2. simpl. rewrite Nat.sub_diag. trivial. lia.
    rewrite ZtoNat_Zlength. rewrite app_length. simpl. lia.
  + case (eq_nat_dec i' (Z.to_nat (Zlength (head :: body)))); intro.
    - subst i'.
      rewrite nth_error_exchange'; simpl. 2: lia.
      rewrite app_comm_cons. rewrite ZtoNat_Zlength.
      rewrite nth_error_app2. simpl. rewrite Nat.sub_diag. trivial. simpl. lia.
      rewrite ZtoNat_Zlength. rewrite app_length. simpl. lia.
    - rewrite nth_error_exchange''; auto.
      destruct i'. contradiction. simpl. rewrite ZtoNat_Zlength in n0. simpl in n0.
      assert (i' < (length body) \/ i' >= length (body ++ [foot]))%nat. { rewrite app_length. simpl. lia. }
      destruct H. repeat rewrite nth_error_app1; auto.
      assert (i' >= length (body ++ [head]))%nat. { rewrite app_length in *. simpl in *. lia. }
      apply nth_error_None in H. apply nth_error_None in H0. congruence.
Qed.

Lemma Permutation_Zlength: forall A (L1 : list A) L2,
  Permutation L1 L2 ->
  Zlength L1 = Zlength L2.
Proof.
  intros. apply Permutation_length in H. do 2 rewrite Zlength_correct. congruence.
Qed.

(* Relation on heap items. *)
Definition heap_item : Type := (int * int)%type.
Definition cmp (a b : heap_item) : bool :=
  negb (Int.lt (fst b) (fst a)).
Definition cmp_rel (a b : heap_item) : Prop :=
  cmp a b = true.
Lemma cmp_dec: forall a a', {cmp_rel a a'} + {~cmp_rel a a'}.
Proof.
  intros [? ?] [? ?]. unfold cmp_rel, cmp. simpl. case (Int.lt i1 i); simpl; auto.
Qed. 
Instance cmp_po: PreOrder cmp_rel.
Proof.
  constructor. intros [? ?]. red. unfold cmp. simpl. case_eq (Int.lt i i); auto; intro. exfalso.
  apply lt_inv in H. lia.
  intros [? ?] [? ?] [? ?]. unfold cmp_rel, cmp. simpl. 
  case_eq (Int.lt i3 i); auto.
  case_eq (Int.lt i1 i); auto.
  case_eq (Int.lt i3 i1); auto. simpl.
  intros ? ? ?. exfalso.
  apply lt_inv in H1.
  apply lt_false_inv in H.
  apply lt_false_inv in H0.
  lia.
Qed.
Lemma cmp_linear: forall a b,
  cmp_rel a b \/ cmp_rel b a.
Proof.
  intros [? ?] [? ?]. unfold cmp_rel, cmp; simpl.
  case_eq (Int.lt i1 i); auto. intro. 
  right.
  case_eq (Int.lt i i1); auto. intro. exfalso. 
  apply lt_inv in H. apply lt_inv in H0.
  lia.
Qed.

(* Not sure if it's a great idea to expose the capacity inside the abstraction boundary. *)
Definition heap : Type := (nat * list heap_item)%type.
Instance heap_inhabitant : Inhabitant heap := (O, []).
Definition heap_capacity (h : heap) : Z := Z.of_nat (fst h).
Definition heap_items (h : heap) : list heap_item := snd h.
Definition heap_size (h : heap) : Z := Zlength (heap_items h).

(*
Definition heap_permutation (h1 h2 : heap) : Prop :=
  heap_capacity h1 = heap_capacity h2 /\ Permutation (heap_items h1) (heap_items h2).
*)

Definition heap_ordered := binary_heap_model.heapOrdered heap_item cmp_rel.
Definition weak_heap_ordered_bottom_up (L : list heap_item) (x : Z) := 
  binary_heap_model.weak_heapOrdered2 heap_item cmp_rel L (Z.to_nat x).
Definition weak_heap_ordered_top_down (L : list heap_item) (x : Z) := 
  binary_heap_model.weak_heapOrdered heap_item cmp_rel L (Z.to_nat x).
Definition swim1 := binary_heap_model.swim1 heap_item cmp_rel cmp_dec.
Definition swim := binary_heap_model.swim heap_item cmp_rel cmp_dec.
Definition insert := binary_heap_model.insert heap_item cmp_rel cmp_dec.
Definition sink1 := binary_heap_model.sink1 heap_item cmp_rel cmp_dec.
Definition sink := binary_heap_model.sink heap_item cmp_rel cmp_dec.
Definition remove_min := binary_heap_model.remove_min heap_item cmp_rel cmp_dec.

(* This may get bundled elsewhere at some point. *)
Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Global Existing Instance CompSpecs.

Definition t_item := Tstruct _structItem noattr.
Definition t_pq := Tstruct _structPQ noattr.

Definition heap_item_rep (i : heap_item) : reptype t_item :=
  (Vint (fst i), Vint (snd i)).

Definition hitem (i : heap_item) : val -> mpred :=
  data_at Tsh t_item (heap_item_rep i).

Definition harray (contents : list heap_item) : val -> mpred :=
  data_at Tsh (tarray t_item (Zlength contents)) (map heap_item_rep contents).

Lemma harray_emp: forall arr,
  harray [] arr |-- emp.
Proof.
  unfold harray. intros. rewrite data_at_isptr. entailer. rewrite data_at_zero_array_eq; auto.
Qed.

Lemma fold_harray': forall L i arr,
  i = Zlength L ->
  data_at Tsh (tarray t_item i) (map heap_item_rep L) arr = harray L arr.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma fold_harray: forall L arr,
  data_at Tsh (tarray t_item (Zlength L)) (map heap_item_rep L) arr = harray L arr.
Proof. reflexivity. Qed.

Lemma harray_split: forall L1 L2 ptr,
  harray (L1 ++ L2) ptr = 
  ((harray L1 ptr) * 
   (harray L2 (field_address0 (tarray t_item (Zlength (L1 ++ L2))) [ArraySubsc (Zlength L1)] ptr)))%logic.
Proof.
  intros. unfold harray.
  rewrite map_app.
  erewrite split2_data_at_Tarray_app.
  2: rewrite Zlength_map; reflexivity. 2: rewrite Zlength_app, Zlength_map; lia.
  rewrite Zlength_app.
  replace (Zlength L1 + Zlength L2 - Zlength L1) with (Zlength L2) by lia.
  trivial.
Qed.

Definition valid_pq (pq : val) (h: heap): mpred :=
  EX arr : val, EX junk: list heap_item,
    (!! heap_ordered (heap_items h)) && (!! (Zlength ((heap_items h) ++ junk) = heap_capacity h)) &&
    (data_at Tsh t_pq (Vint (Int.repr (heap_capacity h)), (Vint (Int.repr (heap_size h)), arr)) pq *
       harray ((heap_items h) ++ junk) arr).

Definition exch_spec :=
  DECLARE _exch WITH i : Z, j : Z, arr: val, arr_contents: list heap_item
  PRE [tuint, tuint, tptr t_item]
    PROP (0 <= i < Zlength arr_contents; 0 <= j < Zlength arr_contents)
    PARAMS (Vint (Int.repr i); Vint (Int.repr j); arr)
    GLOBALS ()
    SEP (harray arr_contents arr)
  POST [tvoid]
    PROP ()
    LOCAL ()
    SEP (harray (Zexchange arr_contents i j) arr).
(* used to be:
 (* no EX *)
    PROP () 
    LOCAL ()
    SEP (harray (Zexchange arr_contents i j) arr).
 *)
(* In my understanding, this tweak 
   should be processed as meaningless 
*)

Definition sink_spec :=
  DECLARE _sink WITH i : Z, arr: val, arr_contents: list heap_item, first_available : Z
  PRE [tuint, tptr t_item, tuint]
    PROP (0 <= i <= Zlength arr_contents; 
          first_available = Zlength arr_contents; 
          weak_heap_ordered_top_down arr_contents i)
    PARAMS (Vint (Int.repr i); arr; Vint (Int.repr first_available))
    GLOBALS ()
    SEP (harray arr_contents arr)
  POST [tvoid]
    EX arr_contents' : list heap_item,
      PROP (heap_ordered arr_contents' /\ Permutation arr_contents arr_contents')
      LOCAL ()
      SEP (harray arr_contents' arr).

Definition less_spec :=
  DECLARE _less WITH i : Z, j : Z, arr: val, arr_contents: list heap_item
  PRE [tuint, tuint, tptr t_item]
    PROP (0 <= i < Zlength arr_contents; 0 <= j < Zlength arr_contents)
    PARAMS (Vint (Int.repr i); Vint (Int.repr j); arr)
    GLOBALS ()
    SEP (harray arr_contents arr)
  POST [tint]
    PROP ()
    LOCAL (temp ret_temp (Val.of_bool (cmp (Znth i arr_contents) (Znth j arr_contents))))
    SEP (harray arr_contents arr).

Definition swim_spec :=
  DECLARE _swim WITH i : Z, arr: val, arr_contents: list heap_item
  PRE [tuint, tptr t_item]
    PROP (0 <= i < Zlength arr_contents; weak_heap_ordered_bottom_up arr_contents i)
    PARAMS (Vint (Int.repr i); arr)
    GLOBALS ()
    SEP (harray arr_contents arr)
  POST [tvoid]
    EX arr_contents' : list (int * int),
      PROP (heap_ordered arr_contents' /\ Permutation arr_contents arr_contents')
      LOCAL ()
      SEP (harray arr_contents' arr).


Definition size_spec := 
  DECLARE _size WITH pq : val, h : heap
  PRE [tptr t_pq]
    PROP ()
    PARAMS (pq)
    GLOBALS ()
    SEP (valid_pq pq h)
  POST [tuint]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (heap_size h))))
    SEP (valid_pq pq h).

Definition capacity_spec := 
  DECLARE _capacity WITH pq : val, h : heap
  PRE [tptr t_pq]
    PROP ()
    PARAMS (pq)
    GLOBALS ()
    SEP (valid_pq pq h)
  POST [tuint]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (heap_capacity h))))
    SEP (valid_pq pq h).

Definition remove_min_nc_spec :=
  DECLARE _remove_min_nc WITH pq : val, h : heap, i : val, iv : heap_item
  PRE [tptr t_pq, tptr t_item]
    PROP (heap_size h > 0)
    PARAMS (pq; i)
    GLOBALS ()
    SEP (valid_pq pq h; hitem iv i)
  POST [tvoid]
  EX h', EX iv' : heap_item,
    PROP (heap_capacity h = heap_capacity h';
          Permutation (heap_items h) (iv' :: heap_items h');
          Forall (cmp_rel iv') (heap_items h'))
    LOCAL ()
    SEP (valid_pq pq h'; hitem iv' i).

Definition insert_nc_spec :=
  DECLARE _insert_nc WITH pq : val, h : heap, i : val, iv : heap_item
  PRE [tptr t_pq, tptr t_item]
    PROP (heap_size h < heap_capacity h)
    PARAMS (pq; i)
    GLOBALS ()
    SEP (valid_pq pq h; hitem iv i)
  POST [tvoid]
  EX h',
    PROP (heap_capacity h = heap_capacity h';
          Permutation (iv :: heap_items h) (heap_items h'))
    LOCAL ()
    SEP (valid_pq pq h'; hitem iv i).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ exch_spec ; less_spec ; swim_spec ; sink_spec ; 
                                   remove_min_nc_spec ; insert_nc_spec ; 
                                   size_spec ; capacity_spec ]).

Lemma body_sink: semax_body Vprog Gprog f_sink sink_spec.
Proof.
  start_function.
Admitted.

Lemma body_remove_min_nc: semax_body Vprog Gprog f_remove_min_nc remove_min_nc_spec.
Proof.
  start_function.
  unfold valid_pq.
  Intros arr junk.
  rewrite harray_split.
  Intros.
  destruct h. destruct l. inversion H.
  unfold heap_items, heap_capacity, heap_size in *. simpl in H, H0, H1 |-*. clear H.
  generalize (foot_split_spec _ (h :: l)).
  case foot_split. destruct o; intro. 2: destruct H; subst l0; discriminate.
  rename h into root. rename h0 into foot.
  assert (Hx: Zlength l = Zlength (root :: l) - 1) by (rewrite Zlength_cons; lia).
  assert (Hy : 0 <= Zlength l) by apply Zlength_nonneg.
  forward.
  forward.
  forward.
  forward.
  unfold harray. entailer!.
  forward_call (0, Zlength l, arr, root :: l).
  entailer!. simpl. congruence. lia.
  forward.
  forward.
  unfold harray at 1. (* Not delighted with this unfold... *)
  forward.
    { entailer!. rewrite Zlength_Zexchange. lia. }
    { entailer!. rewrite Znth_map. rewrite <- Hx. rewrite Znth_Zexchange'; try lia. rewrite Znth_0_cons.
      unfold heap_item_rep. trivial. rewrite Zlength_Zexchange. lia. }
  unfold hitem.
  forward.
  forward.
  forward.
  forward.
    { entailer!. rewrite Zlength_Zexchange. lia. }
    { entailer!. rewrite Znth_map. rewrite <- Hx. rewrite Znth_Zexchange'; try lia. rewrite Znth_0_cons.
      unfold heap_item_rep. admit. (* C-typing issue *) rewrite Zlength_Zexchange. lia. }
  (* this change refolds the harray back up *)
  change (data_at _ _ _ arr) with (harray (Zexchange (root :: l) 0 (Zlength l)) arr).
  forward.
  forward.
  forward.
  (* Just before the final call, let's do some cleanup *)
  rewrite <- Hx.
  rewrite Znth_map. 2: rewrite Zlength_Zexchange; lia.
  rewrite Znth_Zexchange'; try lia. rewrite Znth_0_cons.
  autorewrite with norm. rewrite <- Hx.
  unfold heap_item_rep. rewrite H.
  destruct l.
  * (* corner case: heap is now empty *)
    destruct l0. 2: destruct l0; discriminate.
    inversion H. subst foot. clear H Hx.
    simpl.
    forward_call (0, arr, @nil heap_item, 0); rewrite Zlength_nil. 
      { unfold harray. rewrite data_at_isptr. entailer. (* Surely there's a less heavy hammer way to do this? *)
        rewrite data_at_zero_array_eq; auto. entailer!. }
      { split; auto. split; auto. apply hOwhO. apply cmp_po. apply heapOrdered_empty. }
    (* Prove postcondition *)
    Intro vret. Exists (n, vret) root. entailer. (* Surely there's a less heavy hammer way to do this? *)
    destruct H. apply Permutation_nil in H12. subst vret. clear H Hy.
    sep_apply harray_emp. rewrite emp_sepcon.
    rewrite Zlength_Zexchange. rewrite Zexchange_eq.
    do 2 rewrite fold_harray. unfold valid_pq, hitem.
    apply andp_right. apply prop_right. auto.
    Exists arr (root :: junk). simpl. entailer!.
    apply heapOrdered_empty.
    rewrite <- harray_split. apply derives_refl.
  * (* main line: heap still has items in it *)
    destruct l0; inversion H. subst h0.
    deadvars!.
    assert (Zlength (h :: l) = Zlength (root :: l0)). { rewrite H4, Zlength_app, Zlength_one, Zlength_cons. lia. }
    rewrite H2, Zexchange_head_foot. rewrite harray_split.
    forward_call (0, arr, (foot :: l0), Zlength (foot :: l0)). entailer!.
      { split. rewrite Zlength_cons. generalize (Zlength_nonneg l0). lia.
        split; trivial.
        apply weak_heapOrdered_root with root.
        rewrite H4, app_comm_cons in H0.
        apply heapOrdered_cutfoot in H0. trivial. }
    (* Prove postcondition *)
    Intro vret. Exists (n, vret) root. simpl fst. unfold hitem, heap_item_rep, heap_size, heap_capacity. simpl fst. simpl snd. entailer!.
      { (* Pure part *)
        split. constructor. rewrite H4. transitivity ([foot] ++ l0). apply Permutation_app_comm. destruct H3. auto.
        generalize (root_minimal _ _ _ _ H0 root eq_refl); intro.
        rewrite H4 in H9. apply Forall_inv_tail in H9.
        eapply forall_permutation. apply H9. transitivity ([foot] ++ l0). apply Permutation_app_comm. simpl. tauto. }
    unfold valid_pq. Exists arr (root :: junk). unfold heap_size, heap_capacity. simpl.
    destruct H3.
    replace (Zlength vret) with (Zlength (root :: l0)). 2: { apply Permutation_Zlength in H9. trivial. }
    entailer!. { (* Pure part inside spatial part *)
      rewrite <- H1. apply Permutation_Zlength in H9. autorewrite with sublist. rewrite <- H9.
      autorewrite with sublist in *. lia. }
    (* Spatial part, this seems a bit uglier than necessary? *)
    change (root :: junk) with ([root] ++ junk). rewrite app_assoc. do 2 rewrite harray_split.
    apply Permutation_Zlength in H9.
    rewrite app_comm_cons. rewrite Zlength_app. rewrite H9. rewrite Zlength_app.
    assert (Zlength (root :: l0) = Zlength vret). { rewrite <- H9. do 2 rewrite Zlength_cons. trivial. }
    do 3 rewrite app_comm_cons.
    do 4 rewrite Zlength_app. rewrite H10.
    do 2 rewrite Zlength_one.
    rewrite Zlength_cons.
    rewrite H2, H10. cancel.
(* Done except for C-typing issue *)
Admitted.

Lemma body_less: semax_body Vprog Gprog f_less less_spec.
Proof.
  start_function.
  unfold harray.
  forward.
  rewrite Znth_map; trivial.
  entailer!.
  forward.
  do 2 (rewrite Znth_map; trivial).
  entailer!.
  forward.
  repeat rewrite Znth_map in *; trivial.
  entailer!.
Qed.

Lemma body_size: semax_body Vprog Gprog f_size size_spec.
Proof.
  start_function.
  unfold valid_pq.
  Intros arr junk.
  forward.
  forward.
  unfold valid_pq.
  Exists arr. Exists junk.
  entailer!.
Qed.

Lemma body_capacity: semax_body Vprog Gprog f_capacity capacity_spec.
Proof.
  start_function.
  unfold valid_pq.
  Intros arr junk.
  forward.
  forward.
  unfold valid_pq.
  Exists arr. Exists junk.
  entailer!.
Qed.

(*
typedef struct structItem {
  int priority;
  void* data; /* Should this be a union of void* and int? */
} Item;

void exch(unsigned int j, unsigned int k, Item arr[]) {
  int priority = arr[j].priority;
  void* data = arr[j].data;
  arr[j].priority = arr[k].priority;
  arr[j].data = arr[k].data;
  arr[k].priority = priority;
  arr[k].data = data;
}
*)

Lemma body_exch: semax_body Vprog Gprog f_exch exch_spec.
Proof.
  start_function.
Admitted. 
(*
  unfold harray.
  forward.
  - rewrite Znth_map; trivial.
    entailer!.
  -
match goal with |- context [temp _priority ?a] => set (foo := a) end.
 forward.
    + rewrite Znth_map; trivial.
      entailer!. 
      (* Why is this goal here?
         Absolutely no idea *)
      admit.
    + (* Opaque Znth. *)
(* match goal with |- context [temp _data ?a] => set (food := a) end. *)
      forward.
      1: repeat rewrite Znth_map; trivial; entailer!.
      repeat rewrite Znth_map; trivial.
(* match goal with |- context [temp _t'2 ?a] => set (foo2 := a) end.
set (n := Zlength arr_contents). *)
      forward. forward.
      * entailer!.
        clear H3. (* it's useless info *)
        destruct (Z.eq_dec i j).
        -- subst j. rewrite upd_Znth_same.
           2: rewrite Zlength_map; auto.
           rewrite Znth_map; trivial.
        -- rewrite upd_Znth_diff.  
           2,3: rewrite Zlength_map; auto.
           2: lia.
           rewrite Znth_map; trivial.
           simpl. (* and we're back at the old goal *)
           admit.
      * forward. forward. forward.
        repeat rewrite upd_Znth_overwrite by
            (repeat rewrite upd_Znth_Zlength; rewrite Zlength_map; trivial).
        repeat rewrite upd_Znth_same by
            (try rewrite upd_Znth_Zlength; rewrite Zlength_map; easy).

        Exists (Zexchange arr_contents i j).
        (* had to be added to accommodate the tweak *)

        entailer!.
        destruct (Z.eq_dec i j).
        -- subst i.
           repeat rewrite upd_Znth_same by
               (try rewrite upd_Znth_Zlength; rewrite Zlength_map; easy).
           rewrite upd_Znth_overwrite by
               (repeat rewrite upd_Znth_Zlength; rewrite Zlength_map; trivial).
           unfold harray.
           rewrite Zlength_Zexchange.
           replace (Vint (fst (Znth j arr_contents)), Vint (snd (Znth j arr_contents))) with (heap_item_rep (Znth j arr_contents)).
           2: { unfold heap_item_rep; trivial. }
           rewrite upd_Znth_map.
           unfold Zexchange; rewrite exchange_eq.
           rewrite upd_Znth_same_Znth by trivial.
           entailer!.
        -- rewrite upd_Znth_diff; trivial.
           2,3: rewrite Zlength_map; trivial.
           2: lia.
           rewrite Znth_map; trivial.
           admit.
Admitted.
*)