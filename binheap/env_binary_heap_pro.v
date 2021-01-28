Require Import RelationClasses.
Require Import VST.floyd.proofauto.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.binheap.binary_heap_pro.
Require Import CertiGraph.binheap.binary_heap_model.
Require Import CertiGraph.binheap.binary_heap_Zmodel.

(* Relation on heap items. *)
Definition key_type : Type := Z. Definition priority_type : Type := int. Definition payload_type : Type := int.
Definition heap_item : Type := (key_type * priority_type * payload_type)%type.
Definition heap_item_key (hi : heap_item) : key_type := fst (fst hi).
Definition heap_item_priority (hi : heap_item) : priority_type := snd (fst hi).
Definition heap_item_payload (hi : heap_item) : payload_type := snd hi.

Definition cmp (a b : heap_item) : bool :=
  negb (Int.lt (heap_item_priority b) (heap_item_priority a)).
Definition cmp_rel (a b : heap_item) : Prop :=
  cmp a b = true.
Lemma cmp_dec: forall a a', {cmp_rel a a'} + {~cmp_rel a a'}.
Proof.
  intros [[? ?] ?] [[? ?] ?]. unfold cmp_rel, cmp, heap_item_priority. simpl. case (Int.lt p1 p); simpl; auto.
Qed. 
Instance cmp_po: PreOrder cmp_rel.
Proof.
  constructor. intros [[? ?] ?]. red. unfold cmp, heap_item_priority. simpl. case_eq (Int.lt p p); auto; intro. exfalso.
  apply lt_inv in H. lia.
  intros [[? ?] ?] [[? ?] ?] [[? ?] ?]. unfold cmp_rel, cmp, heap_item_priority. simpl. 
  case_eq (Int.lt p1 p); simpl; try discriminate.
  case_eq (Int.lt p3 p1); simpl; try discriminate.
  case_eq (Int.lt p3 p); auto.
  intros ? ? ?. exfalso.
  apply lt_inv in H.
  apply lt_false_inv in H0.
  apply lt_false_inv in H1.
  lia.
Qed.
Lemma cmp_linear: forall a b,
  cmp_rel a b \/ cmp_rel b a.
Proof.
  intros [[? ?] ?] [[? ?] ?]. unfold cmp_rel, cmp, heap_item_priority; simpl.
  case_eq (Int.lt p1 p); auto. intro. 
  right.
  case_eq (Int.lt p p1); auto. intro. exfalso. 
  apply lt_inv in H. apply lt_inv in H0.
  lia.
Qed.

(* Not sure if it's a great idea to expose the capacity inside the abstraction boundary. *)
Definition heap : Type := (nat * list heap_item)%type.
Instance heap_inhabitant : Inhabitant heap := (O, []).
Definition heap_capacity (h : heap) : Z := Z.of_nat (fst h).
Definition heap_items (h : heap) : list heap_item := snd h.
Definition heap_size (h : heap) : Z := Zlength (heap_items h).

Definition heap_ordered := binary_heap_model.heapOrdered heap_item cmp_rel.
Definition weak_heap_ordered_bottom_up (L : list heap_item) (x : Z) := 
  binary_heap_model.weak_heapOrdered2 heap_item cmp_rel L (Z.to_nat x).
Definition weak_heap_ordered_top_down (L : list heap_item) (x : Z) := 
  binary_heap_model.weak_heapOrdered heap_item cmp_rel L (Z.to_nat x).
Definition swim := binary_heap_model.swim heap_item cmp_rel cmp_dec.
Definition sink L i := binary_heap_model.sink heap_item cmp_rel cmp_dec (L,i).
(* Definition insert := binary_heap_model.insert heap_item cmp_rel cmp_dec. *)
(* Definition remove_min := binary_heap_model.remove_min heap_item cmp_rel cmp_dec. *)

(* This may get bundled elsewhere at some point. *)
Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Global Existing Instance CompSpecs.

Definition t_item := Tstruct _structItem noattr.
Definition t_pq := Tstruct _structPQ noattr.

Definition heap_item_rep (i : heap_item) : reptype t_item :=
  (Vint (Int.repr (fst (fst i))), (Vint (snd (fst i)), Vint (snd i))).

Definition hitem (i : heap_item) : val -> mpred :=
  data_at Tsh t_item (heap_item_rep i).

Definition lookup_array (lookup : list Z) : val -> mpred :=
  data_at Tsh (tarray tuint (Zlength lookup)) (map (fun z => Vint (Int.repr z)) lookup).

Definition heap_array (contents : list heap_item) : val -> mpred :=
 data_at Tsh (tarray t_item (Zlength contents)) (map heap_item_rep contents).

(* Maybe can move this and associated definitons to Zmodel... *)
Definition linked_correctly' (contents : list heap_item) (lookup : list Z) (offset : Z) : Prop :=
  NoDup lookup /\
  forall i, 0 <= i < Zlength contents -> 
    let loc := heap_item_key (Znth i contents) in
    0 <= loc < Zlength lookup /\
    Znth loc lookup = offset + i.

Definition linked_correctly (contents : list heap_item) (lookup : list Z) : Prop :=
  linked_correctly' contents lookup 0.

Lemma linked_correctly_app1: forall contents contents' lookup,
  linked_correctly (contents ++ contents') lookup ->
  linked_correctly contents lookup.
Proof. 
  repeat intro. destruct H. split; trivial.
  repeat intro. specialize (H0 i). rewrite Znth_app1 in H0. 2: lia. 
  apply H0. rewrite Zlength_app. rep_lia.
Qed.

Lemma linked_correctly_app2: forall contents contents' lookup,
  linked_correctly (contents ++ contents') lookup ->
  linked_correctly' contents' lookup (Zlength contents).
Proof.
  repeat intro. destruct H as [Hz H]. split; trivial. intros.
  specialize (H (Zlength contents + i)). rewrite Znth_app2 in H. 2: lia.
  rewrite Z.add_0_l in H. replace (Zlength contents + i - Zlength contents) with i in H by lia.
  apply H. rewrite Zlength_app. rep_lia.
Qed.

Lemma linked_correctly_app3: forall contents contents' lookup,
  linked_correctly contents lookup ->
  linked_correctly' contents' lookup (Zlength contents) ->
  linked_correctly (contents ++ contents') lookup.
Proof.
  repeat intro. destruct H as [Hz H]. destruct H0 as [Hz' H0]. split. trivial. intros.
  rewrite Z.add_0_l. assert (0 <= i < Zlength contents \/ Zlength contents <= i < Zlength (contents ++ contents')) by rep_lia.
  destruct H2. destruct H2. unfold loc. rewrite Znth_app1; try lia. apply H; trivial. rep_lia.
  unfold loc. rewrite Znth_app2; try lia. rewrite Zlength_app in *.
  specialize (H0 (i - Zlength contents)). destruct H0. lia. rewrite H3. lia.
Qed.

Lemma linked_correctly_app_eq: forall contents contents' lookup,
  (linked_correctly contents lookup /\ linked_correctly' contents' lookup (Zlength contents)) =
  linked_correctly (contents ++ contents') lookup.
Proof.
  intros. apply prop_ext. split; intros. eapply linked_correctly_app3; tauto.
  split. eapply linked_correctly_app1; apply H. apply linked_correctly_app2. trivial.
Qed.

Lemma linked_correctly'_shuffle: forall contents lookup lookup' offset,
  linked_correctly' contents lookup offset ->
  Permutation lookup lookup' ->
  (forall i, 0 <= i < Zlength contents -> Znth (heap_item_key (Znth i contents)) lookup = Znth (heap_item_key (Znth i contents)) lookup') ->
  linked_correctly' contents lookup' offset.
Proof.
  intros. destruct H as [Hz H]. split.
  eapply Permutation_NoDup; eauto.
  repeat intro. unfold loc. rewrite <- H1; trivial.
  apply Permutation_Zlength in H0. rewrite <- H0. apply H; trivial.
Qed.

Definition lookup_oob_eq (contents : list heap_item) (lookup lookup' : list Z) : Prop :=
  Permutation lookup lookup' /\
  forall i, (forall j, 0 <= j < Zlength contents -> heap_item_key (Znth j contents) <> i) ->
  Znth i lookup = Znth i lookup'.

Lemma lookup_oob_eq_refl: forall contents lookup,
  lookup_oob_eq contents lookup lookup.
Proof. split. trivial. repeat intro. trivial. Qed.

Lemma lookup_oob_eq_trans: forall contents lookup lookup' lookup'',
  lookup_oob_eq contents lookup lookup' ->
  lookup_oob_eq contents lookup' lookup'' ->
  lookup_oob_eq contents lookup lookup''.
Proof.
  intros. destruct H, H0. split. transitivity lookup'; auto.
  repeat intro. specialize (H1 i H3). rewrite H1. apply H2; trivial. 
Qed.

Instance lookup_oob_po: forall c, PreOrder (lookup_oob_eq c).
Proof. intro c. split. intro x. apply lookup_oob_eq_refl. intros x y z. apply lookup_oob_eq_trans. Qed.

Lemma lookup_oob_eq_shuffle: forall contents contents' lookup lookup',
  Permutation (map heap_item_key contents) (map heap_item_key contents') ->
  lookup_oob_eq contents lookup lookup' ->
  lookup_oob_eq contents' lookup lookup'.
Proof. 
  repeat intro. destruct H0 as [Hz H0]. split; trivial. intros.
  apply H0. repeat intro.
  symmetry in H.
  apply Permutation_Znth in H. 2: exact 0. destruct H as [? [f [? [? ?]]]].
  do 2 rewrite Zlength_map in *. rewrite <- H in *.
  apply (H1 (Z.of_nat (f (Z.to_nat j)))).
  specialize (H4 (Z.to_nat j)). rep_lia.
  specialize (H6 j H2). rewrite Znth_map in H6. 2: lia. rewrite H6 in H3.
  rewrite Znth_map in H3. trivial.
  specialize (H4 (Z.to_nat j)). rep_lia.
Qed.

Lemma lookup_oob_eq_Zexchange: forall L1 L2 j k,
  0 <= j < Zlength L1 ->
  0 <= k < Zlength L1 ->
  linked_correctly L1 L2 ->
  lookup_oob_eq (Zexchange L1 j k) L2 (Zexchange L2 (heap_item_key (Znth j L1)) (heap_item_key (Znth k L1))).
Proof.
  repeat intro. destruct H1 as [Hz H1]. split; repeat rewrite Zlength_Zexchange in *.
  apply Zexchange_Permutation.
  intros. rewrite Znth_Zexchange''; auto.
  destruct (H1 _ H); auto.
  destruct (H1 _ H0); auto.
  intro. subst i. eapply H2. apply H0. rewrite Znth_Zexchange'; auto.
  intro. subst i. eapply H2. apply H. rewrite Znth_Zexchange; auto.
Qed.

Definition linked_heap_array (contents : list heap_item) (v1 : val) (lookup : list Z) (v2 : val) : mpred :=
  (!!(linked_correctly contents lookup) && ((heap_array contents v1) * (lookup_array lookup v2)))%logic.

Lemma harray_emp: forall arr,
  heap_array [] arr |-- emp.
Proof.
  unfold heap_array. intros. rewrite data_at_isptr. entailer. rewrite data_at_zero_array_eq; auto.
Qed.

Lemma fold_heap_array': forall L i arr,
  i = Zlength L ->
  data_at Tsh (tarray t_item i) (map heap_item_rep L) arr = heap_array L arr.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma fold_heap_array: forall L arr,
  data_at Tsh (tarray t_item (Zlength L)) (map heap_item_rep L) arr = heap_array L arr.
Proof. reflexivity. Qed.

Lemma heap_array_split: forall L1 L2 ptr,
  heap_array (L1 ++ L2) ptr = 
  ((heap_array L1 ptr) * 
   (heap_array L2 (field_address0 (tarray t_item (Zlength (L1 ++ L2))) [ArraySubsc (Zlength L1)] ptr)))%logic.
Proof.
  intros. unfold heap_array.
  rewrite map_app.
  erewrite split2_data_at_Tarray_app.
  2: rewrite Zlength_map; reflexivity. 2: rewrite Zlength_app, Zlength_map; lia.
  rewrite Zlength_app.
  replace (Zlength L1 + Zlength L2 - Zlength L1) with (Zlength L2) by lia.
  trivial.
Qed.

Lemma linked_heap_array_split: forall L1 L2 ptr L3 ptr',
  linked_heap_array (L1 ++ L2) ptr L3 ptr' =
  (linked_heap_array L1 ptr L3 ptr' * (!! linked_correctly' L2 L3 (Zlength L1) && heap_array L2 (field_address0 (tarray t_item (Zlength (L1 ++ L2))) [ArraySubsc (Zlength L1)] ptr)))%logic.
Proof.
  unfold linked_heap_array. intros. rewrite heap_array_split.
  rewrite sepcon_assoc.
  rewrite (sepcon_comm (heap_array L2 _)).
  rewrite <- sepcon_assoc.
  rewrite sepcon_andp_prop'.
  rewrite sepcon_andp_prop.
  rewrite <- andp_assoc.
  rewrite <- prop_and.
  rewrite linked_correctly_app_eq.
  trivial.
Qed.

Definition valid_pq (pq : val) (h: heap): mpred :=
  EX arr : val, EX junk: list heap_item, EX arr2 : val, EX lookup : list Z,
    (!! heap_ordered (heap_items h)) && (!! (Zlength ((heap_items h) ++ junk) = heap_capacity h)) &&
    (!! (2 * (heap_capacity h - 1) <= Int.max_unsigned)) &&
(*    (!! Permutation
        (map heap_item_key ((heap_items h) ++ junk))
        (nat_inc_list (Z.to_nat (heap_capacity h)))) && *)
    (data_at Tsh t_pq (Vint (Int.repr (heap_capacity h)), (Vint (Int.repr (heap_size h)), (arr, arr2))) pq *
       linked_heap_array ((heap_items h) ++ junk) arr lookup arr2).

Definition hitem_ (v : val) : mpred :=
  data_at_ Tsh t_item v.

Lemma hitem_hitem_: forall v hi,
  hitem hi v |-- hitem_ v.
Proof.
  intros.
  unfold hitem, hitem_. cancel.
  (* apply data_at_data_at_. *)
Qed.

Lemma weaken_prehitem_: forall v,
  malloc_compatible (sizeof (Tstruct _structItem noattr)) v ->
  (data_at_ Tsh (tarray tint (sizeof (Tstruct _structItem noattr) / sizeof tint)) v) |--
  (hitem_ v).
Proof.
  intros v H.
  sep_apply data_at__memory_block_cancel.
  change (sizeof (tarray _ _)) with (sizeof t_item).
  rewrite memory_block_data_at_.
  apply derives_refl.
  apply malloc_compatible_field_compatible in H; auto.
Qed.

Definition update_pri_if_key (key: key_type) (newpri: priority_type) (hi : heap_item) :=
  if Z.eq_dec key (heap_item_key hi) then (key, newpri, heap_item_payload hi) else hi.

Definition update_pri_by_key (h: list heap_item) (key: key_type) (newpri: priority_type) :=
  map (update_pri_if_key key newpri) h.

Definition find_item_by_key (h: list heap_item) (key: key_type) :=
  filter (fun item => Z.eq_dec (heap_item_key item) key) h.

Inductive Subsequence {A : Type} : list A -> list A -> Prop :=
 | SubNil: forall L, Subsequence nil L
 | SubIn: forall L1 L2, Subsequence L1 L2 -> forall x, Subsequence (x :: L1) (x :: L2)
 | SubOut: forall L1 L2, Subsequence L1 L2 -> forall x, Subsequence L1 (x :: L2).

Definition sub_permutation {A} (l1 l2 : list A) :=
  exists l2', Permutation l2' l2 /\ Subsequence l1 l2'.

Definition keys_valid (h : list heap_item) :=
  NoDup (map heap_item_key h).

Definition proj_keys h :=
  map heap_item_key (heap_items h).

Lemma proj_keys_Zlength: forall h,
    Zlength (proj_keys h) = heap_size h.
Proof.
  intros. unfold proj_keys, heap_size. now rewrite Zlength_map.
Qed.

Lemma Subsequence_In: forall A (l1 l2 : list A),
  Subsequence l1 l2 ->
  forall x, In x l1 -> In x l2.
Proof.
  induction 1; simpl; auto. contradiction.
  destruct 1; auto.
Qed.

Lemma NoDup_Subsequence: forall A (l1 l2 : list A),
  Subsequence l1 l2 ->
  NoDup l2 ->
  NoDup l1.
Proof.
  intros ? ? ? ?. induction H; intros.
  * constructor.
  * constructor. inversion H0. subst x0 l. intro. apply H3. eapply Subsequence_In; eauto.
    apply IHSubsequence. inversion H0. trivial.
  * inversion H0; auto.
Qed.

Lemma NoDup_sub_permutation: forall A (l1 l2 : list A),
  sub_permutation l1 l2 ->
  NoDup l2 ->
  NoDup l1.
Proof.
  intros A l1 l2 [l2' [? ?]] ?.
  eapply NoDup_Subsequence; eauto.
  symmetry in H.
  eapply Permutation_NoDup; eauto.
Qed.

Lemma keys_valid_tl: forall hi h,
  keys_valid (hi :: h) -> keys_valid h.
Proof. intros. eapply List_ext.NoDup_cons_1, H. Qed.

Lemma update_pri_by_key_not_In: forall h key newpri,
  ~In key (map heap_item_key h) ->
  update_pri_by_key h key newpri = h.
Proof.
  induction h. reflexivity. intros.
  simpl. unfold update_pri_if_key. case Z.eq_dec; intro. exfalso. apply H. left. auto.
  rewrite IHh; trivial. intro. apply H. right. trivial.
Qed.

Lemma update_pri_by_key_split: forall h key newpri start xp xd rest,
  keys_valid h ->
  h = start ++ (key, xp, xd) :: rest ->
  update_pri_by_key h key newpri = start ++ (key, newpri, xd) :: rest.
Proof.
  intros h key newpri start xp xd. revert h. induction start; intros; rewrite H0.
  * simpl in *. subst h. rewrite update_pri_by_key_not_In. f_equal.
    unfold update_pri_if_key. case Z.eq_dec. trivial. contradiction.
    intro. red in H. simpl in H. inversion H. contradiction.
  * subst h. simpl in H. generalize (keys_valid_tl _ _ H); intro.
    specialize (IHstart (start ++ (key, xp, xd) :: rest) rest H0 (eq_refl _)).
    simpl. rewrite IHstart. f_equal.
    unfold update_pri_if_key. case Z.eq_dec; auto. intro.
    inversion H. subst key. rewrite map_app in H3. exfalso. apply H3.
    apply in_or_app. right. left. trivial.
Qed.

Lemma can_split: forall (h: heap) (key: key_type),
    (~In key (map heap_item_key (heap_items h))) \/
    exists start xp xd rest,
      (heap_items h) = start ++ (key, xp, xd) :: rest.
Proof.
  destruct h. simpl. induction l. left. intro. inversion H.
  intro key. case (Z.eq_dec key (heap_item_key a)); intro.
  * right. destruct a as [[? ?] ?]. unfold heap_item_key in e. simpl in e. subst k.
    exists nil, p, p0, l. trivial.
  * specialize (IHl key). destruct IHl. left. intro. apply H. simpl in H0. destruct H0; [symmetry in H0|]; contradiction.
    destruct H as [start [xp [xd [rest ?]]]].
    right. exists (a :: start), xp, xd, rest. rewrite H. trivial.
Qed.

Lemma upd_Znth_Zexchange {A} {iA : Inhabitant A}: forall k j (L : list A),
  0 <= k < Zlength L ->
  0 <= j < Zlength L ->
  upd_Znth k (upd_Znth j L (Znth k L)) (Znth j L) = Zexchange L j k.
Proof.
  intros. apply list_eq_Znth; do 2 rewrite Zlength_upd_Znth. rewrite Zlength_Zexchange; trivial.
  intros. case (Z.eq_dec i k); intro.
  * subst k. rewrite Znth_Zexchange'; auto.
    rewrite upd_Znth_same; auto. rewrite Zlength_upd_Znth; auto.
  * rewrite upd_Znth_diff; auto. 2,3: rewrite Zlength_upd_Znth; auto.
    case (Z.eq_dec i j); intro.
    + subst j. rewrite upd_Znth_same; auto. rewrite Znth_Zexchange; auto.
    + rewrite upd_Znth_diff; auto. rewrite Znth_Zexchange''; auto.
Qed.

Lemma linked_correctly_Zexchange: forall L1 L2 j k,
  0 <= j < Zlength L1 ->
  0 <= k < Zlength L1 ->
  linked_correctly L1 L2 ->
  linked_correctly (Zexchange L1 j k) (Zexchange L2 (heap_item_key (Znth j L1)) (heap_item_key (Znth k L1))).
Proof.
  repeat intro. destruct H1 as [Hz ?]. split. 
  * eapply Permutation_NoDup. 2: apply Hz.
    apply Zexchange_Permutation.
  * intros. subst loc. rewrite Zlength_Zexchange in H2. rewrite Zlength_Zexchange.
    destruct (H1 _ H). destruct (H1 _ H0). destruct (H1 _ H2). clear H1.
    case (Z.eq_dec i j); intro.
    - subst j. rewrite Znth_Zexchange; auto. rewrite Znth_Zexchange'; auto.
    - case (Z.eq_dec i k); intro.
      + subst i. rewrite Znth_Zexchange'; auto. rewrite Znth_Zexchange; auto.
      + rewrite Znth_Zexchange''; auto. rewrite Znth_Zexchange''; auto.
        intro. rewrite H1 in H8. rewrite H4 in H8. lia.
        intro. rewrite H1 in H8. rewrite H6 in H8. lia.
Qed.

Lemma exists_min_in_list: forall L,
  0 < Zlength L ->
  exists min_item : heap_item,
  In min_item L /\
  Forall (cmp_rel min_item) L.
Proof.
  induction L. discriminate.
  destruct L. exists a. split. left. trivial. constructor. reflexivity. constructor.
  intros _. assert (0 < Zlength (h :: L)) by (rewrite Zlength_cons; rep_lia).
  specialize (IHL H). clear H. destruct IHL as [mi' [? ?]].
  case_eq (cmp mi' a); intro. exists mi'.
  split. right. trivial.
  constructor. apply H1. trivial.
  exists a. split. left. trivial. constructor. reflexivity.
  rewrite Forall_forall in H0. rewrite Forall_forall. intro hi; intros.
  transitivity mi'.
  destruct (cmp_linear a mi'); auto. unfold cmp_rel in H3. rewrite H1 in H3. discriminate.
  apply H0. trivial.
Qed.

Lemma linked_correctly'_app: forall L1 L1' L2 n,
  linked_correctly' (L1 ++ L1') L2 n <->
  (linked_correctly' L1 L2 n /\ linked_correctly' L1' L2 (Zlength L1 + n)).
Proof.
  split; intros. destruct H. split; split; trivial; repeat intro. subst loc.
  assert (0 <= i < Zlength (L1 ++ L1')) by (rewrite Zlength_app; rep_lia).
  specialize (H0 _ H2). destruct H0.
  rewrite app_Znth1 in *; try lia. subst loc.
  assert (0 <= i + Zlength L1 < Zlength (L1 ++ L1')) by (rewrite Zlength_app; rep_lia).
  specialize (H0 _ H2). destruct H0.
  rewrite app_Znth2 in *; try lia.
  replace (i + Zlength L1 - Zlength L1) with i in * by lia.
  replace (Zlength L1 + n + i) with (n + (i + Zlength L1)) by lia. auto.
  destruct H as [[? ?] [? ?]]. split; trivial. intros. subst loc.
  rewrite Zlength_app in H3. assert (0 <= i < Zlength L1 \/ 0 <= i - Zlength L1 < Zlength L1') by rep_lia.
  destruct H4. rewrite app_Znth1; auto; lia.
  rewrite app_Znth2; try lia.
  specialize (H2 _ H4). destruct H2. replace (Zlength L1 + n + (i - Zlength L1)) with (n + i) in H5 by lia.
  auto.
Qed.

Lemma lookup_oob_eq_nil: forall L1 L2,
  lookup_oob_eq nil L1 L2 ->
  L1 = L2.
Proof.
  intros. destruct H.
  apply Znth_eq_ext. apply Permutation_Zlength; trivial. intros.
  apply H0. intros. rewrite Zlength_nil in H2. lia.
Qed.

Lemma fold_linked_heap_array: forall L1 v1 L2 v2,
  linked_correctly L1 L2 ->
  (heap_array L1 v1) * (lookup_array L2 v2) |-- linked_heap_array L1 v1 L2 v2.
Proof.
  intros. unfold linked_heap_array. entailer!.
Qed.

Lemma relink_tail: forall L0 L1 L2 L1' L2',
  linked_correctly (L0 ++ L1) L1' ->
  Permutation L0 L2 ->
  lookup_oob_eq L2 L1' L2' ->
  forall i, 0 <= i < Zlength L1 ->
  Znth (heap_item_key (Znth i L1)) L1' = Znth (heap_item_key (Znth i L1)) L2'.
Proof.
  intros old_live junk live lookup lookup'. intros.
  destruct H, H1.
  apply Permutation_Znth in H0. 2: apply (0,Int.zero,Int.zero).
  assert (0 <= i + Zlength live < Zlength (old_live ++ junk)) by (rewrite Zlength_app; rep_lia).
  destruct (H3 _ H5).
  rewrite <- H4; trivial.
  repeat intro.
  rewrite Znth_app2 in H7. 2: lia.
  replace (i + Zlength live - Zlength old_live) with i in H7 by lia.
  destruct H0 as [H0 [f [? [? ?]]]].
  rewrite H12 in H9. 2: lia.
  specialize (H10 (Z.to_nat j)).
  assert (0 <= (Z.of_nat (f (Z.to_nat j))) < Zlength (old_live ++ junk)) by lia.
  destruct (H3 _ H13).
  rewrite Znth_app1 in H15. 2: lia.
  rewrite H9 in H15. rewrite H7 in H15. lia.
Qed.

(*
Does not seem to work on arrays.

unfold_data_at (data_at _ (tarray tint 3) _ v).

In environment
v : val
H : field_compatible (Tstruct _structItem noattr) [] v
V := list_repeat (Z.to_nat 3) (default_val tint) : list (reptype tint)
P := v : val
T := tarray tint 3 : type
F := field_at Tsh T [] V P : mpred
id := ?id : ident
Unable to unify "Tunion ?id noattr" with
 "match nested_field_rec (tarray tint 3) [] with
  | Some (_, t0) => t0
  | None => Tvoid
  end".
*)

