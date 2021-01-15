Require Import VST.floyd.proofauto.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.binheap.binary_heap_pro.
Require Import CertiGraph.binheap.binary_heap_model.
Require Import CertiGraph.binheap.binary_heap_Zmodel.
Require Import RelationClasses.

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
  data_at Tsh (tarray tint (Zlength lookup)) (map (fun z => Vint (Int.repr z)) lookup).

Definition heap_array (contents : list heap_item) : val -> mpred :=
 data_at Tsh (tarray t_item (Zlength contents)) (map heap_item_rep contents).

(* Maybe can move this and associated definitons to Zmodel... *)
Definition linked_correctly' (contents : list heap_item) (lookup : list Z) (offset : Z) : Prop :=
  forall i, 0 <= i < Zlength contents -> Znth (heap_item_key (Znth i contents)) lookup = offset + i.

Definition linked_correctly (contents : list heap_item) (lookup : list Z) : Prop :=
  linked_correctly' contents lookup 0.

Lemma linked_correctly_app1: forall contents contents' lookup,
  linked_correctly (contents ++ contents') lookup ->
  linked_correctly contents lookup.
Proof. repeat intro. specialize (H i). rewrite Znth_app1 in H. 2: lia. apply H. rewrite Zlength_app. rep_lia. Qed.

Lemma linked_correctly_app2: forall contents contents' lookup,
  linked_correctly (contents ++ contents') lookup ->
  linked_correctly' contents' lookup (Zlength contents).
Proof. repeat intro. specialize (H (Zlength contents + i)). rewrite Znth_app2 in H. 2: lia.
  rewrite Z.add_0_l in H. replace (Zlength contents + i - Zlength contents) with i in H by lia.
  apply H. rewrite Zlength_app. rep_lia. Qed.

Lemma linked_correctly_app3: forall contents contents' lookup,
  linked_correctly contents lookup ->
  linked_correctly' contents' lookup (Zlength contents) ->
  linked_correctly (contents ++ contents') lookup.
Proof.
  repeat intro. rewrite Z.add_0_l. assert (0 <= i < Zlength contents \/ Zlength contents <= i < Zlength (contents ++ contents')) by rep_lia.
  destruct H2. rewrite Znth_app1; try lia. apply H; trivial.
  rewrite Znth_app2; try lia. rewrite Zlength_app in H2.
  specialize (H0 (i - Zlength contents)). rewrite H0; lia.
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
  (forall i, 0 <= i < Zlength contents -> Znth (heap_item_key (Znth i contents)) lookup = Znth (heap_item_key (Znth i contents)) lookup') ->
  linked_correctly' contents lookup' offset.
Proof. repeat intro. rewrite <- H0; trivial. apply H. trivial. Qed.

Definition lookup_oob_eq (contents : list heap_item) (lookup lookup' : list Z) : Prop :=
  forall i, (forall j, 0 <= j < Zlength contents -> heap_item_key (Znth j contents) <> i) ->
  Znth i lookup = Znth i lookup'.

Lemma lookup_oob_eq_refl: forall contents lookup,
  lookup_oob_eq contents lookup lookup.
Proof. repeat intro. trivial. Qed.

Lemma lookup_oob_eq_trans: forall contents lookup lookup' lookup'',
  lookup_oob_eq contents lookup lookup' ->
  lookup_oob_eq contents lookup' lookup'' ->
  lookup_oob_eq contents lookup lookup''.
Proof. repeat intro. specialize (H i H1). rewrite H. apply H0; trivial. Qed.

Instance lookup_oob_po: forall c, PreOrder (lookup_oob_eq c).
Proof. intro c. split. intro x. apply lookup_oob_eq_refl. intros x y z. apply lookup_oob_eq_trans. Qed.

Lemma lookup_oob_eq_shuffle: forall contents contents' lookup lookup',
  Permutation (map heap_item_key contents) (map heap_item_key contents') ->
  lookup_oob_eq contents lookup lookup' ->
  lookup_oob_eq contents' lookup lookup'.
Proof. 
  repeat intro. apply H0. repeat intro.
  symmetry in H.
  apply Permutation_Znth in H. 2: exact 0. destruct H as [? [f [? [? ?]]]].
  do 2 rewrite Zlength_map in *. rewrite <- H in *.
  apply (H1 (Z.of_nat (f (Z.to_nat j)))).
  specialize (H4 (Z.to_nat j)). rep_lia.
  specialize (H6 j H2). rewrite Znth_map in H6. 2: lia. rewrite H6 in H3.
  rewrite Znth_map in H3. trivial.
  specialize (H4 (Z.to_nat j)). rep_lia.
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
    (!! Permutation
        (map heap_item_key ((heap_items h) ++ junk))
        (nat_inc_list (Z.to_nat (heap_capacity h)))) &&
    (data_at Tsh t_pq (Vint (Int.repr (heap_capacity h)), (Vint (Int.repr (heap_size h)), (arr, arr2))) pq *
       linked_heap_array ((heap_items h) ++ junk) arr lookup arr2).


