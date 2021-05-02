Require Import RelationClasses.
Require Import VST.floyd.proofauto.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.binheap.binary_heap_pro.
Require Import CertiGraph.binheap.binary_heap_malloc_spec.
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
    (!! (Zlength lookup = heap_capacity h)) &&
    (data_at Tsh t_pq (Vint (Int.repr (heap_capacity h)), (Vint (Int.repr (heap_size h)), (arr, arr2))) pq *
       linked_heap_array ((heap_items h) ++ junk) arr lookup arr2 *
(* tokens that allow deallocation *)
       free_tok arr (sizeof (Tstruct _structItem noattr) * (heap_capacity h)) * 
       free_tok arr2 (sizeof tuint * (heap_capacity h)) *
       free_tok pq (sizeof (Tstruct _structPQ noattr))).

Definition hitem_ (v : val) : mpred :=
  data_at_ Tsh t_item v.

Lemma hitem_hitem_: forall v hi,
  hitem hi v |-- hitem_ v.
Proof.
  intros.
  unfold hitem, hitem_. cancel.
  (* apply data_at_data_at_. *)
Qed.

Lemma malloc_hitem: forall v,
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

Lemma free_hitem: forall v,
  hitem_ v |--
  data_at_ Tsh (tarray tint (sizeof (Tstruct _structItem noattr) / sizeof tint)) v.
Proof.
  unfold hitem_. intro.
  saturate_local.
  sep_apply data_at__memory_block_cancel.
  rewrite <- memory_block_data_at_.
  apply derives_refl.
  destruct H as [? [? [? [? ?]]]].
  split3; auto.
  split3; auto.
  hnf in H2 |- *.
  destruct v; auto.
  unfold t_item in H2.
  change (_ / _) with 3.
  apply align_compatible_rec_Tarray; intros.
  assert (i0 = 0 \/ i0 = 1 \/ i0 = 2) by lia.
  destruct H5 as [? | [? | ?]]; subst i0;
  [ eapply align_compatible_rec_Tstruct_inv with (i0 := _key) in H2 |
    eapply align_compatible_rec_Tstruct_inv with (i0 := _priority) in H2 |
    eapply align_compatible_rec_Tstruct_inv with (i0 := _data) in H2 ] ;
  try reflexivity;
  eapply align_compatible_rec_by_value; try reflexivity;
  eapply align_compatible_rec_by_value_inv in H2; try reflexivity; apply H2.
Qed.

Lemma free_pq: forall v,
  (data_at_ Tsh t_pq v) |--
  (data_at_ Tsh (tarray tint (sizeof (Tstruct _structPQ noattr) / sizeof tint)) v).
Proof.
  intro. saturate_local.
  sep_apply data_at__memory_block_cancel.
  rewrite <- memory_block_data_at_.
  apply derives_refl.
  destruct H as [? [? [? [? ?]]]].
  split3; auto.
  split3; auto.
  hnf in H2 |- *.
  destruct v; auto.
  unfold t_pq in H2.
  change (_ / _) with 4.
  apply align_compatible_rec_Tarray; intros.
  assert (i0 = 0 \/ i0 = 1 \/ i0 = 2 \/ i0 = 3) by lia.
  destruct H5 as [? | [? | [? | ?]]]; subst i0;
  [ eapply align_compatible_rec_Tstruct_inv with (i0 := _capacity) in H2 |
    eapply align_compatible_rec_Tstruct_inv with (i0 := _first_available) in H2 |
    eapply align_compatible_rec_Tstruct_inv with (i0 := _heap_cells) in H2 |
    eapply align_compatible_rec_Tstruct_inv with (i0 := _key_table) in H2 ];
  try reflexivity; eapply align_compatible_rec_by_value; try reflexivity;
  eapply align_compatible_rec_by_value_inv in H2; try reflexivity; apply H2.
Qed.

Lemma simpl_size_t_item: forall s,
  12 * s / 4 = 3 * s.
Proof.
  intro. change 12 with (3 * 4).
  rewrite <- Z.mul_assoc. rewrite (Z.mul_comm 4).
  rewrite Z.mul_assoc.
  rewrite Z.div_mul; lia.
Qed.

Lemma malloc_items: forall v size,
  0 <= size ->
  malloc_compatible (sizeof (Tstruct _structItem noattr) * size) v ->
  data_at_ Tsh (tarray tint (sizeof (Tstruct _structItem noattr) * size / sizeof tint)) v |--
  data_at_ Tsh (tarray t_item size) v.
Proof.
  intros.
  sep_apply data_at__memory_block_cancel.
  rewrite <- memory_block_data_at_.
  simpl sizeof.
  apply derives_refl'. f_equal. rewrite (Z.mul_comm 12). change 12 with (3 * 4).
  rewrite Z.mul_assoc.
  rewrite Z_div_mult. 1,2: lia.
  apply malloc_compatible_field_compatible; try reflexivity.
  simpl in *.
  rewrite Z.max_r by lia. trivial.
Qed.

Lemma free_items: forall v size,
(*  malloc_compatible (sizeof (Tstruct _structItem noattr) * size) v *)
  data_at_ Tsh (tarray t_item size) v |--
  data_at_ Tsh (tarray tint (sizeof (Tstruct _structItem noattr) * size / sizeof tint)) v.
Proof.
  intros. saturate_local.
  sep_apply data_at__memory_block_cancel.
  rewrite <- memory_block_data_at_.
  simpl. rewrite simpl_size_t_item.
  apply derives_refl'. f_equal. lia.
  destruct H as [? [? [? [? ?]]]].
  split3; auto.
  split3; auto.
  hnf in H1 |- *.
  destruct v; auto. simpl. rewrite simpl_size_t_item.
  simpl in H1. lia.
  hnf in H2 |- *.
  destruct v; auto.
  simpl sizeof. rewrite simpl_size_t_item.
  apply align_compatible_rec_Tarray; intros.
  assert (exists k, 0 <= k < size /\ (i0 = 3 * k + 0 \/ i0 = 3 * k + 1 \/ i0 = 3 * k + 2)).
  { exists (i0 / 3).
    generalize (Z_div_mod_eq i0 3); intro. spec H5. lia.
    generalize (Z.mod_pos_bound i0 3); intro. spec H6. lia.
    split. 2: lia.
    destruct H4. split.
    apply Z.div_pos; lia.
    apply Z.div_lt_upper_bound; lia. }
  destruct H5 as [k [? ?]].
  eapply align_compatible_rec_Tarray_inv in H2. 2: apply H5.
  destruct H6 as [? | [? | ?]]; subst i0;
  [ eapply align_compatible_rec_Tstruct_inv with (i0 := _key) in H2 |
    eapply align_compatible_rec_Tstruct_inv with (i0 := _priority) in H2 |
    eapply align_compatible_rec_Tstruct_inv with (i0 := _data) in H2 ] ;
  try reflexivity;
  eapply align_compatible_rec_by_value; try reflexivity;
  eapply align_compatible_rec_by_value_inv in H2; try reflexivity;
  simpl in *; rewrite (Z.mul_add_distr_l 4), Z.mul_assoc, Z.add_assoc; simpl; apply H2.
Qed.

Lemma malloc_lookup: forall v size,
  0 <= size ->
  malloc_compatible (sizeof tint * size) v ->
  data_at_ Tsh (tarray tint (sizeof tint * size / sizeof tint)) v |--
  data_at_ Tsh (tarray tuint size) v.
Proof.
  intros.
  sep_apply data_at__memory_block_cancel.
  rewrite <- memory_block_data_at_.
  simpl sizeof.
  apply derives_refl'. f_equal.
  rewrite (Z.mul_comm _ size).
  rewrite Z_div_mult; lia.
  apply malloc_compatible_field_compatible; try reflexivity.
  simpl in *.
  rewrite Z.max_r by lia. trivial.
Qed.

Lemma free_lookup: forall v size,
(*  malloc_compatible (sizeof tint * size) v -> *)
  data_at_ Tsh (tarray tuint size) v |--
  data_at_ Tsh (tarray tint (sizeof tint * size / sizeof tint)) v.
Proof.
  intros. saturate_local.
  sep_apply data_at__memory_block_cancel.
  rewrite <- memory_block_data_at_.
  simpl. rewrite (Z.mul_comm _ size), Z_div_mult; trivial. lia.
  destruct H as [? [? [? [? ?]]]].
  split3; auto.
  split3; auto.
  hnf in H1 |- *.
  destruct v; auto. simpl. rewrite (Z.mul_comm _ size), Z_div_mult; trivial. lia.
  hnf in H2 |- *.
  destruct v; auto.
  simpl sizeof. rewrite (Z.mul_comm _ size), Z_div_mult. 2: lia.
  apply align_compatible_rec_Tarray; intros.
  eapply align_compatible_rec_Tarray_inv in H2. 2: apply H4.
  eapply align_compatible_rec_by_value; try reflexivity.
  eapply align_compatible_rec_by_value_inv in H2. apply H2. reflexivity.
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

Definition proj_payloads h :=
  map heap_item_payload (heap_items h).

Lemma proj_keys_Zlength: forall h,
    Zlength (proj_keys h) = heap_size h.
Proof.
  intros. unfold proj_keys, heap_size. now rewrite Zlength_map.
Qed.

Definition keys_dist_linked_correctly i keys dist h :=
  forall k,
    Znth i keys = k ->
    find_item_by_key (heap_items h) k =
    [(k, Znth i dist, Int.repr i)] \/
    ~ In k (proj_keys h).

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

Lemma valid_pq_NoDup: forall p h,
  valid_pq p h |-- !! NoDup (heap_items h).
Proof.
  intros. unfold valid_pq, linked_heap_array, linked_correctly, linked_correctly'. Intros arr junk lookup lookup'.
  entailer!. clear H5 H6.
  apply NoDup_nth_error. rewrite NoDup_nth_error in H3. intros.
  rewrite <- (Nat2Z.id i) in H6.
  rewrite Znth_nth_error in H6. 2: rewrite Zlength_correct; rep_lia.
  remember (nth_error (heap_items h) j). destruct o. 2: discriminate.
  assert (j < length (heap_items h))%nat. { eapply nth_error_Some. intro. congruence. }
  assert (0 <= Z.of_nat j < Zlength (heap_items h)) by (rewrite Zlength_correct; lia).
  rewrite <- (Nat2Z.id j) in Heqo. rewrite Znth_nth_error in Heqo; auto.
  inversion Heqo. subst h0. clear Heqo. inversion H6. clear H6.
  generalize (H4 (Z.of_nat i)); generalize (H4 (Z.of_nat j)); intros. clear H4.
  rewrite Zlength_app in *. spec H6. rep_lia. spec H9. rewrite Zlength_correct; rep_lia.
  rewrite Znth_app1 in H6. 2: lia.
  rewrite Znth_app1 in H9. 2: rewrite Zlength_correct; lia.
  destruct H6, H9.
  rewrite H10 in H11. rewrite H11 in H6. lia.
Qed.

Lemma upd_Znth_update {A} {iA : Inhabitant A}: forall t (L: list A) x,
  0 <= t < Zlength L ->
  upd_Znth t L x = update L (Z.to_nat t) x.
Proof.
  intros.
  apply List_ext.list_eq_Znth. 
    { rewrite Zlength_upd_Znth. do 2 rewrite Zlength_correct. rewrite update_length. trivial. }
  intros. rewrite Zlength_upd_Znth in H0.
  case (eq_dec i t); intros.
  subst i. rewrite upd_Znth_same; auto.
  assert (nth_error (update L (Z.to_nat t) x) (Z.to_nat t) = Some x). 
    { rewrite nth_error_update; auto. rewrite Zlength_correct in H. lia. }
  rewrite Znth_nth_error in H1. inversion H1. do 2 rewrite H3. trivial. 
  rewrite Zlength_correct. rewrite update_length. rewrite Zlength_correct in H. lia.
  rewrite Znth_upd_Znth_diff; auto.
  apply nth_error_Znth; auto. rewrite Zlength_correct. rewrite update_length. rewrite Zlength_correct in H0; lia.
  rewrite nth_error_update'. trivial.
  lia.
Qed.

Lemma Perm_Perm_cons_Perm: forall {A} {l1 l2 l3: list A} {a b},
  Permutation l1 (a :: l2) ->
  Permutation l2 (b :: l3) ->
  Permutation l1 (a :: b :: l3).
Proof.
  intros. transitivity (a :: l2). trivial. constructor. trivial.
Qed.

Lemma NoDup_Perm_False: forall {A} {l1 l2: list A} {a},
  NoDup l1 ->
  Permutation l1 (a :: a :: l2) -> False.
Proof.
  intros. assert (NoDup (a :: a :: l2)).
  eapply Permutation_NoDup; eauto.
  inversion H1. apply H4. left. trivial.
Qed.

Lemma malloc_pq: forall v,
  malloc_compatible (sizeof (Tstruct _structPQ noattr)) v ->
  (data_at_ Tsh (tarray tint (sizeof (Tstruct _structPQ noattr) / sizeof tint)) v) |--
  (data_at_ Tsh t_pq v).
Proof.
  intros v H.
  sep_apply data_at__memory_block_cancel.
  change (sizeof (tarray _ _)) with (sizeof t_pq).
  rewrite memory_block_data_at_.
  apply derives_refl.
  apply malloc_compatible_field_compatible in H; auto.
Qed.

Lemma Zlength_default_val_array: forall t size,
  0 <= size ->
  Zlength (default_val (tarray t size)) = size.
Proof.
  unfold default_val. simpl. intros. rewrite Zlength_repeat; lia.
Qed.

Definition initializing_inc_list (size capacity : Z) : list val :=
  (map (fun z => Vint (Int.repr z)) (List_ext.nat_inc_list (Z.to_nat size))) ++ 
  default_val (tarray tuint (capacity - size)).

Lemma initializing_inc_list_inc: forall size capacity,
  0 <= size < capacity ->
  upd_Znth size (initializing_inc_list size capacity) (Vint (Int.repr size)) =
  initializing_inc_list (size + 1) capacity.
Proof.
  unfold initializing_inc_list. intros.
  rewrite upd_Znth_app2.
  1,2: rewrite Zlength_map, List_ext.nat_inc_list_Zlength.
  2: rewrite (Zlength_default_val_array tuint); lia.
  rewrite Z2Nat.id. 2: lia. rewrite Z.sub_diag.
  apply List_ext.list_eq_Znth.
  rewrite Zlength_app, Zlength_app, Zlength_upd_Znth, Zlength_map, Zlength_map.
  rewrite (Zlength_default_val_array tuint), (Zlength_default_val_array tuint).
  rewrite List_ext.nat_inc_list_Zlength, List_ext.nat_inc_list_Zlength. 1,2,3: lia.
  rewrite Zlength_app, Zlength_upd_Znth, Zlength_map.
  rewrite List_ext.nat_inc_list_Zlength, (Zlength_default_val_array tuint). 2: lia.
  replace (Z.of_nat (Z.to_nat size) + (capacity - size)) with capacity by lia.
  intros. assert (i < size \/ size <= i) by lia. destruct H1.
  rewrite Znth_app1, Znth_app1. rewrite Znth_map, Znth_map.
  rewrite List_ext.nat_inc_list_i, List_ext.nat_inc_list_i. trivial.
  5,6: rewrite Zlength_map. 3,4,5,6: rewrite List_ext.nat_inc_list_Zlength.
  1,2,3,4,5,6: lia.
  rewrite Znth_app2. 1,2 : rewrite Zlength_map, List_ext.nat_inc_list_Zlength. 2: lia.
  assert (i = size \/ size < i) by lia. destruct H2. subst i.
  rewrite Znth_app1. rewrite Znth_map, List_ext.nat_inc_list_i, Z2Nat.id, Z.sub_diag, Znth_upd_Znth_same; trivial.
  5: rewrite Zlength_map. 4,5: rewrite List_ext.nat_inc_list_Zlength.
  rewrite (Zlength_default_val_array tuint).
  1,2,3,4,5,6: lia.
  rewrite Znth_app2. 1,2: rewrite Zlength_map, List_ext.nat_inc_list_Zlength.
  rewrite Znth_upd_Znth_diff.
  unfold default_val. simpl.
  rewrite Znth_repeat_inrange, Znth_repeat_inrange; trivial.
  1,2,3,4: lia.
Qed.

Lemma initializing_inc_list_done: forall capacity,
  initializing_inc_list capacity capacity =
  map (fun z => Vint (Int.repr z)) (List_ext.nat_inc_list (Z.to_nat capacity)).
Proof.
  unfold initializing_inc_list. intros. rewrite Z.sub_diag.
  apply app_nil_r.
Qed.

Definition initial_item_list (size : Z) : list heap_item :=
  map (fun i => (i, Int.zero, Int.zero)) (List_ext.nat_inc_list (Z.to_nat size)).

Lemma Zlength_initial_item_list: forall size,
  0 <= size ->
  Zlength (initial_item_list size) = size.
Proof. intros. unfold initial_item_list. rewrite Zlength_map, List_ext.nat_inc_list_Zlength. lia. Qed.

Definition initializing_item_list (size capacity : Z) : list (reptype t_item) :=
  map heap_item_rep (initial_item_list size) ++ default_val (tarray t_item (capacity - size)).

Lemma Zlength_initializing_item_list: forall size capacity,
  0 <= size < capacity ->
  Zlength (initializing_item_list size capacity) = capacity.
Proof.
  unfold initializing_item_list. intros. 
  rewrite Zlength_app, Zlength_map, Zlength_initial_item_list, (Zlength_default_val_array t_item); lia.
Qed.

Lemma initial_item_list_i: forall i size,
  0 <= i < size ->
  Znth i (initial_item_list size) = (i, Int.zero, Int.zero).
Proof.
  intros. unfold initial_item_list. rewrite Znth_map. rewrite List_ext.nat_inc_list_i. trivial.
  2: rewrite List_ext.nat_inc_list_Zlength. 1,2: lia.
Qed.

(* BUG, we shouldn't need this but it seems like a bad guess is being made for implicit assumptions without it? *)
Definition initializing_item_array (size capacity : Z) (v : val) : mpred :=
  data_at Tsh (tarray t_item capacity) (initializing_item_list size capacity) v.

Lemma initializing_item_list_inc: forall size capacity : Z,
  0 <= size < capacity ->
    upd_Znth size (initializing_item_list size capacity) (Vint (Int.repr size), (Vzero, Vzero)) =
    initializing_item_list (size + 1) capacity.
Proof.
  unfold initializing_item_list. intros.
  rewrite upd_Znth_app2.
  1,2: rewrite Zlength_map, Zlength_initial_item_list.
  3: rewrite (Zlength_default_val_array t_item); lia.
  2,3: lia. rewrite Z.sub_diag.
  apply List_ext.list_eq_Znth.
  rewrite Zlength_app, Zlength_app, Zlength_upd_Znth, Zlength_map, Zlength_map.
  rewrite (Zlength_default_val_array t_item), (Zlength_default_val_array t_item).
  rewrite Zlength_initial_item_list, Zlength_initial_item_list. 1-5: lia.
  rewrite Zlength_app, Zlength_upd_Znth, Zlength_map.
  rewrite Zlength_initial_item_list, (Zlength_default_val_array t_item). 2,3: lia.
  replace (size + (capacity - size)) with capacity by lia.
  intros. assert (i < size \/ size <= i) by lia. destruct H1.
  rewrite Znth_app1, Znth_app1. rewrite Znth_map, Znth_map.
  rewrite initial_item_list_i, initial_item_list_i. trivial. 
  5,6: rewrite Zlength_map. 3-6: rewrite Zlength_initial_item_list. 1-10: lia.
  rewrite Znth_app2. 1,2 : rewrite Zlength_map, Zlength_initial_item_list. 2-4: lia.
  assert (i = size \/ size < i) by lia. destruct H2. subst i.
  rewrite Znth_app1. rewrite Znth_map, Z.sub_diag, Znth_upd_Znth_same, initial_item_list_i. trivial.
  2: rewrite (Zlength_default_val_array t_item). 6: rewrite Zlength_map.
  5,6: rewrite Zlength_initial_item_list. 1-8: lia.
  rewrite Znth_app2. 1,2: rewrite Zlength_map, Zlength_initial_item_list.
  rewrite Znth_upd_Znth_diff.
  unfold default_val. simpl.
  rewrite Znth_repeat_inrange, Znth_repeat_inrange; trivial.
  1-6: lia.
Qed.

Lemma initializing_item_list_done: forall capacity,
  initializing_item_list capacity capacity = map heap_item_rep (initial_item_list capacity).
Proof.
  unfold initializing_item_list. intros. rewrite Z.sub_diag.
  apply app_nil_r.
Qed.

Lemma initial_link_ok: forall size,
  0 <= size ->
  linked_correctly (initial_item_list size) (List_ext.nat_inc_list (Z.to_nat size)).
Proof.
  split. apply List_ext.nat_inc_list_NoDup.
  intros. rewrite List_ext.nat_inc_list_Zlength. rewrite Zlength_initial_item_list in H0; trivial.
  subst loc. unfold initial_item_list. rewrite Znth_map.
  unfold heap_item_key. simpl.
  rewrite List_ext.nat_inc_list_i. 
  rewrite List_ext.nat_inc_list_i.
  4: rewrite List_ext.nat_inc_list_Zlength. 
  1,2,3,4: lia.
Qed.

Lemma valid_heap_NoDup_keys: forall p h,
    valid_pq p h |-- !!(NoDup (proj_keys h)).
Proof.
  intros. unfold valid_pq, linked_heap_array, proj_keys.
  Intros arr junk arr2 lookup. entailer!.
  destruct H3. clear H4 H5.
  apply NoDup_nth_error. intros.
  remember (nth_error (map heap_item_key (heap_items h)) i). destruct o. 
  2: { symmetry in Heqo. apply nth_error_Some in Heqo. contradiction. lia. }
  assert (j < length (map heap_item_key (heap_items h)))%nat. { apply nth_error_Some. intro. rewrite H7 in H5. discriminate. }
  assert (0 <= Z.of_nat i < Zlength (heap_items h)). { rewrite map_length in H4. rewrite Zlength_correct. lia. } clear H4.
  assert (0 <= Z.of_nat j < Zlength (heap_items h)). { rewrite map_length in H7. rewrite Zlength_correct. lia. } clear H7.
  destruct (H6 (Z.of_nat i)). 2: destruct (H6 (Z.of_nat j)). 1,2: rewrite Zlength_app; rep_lia.
  rewrite Znth_app1 in H7, H9, H10, H11. 2-5: lia.
  rewrite Heqo in H5.
  rewrite <- (Nat2Z.id i) in H5.
  rewrite <- (Nat2Z.id j) in H5.
  rewrite nth_error_Znth in H5.
  2,3: rewrite Zlength_map; lia.
  rewrite <- (Znth_map _ heap_item_key) in H9. 2: lia.
  rewrite H5 in H9. rewrite Znth_map in H9. 2: lia.
  rewrite H9 in H11. lia.
Qed.

Lemma nat_inc_list_plus_1_Permutation: forall (i : Z),
  0 <= i ->
  Permutation (nat_inc_list (Z.to_nat (i + 1))) (i :: nat_inc_list (Z.to_nat i)).
Proof.
  intros.
  replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by lia.
  simpl. symmetry.
  rewrite Z2Nat.id; auto.
  apply Permutation_cons_append.
Qed.

Lemma Permutation_filter: forall A (L1 L2 : list A) (f : A -> bool),
  Permutation L1 L2 ->
  Permutation (filter f L1) (filter f L2).
Proof.
  intros. induction H.
  constructor. simpl. case (f x). constructor. trivial. trivial.
  simpl. case (f x); case (f y). constructor. constructor. reflexivity.
  constructor. reflexivity. reflexivity. transitivity (filter f l'); trivial.
Qed.

Lemma filter_map_comm: forall A B (f : A -> bool) (g : B -> bool) (h : A -> B) (L : list A),
  (forall x, f x = g (h x)) ->
  filter g (map h L) = map h (filter f L).
Proof.
  induction L; intros. reflexivity.
  simpl. rewrite <- H. case (f a); auto. simpl. f_equal. auto.
Qed.

Lemma filter_map_comm': forall A f g (L : list A),
  (forall x, f x = f (g x)) ->
  filter f (map g L) = map g (filter f L).
Proof. intros. rewrite filter_map_comm with (f := f); auto. Qed.

Lemma find_item_by_key_update_pri_by_key: forall L k op v np,
  find_item_by_key L k = [(k, op, v)] ->
  find_item_by_key (update_pri_by_key L k np) k = [(k, np, v)].
Proof.
  intros. unfold find_item_by_key, update_pri_by_key in *.
  rewrite filter_map_comm'. 2: { unfold update_pri_if_key. intros.
    destruct x as [[kk ?] ?].
    unfold heap_item_key. simpl.
    case (Z.eq_dec kk); case (Z.eq_dec _ kk); simpl; 
    case (Z.eq_dec _ k); simpl; intros; auto; exfalso; auto. }
  change (key_type * priority_type * payload_type)%type with heap_item.
  rewrite H.
  unfold update_pri_if_key, heap_item_key. simpl.
  case Z.eq_dec; trivial. destruct 1; trivial.
Qed.

Lemma Permutation_find_item_by_key: forall L1 L2 k,
  Permutation L1 L2 ->
  Permutation (find_item_by_key L1 k) (find_item_by_key L2 k).
Proof. intros. unfold find_item_by_key. apply Permutation_filter. trivial. Qed.

Lemma not_In_app: forall A x (L1 L2 : list A),
  ~ In x (L1 ++ L2) ->
  ~ In x L1 /\ ~ In x L2.
Proof.
  split; intro; apply H; apply in_or_app; auto.
Qed.

Lemma Permutation_two_eq: forall A (L : list A) x,
  Permutation L [x ; x] ->
  L = [x ; x].
Proof.
  intros. remember [x ; x]. revert Heql. induction H.
  * discriminate.
  * inversion 1. subst. symmetry in H. apply Permutation_length_1_inv in H. subst. trivial.
  * inversion 1. trivial.
  * intros. subst l''. spec IHPermutation2. trivial. specialize (IHPermutation1 IHPermutation2). subst l'. trivial.
Qed.

Lemma filter_empty: forall A f (L : list A),
  (forall x, In x L -> f x = false) ->
  filter f L = [].
Proof.
  induction L; intros. reflexivity.
  simpl. rewrite H. apply IHL. intros. apply H. right. trivial.
  left. trivial.
Qed.

Lemma find_item_by_key_app: forall L1 L2 k,
  find_item_by_key (L1 ++ L2) k = find_item_by_key L1 k ++ find_item_by_key L2 k.
Proof. intros. unfold find_item_by_key. rewrite filter_app. trivial. Qed.

Lemma filter_false_nil:
    forall A (l: list A) f,
      (forall a, In a l -> f a = false) ->
      filter f l = [].
  Proof. intros. apply filter_empty. trivial. Qed.
  
  Lemma find_item_by_key_finds_item:
    forall h item,
      In item h ->
      NoDup (map heap_item_key h) ->
      find_item_by_key h (heap_item_key item) =
      [item].
  Proof.
    intros.
    unfold find_item_by_key. induction h; [inversion H|].
    destruct H.
    - subst a. simpl.
      destruct (Z.eq_dec (heap_item_key item) (heap_item_key item)).
      2: exfalso; apply n; trivial. 
      simpl. simpl in H0.
      apply NoDup_cons_2 in H0.
      replace (filter
                 (fun item0 : heap_item =>
                    Z.eq_dec (heap_item_key item0) (heap_item_key item)) h)
        with (@nil heap_item); trivial.
      rewrite filter_false_nil; trivial.
      intros.
      rewrite <- not_true_iff_false.
      intro.
      apply (in_map heap_item_key) in H.
      replace (heap_item_key a) with (heap_item_key item) in H.
      apply H0; trivial.
      destruct (Z.eq_dec (heap_item_key a) (heap_item_key item)).
      + lia.
      + simpl in H1. inversion H1.
    - simpl.
      destruct (Z.eq_dec (heap_item_key a) (heap_item_key item)).
      + exfalso.
        simpl in H0.
        apply NoDup_cons_2 in H0. 
        apply H0. rewrite e. apply in_map; trivial.
      + simpl. apply IHh; trivial.
        simpl in H0.
        apply (NoDup_cons_1 _ (heap_item_key a)); trivial.
  Qed.

Lemma filter_absorb_map: forall A (f : A -> A) (g : A -> bool) L,
  (forall x, (g (f x) = g x) /\ ((g (f x) = false) \/ f x = x)) ->
  filter g (map f L) = filter g L.
Proof.
  induction L; auto; intros.
  simpl.
  case_eq (g (f a)); intro. destruct (H a). rewrite H0 in H2. destruct H2. discriminate.
  rewrite H1 in *. rewrite H0. rewrite H2, IHL; trivial.
  destruct (H a). rewrite H1 in H0. rewrite H0.
  apply IHL; auto.
Qed.

Lemma find_item_by_key_update_pri_by_key': forall L k1 k2 np,
  k1 <> k2 ->
  find_item_by_key (update_pri_by_key L k1 np) k2 = find_item_by_key L k2.
Proof.
  intros. unfold find_item_by_key, update_pri_by_key.
  rewrite filter_absorb_map. trivial. intros.
  unfold update_pri_if_key, heap_item_key. destruct x as [[? ?] ?].
  simpl. case Z.eq_dec; intro; simpl. subst k1. split; trivial.
  case Z.eq_dec; auto; intro; simpl. contradiction.
  case Z.eq_dec; simpl; split; auto.
Qed.

Lemma update_pri_by_key_keys_unaffected:
  forall l key newpri,
    map heap_item_key (update_pri_by_key l key newpri) = map heap_item_key l.
Proof.
  intros. induction l; trivial.
  simpl. rewrite IHl. f_equal.
  unfold update_pri_by_key, update_pri_if_key, heap_item_key.
  destruct (Z.eq_dec key (fst (fst a))); simpl fst; trivial.
Qed.

Lemma update_pri_by_key_payloads_unaffected:
  forall l key newpri,
    map heap_item_payload (update_pri_by_key l key newpri) = map heap_item_payload l.
Proof.
  intros. induction l; trivial.
  simpl. rewrite IHl. f_equal.
  unfold update_pri_by_key, update_pri_if_key, heap_item_payload, heap_item_key.
  destruct (Z.eq_dec key (fst (fst a))); simpl fst; trivial.
Qed.

Lemma In_update_pri_by_key: forall i L k np,
    In i (update_pri_by_key L k np) ->
    (In i L /\ heap_item_key i <> k) \/
    (exists oi, In oi L /\ 
                heap_item_key i = k /\ 
                heap_item_payload i = heap_item_payload oi /\ 
                heap_item_key i = heap_item_key oi /\
                heap_item_priority i = np).
Proof.
  intros.
  unfold update_pri_by_key in H.
  rewrite in_map_iff in H. destruct H as [oi [? ?]].
  revert H. unfold update_pri_if_key. case Z.eq_dec; intros.
  2: left; subst; auto.
  right. exists oi. split; trivial. subst i.
  unfold heap_item_key, heap_item_payload, heap_item_priority in *.
  simpl. tauto.
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

