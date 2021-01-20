Require Import VST.floyd.proofauto.
Require Import CertiGraph.binheap.binary_heap.
Require Import CertiGraph.binheap.binary_heap_model.
Require Import CertiGraph.binheap.binary_heap_Zmodel.
Require Import RelationClasses.
(* Require Import VST.floyd.sublist. *)

Set Nested Proofs Allowed.

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
Definition heap_ordered_bounded (L : list heap_item) (b : Z) := 
  binary_heap_model.heapOrdered_bounded heap_item cmp_rel L (Z.to_nat b).
Definition weak_heap_ordered_bottom_up (L : list heap_item) (x : Z) := 
  binary_heap_model.weak_heapOrdered2 heap_item cmp_rel L (Z.to_nat x).
Definition weak_heap_ordered_top_down_bounded (L : list heap_item) (b : Z) (x : Z) := 
  binary_heap_model.weak_heapOrdered_bounded heap_item cmp_rel L (Z.to_nat b) (Z.to_nat x).
Definition swim := binary_heap_model.swim heap_item cmp_rel cmp_dec.
Definition sink L i := binary_heap_model.sink heap_item cmp_rel cmp_dec (L,i).
Definition build_heap_helper L i := binary_heap_model.build_heap_helper heap_item cmp_rel cmp_dec L i.
(* Definition insert := binary_heap_model.insert heap_item cmp_rel cmp_dec. *)
(* Definition remove_min := binary_heap_model.remove_min heap_item cmp_rel cmp_dec. *)

Lemma Zparent_repr: forall i,
  0 < i <= Int.max_unsigned ->
  Int.repr (Zparent i) = Int.divu (Int.repr (i - 1)) (Int.repr 2).
Proof.
  intros. unfold Int.divu. repeat rewrite Int.unsigned_repr.
  2,3: rep_lia. rewrite Zparent_unfold. trivial. lia.
Qed.

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
    (!! (2 * (heap_capacity h - 1) <= Int.max_unsigned)) &&
    (data_at Tsh t_pq (Vint (Int.repr (heap_capacity h)), (Vint (Int.repr (heap_size h)), arr)) pq *
       harray ((heap_items h) ++ junk) arr).
