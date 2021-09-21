Require Import VST.floyd.proofauto.
Require Import Coq.ZArith.ZArith.
Require Import CertiGraph.floyd_ext.closed_lemmas.
Require Export CertiGraph.kruskal.kruskal_edgelist.

Local Open Scope Z.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.

Definition MAX_EDGES:= 8. (*We can malloc, but it's not quite relevant*)
Definition t_struct_edge := Tstruct _edge noattr.
Definition t_wedgearray_graph := Tstruct _graph noattr.
Definition wedgerep := reptype t_struct_edge.
Instance wedgerep_inhabitant : Inhabitant wedgerep :=
                                    (Vundef, (Vundef, Vundef)).

(*Warning: reptype of a struct doesn’t destruct nicely*)
Definition def_wedgerep (x: reptype t_struct_edge) :=
  is_int I32 Signed (fst x) /\
  is_int I32 Signed (fst (snd x)) /\
  is_int I32 Signed (snd (snd x)).

(*Comparator*)
Definition wedge_le (x y: wedgerep) :=
match x, y with
| (Vint x',_),(Vint y',_) => Int.signed x' <= Int.signed y'
| _,_ => False
end.

Lemma wedge_le_refl: forall x, def_wedgerep x -> wedge_le x x.
Proof.
  intros. destruct H as [? [? ?]].
  unfold wedge_le. 
  rewrite (surjective_pairing x).
  destruct (fst x); trivial. lia.
Qed.

Definition wedge_eq (x y: wedgerep) :=
match x, y with
| (Vint x',_),(Vint y',_) => Int.signed x' = Int.signed y'
| _,_ => False
end.

Lemma wedge_eq_refl:
  forall x, def_wedgerep x -> wedge_eq x x.
Proof.
  intros. destruct H as [? [? ?]].
  unfold wedge_eq. rewrite (surjective_pairing x).
  destruct (fst x); trivial.
Qed.

Lemma wedge_eq_symm:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_eq x y -> wedge_eq y x.
Proof.
  intros.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  rewrite (surjective_pairing x) in *.
  rewrite (surjective_pairing y) in *.
  unfold wedge_eq in *.
  destruct x, y; simpl fst in *; simpl snd in *.
  destruct y, y0; trivial. lia.
Qed.

Definition wedge_lt (x y: wedgerep) :=
match x, y with
| (Vint x',_),(Vint y',_) => Int.signed x' < Int.signed y'
| _,_ => False
end.

Lemma wedge_lt_irrefl:
   forall a, def_wedgerep a -> wedge_lt a a -> False.
Proof.
intros.
destruct H as [? [? ?]].
unfold wedge_lt in H0.
rewrite (surjective_pairing a) in *.
destruct (fst a); trivial. lia.
Qed.

Lemma wedge_lt_le:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_lt x y -> wedge_le x y.
Proof.
intros.
destruct H as [? [? ?]].
destruct H0 as [? [? ?]].
unfold wedge_lt in H1.
unfold wedge_le.
rewrite (surjective_pairing x) in *.
rewrite (surjective_pairing y) in *.
destruct x, y.
simpl fst in *. simpl snd in *.
destruct y0, y; trivial. lia.
Qed.

Lemma wedge_lt_le_flip:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_lt x y -> ~ (wedge_le y x).
Proof.
  unfold not; intros.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  unfold wedge_le in H2; unfold wedge_lt in H1.
  rewrite (surjective_pairing x) in *.
  rewrite (surjective_pairing y) in *.
  destruct x, y.
  simpl fst in *. simpl snd in *.
  destruct y0, y; trivial. lia.
Qed.

Lemma wedge_lt_eq_flip:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_lt x y -> ~ (wedge_eq y x).
Proof.
  unfold not; intros.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  unfold wedge_eq in H2; unfold wedge_lt in H1.
  rewrite (surjective_pairing x) in *.
  rewrite (surjective_pairing y) in *.
  destruct x, y.
  simpl fst in *. simpl snd in *.
  destruct y0, y; trivial. lia.
Qed.

Lemma wedge_le_lt_flip:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_le x y -> ~ (wedge_lt y x).
Proof.
  unfold not; intros.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  unfold wedge_lt in H2; unfold wedge_le in H1.
  rewrite (surjective_pairing x) in *.
  rewrite (surjective_pairing y) in *.
  destruct x, y.
  simpl fst in *. simpl snd in *.
  destruct y0, y; trivial. lia.
Qed.

Lemma wedge_eq_lt_flip:
  forall x y, def_wedgerep x -> def_wedgerep y -> wedge_eq x y -> ~ (wedge_lt y x).
Proof.
  unfold not; intros.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  unfold wedge_lt in H2; unfold wedge_eq in H1.
  rewrite (surjective_pairing x) in *.
  rewrite (surjective_pairing y) in *.
  destruct x, y.
  simpl fst in *. simpl snd in *.
  destruct y0, y; trivial. lia.
Qed.

Lemma is_wedge_middle:
  forall (before: list wedgerep) (bl: list wedgerep) (after: list wedgerep) i,
       Forall def_wedgerep bl ->
       Zlength before <= i < Zlength before + Zlength bl ->
       is_int I32 Signed (fst (Znth i (before ++ bl ++ after))) /\
       is_int I32 Signed (fst (snd (Znth i (before ++ bl ++ after)))) /\
       is_int I32 Signed (snd (snd (Znth i (before ++ bl ++ after)))).
Proof.
intros.
rewrite app_Znth2 by lia. rewrite app_Znth1 by lia.
eapply Forall_Znth; eauto. lia.
Qed.

(* For the sorting *)

Require Import RelationClasses.
Require Import CertiGraph.binheap.binary_heap_model.
Require Import CertiGraph.binheap.binary_heap_Zmodel.

Definition heap_item : Type := int * (int * int).
(* This should be x >= y *)
Definition cmp (x y: heap_item) := negb (Int.lt (fst x) (fst y)).
Definition cmp_rel (a b : heap_item) : Prop :=
  cmp a b = true.
Lemma cmp_dec: forall a a', {cmp_rel a a'} + {~cmp_rel a a'}.
Proof.
  intros [? ?] [? ?]. unfold cmp_rel, cmp. simpl. case (Int.lt i i0); simpl; auto.
Qed. 
Instance cmp_po: PreOrder cmp_rel.
Proof.
  constructor. intros [? ?]. red. unfold cmp. simpl. case_eq (Int.lt i i); auto; intro. exfalso.
  apply lt_inv in H. lia.
  intros [? ?] [? ?] [? ?]. unfold cmp_rel, cmp. simpl. 
  case_eq (Int.lt i i0); auto. discriminate.
  case_eq (Int.lt i i0); auto. discriminate.
  case_eq (Int.lt i i0); auto. discriminate. simpl.
  intros ? _ _ _.
  apply lt_false_inv in H.
  intro.
  assert (Int.lt i0 i1 = false). {
    rewrite <- (negb_involutive (Int.lt i0 i1)). rewrite H0. trivial. }
  apply lt_false_inv in H1.
  case_eq (Int.lt i i1). 2: trivial. intro.
  apply lt_inv in H2. lia.
Qed.
Lemma cmp_linear: forall a b,
  cmp_rel a b \/ cmp_rel b a.
Proof.
  intros [? ?] [? ?]. unfold cmp_rel, cmp; simpl.
  case_eq (Int.lt i i0); auto. intro. 
  right.
  case_eq (Int.lt i0 i); auto. intro. exfalso. 
  apply lt_inv in H. apply lt_inv in H0.
  lia.
Qed.

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

Lemma Zparent_repr: forall i,
  0 < i <= Int.max_unsigned ->
  Int.repr (Zparent i) = Int.divu (Int.repr (i - 1)) (Int.repr 2).
Proof.
  intros. unfold Int.divu. repeat rewrite Int.unsigned_repr.
  2,3: rep_lia. rewrite Zparent_unfold. trivial. lia.
Qed.

Definition heap_item_rep (i : heap_item) : wedgerep :=
  (Vint (fst i), (Vint (fst (snd i)), Vint (snd (snd i)))).

Definition hitem (sh : share) (i : heap_item) : val -> mpred :=
  data_at sh t_struct_edge (heap_item_rep i).

Definition harray (sh : share) (contents : list heap_item) : val -> mpred :=
  data_at sh (tarray t_struct_edge (Zlength contents)) (map heap_item_rep contents).

Lemma harray_emp: forall sh arr,
  harray sh [] arr |-- emp.
Proof.
  unfold harray. intros. rewrite data_at_isptr. entailer. rewrite data_at_zero_array_eq; auto.
Qed.

Lemma fold_harray': forall sh L i arr,
  i = Zlength L ->
  data_at sh (tarray t_struct_edge i) (map heap_item_rep L) arr = harray sh L arr.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma fold_harray: forall sh L arr,
  data_at sh (tarray t_struct_edge (Zlength L)) (map heap_item_rep L) arr = harray sh L arr.
Proof. reflexivity. Qed.

Lemma harray_split: forall sh L1 L2 ptr,
  harray sh (L1 ++ L2) ptr = 
  ((harray sh L1 ptr) * 
   (harray sh L2 (field_address0 (tarray t_struct_edge (Zlength (L1 ++ L2))) [ArraySubsc (Zlength L1)] ptr)))%logic.
Proof.
  intros. unfold harray.
  rewrite map_app.
  rewrite (split2_data_at_Tarray_app (Zlength L1) (Zlength (L1 ++ L2)) sh t_struct_edge (map heap_item_rep L1) (map heap_item_rep L2)).
  2: rewrite Zlength_map; reflexivity. 2: rewrite Zlength_app, Zlength_map; lia.
  rewrite Zlength_app.
  replace (Zlength L1 + Zlength L2 - Zlength L1) with (Zlength L2) by lia.
  trivial.
Qed.

