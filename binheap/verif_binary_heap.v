Require Import RelationClasses.
Require Import Sorting.
Require Import VST.floyd.proofauto.
Require Import CertiGraph.binheap.binary_heap_model.
Require Import CertiGraph.binheap.binary_heap_Zmodel.
Require Import CertiGraph.binheap.binary_heap.
Require Import CertiGraph.binheap.env_binary_heap.

Set Nested Proofs Allowed.

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
    PROP (0 <= i < Zlength arr_contents;
          weak_heap_ordered_bottom_up arr_contents i)
    PARAMS (Vint (Int.repr i); arr)
    GLOBALS ()
    SEP (harray arr_contents arr)
  POST [tvoid]
    EX arr_contents' : list (int * int),
      PROP (heap_ordered arr_contents'; Permutation arr_contents arr_contents')
      LOCAL ()
      SEP (harray arr_contents' arr).

Definition sink_spec :=
  DECLARE _sink WITH i : Z, arr: val, arr_contents: list heap_item, first_available : Z, b : Z
  PRE [tuint, tptr t_item, tuint]
    PROP (0 <= i <= Zlength arr_contents; 
          first_available = Zlength arr_contents;
          (i = Zlength arr_contents -> (2 * i) <= Int.max_unsigned);
          (i < Zlength arr_contents -> (2 * (first_available - 1) <= Int.max_unsigned)); (* i = fa - 1 -> (2 * i + 1) = 2 * fa - 1, must be representable *)
          weak_heap_ordered_top_down_bounded arr_contents b i)
    PARAMS (Vint (Int.repr i); arr; Vint (Int.repr first_available))
    GLOBALS ()
    SEP (harray arr_contents arr)
  POST [tvoid]
    EX arr_contents' : list heap_item,
      PROP (heap_ordered_bounded arr_contents' b;
            Permutation arr_contents arr_contents')
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

Definition build_heap_spec :=
  DECLARE _build_heap WITH arr: val, arr_contents: list heap_item, size : Z
  PRE [tptr t_item, tuint]
    PROP (size > 0 ; (* Required because PARENT subtracts 1u *)
          Zlength arr_contents = size)
    PARAMS (arr; Vint (Int.repr size))
    GLOBALS ()
    SEP (harray arr_contents arr)
  POST [tvoid]
  EX arr_contents' : list heap_item,
    PROP (heap_ordered arr_contents';
          Permutation arr_contents arr_contents')
    LOCAL ()
    SEP (harray arr_contents' arr).

Definition heapsort_rev_spec :=
  DECLARE _heapsort_rev WITH arr : val, arr_contents : list heap_item, size : Z
  PRE [tptr t_item, tuint]
    PROP (size > 0 ;
          Zlength arr_contents = size)
    PARAMS (arr; Vint (Int.repr size))
    GLOBALS ()
    SEP (harray arr_contents arr)
  POST [tvoid]
  EX arr_contents' : list heap_item,
    PROP (Sorted (Basics.flip cmp_rel) arr_contents';
          Permutation arr_contents arr_contents')
    LOCAL ()
    SEP (harray arr_contents' arr).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ exch_spec ; less_spec ; swim_spec ; sink_spec ; 
                                   remove_min_nc_spec ; insert_nc_spec ; 
                                   size_spec ; capacity_spec ; 
                                   build_heap_spec ; heapsort_rev_spec ]).

Lemma body_heapsort: semax_body Vprog Gprog f_heapsort_rev heapsort_rev_spec.
Proof.
  start_function.
  assert_PROP (2 * (size - 2) <= Int.max_unsigned). { 
    go_lower. unfold harray. saturate_local. apply prop_right.
    destruct H1 as [? [? [? [? ?]]]].
    destruct arr; try contradiction. simpl in H5. rep_lia. }
  forward_call (arr, arr_contents, size).
  Intros arr_contents'.
  forward.
  forward_loop (EX s : Z, EX arr_contents1 : list heap_item, EX arr_contents2 : list heap_item,
                 PROP (s > 0 ;
                       s = Zlength arr_contents1;
                       heap_ordered arr_contents1;
                       Sorted (Basics.flip cmp_rel) arr_contents2;
                       Forall (fun x => HdRel (Basics.flip cmp_rel) x arr_contents2) arr_contents1;
                       Permutation arr_contents (arr_contents1 ++ arr_contents2))
                 LOCAL (temp _arr arr; temp _active (Vint (Int.repr s)))
                 SEP (harray (arr_contents1 ++ arr_contents2) arr)).
  { Exists size arr_contents' (@nil heap_item).
    rewrite app_nil_r. entailer!. split. apply Permutation_Zlength. trivial.
    apply Forall_forall. constructor. }
  Intros s arrc1 arrc2.
  generalize (Permutation_Zlength _ _ _ H9); intro.
  rewrite Zlength_app in H10.
  forward_if.
  2: { assert (s = 1) by rep_lia. subst s.
       destruct arrc1. rewrite Zlength_nil in H12; lia.
       destruct arrc1. 2: do 2 rewrite Zlength_cons in H12; rep_lia.
       rewrite H12.
       forward. Exists (h :: arrc2). entailer!. 2: apply derives_refl.
       constructor. trivial. rewrite Forall_forall in H8.
       apply H8. left. trivial. }
  forward.
  rewrite harray_split. Intros.
  forward_call (0, s-1, arr, arrc1). 
  destruct arrc1. rewrite Zlength_nil in H5. lia.
  generalize (foot_split_spec _ (h :: arrc1)). case foot_split. destruct o. 2: intros [? ?]; subst; discriminate.
  intros. destruct l. destruct arrc1. 2: discriminate. inversion H12. subst h0. clear H12.
  { (* Degenerate case: only one item, which simplies nicely after chaning the bound! *)
    rewrite Zlength_one in H5. lia. }

(*  subst s. simpl.
    rewrite Zexchange_eq.
    rewrite Int.sub_idem.
    change [h] with (nil ++ [h]) at 1.
    rewrite harray_split. Intros.
    assert (weak_heap_ordered_top_down_bounded [] 0 0). {
      apply weak_heapOrdered_bounded_root_weak_heapOrdered.
      apply hOwhO.
      apply cmp_po.
      apply heapOrdered_empty. }
    forward_call (0, arr, @nil heap_item, 0, 0).
    rewrite Zlength_nil. simpl. intuition. rep_lia.
    Intros arrcx.
    apply Permutation_nil in H12. subst arrcx.
    Exists 0 (@nil heap_item) (h :: arrc2). entailer!.
    split. apply heapOrdered_empty. constructor. trivial. inversion H7. trivial.
    rewrite <- harray_split. simpl. change (h :: arrc2) with ([h] ++ arrc2).
    rewrite <- harray_split. apply derives_refl. } *)

  (* Main line *)
  assert (h1 = h) by (inversion H12; auto). subst h1.
  rewrite H12 in *. clear H12 arrc1.
  replace (s - 1) with (Zlength (h :: l)).
  2: autorewrite with sublist in *; rep_lia.
  rewrite Zexchange_head_foot.
  rewrite harray_split. Intros.
  forward_call (0, arr, (h0 :: l), s-1, 0).
  { split. autorewrite with sublist in *. rep_lia.
    apply weak_heapOrdered_bounded_root_weak_heapOrdered.
    eapply weak_heapOrdered_root.
    apply heapOrdered_cutfoot in H6. apply H6. }
  Intros arrc1. Exists (s-1) arrc1 (h :: arrc2). entailer!.
  { split. apply Permutation_Zlength in H13. autorewrite with sublist in *. trivial.
    split. apply heapOrdered_bounded_root_heapOrdered. apply H12.
    split. constructor. trivial. inversion H8. trivial.
    split.
    * apply Forall_forall. intros. constructor.
      symmetry in H13.
      generalize (Permutation_in x H13 H0); intro.
      generalize (root_minimal _ cmp_rel cmp_po _ H6 h eq_refl); intro.
      rewrite Forall_forall in H14. apply H14.
      rewrite <- app_comm_cons. right.
      apply in_or_app.
      destruct H5. subst x. right. left. trivial. auto.
    * apply Permutation_trans with (((h :: l) ++ [h0]) ++ arrc2). trivial.
      change (h :: arrc2) with ([h] ++ arrc2). rewrite app_assoc.
      apply Permutation_app. 2: apply Permutation_refl.
      apply Permutation_trans with (h :: arrc1).
      2: apply Permutation_cons_append.
      simpl. constructor.
      apply Permutation_app_comm_trans. apply H13. }
  { apply Permutation_Zlength in H13.
    rewrite Zlength_app. rewrite H13. rewrite <- Zlength_app.
    rewrite <- harray_split.
    rewrite Zlength_app.
    replace (Zlength ((h :: l) ++ [h0])) with (Zlength (arrc1 ++ [h])).
    rewrite <- Zlength_app.
    rewrite <- harray_split. rewrite <- app_assoc. apply derives_refl.
    autorewrite with sublist in *. lia. }
Qed.

Lemma body_build_heap: semax_body Vprog Gprog f_build_heap build_heap_spec.
Proof.
  start_function.
  assert_PROP (2 * (size - 1) <= Int.max_unsigned). {
    go_lower. unfold harray. saturate_local. apply prop_right.
    destruct H1 as [? [? [? [? ?]]]].
    destruct arr; try contradiction. simpl in H5. rep_lia. }
  assert (Zlength arr_contents <= Int.max_unsigned) by rep_lia.
  forward.
  rewrite sub_repr. rewrite <- Zparent_repr. 2: lia.
  forward_loop (EX s : Z, EX arr_contents' : list heap_item,
                 PROP (0 <= s < Zlength arr_contents;
                       weak_heap_ordered_top_down_bounded arr_contents' s s;
                       Permutation arr_contents arr_contents')
                 LOCAL (temp _arr arr; temp _size__1 (Vint (Int.repr size)); temp _start (Vint (Int.repr s)))
                 SEP (harray arr_contents' arr)).
  { Exists (Zparent size) arr_contents. entailer!.
    split. rewrite Zparent_unfold. 2: lia.
    split. apply Z_div_pos; lia.
    eapply Z.le_lt_trans.
    2: apply Z.div_lt.
    apply Z.div_le_mono. 1,2,3,4: lia.
    red. generalize (weak_heapOrdered_bounded_half _ cmp_rel arr_contents); intro.
    unfold Zparent. rewrite ZtoNat_Zlength, Nat2Z.id. trivial. }
  Intros s arr_contents'.
  generalize (Permutation_Zlength _ _ _ H5); intro.
  forward_call (s, arr, arr_contents', size, s).
  Intros arr_contents''.
  forward_if (s > 0).
  { forward. subst s. Exists arr_contents''. entailer!.
    split. 2: eapply Permutation_trans; eauto.
    apply heapOrdered_bounded_root_heapOrdered. apply H7. }
  { forward. entailer!. }
  forward.
  Exists (s - 1) arr_contents''. entailer!.
  split. 2: eapply Permutation_trans; eauto.
  red in H7. apply hObU_whObU_pred.
  replace (1 + Z.to_nat (s-1))%nat with (Z.to_nat s) by rep_lia. trivial.
Qed.

Lemma body_sink: semax_body Vprog Gprog f_sink sink_spec.
Proof.
  start_function.
  assert (Hc : i = Zlength arr_contents \/ 0 <= i < Zlength arr_contents) by lia. destruct Hc as [Hc | Hc].
* (* Special case: oob sink, used when removing the last element of the heap. *)
  forward_loop ( PROP () LOCAL (temp _k (Vint (Int.repr i)); temp _first_available (Vint (Int.repr first_available))) SEP (harray arr_contents arr) ).
  entailer!.
  forward_if False. exfalso. lia. (* This is where the bound is needed.  For some reason I need a slightly different bound than I expect. *)
  forward.
  Exists arr_contents. entailer!.
  eapply weak_heapOrdered_bounded_oob. 2: apply H3.
  rewrite Zlength_correct, Nat2Z.id. apply le_refl.
* (* Main line *)
  assert (Hx : i < Zlength arr_contents) by lia. specialize (H2 Hx). clear H1 Hx. rename H2 into H1. rename H3 into H2.
  forward_loop (EX i' : Z, EX arr_contents' : list heap_item, 
                 PROP (0 <= i' < Zlength arr_contents; 
                       sink arr_contents (Z.to_nat i) = sink arr_contents' (Z.to_nat i'))
                 LOCAL (temp _k (Vint (Int.repr i')); temp _arr arr; temp _first_available (Vint (Int.repr first_available)))
                 SEP (harray arr_contents' arr)).
  Exists i arr_contents. entailer!.
  Intros i' arr_contents'.
  assert (Zlength arr_contents = Zlength arr_contents'). { unfold sink in H4. 
    generalize (sink_permutation _ cmp_rel cmp_dec arr_contents (Z.to_nat i)); intro.
    generalize (sink_permutation _ cmp_rel cmp_dec arr_contents' (Z.to_nat i')); intro.
    apply Permutation_Zlength in H5. apply Permutation_Zlength in H6. congruence. }
  forward_if (Zleft_child i' < first_available).
    { forward. entailer!. rewrite Zleft_child_unfold; lia. }
    { forward. (* Prove postcondition *)
      Exists arr_contents'. entailer!. unfold sink at 2 in H4.
      rewrite <- Zleft_child_unfold in H6; try lia.
      unfold Zleft_child in H6. rewrite H5 in H6. rewrite Zlength_correct in H6.
      erewrite sink_done in H4. 2: apply Znth_nth_error; lia.
      rewrite <- H4. { split. 
      * apply sink_hO_bounded. apply cmp_po. apply cmp_linear. apply H2. 
      * apply sink_permutation. }
      intros. assert (left_child (Z.to_nat i') < length arr_contents')%nat by (apply nth_error_Some; congruence).
      lia.
      intros. assert (right_child (Z.to_nat i') < length arr_contents')%nat by (apply nth_error_Some; congruence).
      unfold right_child in H7. lia. }
  forward.
  rewrite mul_repr, add_repr. rewrite <- Zleft_child_unfold. 2: lia.
  forward_if (EX b : bool, PROP (if b then Zright_child i' <  first_available /\  cmp_rel (Znth (Zright_child i') arr_contents') (Znth (Zleft_child i') arr_contents')
                                      else Zright_child i' >= first_available \/ ~cmp_rel (Znth (Zright_child i') arr_contents') (Znth (Zleft_child i') arr_contents') )
                           LOCAL (temp _t'1 (Val.of_bool b); temp _k (Vint (Int.repr i')); temp _j (Vint (Int.repr (Zleft_child i'))); temp _arr arr; temp _first_available (Vint (Int.repr first_available))) 
                           SEP (harray arr_contents' arr)).
    { forward_call (Zright_child i', Zleft_child i', arr, arr_contents').
        { entailer!. simpl. repeat f_equal. rewrite Zright_child_unfold, Zleft_child_unfold; lia. }
        { rewrite Int.unsigned_repr in H7. rewrite Zright_child_unfold, Zleft_child_unfold in *; lia.
          (* Here is where we seem to need the precise bound on first_available? *)
          rewrite Zleft_child_unfold in *; rep_lia. }
      forward. Exists (cmp (Znth (Zright_child i') arr_contents') (Znth (Zleft_child i') arr_contents')).
      unfold cmp_rel. rewrite Zright_child_unfold, Zleft_child_unfold in *.
      rewrite Int.unsigned_repr in H7. 2,3,4,5: rep_lia.
      case cmp; entailer!. }
    { forward. Exists false.
      rewrite Zright_child_unfold, Zleft_child_unfold in *. rewrite Int.unsigned_repr in H7. 
      entailer!. all: rep_lia. }
  Intro bo.
  set (j' := if bo then Zright_child i' else Zleft_child i').
  forward_if (PROP (if bo then Zright_child i' <  first_available /\  cmp_rel (Znth (Zright_child i') arr_contents') (Znth (Zleft_child i') arr_contents')
                          else Zright_child i' >= first_available \/ ~cmp_rel (Znth (Zright_child i') arr_contents') (Znth (Zleft_child i') arr_contents') )
              LOCAL (temp _t'1 (Val.of_bool bo); temp _k (Vint (Int.repr i')); temp _j (Vint (Int.repr j')); temp _arr arr; temp _first_available (Vint (Int.repr first_available))) 
              SEP (harray arr_contents' arr)).
    { forward. subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. entailer!. tauto. }
    { forward. entailer!. }
    Intros. (* Need to get the PROP above the bar... why doesn't forward_call do this for me? *)
    forward_call (i', j', arr, arr_contents'). { subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. destruct bo; lia. }
    forward_if (~cmp_rel (Znth i' arr_contents') (Znth j' arr_contents')).
      { forward. (* Prove function postcondition *)
        Exists arr_contents'. entailer!. unfold sink at 2 in H4. erewrite sink_done in H4; intros.
        rewrite <- H4. split. apply sink_hO_bounded. apply cmp_po. apply cmp_linear. apply H2.
        apply sink_permutation.
        apply Znth_nth_error. lia.
        * rewrite <- (Nat2Z.id (left_child _)) in H0. change (Z.of_nat _) with (Zleft_child i') in H0.
          rewrite Znth_nth_error in H0. 2: rewrite Zright_child_unfold, Zleft_child_unfold in *; lia.
          inversion H0. subst b0. clear H0.
          destruct bo; subst j'; auto.
          transitivity (Znth (Zright_child i') arr_contents'); tauto.
        * assert (0 <= Zright_child i' < Zlength arr_contents'). {
            split. unfold Zright_child. lia.
            apply Z2Nat.inj_lt. unfold Zright_child. lia. lia.
            rewrite ZtoNat_Zlength.
            eapply nth_error_Some.
            unfold Zright_child.
            rewrite Nat2Z.id. congruence. }
          rewrite <- (Nat2Z.id (right_child _)) in H0. change (Z.of_nat _) with (Zright_child i') in H0.
          rewrite Znth_nth_error in H0; try lia.
          inversion H0. subst b0. clear H0.
          destruct bo; subst j'. tauto. destruct H7. lia.
          transitivity (Znth (Zleft_child i') arr_contents'). trivial.
          destruct (cmp_linear (Znth (Zleft_child i') arr_contents') (Znth (Zright_child i') arr_contents')); auto.
          contradiction. }
      { forward.  entailer!. unfold cmp_rel, j' in H0. congruence. }
    forward_call (i', j', arr, arr_contents').
      { subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. destruct bo; lia. }
    forward.
    (* Prove loop invariant at loop bottom *)
    Exists j' (Zexchange arr_contents' i' j').
    entailer!. split. subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. destruct bo; lia.
    unfold sink at 2. unfold Zexchange. erewrite sink_step. apply H4.
    apply Znth_nth_error; lia.
    unfold left_child. replace (1 + Z.to_nat i' + Z.to_nat i')%nat with (Z.to_nat (2 * i' + 1)) by lia.
    apply Znth_nth_error.
    split. lia. rewrite <- Zleft_child_unfold; try lia.
    rewrite <- Zleft_child_unfold; try lia.
    case_eq (nth_error arr_contents' (right_child (Z.to_nat i'))); intros.
    + (* From H0... feels like it should be a lemma. *)
      assert (h = Znth (Zright_child i') arr_contents'). {
        rewrite <- (nat_of_Z_eq (right_child _)) in H0.
        rewrite Znth_nth_error in H0. inversion H0. trivial.
        assert ((Z.to_nat (Z.of_nat (right_child (Z.to_nat i')))) < length arr_contents')%nat by (apply nth_error_Some; congruence).
        rewrite Zlength_correct. lia. } subst h.
      (* Probably another lemma... *)
      assert (Zright_child i' < Zlength arr_contents'). {
        assert (right_child (Z.to_nat i') < length arr_contents')%nat by (apply nth_error_Some; congruence).
        unfold Zright_child. rewrite Zlength_correct. lia. }
      clear H0. subst j'.
      destruct bo.
      - right. split. unfold Zright_child. lia. tauto.
      - left. split. unfold Zleft_child. lia. destruct H7. lia. tauto.
    + subst j'. destruct bo.
      - rewrite H5 in H7. apply nth_error_None in H0. destruct H7. unfold Zright_child in H7. rewrite Zlength_correct in H7. lia.
      - split. unfold Zleft_child. lia. tauto.
Time Qed.

Lemma body_swim: semax_body Vprog Gprog f_swim swim_spec.
Proof.
  start_function.
  assert_PROP (Zlength arr_contents <= Int.max_unsigned) as Hz. 
    { go_lower. unfold harray. saturate_local. apply prop_right.
      destruct H1 as [? [? [? [? ?]]]].
      destruct arr; try contradiction. simpl in H5. rep_lia. }
  forward_loop (EX i' : Z, EX arr_contents' : list heap_item, 
                PROP (0 <= i' < Zlength arr_contents; 
                      swim arr_contents (Z.to_nat i) = swim arr_contents' (Z.to_nat i'))
                LOCAL (temp _k (Vint (Int.repr i')); temp _arr arr)
                SEP (harray arr_contents' arr)).
  Exists i arr_contents. entailer!.
  Intros i' arr_contents'.
  assert (Zlength arr_contents = Zlength arr_contents'). {
    unfold swim in H2. 
    generalize (swim_permutation _ cmp_rel cmp_dec arr_contents (Z.to_nat i)); intro.
    generalize (swim_permutation _ cmp_rel cmp_dec arr_contents' (Z.to_nat i')); intro.
    apply Permutation_Zlength in H3. apply Permutation_Zlength in H4. congruence. }
  generalize (parent_le (Z.to_nat i')); intro Hq.
  assert (Hx: i' = 0 \/ i' > 0) by lia.
  forward_if (EX b : bool, PROP (if b then i' > 0 /\  cmp_rel (Znth i' arr_contents') (Znth (Zparent i') arr_contents')
                                      else i' = 0 \/ ~cmp_rel (Znth i' arr_contents') (Znth (Zparent i') arr_contents') )
                           LOCAL (temp _t'1 (Val.of_bool b); temp _k (Vint (Int.repr i')); temp _arr arr) 
                           SEP (harray arr_contents' arr)).
    { (* if-branch *)
      destruct Hx as [Hx | Hx]. subst i'. inversion H4.
      forward_call (i', Zparent i', arr, arr_contents').
      { entailer!. simpl. rewrite Zparent_repr. trivial. lia. }
      { assert (parent (Z.to_nat i') <= (Z.to_nat i'))%nat by apply parent_le. unfold Zparent. lia. }
      forward. unfold cmp_rel. case (cmp (Znth i' arr_contents') (Znth (Zparent i') arr_contents')).
      Exists true. entailer!.
      Exists false. entailer!. }
    { (* else-branch *)
      forward. Exists false. entailer!. }
  Intro b.
  forward_if (PROP (i' > 0 /\ cmp_rel (Znth i' arr_contents') (Znth (Zparent i') arr_contents'))
              LOCAL (temp _k (Vint (Int.repr i')); temp _arr arr)
              SEP (harray arr_contents' arr)).
    { subst b. forward. entailer!. tauto. }
    { subst b. forward. (* Prove postcondition *)
      Exists arr_contents'. entailer!. split.
      { assert (heap_ordered (swim arr_contents (Z.to_nat i))). { apply swim_hO; auto. apply cmp_po. apply cmp_linear. }
        unfold swim at 2 in H2. destruct H5.
        * subst i'. simpl in H2. rewrite swim_0 in H2. rewrite <- H2. trivial. 
        * erewrite swim_done in H2; eauto. rewrite <- H2. trivial.
          apply Znth_nth_error; lia.
          unfold Zparent. rewrite <- Znth_nth_error; try lia.
          rewrite Nat2Z.id. trivial. }
      { unfold swim in H2. 
        generalize (swim_permutation _ cmp_rel cmp_dec arr_contents (Z.to_nat i)); intro.
        generalize (swim_permutation _ cmp_rel cmp_dec arr_contents' (Z.to_nat i')); intro.
        rewrite H2 in H4. etransitivity. apply H4. symmetry. trivial. } }
  forward_call (i', Zparent i', arr, arr_contents').
    { entailer!. simpl. rewrite Zparent_repr. trivial. lia. }
    { unfold Zparent. lia. }
  forward.
  Exists (Zparent i') (Zexchange arr_contents' i' (Zparent i')).
  entailer!. split. unfold Zparent. lia.
  split.
  * destruct H4.
    unfold swim, Zparent, Zexchange in *. rewrite Nat2Z.id. erewrite swim_step. congruence.
    rewrite H3, Zlength_correct in H1.
    4: apply H5. 2: apply Znth_nth_error.
    3: rewrite <- Znth_nth_error. 3: rewrite Nat2Z.id; trivial.
    1,2,3: lia.
  * rewrite Zparent_repr. trivial. lia.
Time Qed.

Lemma body_insert_nc: semax_body Vprog Gprog f_insert_nc insert_nc_spec.
Proof.
  start_function.
  unfold valid_pq.
  Intros arr junk.
  destruct junk. { exfalso. unfold heap_size, heap_capacity in *. rewrite Zlength_app, Zlength_nil in H2. lia. }
  change (h0 :: junk) with ([h0] ++ junk) in *. rewrite app_assoc in *.
  rewrite harray_split. Intros.
  assert (0 <= heap_size h) by apply Zlength_nonneg.
  forward. unfold harray. entailer!.
  forward. unfold hitem.
  forward.
  unfold harray at 1.
  forward. entailer!. rewrite Zlength_app, Zlength_one. unfold heap_size in *. lia.
  forward.
  forward.
  forward. { (* C typing issue? *) entailer!. apply H10. discriminate. }
  forward. entailer!. rewrite Zlength_app, Zlength_one. unfold heap_size in *. lia.
  forward.
  forward.
  (* Just before the call, let's do some cleanup *)
  deadvars!.
  rewrite upd_Znth_overwrite, upd_Znth_same, map_app, upd_Znth_app2, Zlength_map.
  unfold heap_size at 3. rewrite Z.sub_diag.
  simpl fst. change (Vint (fst iv), Vint (snd iv)) with (heap_item_rep iv). rewrite upd_Znth_map.
  rewrite <- map_app. rewrite upd_Znth0.
  2,3,4: autorewrite with sublist; unfold heap_size in *; lia.
  replace (Zlength (heap_items h ++ [h0])) with (Zlength (heap_items h ++ [iv])). 
  2: do 2 rewrite Zlength_app, Zlength_one; lia.
  forward_call (heap_size h, arr, heap_items h ++ [iv]).
    { rewrite Zlength_app, Zlength_one. unfold heap_size in *. split. lia.
      red. rewrite Zlength_correct, Nat2Z.id.
      apply weak_heapOrdered2_postpend. apply cmp_po. trivial. }
  Intro vret.
  forward.
  forward.
  (* Prove postcondition *)
  Exists ((Z.to_nat (heap_capacity h))%nat, vret).
  unfold heap_capacity. rewrite Nat2Z.id. simpl fst.
  unfold valid_pq. entailer!.
  * transitivity (snd h ++ [iv]); trivial. change (iv :: heap_items h) with ([iv] ++ heap_items h).
    apply Permutation_app_comm.
  * Exists arr junk. entailer!.
    + rewrite Zlength_app. apply Permutation_Zlength in H5.
      unfold heap_items. simpl. rewrite <- H5. unfold heap_capacity in *. simpl. rewrite <- H2.
      autorewrite with sublist. lia.
    + unfold heap_size, heap_capacity, heap_items. simpl fst. simpl snd.
      generalize (Permutation_Zlength _ _ _ H5); intro. rewrite <- H10.
      replace (Zlength (heap_items h ++ [iv])) with (Zlength (snd h) + 1). 2: rewrite Zlength_app; trivial.
      cancel.
      rewrite harray_split. cancel.
      repeat rewrite Zlength_app. rewrite <- H10. rewrite Zlength_app. apply derives_refl.
Time Qed.

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
  entailer!. simpl. congruence. 
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
    { entailer!. rewrite Znth_map. 2: rewrite Zlength_Zexchange; lia.
      rewrite <- Hx. rewrite Znth_Zexchange'; try lia. rewrite Znth_0_cons.
      apply Forall_map in H6.
      rewrite Forall_Znth in H6. specialize (H6 (Zlength l)). do 2 rewrite Zlength_map in H6. rewrite Zlength_Zexchange in H6.
      assert (Hq: 0 <= (Zlength l) < Zlength (root :: l)) by lia.
      specialize (H6 Hq). rewrite Znth_map in H6. 2: rewrite Zlength_map, Zlength_Zexchange; lia.
      rewrite Znth_map in H6. 2: rewrite Zlength_Zexchange; lia.
      rewrite Znth_Zexchange' in H6; try lia.
      (* Flailing around solves the goal... *)
      apply H6. discriminate. }
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
    forward_call (0, arr, @nil heap_item, 0, 0). rewrite Zlength_nil. 
      { rewrite Zexchange_eq. unfold harray. rewrite data_at_isptr. entailer. (* Surely there's a less heavy hammer way to do this? *)
        rewrite data_at_zero_array_eq; auto. entailer!. }
      { split. split; inversion 1.
        apply weak_heapOrdered_bounded_root_weak_heapOrdered.
        apply hOwhO. apply cmp_po. apply heapOrdered_empty. }
    (* Prove postcondition *)
    Intro vret. Exists (n, vret) root. entailer. (* Surely there's a less heavy hammer way to do this? *)
    apply Permutation_nil in H3. subst vret. clear H Hy.
    sep_apply harray_emp. rewrite emp_sepcon.
    do 2 rewrite fold_harray. unfold valid_pq, hitem.
    apply andp_right. apply prop_right. auto.
    Exists arr (root :: junk). simpl. entailer!.
    apply heapOrdered_empty.
    rewrite <- harray_split. apply derives_refl.
  * (* main line: heap still has items in it *)
    destruct l0; inversion H. subst h0.
    deadvars!.
    assert (Zlength (h :: l) = Zlength (root :: l0)). { rewrite H5, Zlength_app, Zlength_one, Zlength_cons. lia. }
    rewrite H3, Zexchange_head_foot. rewrite harray_split.
    forward_call (0, arr, (foot :: l0), Zlength (foot :: l0), 0). entailer!.
      { split. intros _. generalize (Zlength_nonneg junk); intro.
        simpl in H2. repeat rewrite Zlength_cons in *. rewrite Zlength_app in H2. lia.
        apply weak_heapOrdered_bounded_root_weak_heapOrdered.
        apply weak_heapOrdered_root with root.
        rewrite H5, app_comm_cons in H1.
        apply heapOrdered_cutfoot in H1. trivial. }
    (* Prove postcondition *)
    Intro vret. Exists (n, vret) root. simpl fst. unfold hitem, heap_item_rep, heap_size, heap_capacity. simpl fst. simpl snd. entailer!.
      { (* Pure part *)
        split. constructor. rewrite H5. transitivity ([foot] ++ l0). apply Permutation_app_comm. auto.
        generalize (root_minimal _ _ _ _ H1 root eq_refl); intro.
        rewrite H5 in H11. apply Forall_inv_tail in H11.
        eapply forall_permutation. apply H11. transitivity ([foot] ++ l0). apply Permutation_app_comm. simpl. tauto. }
    unfold valid_pq. Exists arr (root :: junk). unfold heap_size, heap_capacity. simpl.
    replace (Zlength vret) with (Zlength (root :: l0)). 2: { apply Permutation_Zlength in H6. trivial. }
    apply heapOrdered_bounded_root_heapOrdered in H4.
    entailer!. { (* Pure part inside spatial part *)
      simpl fst in H2. rewrite <- H2. apply Permutation_Zlength in H6. autorewrite with sublist. rewrite <- H6.
      simpl snd. autorewrite with sublist in *. lia. }
    (* Spatial part, this seems a bit uglier than necessary? *)
    change (root :: junk) with ([root] ++ junk). rewrite app_assoc. do 2 rewrite harray_split.
    apply Permutation_Zlength in H6.
    rewrite app_comm_cons. rewrite Zlength_app. rewrite H6. rewrite Zlength_app.
    assert (Zlength (root :: l0) = Zlength vret). { rewrite <- H6. do 2 rewrite Zlength_cons. trivial. }
    do 3 rewrite app_comm_cons.
    do 4 rewrite Zlength_app. rewrite H11.
    do 2 rewrite Zlength_one.
    rewrite Zlength_cons.
    rewrite H3, H11. cancel.
Time Qed.

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
Time Qed.

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
Time Qed.

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
Time Qed.

(* I need this to make a replace work... ugly... *)
Lemma heap_item_rep_morph: forall x y,
  (fst (heap_item_rep x), snd (heap_item_rep y)) = heap_item_rep (fst x, snd y).
Proof. unfold heap_item_rep. destruct x,y; reflexivity. Qed.

Lemma body_exch: semax_body Vprog Gprog f_exch exch_spec.
Proof.
  start_function.
  unfold harray.
  forward. { rewrite Znth_map; trivial. entailer!. }
  forward. { rewrite Znth_map; trivial. entailer!.
    (* C-typing issue? *)
    apply Forall_map in H3.
    rewrite Forall_Znth in H3. specialize (H3 i). do 2 rewrite Zlength_map in H3.
    specialize (H3 H). rewrite Znth_map in H3. 2: rewrite Zlength_map; trivial.
    (* Flailing around solves the goal... *)
    simplify_value_fits in H3. destruct H3.
    rewrite Znth_map in H4; trivial.
    apply H4. discriminate. }
  forward. { repeat rewrite Znth_map; trivial. entailer!. }
  forward.
  forward. { repeat rewrite Znth_map; trivial. entailer!.
    clear H3.
    (* We may be in another C-typing issue... *)
    case (eq_dec i j); intro.
    + subst j. rewrite upd_Znth_same. trivial. rewrite Zlength_map; auto.
    + rewrite upd_Znth_diff; auto. 2,3: rewrite Zlength_map; auto.
      (* So ugly... is there no easier way? *)
      replace (let (x, _) := heap_item_rep _ in x) with (fst (heap_item_rep (Znth j arr_contents))) in H4 by trivial.
      rewrite heap_item_rep_morph, upd_Znth_map in H4.
      apply Forall_map in H4.
      rewrite Forall_Znth in H4. specialize (H4 j).
      do 2 rewrite Zlength_map in H4. rewrite Zlength_upd_Znth in H4. specialize (H4 H0).
      do 2 rewrite Znth_map in H4. 2,3,4: autorewrite with sublist; trivial.
      rewrite upd_Znth_diff in H4; auto. rewrite Znth_map; trivial.
      (* Flailing around solves the goal... *)
      simplify_value_fits in H4. destruct H4.
      apply H4. discriminate. }
  forward.
  forward.
  forward.
  (* Prove postcondition *)
  repeat rewrite upd_Znth_overwrite.
  2,3,4: autorewrite with sublist; auto.
  repeat rewrite upd_Znth_same.
  2,3: autorewrite with sublist; auto.
  case (eq_dec i j); intro.
  + subst j. rewrite upd_Znth_overwrite, upd_Znth_same. 2,3: autorewrite with sublist; auto. simpl fst.
    simpl fst; simpl snd.
    replace (let (x, _) := Znth i (map heap_item_rep arr_contents) in x,
             let (_, y) := Znth i (map heap_item_rep arr_contents) in y)
            with (heap_item_rep (Znth i arr_contents)) by (rewrite Znth_map; auto).
    rewrite upd_Znth_map, upd_Znth_same_Znth; trivial.
    rewrite Zexchange_eq. Intros. unfold harray. go_lower. cancel.
  + rewrite upd_Znth_diff; auto. 2,3: rewrite Zlength_map; auto. simpl fst.
    simpl fst; simpl snd.
    replace (let (x, _) := Znth j (map heap_item_rep arr_contents) in x,
             let (_, y) := Znth j (map heap_item_rep arr_contents) in y) 
            with (heap_item_rep (Znth j arr_contents)) by (rewrite Znth_map; auto).
    replace (let (x, _) := Znth i (map heap_item_rep arr_contents) in x,
             let (_, y) := Znth i (map heap_item_rep arr_contents) in y) 
            with (heap_item_rep (Znth i arr_contents)) by (rewrite Znth_map; auto).
    do 2 rewrite upd_Znth_map.
    rewrite fold_harray'. 2: autorewrite with sublist; trivial.
    replace (upd_Znth j (upd_Znth i arr_contents (Znth j arr_contents)) (Znth i arr_contents)) with (Zexchange arr_contents i j).
    go_lower. cancel.
    apply Znth_eq_ext. { rewrite Zlength_Zexchange. autorewrite with sublist. trivial. }
    intros. rewrite Zlength_Zexchange in H1. case (eq_dec i0 j); intro.
    * subst i0. rewrite upd_Znth_same. 2: autorewrite with sublist; trivial.
      rewrite Znth_Zexchange'; trivial.
    * case (eq_dec i0 i); intro. subst i0.
      rewrite upd_Znth_diff. rewrite upd_Znth_same. rewrite Znth_Zexchange; trivial. 1,2,3,4: autorewrite with sublist; trivial.
      rewrite Znth_Zexchange''; auto.
      repeat rewrite upd_Znth_diff; autorewrite with sublist; trivial.
Time Qed.
