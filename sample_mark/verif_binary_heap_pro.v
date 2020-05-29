Require Import RelationClasses.
Require Import VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.binary_heap_model.
Require Import RamifyCoq.sample_mark.binary_heap_Zmodel.
Require Import RamifyCoq.sample_mark.binary_heap_pro.
Require Import RamifyCoq.sample_mark.env_binary_heap_pro.

Set Nested Proofs Allowed.

Definition exch_spec :=
  DECLARE _exch WITH j : Z, k : Z, arr: val, arr_contents: list heap_item, lookup : val, lookup_contents : list Z
  PRE [tuint, tuint, tptr t_item, tptr tuint]
    PROP (0 <= j < Zlength arr_contents; 0 <= k < Zlength arr_contents)
    PARAMS (Vint (Int.repr j); Vint (Int.repr k); arr; lookup)
    GLOBALS ()
    SEP (linked_heap_array arr_contents arr lookup_contents lookup)
  POST [tvoid]
    EX lookup_contents' : list Z,
      PROP ()
      LOCAL ()
      SEP (linked_heap_array (Zexchange arr_contents j k) arr lookup_contents' lookup).

Definition less_spec :=
  DECLARE _less WITH i : Z, j : Z, arr: val, arr_contents: list heap_item, arr' : val, lookup : list Z
  PRE [tuint, tuint, tptr t_item]
    PROP (0 <= i < Zlength arr_contents; 0 <= j < Zlength arr_contents)
    PARAMS (Vint (Int.repr i); Vint (Int.repr j); arr)
    GLOBALS ()
    SEP (linked_heap_array arr_contents arr lookup arr')
  POST [tint]
    PROP ()
    LOCAL (temp ret_temp (Val.of_bool (cmp (Znth i arr_contents) (Znth j arr_contents))))
    SEP (linked_heap_array arr_contents arr lookup arr').

Definition swim_spec :=
  DECLARE _swim WITH i : Z, arr: val, arr_contents: list heap_item, arr' : val, lookup : list Z
  PRE [tuint, tptr t_item, tptr tuint]
    PROP (0 <= i < Zlength arr_contents;
          weak_heap_ordered_bottom_up arr_contents i)
    PARAMS (Vint (Int.repr i); arr; arr')
    GLOBALS ()
    SEP (linked_heap_array arr_contents arr lookup arr')
  POST [tvoid]
    EX arr_contents' : list (Z * int * int), EX lookup' : list Z,
      PROP (heap_ordered arr_contents'; Permutation arr_contents arr_contents')
      LOCAL ()
      SEP (linked_heap_array arr_contents' arr lookup' arr').

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

Definition sink_spec :=
  DECLARE _sink WITH i : Z, arr: val, arr_contents: list heap_item, first_available : Z, arr' : val, lookup : list Z
  PRE [tuint, tptr t_item, tuint, tptr tuint]
    PROP (0 <= i <= Zlength arr_contents; 
          first_available = Zlength arr_contents;
          (i = Zlength arr_contents -> (2 * i) <= Int.max_unsigned);
          (i < Zlength arr_contents -> (2 * (first_available - 1) <= Int.max_unsigned)); (* i = fa - 1 -> (2 * i + 1) = 2 * fa - 1, must be representable *)
          weak_heap_ordered_top_down arr_contents i)
    PARAMS (Vint (Int.repr i); arr; Vint (Int.repr first_available); arr')
    GLOBALS ()
    SEP (linked_heap_array arr_contents arr lookup arr')
  POST [tvoid]
    EX arr_contents' : list heap_item, EX lookup' : list Z,
      PROP (heap_ordered arr_contents' /\ Permutation arr_contents arr_contents')
      LOCAL ()
      SEP (linked_heap_array arr_contents' arr lookup' arr).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ exch_spec ; less_spec ; swim_spec ; sink_spec ; 
                                   remove_min_nc_spec ; insert_nc_spec ; 
                                   size_spec ; capacity_spec ]).

Lemma body_sink: semax_body Vprog Gprog f_sink sink_spec.
Proof.
  start_function.
Admitted.
(*
  assert (Hc : i = Zlength arr_contents \/ 0 <= i < Zlength arr_contents) by lia. destruct Hc as [Hc | Hc].
* (* Special case: oob sink, used when removing the last element of the heap. *)
  forward_loop ( PROP () LOCAL (temp _k (Vint (Int.repr i)); temp _first_available (Vint (Int.repr first_available))) SEP (harray arr_contents arr) ).
  entailer!.
  forward_if False. exfalso. lia. (* This is where the bound is needed.  For some reason I need a slightly different bound than I expect. *)
  forward.
  Exists arr_contents. entailer!.
  eapply weak_heapOrdered_oob. 2: apply H3.
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
      * apply sink_hO. apply cmp_po. apply cmp_linear. apply H2. 
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
      entailer!. 1,2,3,4: rep_lia. }
  Intro b.
  set (j' := if b then Zright_child i' else Zleft_child i').
  forward_if (PROP (if b then Zright_child i' <  first_available /\  cmp_rel (Znth (Zright_child i') arr_contents') (Znth (Zleft_child i') arr_contents')
                         else Zright_child i' >= first_available \/ ~cmp_rel (Znth (Zright_child i') arr_contents') (Znth (Zleft_child i') arr_contents') )
              LOCAL (temp _t'1 (Val.of_bool b); temp _k (Vint (Int.repr i')); temp _j (Vint (Int.repr j')); temp _arr arr; temp _first_available (Vint (Int.repr first_available))) 
              SEP (harray arr_contents' arr)).
    { forward. subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. entailer!. tauto. }
    { forward. entailer!. }
    Intros. (* Need to get the PROP above the bar... why doesn't forward_call do this for me? *)
    forward_call (i', j', arr, arr_contents'). { subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. destruct b; lia. }
    forward_if (~cmp_rel (Znth i' arr_contents') (Znth j' arr_contents')).
      { forward. (* Prove function postcondition *)
        Exists arr_contents'. entailer!. unfold sink at 2 in H4. erewrite sink_done in H4; intros.
        rewrite <- H4. split. apply sink_hO. apply cmp_po. apply cmp_linear. apply H2.
        apply sink_permutation.
        apply Znth_nth_error. lia.
        * rewrite <- (Nat2Z.id (left_child _)) in H0. change (Z.of_nat _) with (Zleft_child i') in H0.
          rewrite Znth_nth_error in H0. 2: rewrite Zright_child_unfold, Zleft_child_unfold in *; lia.
          inversion H0. subst b0. clear H0.
          destruct b; subst j'; auto.
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
          destruct b; subst j'. tauto. destruct H7. lia.
          transitivity (Znth (Zleft_child i') arr_contents'). trivial.
          destruct (cmp_linear (Znth (Zleft_child i') arr_contents') (Znth (Zright_child i') arr_contents')); auto.
          contradiction. }
      { forward.  entailer!. unfold cmp_rel in H0. congruence. }
    forward_call (i', j', arr, arr_contents').
      { subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. destruct b; lia. }
    forward.
    (* Prove loop invariant at loop bottom *)
    Exists j' (Zexchange arr_contents' i' j').
    entailer!. split. subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. destruct b; lia.
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
      destruct b.
      - right. split. unfold Zright_child. lia. tauto.
      - left. split. unfold Zleft_child. lia. destruct H7. lia. tauto.
    + subst j'. destruct b.
      - rewrite H5 in H7. apply nth_error_None in H0. destruct H7. unfold Zright_child in H7. rewrite Zlength_correct in H7. lia.
      - split. unfold Zleft_child. lia. tauto.
Time Qed.
*)

Lemma body_swim: semax_body Vprog Gprog f_swim swim_spec.
Proof.
  start_function.
Admitted.
(*
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
*)

Lemma body_insert_nc: semax_body Vprog Gprog f_insert_nc insert_nc_spec.
Proof.
  start_function.
Admitted.
(*
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
  unfold heap_size at 3. replace (Zlength (heap_items h) - Zlength (heap_items h)) with 0 by lia.
  change (Vint (fst iv), Vint (snd iv)) with (heap_item_rep iv). rewrite upd_Znth_map.
  rewrite <- map_app. change (upd_Znth 0 [h0] iv) with [iv].
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
*)

Lemma body_remove_min_nc: semax_body Vprog Gprog f_remove_min_nc remove_min_nc_spec.
Proof.
  start_function.
Admitted.
(*
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
    forward_call (0, arr, @nil heap_item, 0); rewrite Zlength_nil. 
      { unfold harray. rewrite data_at_isptr. entailer. (* Surely there's a less heavy hammer way to do this? *)
        rewrite data_at_zero_array_eq; auto. entailer!. }
      { split; auto. split; auto. split. rep_lia. split. rep_lia.
        apply hOwhO. apply cmp_po. apply heapOrdered_empty. }
    (* Prove postcondition *)
    Intro vret. Exists (n, vret) root. entailer. (* Surely there's a less heavy hammer way to do this? *)
    destruct H. apply Permutation_nil in H13. subst vret. clear H Hy.
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
    assert (Zlength (h :: l) = Zlength (root :: l0)). { rewrite H5, Zlength_app, Zlength_one, Zlength_cons. lia. }
    rewrite H3, Zexchange_head_foot. rewrite harray_split.
    forward_call (0, arr, (foot :: l0), Zlength (foot :: l0)). entailer!.
      { split. rewrite Zlength_cons. generalize (Zlength_nonneg l0). lia.
        split; trivial. split. rep_lia.
        (* Here is where we use the bound. *)
        split. intros _. generalize (Zlength_nonneg junk); intro.
        simpl in H2. repeat rewrite Zlength_cons in *. rewrite Zlength_app in H2. lia.
        apply weak_heapOrdered_root with root.
        rewrite H5, app_comm_cons in H1.
        apply heapOrdered_cutfoot in H1. trivial. }
    (* Prove postcondition *)
    Intro vret. Exists (n, vret) root. simpl fst. unfold hitem, heap_item_rep, heap_size, heap_capacity. simpl fst. simpl snd. entailer!.
      { (* Pure part *)
        split. constructor. rewrite H5. transitivity ([foot] ++ l0). apply Permutation_app_comm. destruct H4. auto.
        generalize (root_minimal _ _ _ _ H1 root eq_refl); intro.
        rewrite H5 in H10. apply Forall_inv_tail in H10.
        eapply forall_permutation. apply H10. transitivity ([foot] ++ l0). apply Permutation_app_comm. simpl. tauto. }
    unfold valid_pq. Exists arr (root :: junk). unfold heap_size, heap_capacity. simpl.
    destruct H4.
    replace (Zlength vret) with (Zlength (root :: l0)). 2: { apply Permutation_Zlength in H10. trivial. }
    entailer!. { (* Pure part inside spatial part *)
      simpl fst in H2. rewrite <- H2. apply Permutation_Zlength in H10. autorewrite with sublist. rewrite <- H10.
      simpl snd. autorewrite with sublist in *. lia. }
    (* Spatial part, this seems a bit uglier than necessary? *)
    change (root :: junk) with ([root] ++ junk). rewrite app_assoc. do 2 rewrite harray_split.
    apply Permutation_Zlength in H10.
    rewrite app_comm_cons. rewrite Zlength_app. rewrite H10. rewrite Zlength_app.
    assert (Zlength (root :: l0) = Zlength vret). { rewrite <- H10. do 2 rewrite Zlength_cons. trivial. }
    do 3 rewrite app_comm_cons.
    do 4 rewrite Zlength_app. rewrite H11.
    do 2 rewrite Zlength_one.
    rewrite Zlength_cons.
    rewrite H3, H11. cancel.
Time Qed.
*)

Lemma body_less: semax_body Vprog Gprog f_less less_spec.
Proof.
  start_function.
  unfold linked_heap_array, heap_array.
  Intros.
  forward.
  rewrite Znth_map; trivial.
  entailer!.
  forward.
  do 2 (rewrite Znth_map; trivial).
  entailer!.
  forward.
  repeat rewrite Znth_map in *; trivial.
  unfold linked_heap_array, heap_array.
  entailer!.
Time Qed.

Lemma body_size: semax_body Vprog Gprog f_size size_spec.
Proof.
  start_function.
  unfold valid_pq.
  Intros arr junk arr2 lookup.
  forward.
  forward.
  unfold valid_pq.
  Exists arr junk arr2 lookup.
  entailer!.
Time Qed.

Lemma body_capacity: semax_body Vprog Gprog f_capacity capacity_spec.
Proof.
  start_function.
  unfold valid_pq.
  Intros arr junk arr2 lookup.
  forward.
  forward.
  unfold valid_pq.
  Exists arr junk arr2 lookup.
  entailer!.
Time Qed.

(* I need this to make a replace work... ugly... *)
Lemma heap_item_rep_morph: forall x y,
  (fst (heap_item_rep x), (fst (snd (heap_item_rep y)), snd (snd (heap_item_rep x)))) = 
  heap_item_rep (fst (fst x), snd (fst y), snd x).
Proof. unfold heap_item_rep. destruct x,y; reflexivity. Qed.

Lemma body_exch: semax_body Vprog Gprog f_exch exch_spec.
Proof.
  start_function.
  unfold linked_heap_array, heap_array. Intros.
  forward. { rewrite Znth_map; trivial. entailer!. }
  forward. { rewrite Znth_map; trivial. entailer!.
    (* C-typing issue? *)
    apply Forall_map in H4.
    rewrite Forall_Znth in H4. specialize (H4 j). do 2 rewrite Zlength_map in H4.
    specialize (H4 H). rewrite Znth_map in H4. 2: rewrite Zlength_map; trivial.
    (* Flailing around solves the goal... *)
    simplify_value_fits in H4. destruct H4.
    rewrite Znth_map in H5; trivial.
    apply H5. discriminate. }
  forward. { repeat rewrite Znth_map; trivial. entailer!. }
  forward. { repeat rewrite Znth_map; trivial. entailer!. }
  forward. { repeat rewrite Znth_map; trivial. entailer!. }
  forward.
  forward. { repeat rewrite Znth_map; trivial. entailer!.
    clear H4.
    (* We may be in another C-typing issue... *)
    case (eq_dec j k); intro.
    + subst k. rewrite upd_Znth_same. trivial. rewrite Zlength_map; auto.
    + rewrite upd_Znth_diff; auto. 2,3: rewrite Zlength_map; auto.
      (* So ugly... is there no easier way? *)
      replace (let (x, _) := heap_item_rep _ in x) with (fst (heap_item_rep (Znth j arr_contents))) in H5 by trivial.
      replace (let (x, _) := let (_, y) := heap_item_rep _ in y in x) with (fst (snd (heap_item_rep (Znth k arr_contents)))) in H5 by trivial.
      replace (let (_, y) := let (_, y) := heap_item_rep _ in y in y) with (snd (snd (heap_item_rep (Znth j arr_contents)))) in H5 by trivial.
      rewrite heap_item_rep_morph, upd_Znth_map in H5.
      apply Forall_map in H5.
      rewrite Forall_Znth in H5. specialize (H5 k).
      do 2 rewrite Zlength_map in H5. rewrite Zlength_upd_Znth in H5. specialize (H5 H0).
      do 2 rewrite Znth_map in H5. 2,3,4: autorewrite with sublist; trivial.
      rewrite upd_Znth_diff in H5; auto. rewrite Znth_map; trivial.
      (* Flailing around solves the goal... *)
      simplify_value_fits in H5. destruct H5 as [? [? ?]].
      apply H6. discriminate. }
  forward.
  forward.
  (* Some cleanup *)
  unfold lookup_array.
  repeat rewrite upd_Znth_same, upd_Znth_overwrite.
  3,4: rewrite Zlength_upd_Znth. 2,3,4,5: rewrite Zlength_map; lia.
  repeat rewrite Znth_map. 2,3: lia.
  (* This is ugly and very confusing, if you try to "forward" now, or anywhere between the cleanup and here... *)
  replace (let (x, _) := heap_item_rep (Znth k arr_contents) in x) with (fst (heap_item_rep (Znth k arr_contents))) by trivial.
Admitted.
(*
forward.
Check heap_item_rep.
Compute (reptype t_item). _rep.
forward.
, Zlength_map; lia.
Search upd_Znth.
deadvars!.
Search Znth upd_Znth.
repeat rewrite Znth_upd_Znth.
  forward.
  (* Prove postcondition *)
  repeat rewrite upd_Znth_overwrite.
  2,3,4: autorewrite with sublist; auto.
  repeat rewrite upd_Znth_same.
  2,3: autorewrite with sublist; auto.
  case (eq_dec i j); intro.
  + subst j. rewrite upd_Znth_overwrite, upd_Znth_same. 2,3: autorewrite with sublist; auto.
    replace (let (x, _) := Znth i (map heap_item_rep arr_contents) in x,
             let (_, y) := Znth i (map heap_item_rep arr_contents) in y) 
            with (heap_item_rep (Znth i arr_contents)) by (rewrite Znth_map; auto).
    rewrite upd_Znth_map. rewrite upd_Znth_same_Znth; trivial.
    rewrite Zexchange_eq. unfold harray. go_lower. cancel.
  + rewrite upd_Znth_diff; auto. 2,3: rewrite Zlength_map; auto.
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
*)