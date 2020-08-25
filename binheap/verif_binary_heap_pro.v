Require Import RelationClasses.
Require Import VST.floyd.proofauto.
Require Import CertiGraph.sample_mark.binary_heap_model.
Require Import CertiGraph.sample_mark.binary_heap_Zmodel.
Require Import CertiGraph.sample_mark.binary_heap_pro.
Require Import CertiGraph.sample_mark.env_binary_heap_pro.

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
      PROP (lookup_oob_eq (Zexchange arr_contents j k) lookup_contents lookup_contents')
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
  DECLARE _swim WITH k : Z, arr: val, arr_contents: list heap_item, lookup : val, lookup_contents : list Z
  PRE [tuint, tptr t_item, tptr tuint]
    PROP (0 <= k < Zlength arr_contents;
          weak_heap_ordered_bottom_up arr_contents k)
    PARAMS (Vint (Int.repr k); arr; lookup)
    GLOBALS ()
    SEP (linked_heap_array arr_contents arr lookup_contents lookup)
  POST [tvoid]
    EX arr_contents' : list (Z * int * int), EX lookup_contents' : list Z,
      PROP (lookup_oob_eq arr_contents' lookup_contents lookup_contents'; 
            heap_ordered arr_contents'; Permutation arr_contents arr_contents')
      LOCAL ()
      SEP (linked_heap_array arr_contents' arr lookup_contents' lookup).

Definition sink_spec :=
  DECLARE _sink WITH k : Z, arr: val, arr_contents: list heap_item, first_available : Z, lookup : val, lookup_contents : list Z
  PRE [tuint, tptr t_item, tuint, tptr tuint]
    PROP (0 <= k <= Zlength arr_contents; 
          first_available = Zlength arr_contents;
          (k = Zlength arr_contents -> (2 * k) <= Int.max_unsigned);
          (k < Zlength arr_contents -> (2 * (first_available - 1) <= Int.max_unsigned)); (* i = fa - 1 -> (2 * i + 1) = 2 * fa - 1, must be representable *)
          weak_heap_ordered_top_down arr_contents k)
    PARAMS (Vint (Int.repr k); arr; Vint (Int.repr first_available); lookup)
    GLOBALS ()
    SEP (linked_heap_array arr_contents arr lookup_contents lookup)
  POST [tvoid]
    EX arr_contents' : list heap_item, EX lookup_contents' : list Z,
      PROP (lookup_oob_eq arr_contents' lookup_contents lookup_contents'; 
            heap_ordered arr_contents'; Permutation arr_contents arr_contents')
      LOCAL ()
      SEP (linked_heap_array arr_contents' arr lookup_contents' lookup).

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
  DECLARE _insert_nc WITH pq : val, h : heap, priority : Z, data : int
  PRE [tptr t_pq, tint, tptr tvoid]
    PROP (heap_size h < heap_capacity h)
    PARAMS (pq; Vint (Int.repr priority); Vint data)
    GLOBALS ()
    SEP (valid_pq pq h)
  POST [tuint]
  EX h' : heap, EX key : Z,
    PROP (heap_capacity h = heap_capacity h';
          Permutation ((key, Int.repr priority, data) :: heap_items h) (heap_items h'))
    LOCAL (temp ret_temp (Vint (Int.repr key)))
    SEP (valid_pq pq h').

Definition Gprog : funspecs :=
         ltac:(with_library prog [ exch_spec ; less_spec ; swim_spec ; sink_spec ; 
                                   remove_min_nc_spec ; insert_nc_spec ; 
                                   size_spec ; capacity_spec ]).

Lemma body_sink: semax_body Vprog Gprog f_sink sink_spec.
Proof.
  start_function.
  assert (Hc : k = Zlength arr_contents \/ 0 <= k < Zlength arr_contents) by lia. destruct Hc as [Hc | Hc].
* (* Special case: oob sink, used when removing the last element of the heap. *)
  forward_loop ( PROP () LOCAL (temp _k (Vint (Int.repr k)); temp _first_available (Vint (Int.repr first_available))) 
                 SEP (linked_heap_array arr_contents arr lookup_contents lookup) ).
  entailer!.
  forward_if False. exfalso. lia. (* This is where the bound is needed.  For some reason I need a slightly different bound than I expect. *)
  forward.
  Exists arr_contents lookup_contents. entailer!.
  eapply weak_heapOrdered_oob. 2: apply H3.
  rewrite Zlength_correct, Nat2Z.id. apply le_refl.
* (* Main line *)
  assert (Hx : k < Zlength arr_contents) by lia. specialize (H2 Hx). clear H1 Hx. rename H2 into H1. rename H3 into H2.
  forward_loop (EX k' : Z, EX arr_contents' : list heap_item, EX lookup_contents' : list Z,
                 PROP (0 <= k' < Zlength arr_contents; 
                       sink arr_contents (Z.to_nat k) = sink arr_contents' (Z.to_nat k');
                       lookup_oob_eq arr_contents' lookup_contents lookup_contents')
                 LOCAL (temp _k (Vint (Int.repr k')); temp _arr arr; temp _lookup lookup; 
                        temp _first_available (Vint (Int.repr first_available)))
                 SEP (linked_heap_array arr_contents' arr lookup_contents' lookup)).
  Exists k arr_contents lookup_contents. entailer!.
  Intros k' arr_contents' lookup_contents'.
  assert (Zlength arr_contents = Zlength arr_contents'). { unfold sink in H4. 
    generalize (sink_permutation _ cmp_rel cmp_dec arr_contents (Z.to_nat k)); intro.
    generalize (sink_permutation _ cmp_rel cmp_dec arr_contents' (Z.to_nat k')); intro.
    apply Permutation_Zlength in H6. apply Permutation_Zlength in H7. congruence. }
  forward_if (Zleft_child k' < first_available).
    { forward. entailer!. rewrite Zleft_child_unfold; lia. }
    { forward. (* Prove postcondition *)
      Exists arr_contents' lookup_contents'. entailer!. unfold sink at 2 in H4.
      rewrite <- Zleft_child_unfold in H7; try lia.
      unfold Zleft_child in H7. rewrite H6 in H7. rewrite Zlength_correct in H7.
      erewrite sink_done in H4. 2: apply Znth_nth_error; lia.
      rewrite <- H4. { split. 
      * apply sink_hO. apply cmp_po. apply cmp_linear. apply H2. 
      * apply sink_permutation. }
      intros. assert (left_child (Z.to_nat k') < length arr_contents')%nat by (apply nth_error_Some; congruence).
      lia.
      intros. assert (right_child (Z.to_nat k') < length arr_contents')%nat by (apply nth_error_Some; congruence).
      unfold right_child in H8. lia. }
  forward.
  rewrite mul_repr, add_repr. rewrite <- Zleft_child_unfold. 2: lia.
  forward_if (EX b : bool, PROP (if b then Zright_child k' <  first_available /\  cmp_rel (Znth (Zright_child k') arr_contents') (Znth (Zleft_child k') arr_contents')
                                      else Zright_child k' >= first_available \/ ~cmp_rel (Znth (Zright_child k') arr_contents') (Znth (Zleft_child k') arr_contents') )
                           LOCAL (temp _t'1 (Val.of_bool b); temp _k (Vint (Int.repr k')); 
                                  temp _j (Vint (Int.repr (Zleft_child k'))); temp _arr arr; temp _lookup lookup;
                                  temp _first_available (Vint (Int.repr first_available))) 
                           SEP (linked_heap_array arr_contents' arr lookup_contents' lookup)).
    { forward_call (Zright_child k', Zleft_child k', arr, arr_contents', lookup, lookup_contents').
        { entailer!. simpl. repeat f_equal. rewrite Zright_child_unfold, Zleft_child_unfold; lia. }
        { rewrite Int.unsigned_repr in H8. rewrite Zright_child_unfold, Zleft_child_unfold in *; lia.
          (* Here is where we seem to need the precise bound on first_available? *)
          rewrite Zleft_child_unfold in *; rep_lia. }
      forward. Exists (cmp (Znth (Zright_child k') arr_contents') (Znth (Zleft_child k') arr_contents')).
      unfold cmp_rel. rewrite Zright_child_unfold, Zleft_child_unfold in *.
      rewrite Int.unsigned_repr in H8. 2,3,4,5: rep_lia.
      case cmp; entailer!. }
    { forward. Exists false.
      rewrite Zright_child_unfold, Zleft_child_unfold in *. rewrite Int.unsigned_repr in H8. 
      entailer!. 1,2,3,4: rep_lia. }
  Intro b.
  set (j' := if b then Zright_child k' else Zleft_child k').
  forward_if (PROP (if b then Zright_child k' <  first_available /\  cmp_rel (Znth (Zright_child k') arr_contents') (Znth (Zleft_child k') arr_contents')
                         else Zright_child k' >= first_available \/ ~cmp_rel (Znth (Zright_child k') arr_contents') (Znth (Zleft_child k') arr_contents') )
              LOCAL (temp _t'1 (Val.of_bool b); temp _k (Vint (Int.repr k'));
                     temp _j (Vint (Int.repr j')); temp _arr arr; temp _lookup lookup;
                     temp _first_available (Vint (Int.repr first_available)))
              SEP (linked_heap_array arr_contents' arr lookup_contents' lookup)).
    { forward. subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. entailer!. tauto. }
    { forward. entailer!. }
    Intros. (* Need to get the PROP above the bar... why doesn't forward_call do this for me? *)
    forward_call (k', j', arr, arr_contents', lookup, lookup_contents'). { subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. destruct b; lia. }
    forward_if (~cmp_rel (Znth k' arr_contents') (Znth j' arr_contents')).
      { forward. (* Prove function postcondition *)
        Exists arr_contents' lookup_contents'. entailer!. unfold sink at 2 in H4. erewrite sink_done in H4; intros.
        rewrite <- H4. split. apply sink_hO. apply cmp_po. apply cmp_linear. apply H2.
        apply sink_permutation.
        apply Znth_nth_error. lia.
        * rewrite <- (Nat2Z.id (left_child _)) in H0. change (Z.of_nat _) with (Zleft_child k') in H0.
          rewrite Znth_nth_error in H0. 2: rewrite Zright_child_unfold, Zleft_child_unfold in *; lia.
          inversion H0. subst b0. clear H0.
          destruct b; subst j'; auto.
          transitivity (Znth (Zright_child k') arr_contents'); tauto.
        * assert (0 <= Zright_child k' < Zlength arr_contents'). {
            split. unfold Zright_child. lia.
            apply Z2Nat.inj_lt. unfold Zright_child. lia. lia.
            rewrite ZtoNat_Zlength.
            eapply nth_error_Some.
            unfold Zright_child.
            rewrite Nat2Z.id. congruence. }
          rewrite <- (Nat2Z.id (right_child _)) in H0. change (Z.of_nat _) with (Zright_child k') in H0.
          rewrite Znth_nth_error in H0; try lia.
          inversion H0. subst b0. clear H0.
          destruct b; subst j'. tauto. destruct H8. lia.
          transitivity (Znth (Zleft_child k') arr_contents'). trivial.
          destruct (cmp_linear (Znth (Zleft_child k') arr_contents') (Znth (Zright_child k') arr_contents')); auto.
          contradiction. }
      { forward.  entailer!. unfold cmp_rel in H0. congruence. }
    forward_call (k', j', arr, arr_contents', lookup, lookup_contents').
      { subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. destruct b; lia. }
    Intros lookup_contents''.
    forward.
    (* Prove loop invariant at loop bottom *)
    Exists j' (Zexchange arr_contents' k' j') lookup_contents''.
    entailer!. split. subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. destruct b; lia.
    split. 
    + unfold sink at 2. unfold Zexchange. erewrite sink_step. apply H4.
      apply Znth_nth_error; lia.
      unfold left_child. replace (1 + Z.to_nat k' + Z.to_nat k')%nat with (Z.to_nat (2 * k' + 1)) by lia.
      apply Znth_nth_error.
      split. lia. rewrite <- Zleft_child_unfold; try lia.
      rewrite <- Zleft_child_unfold; try lia.
      case_eq (nth_error arr_contents' (right_child (Z.to_nat k'))); intros.
      - (* From H0... feels like it should be a lemma. *)
        assert (h = Znth (Zright_child k') arr_contents'). {
          rewrite <- (nat_of_Z_eq (right_child _)) in H0.
          rewrite Znth_nth_error in H0. inversion H0. trivial.
          assert ((Z.to_nat (Z.of_nat (right_child (Z.to_nat k')))) < length arr_contents')%nat by (apply nth_error_Some; congruence).
          rewrite Zlength_correct. lia. } subst h.
        (* Probably another lemma... *)
        assert (Zright_child k' < Zlength arr_contents'). {
          assert (right_child (Z.to_nat k') < length arr_contents')%nat by (apply nth_error_Some; congruence).
          unfold Zright_child. rewrite Zlength_correct. lia. }
        clear H0. subst j'.
        destruct b.
        ** right. split. unfold Zright_child. lia. tauto.
        ** left. split. unfold Zleft_child. lia. destruct H8. lia. tauto.
      - subst j'. destruct b.
        ** rewrite H6 in H8. apply nth_error_None in H0. destruct H8. unfold Zright_child in H8. rewrite Zlength_correct in H8. lia.
        ** split. unfold Zleft_child. lia. tauto.
    + transitivity lookup_contents'; trivial.
      eapply lookup_oob_eq_shuffle. 2: apply H5.
      apply Permutation_map, Zexchange_Permutation.
Time Qed.

Lemma body_swim: semax_body Vprog Gprog f_swim swim_spec.
Proof.
  start_function.
  assert_PROP (Zlength arr_contents <= Int.max_unsigned) as Hz. 
    { go_lower. unfold linked_heap_array, heap_array. apply andp_left2. saturate_local. apply prop_right.
      destruct H1 as [? [? [? [? ?]]]].
      destruct arr; try contradiction. simpl in H5. rep_lia. }
  forward_loop (EX k' : Z, EX arr_contents' : list heap_item, EX lookup_contents' : list Z,
                PROP (0 <= k' < Zlength arr_contents; 
                      swim arr_contents (Z.to_nat k) = swim arr_contents' (Z.to_nat k');
                      lookup_oob_eq arr_contents' lookup_contents lookup_contents')
                LOCAL (temp _k (Vint (Int.repr k')); temp _arr arr; temp _lookup lookup)
                SEP (linked_heap_array arr_contents' arr lookup_contents' lookup)).
  Exists k arr_contents lookup_contents. entailer!.
  Intros k' arr_contents' lookup_contents'.
  assert (Zlength arr_contents = Zlength arr_contents'). {
    unfold swim in H2.
    generalize (swim_permutation _ cmp_rel cmp_dec arr_contents (Z.to_nat k)); intro.
    generalize (swim_permutation _ cmp_rel cmp_dec arr_contents' (Z.to_nat k')); intro.
    apply Permutation_Zlength in H4. apply Permutation_Zlength in H5. congruence. }
  generalize (parent_le (Z.to_nat k')); intro Hq.
  assert (Hx: k' = 0 \/ k' > 0) by lia.
  forward_if (EX b : bool, PROP (if b then k' > 0 /\  cmp_rel (Znth k' arr_contents') (Znth (Zparent k') arr_contents')
                                      else k' = 0 \/ ~cmp_rel (Znth k' arr_contents') (Znth (Zparent k') arr_contents') )
                           LOCAL (temp _t'1 (Val.of_bool b); temp _k (Vint (Int.repr k')); temp _arr arr; temp _lookup lookup) 
                           SEP (linked_heap_array arr_contents' arr lookup_contents' lookup)).
    { (* if-branch *)
      destruct Hx as [Hx | Hx]. subst k'. inversion H5.
      forward_call (k', Zparent k', arr, arr_contents', lookup, lookup_contents').
      { entailer!. simpl. rewrite Zparent_repr. trivial. lia. }
      { assert (parent (Z.to_nat k') <= (Z.to_nat k'))%nat by apply parent_le. unfold Zparent. lia. }
      forward. unfold cmp_rel. case (cmp (Znth k' arr_contents') (Znth (Zparent k') arr_contents')).
      Exists true. entailer!.
      Exists false. entailer!. }
    { (* else-branch *)
      forward. Exists false. entailer!. }
  Intro b.
  forward_if (PROP (k' > 0 /\ cmp_rel (Znth k' arr_contents') (Znth (Zparent k') arr_contents'))
              LOCAL (temp _k (Vint (Int.repr k')); temp _lookup lookup; temp _arr arr)
              SEP (linked_heap_array arr_contents' arr lookup_contents' lookup)).
    { subst b. forward. entailer!. tauto. }
    { subst b. forward. (* Prove postcondition *)
      Exists arr_contents' lookup_contents'. entailer!. split.
      { assert (heap_ordered (swim arr_contents (Z.to_nat k))). { apply swim_hO; auto. apply cmp_po. apply cmp_linear. }
        unfold swim at 2 in H2. destruct H6.
        * subst k'. simpl in H2. rewrite swim_0 in H2. rewrite <- H2. trivial. 
        * erewrite swim_done in H2; eauto. rewrite <- H2. trivial.
          apply Znth_nth_error; lia.
          unfold Zparent. rewrite <- Znth_nth_error; try lia.
          rewrite Nat2Z.id. trivial. }
      { unfold swim in H2. 
        generalize (swim_permutation _ cmp_rel cmp_dec arr_contents (Z.to_nat k)); intro.
        generalize (swim_permutation _ cmp_rel cmp_dec arr_contents' (Z.to_nat k')); intro.
        rewrite H2 in H5. etransitivity. apply H5. symmetry. trivial. } }
  forward_call (k', Zparent k', arr, arr_contents', lookup, lookup_contents').
    { entailer!. simpl. rewrite Zparent_repr. trivial. lia. }
    { unfold Zparent. lia. }
  Intros lookup_contents''.
  forward.
  Exists (Zparent k') (Zexchange arr_contents' k' (Zparent k')) lookup_contents''.
  entailer!. split. unfold Zparent. lia.
  split. 2: split.
  * unfold swim, Zparent, Zexchange in *. rewrite Nat2Z.id. erewrite swim_step. congruence.
    rewrite H4, Zlength_correct in H1.
    4: apply H6. 2: apply Znth_nth_error.
    3: rewrite <- Znth_nth_error. 3: rewrite Nat2Z.id; trivial.
    1,2,3: lia.
  * transitivity lookup_contents'; trivial.
    eapply lookup_oob_eq_shuffle. 2: apply H3.
    apply Permutation_map, Zexchange_Permutation.
  * rewrite Zparent_repr. trivial. lia.
Time Qed.

Lemma body_insert_nc: semax_body Vprog Gprog f_insert_nc insert_nc_spec.
Proof.
  start_function.
  unfold valid_pq.
  Intros arr junk lookup lookup_contents.
  destruct junk. { exfalso. unfold heap_size, heap_capacity in *. rewrite Zlength_app, Zlength_nil in H2. lia. }
  change (h0 :: junk) with ([h0] ++ junk) in *. rewrite app_assoc in *.
  rewrite linked_heap_array_split. Intros.
  assert (0 <= heap_size h) by apply Zlength_nonneg.
  forward.
  forward. unfold linked_heap_array, heap_array, heap_size in *. Intros. entailer!.
  unfold linked_heap_array at 1. Intros. unfold heap_array.
  assert (0 <= heap_size h < Zlength (heap_items h ++ [h0])). { autorewrite with sublist. unfold heap_size. rep_lia. }
  forward. { (* C typing issue? *) entailer!. rewrite Znth_map. apply I. trivial. }
  forward.
  forward.
  forward. { unfold lookup_array. entailer!. }
  (* Just before the call, let's do some cleanup *)
  deadvars!.
  rewrite upd_Znth_overwrite, upd_Znth_same, map_app, upd_Znth_app2, Zlength_map.
  unfold heap_size. simpl. rewrite Znth_app2, Zlength_map. rewrite Z.sub_diag. simpl.
  2,3,4,5: autorewrite with sublist; unfold heap_size in *; lia. rewrite Zlength_app, Zlength_one.
  rewrite upd_Znth0.
  change ([(Vint (Int.repr (fst (fst h0))), (Vint (Int.repr priority), Vint data))]) with 
    (map heap_item_rep [(fst (fst h0), Int.repr priority, data)]).
  rewrite <- map_app.
(*  replace (Zlength (heap_items h ++ [h0])) with (Zlength (heap_items h ++ [(fst (fst h0), Int.repr priority, data)])).
  2: do 2 rewrite Zlength_app, Zlength_one; lia. *)
  forward_call (heap_size h, arr, heap_items h ++ [(fst (fst h0), Int.repr priority, data)], lookup, lookup_contents).
    { unfold linked_heap_array, heap_array. unfold heap_size in *. repeat rewrite Zlength_app. repeat rewrite Zlength_one.
      entailer!.
      repeat intro. specialize (H5 i).
      rewrite Zlength_app, Zlength_one in H15. rewrite Zlength_app, Zlength_one in H5.
      specialize (H5 H15). rewrite <- H5. f_equal.
      assert (i < Zlength (heap_items h) \/ i = Zlength (heap_items h)) by lia.
      destruct H16. repeat rewrite Znth_app1. 2,3: lia. trivial.
      subst i. repeat rewrite Znth_app2. 2,3: lia. rewrite Z.sub_diag. trivial. }
    { split. repeat rewrite Zlength_app in *. repeat rewrite Zlength_one in *. unfold heap_size in *. lia.
      red. unfold heap_size. rewrite Zlength_correct, Nat2Z.id.
      apply weak_heapOrdered2_postpend. apply cmp_po. trivial. }
  Intro vret.
  forward.
  forward.
  destruct vret as [vret lookup'].
  Exists ((Z.to_nat (heap_capacity h))%nat, vret) (fst (fst h0)).
  unfold heap_capacity. rewrite Nat2Z.id. simpl fst.
  unfold valid_pq. entailer!.
  * transitivity (snd h ++ [(fst (fst h0), Int.repr priority, data)]); trivial. 
    change ((fst (fst h0), Int.repr priority, data) :: heap_items h) with ([(fst (fst h0), Int.repr priority, data)] ++ heap_items h).
    apply Permutation_app_comm.
  * Exists arr junk lookup lookup'. entailer!.
    + rewrite Zlength_app. apply Permutation_Zlength in H9.
      unfold heap_items. simpl in *. rewrite <- H9. unfold heap_capacity in *. simpl. rewrite <- H2.
      autorewrite with sublist. lia.
    + unfold heap_size, heap_capacity, heap_items. simpl fst in *. simpl snd in *.
      generalize (Permutation_Zlength _ _ _ H9); intro. rewrite <- H16.
      rewrite Zlength_app, Zlength_one in *. cancel.
      rewrite linked_heap_array_split. cancel.
      repeat rewrite Zlength_app. rewrite <- H16. unfold heap_array. entailer!.
      (* Show things are still linked correctly, a bit of a mess... *)
      eapply linked_correctly'_shuffle. apply H3.
      intros. apply H7. repeat intro.
      apply Permutation_Znth in H9. 2: auto. destruct H9 as [? [f [? [? ?]]]].
      rewrite H23 in H20. 2: lia.
      red in H21. repeat rewrite Zlength_app, Zlength_one in *.
      specialize (H21 (Z.to_nat j)). spec H21. lia.
      remember (Z.of_nat (f (Z.to_nat j))) as j'.
      specialize (H5 j'). spec H5. autorewrite with sublist; lia. rewrite Z.add_0_l in H5.
      assert (0 <= j' < Zlength (heap_items h) \/ j' = Zlength (heap_items h)) by lia. destruct H24.
      - rewrite Znth_app1 in H20; rewrite Znth_app1 in H5; try lia.
        rewrite H20 in H5. specialize (H3 i H18). lia.
      - subst j'. rewrite Znth_app2 in H20; rewrite Znth_app2 in H5; try lia.
        rewrite H24, Z.sub_diag, Znth_0_cons in H20, H5. 
        unfold heap_item_key in H20 at 1. simpl in H20.
        specialize (H3 i H18). rewrite <- H20 in H3. unfold heap_item_key in H5. lia.
Time Qed.

Lemma body_remove_min_nc: semax_body Vprog Gprog f_remove_min_nc remove_min_nc_spec.
Proof.
  start_function.
  unfold valid_pq.
  Intros arr junk lookup lookup_contents.
  assert_PROP (linked_correctly (heap_items h ++ junk) lookup_contents). { unfold linked_heap_array. entailer!. }
  rename H3 into Hz.
  rewrite linked_heap_array_split. Intros.
  destruct h. destruct l. inversion H.
  unfold heap_items, heap_capacity, heap_size in *. simpl in H, H0, H1 |-*. clear H.
  generalize (foot_split_spec _ (h :: l)).
  case foot_split. destruct o; intro. 2: destruct H; subst l0; discriminate.
  rename h into root. rename h0 into foot.
  assert (Hx: Zlength l = Zlength (root :: l) - 1) by (rewrite Zlength_cons; lia).
  assert (Hy : 0 <= Zlength l) by apply Zlength_nonneg.
  forward.
  forward.
  forward. { unfold linked_heap_array, heap_array. Intros. entailer!. }
  forward. { unfold linked_heap_array, lookup_array. Intros. entailer!. }
  forward_call (0, Zlength l, arr, root :: l, lookup, lookup_contents).
    { entailer!. simpl. congruence. }
    { lia. }
  Intros lookup_contents'.
  unfold linked_heap_array at 1. (* Not delighted with these unfolds... *)
  unfold heap_array. Intros.
  forward.
    { entailer!. rewrite Zlength_Zexchange. lia. }
    { entailer!. rewrite Znth_map. rewrite <- Hx. rewrite Znth_Zexchange'; try lia. rewrite Znth_0_cons.
      unfold heap_item_rep. trivial. rewrite Zlength_Zexchange. lia. }
  unfold hitem.
  forward.
  forward.
    { entailer!. rewrite Zlength_Zexchange. lia. }
    { entailer!. rewrite Znth_map. 2: rewrite Zlength_Zexchange; lia.
      rewrite <- Hx. rewrite Znth_Zexchange'; try lia. rewrite Znth_0_cons.
      apply Forall_map in H9.
      rewrite Forall_Znth in H9. specialize (H9 (Zlength l)). do 2 rewrite Zlength_map in H9. rewrite Zlength_Zexchange in H9.
      spec H9. lia.
      rewrite Znth_map in H9. 2: rewrite Zlength_map, Zlength_Zexchange; lia.
      rewrite Znth_map in H9. 2: rewrite Zlength_Zexchange; lia.
      rewrite Znth_Zexchange' in H9; try lia.
      (* Flailing around solves the goal... *)
      apply H9. discriminate. }
  forward.
  forward.
    { entailer!. rewrite Zlength_Zexchange. lia. }
    { entailer!. rewrite Znth_map. rewrite <- Hx. rewrite Znth_Zexchange'; try lia. rewrite Znth_0_cons.
      unfold heap_item_rep. trivial. rewrite Zlength_Zexchange. lia. }
  forward.
change (data_at _ _ _ arr) with (heap_array (Zexchange (root :: l) 0 (Zlength l)) arr).
deadvars!.
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
    forward_call (0, arr, @nil heap_item, 0, lookup, lookup_contents'); rewrite Zlength_nil. 
      { unfold linked_heap_array, heap_array. rewrite data_at_isptr. entailer. (* Surely there's a less heavy hammer way to do this? *)
        rewrite data_at_zero_array_eq; auto. entailer!. repeat intro. rewrite Zlength_nil in H14. lia. }
      { split; auto. split; auto. split. rep_lia. split. rep_lia.
        apply hOwhO. apply cmp_po. apply heapOrdered_empty. }
    (* Prove postcondition *)
    Intro vret. destruct vret as [vret lookup_contents''].
    forward.
    Exists (n, vret) root. entailer. (* Surely there's a less heavy hammer way to do this? *)
    (* destruct H1. *)
    apply Permutation_nil in H7. simpl in H7. subst vret. clear (* H *) Hy.
    unfold linked_heap_array. Intros.
    sep_apply harray_emp. rewrite emp_sepcon.
    rewrite Zlength_Zexchange. rewrite Zexchange_eq.
    do 2 rewrite fold_heap_array. unfold valid_pq, hitem.
    apply andp_right. apply prop_right. auto.
    Exists arr (root :: junk) lookup lookup_contents''. simpl. unfold linked_heap_array. entailer!.
    2: rewrite <- heap_array_split; apply derives_refl.
    rewrite Zlength_nil in *. rewrite Zexchange_eq in *. simpl in Hz, H3, H6, H.
    change (root :: junk) with ([root] ++ junk). red.
    apply linked_correctly'_shuffle with lookup_contents'.
    apply linked_correctly_app3; trivial.
    apply linked_correctly'_shuffle with lookup_contents. trivial.
    intros. apply H4; repeat intro. rewrite Zlength_one in H18. assert (j = 0) by lia. subst j. rewrite Znth_0_cons in H19.
specialize (Hz (i0 + 1)). spec Hz. rewrite Zlength_cons; lia.
Search Znth cons.
rewrite Znth_pos_cons in Hz. 2: lia. replace (i0 + 1 - 1) with i0 in Hz by lia.
specialize (H5 0 H18). rewrite Znth_0_cons in H5. simpl in H5.
specialize (H4 (i0 + 1)).
rewrite H4 in Hz.
rewrite <- H19 in Hz.

 simpl. H17).
rewrite <- H19 in H3. rewrite Zlength_one in H3.
red in H4.

Search lookup_contents'.

specialize 
Search Znth 0.

 rewrite Znth_0.

    admit.
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
(* Perhaps a BUG, related to overly-aggressive unfolding of fst/snd that has to be repaired later? 
   I end up with the messy LHS and would really prefer the nicer RHS. *)
Lemma heap_item_rep_morph: forall x y,
  (fst (heap_item_rep x), (fst (snd (heap_item_rep y)), snd (snd (heap_item_rep x)))) = 
  heap_item_rep (fst (fst x), snd (fst y), snd x).
Proof. unfold heap_item_rep. destruct x,y; reflexivity. Qed.

Lemma body_exch: semax_body Vprog Gprog f_exch exch_spec.
Proof.
  start_function.
  unfold linked_heap_array, heap_array. Intros.
  forward. (* BUG, fst and snd are unfolded too far *) { rewrite Znth_map; trivial. entailer!. }
  forward. { rewrite Znth_map; trivial. entailer!.
    (* BUG?  Maybe this pain isn't totally needed... *)
    apply Forall_map in H4.
    rewrite Forall_Znth in H4. specialize (H4 j). do 2 rewrite Zlength_map in H4.
    specialize (H4 H). rewrite Znth_map in H4. 2: rewrite Zlength_map; trivial.
    simplify_value_fits in H4. destruct H4 as [? [? ?]].
    rewrite Znth_map in H6; trivial.
    apply H6. discriminate. }
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
      (* BUG?  So ugly... is there no easier way? *)
      (* BUG?  These "replace"s are very slow... *)
      replace (let (x, _) := heap_item_rep _ in x) with (fst (heap_item_rep (Znth j arr_contents))) in H5 by trivial.
      replace (let (x, _) := let (_, y) := heap_item_rep _ in y in x) with (fst (snd (heap_item_rep (Znth k arr_contents)))) in H5 by trivial.
      replace (let (_, y) := let (_, y) := heap_item_rep _ in y in y) with (snd (snd (heap_item_rep (Znth j arr_contents)))) in H5 by trivial.
      (* BUG? here is where I need to repack the unpacked rep... *)
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
Fail forward. (* BUG, wrong error message here *)
  (* Some cleanup *)
  repeat rewrite upd_Znth_same, upd_Znth_overwrite.
  3,4: rewrite Zlength_upd_Znth. 2,3,4,5: rewrite Zlength_map; lia.
  repeat rewrite Znth_map. 2,3: lia.
  replace (let (x, _) := heap_item_rep (Znth k arr_contents) in x) with (fst (heap_item_rep (Znth k arr_contents))) by trivial.
simpl fst.
unfold lookup_array.
Fail forward. (* BUG, should let me prove it's within bounds *)
  (* This is ugly and very confusing, if you try to "forward" now, or anywhere between the cleanup and here... *)
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
