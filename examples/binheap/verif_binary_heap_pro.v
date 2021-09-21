Require Import RelationClasses.
Require Import VST.floyd.proofauto.
Require Import CertiGraph.binheap.binary_heap_model.
Require Import CertiGraph.binheap.binary_heap_Zmodel.
Require Import CertiGraph.binheap.binary_heap_pro.
Require Import CertiGraph.binheap.binary_heap_malloc_spec.
Require Import CertiGraph.binheap.env_binary_heap_pro.
Require Import CertiGraph.binheap.spec_binary_heap_pro.

Definition Gprog : funspecs :=
  ltac:(with_library prog [exch_spec;
                          less_spec;
                          swim_spec;
                          sink_spec; 
                          pq_remove_min_nc_spec;
                          pq_insert_nc_spec; 
                          pq_size_spec;
                          capacity_spec;
                          mallocN_spec;
                          freeN_spec;
                          pq_make_spec;
                          pq_free_spec;
                          pq_edit_priority_spec]).

Set Nested Proofs Allowed.

Lemma body_free: semax_body Vprog Gprog f_pq_free pq_free_spec.
Proof.
  start_function. unfold valid_pq, linked_heap_array, heap_array, lookup_array.
  Intros arr junk lookup lookup_contents.
  forward.
  sep_apply (data_at_data_at_ Tsh (tarray t_item (Zlength (heap_items h ++ junk)))).
  sep_apply free_items.
  sep_apply (data_at_data_at_ Tsh (tarray tuint (Zlength lookup_contents))).
  sep_apply free_lookup.
  simpl.
  rewrite H2. change (16 / 4) with 4.
  rewrite Z.mul_comm, Z_div_mult.
  change 12 with (3 * 4) at 1.
  rewrite <- Z.mul_assoc.
  rewrite (Z.mul_comm 4), Z.mul_assoc, Z_div_mult.
  2,3: lia.
  rewrite H.
  rewrite (Z.mul_comm (heap_capacity h)).
  forward_call (lookup, heap_capacity h).
  forward.
  change 12 with (4 * 3). rewrite <- Z.mul_assoc.
  forward_call (arr, 3 * heap_capacity h).
  sep_apply data_at_data_at_.
  sep_apply free_pq.
  forward_call (pq, 4).
  entailer!.
Time Qed.

Lemma body_pq_make: semax_body Vprog Gprog f_pq_make pq_make_spec.
Proof.
  start_function.
  forward_call (sizeof(Tstruct _structPQ noattr)).
  Intros pq.
  sep_apply malloc_pq.
  forward_call (sizeof(tuint) * size). 
   { simpl; lia. }
  Intros table.
  sep_apply malloc_lookup. lia.
  forward_call ((sizeof(Tstruct _structItem noattr) * size)).
  Intros arr.
  sep_apply malloc_items. lia.

  forward_for_simple_bound size
    (EX i : Z,
     PROP ()
     LOCAL (temp _table (pointer_val_val table);
            temp _arr (pointer_val_val arr);
            temp _size (Vint (Int.repr size));
            temp _pq (pointer_val_val pq))
(* BUG, you can't just use "data_at Tsh (tarray t_item size) (initializing_item_list size size) v" *)
     SEP (initializing_item_array i size (pointer_val_val arr);
          free_tok (pointer_val_val arr) (sizeof (Tstruct _structItem noattr) * size);
          data_at Tsh (tarray tuint size) (initializing_inc_list i size) (pointer_val_val table);
          free_tok (pointer_val_val table) (sizeof tuint * size);
          data_at_ Tsh t_pq (pointer_val_val pq);
          free_tok (pointer_val_val pq) (sizeof (Tstruct _structPQ noattr)))).
  { entailer!. unfold initializing_item_array, initializing_inc_list, initializing_item_list.
    simpl. replace (size - 0) with size by lia. cancel. }
  { unfold initializing_item_array.
    forward.
    forward.
    rewrite upd_Znth_overwrite, upd_Znth_same. simpl snd. simpl fst.
    2,3: rewrite Zlength_initializing_item_list; lia.
    forward.
    rewrite upd_Znth_overwrite, upd_Znth_same. simpl snd. simpl fst.
    2,3: rewrite Zlength_initializing_item_list; lia.
    forward.
    (* Prove loop invariant *)
    rewrite initializing_inc_list_inc. 2: lia.
    rewrite initializing_item_list_inc. 2: lia.
    entailer!. }
  forward.
  forward.
  forward.
  forward.
  forward.
  (* Prove postcondition *)
  Exists (pointer_val_val pq) (Z.to_nat size, @nil heap_item).
  unfold valid_pq, heap_size, heap_capacity. entailer!. lia.
  Exists (pointer_val_val arr) (initial_item_list size) (pointer_val_val table) (List_ext.nat_inc_list (Z.to_nat size)).
  unfold initializing_item_array, linked_heap_array, heap_array, lookup_array.
  rewrite Zlength_app, Zlength_nil.
  rewrite initializing_inc_list_done, initializing_item_list_done.
  rewrite Z2Nat.id, Zlength_initial_item_list, List_ext.nat_inc_list_Zlength. 2,3: lia.
  entailer!.
  { split. 
    apply heapOrdered_empty. simpl heap_items. simpl.
    apply initial_link_ok. lia. }
  { rewrite Z2Nat.id. cancel. lia. }
Time Qed.

Lemma body_edit_priority: semax_body Vprog Gprog f_pq_edit_priority pq_edit_priority_spec.
Proof.
  start_function.
  unfold valid_pq.
  Intros arr junk lookup lookup_contents.
  rename H0 into Hxx. rename H1 into H0. rename H2 into H1. rename H3 into H2.
  assert_PROP (linked_correctly (heap_items h ++ junk) lookup_contents). { unfold linked_heap_array. entailer!. }
  rewrite linked_heap_array_split. Intros.
  forward. { unfold linked_heap_array, lookup_array. Intros. entailer!. }
  forward. { unfold linked_heap_array, heap_array. Intros. entailer!. }
  unfold linked_heap_array, lookup_array. Intros.
  generalize H; intro.
  apply In_Znth_iff in H6.
  destruct H6 as [target [? ?]].
  destruct H5.
  unfold proj_keys in H6, H7. rewrite Zlength_map in H6. rewrite Znth_map in H7; auto.
  destruct (H8 target H6).
  forward.
  unfold heap_array.
  forward. { entailer!. } { entailer!. rewrite Znth_map. 2: lia. rewrite H10. apply I. }
  forward. { entailer!. }
  rewrite Znth_map. 2: { rewrite <- H7. rewrite H10. lia. }
  rewrite <- H7. rewrite H10. change (0 + target) with target in *.
  remember (Znth target (heap_items h)) as hi.
  remember (key, newpri, heap_item_payload hi) as new_hi.
  forward_if.
  * assert (cmp_rel (key, newpri, heap_item_payload hi) hi).
      { unfold cmp_rel. unfold cmp. unfold heap_item_priority. simpl. rewrite H11. trivial. }
    forward_call (target, arr, upd_Znth target (heap_items h) new_hi, lookup, lookup_contents).
      { unfold linked_heap_array, heap_array, lookup_array. entailer!.
        * split; trivial. simpl. rewrite Zlength_upd_Znth. intros.
          replace (heap_item_key (Znth i
            (upd_Znth (Znth (heap_item_key hi) lookup_contents) (heap_items h)
              (heap_item_key hi, newpri, heap_item_payload hi)))) 
            with (heap_item_key (Znth i (heap_items h))).
          apply H8; trivial.
          rewrite <- Znth_map. 2: lia.
          rewrite <- (Znth_map _ heap_item_key). 2: rewrite Zlength_upd_Znth; lia.
          rewrite <- upd_Znth_map. unfold heap_item_key at 4. simpl fst.
          case (eq_dec i (Znth (heap_item_key hi) lookup_contents)); intro.
          2: rewrite Znth_upd_Znth_diff; auto.
          subst i.
          rewrite Znth_upd_Znth_same.
          rewrite Znth_map.
          rewrite <- Heqhi. trivial.
          lia. rewrite Zlength_map. lia. trivial.
        * rewrite <- upd_Znth_map. rewrite Zlength_upd_Znth. cancel. }
      { rewrite Zlength_upd_Znth. split; trivial.
        generalize (Znth_nth_error _ _ H6); intro.
        rewrite <- Heqhi in H13.
        generalize (heapOrdered_lower_priority_weak_heapOrdered2 _ _ _ _ H1 _ _ H13 _ H12); intros.
        rewrite upd_Znth_update. rewrite Heqnew_hi. apply H14. trivial. }
    Intros vret. destruct vret as [heap_contents' lookup_contents'].
    Exists (fst h, heap_contents'). entailer!.
    + unfold heap_items. simpl snd. simpl fst in H15. symmetry in H15.
      transitivity (upd_Znth (Znth (heap_item_key hi) lookup_contents) 
             (heap_items h) (heap_item_key hi, newpri, heap_item_payload hi)); trivial.
      replace (upd_Znth (Znth (heap_item_key hi) lookup_contents) (heap_items h)
         (heap_item_key hi, newpri, heap_item_payload hi))
        with (update_pri_by_key (snd h) (heap_item_key hi) newpri). reflexivity.
      unfold update_pri_by_key.
      apply List_ext.list_eq_Znth; rewrite Zlength_map. { rewrite Zlength_upd_Znth. trivial. }
      intros.
      case (eq_dec i (Znth (heap_item_key hi) lookup_contents)); intro.
      - subst i. rewrite Znth_upd_Znth_same. 2,3: lia.
        rewrite Znth_map. 2: lia.
        change (snd h) with (heap_items h). rewrite <- Heqhi.
        unfold update_pri_if_key. case Z.eq_dec; auto. intro Hx; contradiction.
      - rewrite Znth_upd_Znth_diff; auto.
        rewrite Znth_map. 2: lia.
        unfold update_pri_if_key. case Z.eq_dec; intro; auto.
        destruct (H8 _ H7).
        unfold heap_items in H21.
        rewrite <- e in H21. lia.
    + unfold valid_pq. Exists arr junk lookup lookup_contents'.
      rewrite linked_heap_array_split. unfold heap_capacity, heap_size, heap_items. simpl fst in *. simpl snd in *.
      generalize H15; intro. apply Permutation_Zlength in H7. rewrite Zlength_upd_Znth in H7.
      unfold heap_items in H7. do 2 rewrite Zlength_app. rewrite H7. entailer!.
      (* Pure part inside spatial part. *)
      split. { destruct H13. apply Permutation_Zlength in H13. rewrite <- H13. trivial. }
      split. { rewrite <- H7. unfold heap_items, heap_capacity in H2. 
        rewrite <- H2. rewrite Zlength_app; trivial. }
      clear H17 H18 H10 H21 H11.
      destruct H13. split. eapply Permutation_NoDup; eauto.
      simpl. intros. destruct H3.
      generalize (H17 ((Zlength (heap_items h)) + i)); intro. spec H18.
      rewrite Zlength_app; rep_lia. destruct H18.
      rewrite Znth_app2 in H18, H21. 2,3: lia.
      replace (Zlength (heap_items h) + i - Zlength (heap_items h)) with i in * by lia.
      generalize H10; intro. apply Permutation_Zlength in H22. rewrite <- H22. split; trivial.
      rewrite <- H11. rewrite H21. apply Permutation_Zlength in H15. rewrite <- H15.
      rewrite Zlength_upd_Znth. lia.
      repeat intro. rename H24 into Hk.
      rename H21 into Hkk.
      apply Permutation_Znth in H15. 2: apply (0, Int.zero, Int.zero).
      rewrite Zlength_upd_Znth in H15. destruct H15 as [? [f [? [? ?]]]].
      rewrite H25 in Hk. 2: lia.
      specialize (H17 (Z.of_nat (f (Z.to_nat j)))). spec H17.
      specialize (H21 (Z.to_nat j)). spec H21. lia. rewrite Zlength_app. lia.
      destruct H17.
      rewrite Znth_app1 in H17, H26. 2,3: specialize (H21 (Z.to_nat j)); lia.
      rewrite <- Znth_map in Hk. 2: rewrite Zlength_upd_Znth; specialize (H21 (Z.to_nat j)); lia.
      rewrite <- upd_Znth_map in Hk. unfold heap_item_key in Hk at 3; simpl in Hk.
      rewrite upd_Znth_map in Hk. 
      rewrite Znth_map in Hk. 2: rewrite Zlength_upd_Znth; specialize (H21 (Z.to_nat j)); lia.
      clear PNarr PNlookup PNpq H16.
      replace (upd_Znth (Znth (heap_item_key hi) lookup_contents) (heap_items h) hi) with (heap_items h) in Hk.
      rewrite Hk in H26. rewrite Hkk in H26. specialize (H21 (Z.to_nat j)); lia.
      rewrite In_Znth_iff in H. destruct H as [spot [? ?]].
      generalize (H8 spot); intro. spec H27. unfold proj_keys in H. rewrite Zlength_map in H. apply H.
      destruct H27.
      unfold proj_keys in H16.
      rewrite Znth_map in H16. 2: { unfold proj_keys in H. rewrite Zlength_map in H. rep_lia. }
      rewrite H16 in H28.
      rewrite H28.
      rewrite Heqhi. rewrite H28.
      rewrite upd_Znth_same_Znth. 2: lia. trivial.
  * assert (cmp_rel hi (heap_item_key hi, newpri, heap_item_payload hi)).
      { unfold cmp_rel. unfold cmp. unfold heap_item_priority. simpl.
        apply lt_inv in H11.
        case_eq (Int.lt newpri (snd (fst hi))); auto. intro.
        apply lt_inv in H12. lia. }
    forward.
    forward_call (target, arr, upd_Znth target (heap_items h) new_hi, heap_size h, lookup, lookup_contents).
      { unfold linked_heap_array, heap_array, lookup_array. entailer!.
        * split; trivial. simpl. rewrite Zlength_upd_Znth. intros.
          replace (heap_item_key (Znth i
            (upd_Znth (Znth (heap_item_key hi) lookup_contents) (heap_items h)
              (heap_item_key hi, newpri, heap_item_payload hi)))) 
            with (heap_item_key (Znth i (heap_items h))).
          apply H8; trivial.
          rewrite <- Znth_map. 2: lia.
          rewrite <- (Znth_map _ heap_item_key). 2: rewrite Zlength_upd_Znth; lia.
          rewrite <- upd_Znth_map. unfold heap_item_key at 4. simpl fst.
          case (eq_dec i (Znth (heap_item_key hi) lookup_contents)); intro.
          2: rewrite Znth_upd_Znth_diff; auto.
          subst i.
          rewrite Znth_upd_Znth_same.
          rewrite Znth_map.
          rewrite <- Heqhi. trivial.
          lia. rewrite Zlength_map. lia. trivial.
        * rewrite <- upd_Znth_map. rewrite Zlength_upd_Znth. cancel. }
      { rewrite Zlength_upd_Znth. split. lia. split; trivial.
        split. lia. split. intros.
        unfold heap_size. rewrite Zlength_app in H2. rep_lia.
        generalize (Znth_nth_error _ _ H6); intro.
        rewrite <- Heqhi in H13.
        generalize (heapOrdered_raise_priority_weak_heapOrdered _ _ _ _ H1 _ _ H13 _ H12); intros.
        rewrite upd_Znth_update. 2: trivial. rewrite Heqnew_hi. rewrite H7 in H14. apply H14. }
    Intros vret. destruct vret as [heap_contents' lookup_contents'].
    Exists (fst h, heap_contents'). entailer!.
    + unfold heap_items. simpl snd. simpl fst in H15. symmetry in H15.
      transitivity (upd_Znth (Znth (heap_item_key hi) lookup_contents) 
             (heap_items h) (heap_item_key hi, newpri, heap_item_payload hi)); trivial.
      replace (upd_Znth (Znth (heap_item_key hi) lookup_contents) (heap_items h)
         (heap_item_key hi, newpri, heap_item_payload hi))
        with (update_pri_by_key (snd h) (heap_item_key hi) newpri). reflexivity.
      unfold update_pri_by_key.
      apply List_ext.list_eq_Znth; rewrite Zlength_map. { rewrite Zlength_upd_Znth. trivial. }
      intros.
      case (eq_dec i (Znth (heap_item_key hi) lookup_contents)); intro.
      - subst i. rewrite Znth_upd_Znth_same. 2,3: lia.
        rewrite Znth_map. 2: lia.
        change (snd h) with (heap_items h). rewrite <- Heqhi.
        unfold update_pri_if_key. case Z.eq_dec; auto. intro Hx; contradiction.
      - rewrite Znth_upd_Znth_diff; auto.
        rewrite Znth_map. 2: lia.
        unfold update_pri_if_key. case Z.eq_dec; intro; auto.
        destruct (H8 _ H7).
        unfold heap_items in H21.
        rewrite <- e in H21. lia.
    + unfold valid_pq. Exists arr junk lookup lookup_contents'.
      rewrite linked_heap_array_split. unfold heap_capacity, heap_size, heap_items. simpl fst in *. simpl snd in *.
      generalize H15; intro. apply Permutation_Zlength in H7. rewrite Zlength_upd_Znth in H7.
      unfold heap_items in H7. do 2 rewrite Zlength_app. rewrite H7. entailer!.
      (* Pure part inside spatial part. *)
      split. { destruct H13. apply Permutation_Zlength in H13. rewrite <- H13. trivial. }
      split. { rewrite <- H7; unfold heap_items, heap_capacity in H2; rewrite <- H2; rewrite Zlength_app; trivial. }
      clear H17 H18 H10 H21 H11.
      destruct H13. split. eapply Permutation_NoDup; eauto.
      simpl. intros. destruct H3.
      generalize (H17 ((Zlength (heap_items h)) + i)); intro. spec H18.
      rewrite Zlength_app; rep_lia. destruct H18.
      rewrite Znth_app2 in H18, H21. 2,3: lia.
      replace (Zlength (heap_items h) + i - Zlength (heap_items h)) with i in * by lia.
      generalize H10; intro. apply Permutation_Zlength in H22. rewrite <- H22. split; trivial.
      rewrite <- H11. rewrite H21. apply Permutation_Zlength in H15. rewrite <- H15.
      rewrite Zlength_upd_Znth. lia.
      repeat intro. rename H24 into Hk.
      rename H21 into Hkk.
      apply Permutation_Znth in H15. 2: apply (0, Int.zero, Int.zero).
      rewrite Zlength_upd_Znth in H15. destruct H15 as [? [f [? [? ?]]]].
      rewrite H25 in Hk. 2: lia.
      specialize (H17 (Z.of_nat (f (Z.to_nat j)))). spec H17.
      specialize (H21 (Z.to_nat j)). spec H21. lia. rewrite Zlength_app. lia.
      destruct H17.
      rewrite Znth_app1 in H17, H26. 2,3: specialize (H21 (Z.to_nat j)); lia.
      rewrite <- Znth_map in Hk. 2: rewrite Zlength_upd_Znth; specialize (H21 (Z.to_nat j)); lia.
      rewrite <- upd_Znth_map in Hk. unfold heap_item_key in Hk at 3; simpl in Hk.
      rewrite upd_Znth_map in Hk. 
      rewrite Znth_map in Hk. 2: rewrite Zlength_upd_Znth; specialize (H21 (Z.to_nat j)); lia.
      clear PNarr PNlookup PNpq H16.
      replace (upd_Znth (Znth (heap_item_key hi) lookup_contents) (heap_items h) hi) with (heap_items h) in Hk.
      rewrite Hk in H26. rewrite Hkk in H26. specialize (H21 (Z.to_nat j)); lia.
      rewrite In_Znth_iff in H. destruct H as [spot [? ?]].
      generalize (H8 spot); intro. spec H27. unfold proj_keys in H. rewrite Zlength_map in H. apply H.
      destruct H27.
      unfold proj_keys in H16.
      rewrite Znth_map in H16. 2: { unfold proj_keys in H. rewrite Zlength_map in H. rep_lia. }
      rewrite H16 in H28.
      rewrite H28.
      rewrite Heqhi. rewrite H28.
      rewrite upd_Znth_same_Znth. 2: lia. trivial.
Time Qed.

Lemma body_remove_min_nc: semax_body Vprog Gprog f_pq_remove_min_nc pq_remove_min_nc_spec.
Proof.
  start_function.
  unfold valid_pq.
  Intros arr junk lookup lookup_contents.
  rename H0 into Hxx. rename H1 into H0. rename H2 into H1. rename H3 into H2.
  assert_PROP (linked_correctly (heap_items h ++ junk) lookup_contents). { unfold linked_heap_array. entailer!. }
  rename H3 into Hz.
  rewrite linked_heap_array_split. Intros.
  destruct h. destruct l. inversion H.
  unfold heap_items, heap_capacity, heap_size in *. simpl in H, H0, H1, Hz |-*. clear H.
  generalize (foot_split_spec _ (h :: l)).
  case foot_split. destruct o; intro. 2: destruct H; subst l0; discriminate.
  rename h into root. rename h0 into foot.
  assert (Hx: Zlength l = Zlength (root :: l) - 1) by (rewrite Zlength_cons; lia).
  assert (Hy : 0 <= Zlength l) by apply Zlength_nonneg.
  forward.
  forward.
  forward.
  forward. { unfold linked_heap_array, heap_array, lookup_array. Intros. entailer!. }
  forward. { unfold linked_heap_array, heap_array, lookup_array. Intros. entailer!. }
  forward_call (0, Zlength l, arr, root :: l, lookup, lookup_contents).
    { entailer!. simpl. congruence. }
  Intros lookup_contents'.
  forward.
  forward.
  unfold linked_heap_array at 1. (* Not delighted with these unfolds... *)
  unfold heap_array at 1. Intros.
  forward. 
    { entailer!. rewrite Zlength_Zexchange. lia. }
    { entailer!. rewrite Znth_map. rewrite <- Hx. rewrite Znth_Zexchange'; try lia. rewrite Znth_0_cons.
      unfold heap_item_rep. trivial. rewrite Zlength_Zexchange. lia. }
  unfold hitem_.
  forward.
  forward.
  forward.
  forward.
    { entailer!. rewrite Zlength_Zexchange. lia. }
    { entailer!. rewrite Znth_map. rewrite <- Hx. rewrite Znth_Zexchange'; try lia. rewrite Znth_0_cons.
      unfold heap_item_rep. trivial. rewrite Zlength_Zexchange. lia. }
  forward.
  forward.
  forward.
  forward.
    { entailer!. rewrite Zlength_Zexchange. lia. }
    { entailer!. rewrite Znth_map. rewrite <- Hx. rewrite Znth_Zexchange'; try lia. rewrite Znth_0_cons.
      unfold heap_item_rep. trivial. rewrite Zlength_Zexchange. lia. }
  forward.
  forward.
  forward.
  forward.
  (* Time to cleanup! *)
  deadvars!.
  rewrite <- Hx.
  rewrite Znth_map. 2: rewrite Zlength_Zexchange; lia.
  rewrite Znth_Zexchange'; try lia. rewrite Znth_0_cons.
  change (data_at _ t_item _) with (data_at Tsh t_item (heap_item_rep root)).
  autorewrite with norm. rewrite <- Hx.
  rewrite H.
  (* Take cases... *)
  destruct l.
  * (* corner case: heap is now empty *)
    destruct l0. 2: destruct l0; discriminate.
    inversion H. subst foot. clear H Hx.
    simpl.
    forward_call (0, arr, @nil heap_item, 0, lookup, lookup_contents');
      try rewrite Zlength_nil. 
      { unfold linked_heap_array, heap_array. rewrite data_at_isptr. entailer. (* Surely there's a less heavy hammer way to do this? *)
        rewrite data_at_zero_array_eq; auto. entailer!. split.
        destruct H5; trivial. repeat intro. rewrite Zlength_nil in H15. lia. }
      { apply hOwhO. apply cmp_po. apply heapOrdered_empty. }
    (* Prove postcondition *)
    Intro vret. destruct vret as [vret lookup_contents''].
    Exists (n, vret) root. entailer. (* Surely there's a less heavy hammer way to do this? *)
    (* destruct H1. *)
    apply Permutation_nil in H7. simpl in H7. subst vret. clear (* H *) Hy.
    unfold linked_heap_array. Intros.
    sep_apply harray_emp. rewrite emp_sepcon.
    rewrite Zlength_Zexchange.
    do 2 rewrite fold_heap_array. unfold valid_pq, hitem.
    apply andp_right. apply prop_right. auto.
    Exists arr (root :: junk) lookup lookup_contents''. simpl. unfold linked_heap_array. entailer!.
    2: rewrite <- heap_array_split; apply derives_refl.
    split. { destruct H. apply Permutation_Zlength in H. simpl in H. rewrite <- H.
             destruct H4. apply Permutation_Zlength in H4. rewrite <- H4. trivial. }
    rewrite Zlength_nil in *. rewrite Zexchange_eq in *. simpl in Hz, H3, H6, H.
    change (root :: junk) with ([root] ++ junk). red.
    destruct H, H4.
    apply linked_correctly'_shuffle with lookup_contents'; trivial.
    apply linked_correctly_app3; trivial.
    apply linked_correctly'_shuffle with lookup_contents; trivial.
    + intros.
      rewrite H19; trivial. intros. rewrite Zlength_one in H21. assert (j = 0) by lia. subst j.
      change (Znth 0 [root]) with root.
      intro.
      clear -Hz H22 H20.
      destruct Hz.
      assert (0 <= 0 < Zlength (root :: junk)) by (rewrite Zlength_cons; rep_lia).
      destruct (H0 _ H1).
      assert (0 <= (1 + i0) < Zlength (root :: junk)) by (rewrite Zlength_cons; rep_lia).
      destruct (H0 _ H4).
      clear -H22 H3 H6 H20.
      rewrite Znth_0_cons, H22 in H3.
      change (root :: junk) with ([root] ++ junk) in H6.
      rewrite Znth_app2 in H6; rewrite Zlength_one in *. 2: lia.
      replace (1 + i0 - 1) with i0 in H6 by lia. rewrite H3 in H6. lia.
    + intros. rewrite H18; auto. rewrite Zlength_nil. lia.
  * (* main line: heap still has items in it *)
    destruct l0; inversion H. subst h0.
    assert (Zlength (h :: l) = Zlength (root :: l0)).
    { rewrite H8, Zlength_app, Zlength_one, Zlength_cons. lia. }
    rewrite H6, Zexchange_head_foot.
    rewrite fold_heap_array.
    sep_apply fold_linked_heap_array.
    { rewrite H8 in H5.
      replace (Zlength (l0 ++ [foot])) with (Zlength (root :: l0)) in H5 by congruence.
      rewrite app_comm_cons in H5.
      rewrite Zexchange_head_foot in H5. trivial. }
    rewrite linked_heap_array_split. Intros.
    forward_call (0, arr, (foot :: l0), Zlength (foot :: l0), lookup, lookup_contents').
      { split. intros _. generalize (Zlength_nonneg junk); intro.
        simpl in H2. repeat rewrite Zlength_cons in *. rewrite Zlength_app in H2. lia.
        apply weak_heapOrdered_root with root.
        rewrite H8, app_comm_cons in H1.
        apply heapOrdered_cutfoot in H1. trivial. }
    (* Prove postcondition *)
    Intros vret. destruct vret as [vret lookup_contents''].
    Exists (n, vret) root. simpl fst. simpl snd. unfold hitem, heap_item_rep, heap_size, heap_capacity. entailer!.
      { (* Pure part *)
        split. constructor. rewrite H8. transitivity ([foot] ++ l0). apply Permutation_app_comm. destruct H4. auto.
        generalize (root_minimal _ _ _ _ H1 root eq_refl); intro.
        rewrite H8 in H16. apply Forall_inv_tail in H16.
        eapply forall_permutation. apply H16. transitivity ([foot] ++ l0). apply Permutation_app_comm. simpl. tauto. }
    unfold valid_pq. Exists arr (root :: junk) lookup lookup_contents''. unfold heap_size, heap_capacity. simpl.
    replace (Zlength vret) with (Zlength (root :: l0)). 2: { apply Permutation_Zlength in H11. trivial. }
(*    destruct H4. *)
    entailer!. { (* Pure part inside spatial part *)
      split. { destruct H9. apply Permutation_Zlength in H9. simpl in H9. rewrite <- H9.
             destruct H4. apply Permutation_Zlength in H4. rewrite <- H4. trivial. }
      simpl in *. rewrite <- H2. apply Permutation_Zlength in H11. autorewrite with sublist. rewrite <- H11.
      autorewrite with sublist in *. lia. }
    (* Spatial part, this seems a bit uglier than necessary? *)
    change (root :: junk) with ([root] ++ junk). rewrite app_assoc. do 2 rewrite linked_heap_array_split.
    generalize H11; intro Hq.
    apply Permutation_Zlength in H11.
    rewrite app_comm_cons. rewrite Zlength_app. rewrite H11. rewrite Zlength_app.
    assert (Zlength (root :: l0) = Zlength vret). { simpl in H11. rewrite <- H11. do 2 rewrite Zlength_cons. trivial. }
    do 3 rewrite app_comm_cons.
    do 4 rewrite Zlength_app.
    rewrite H16.
    do 2 rewrite Zlength_one.
    rewrite Zlength_cons. simpl fst in *.
    rewrite H8. replace (Z.succ (Zlength (l0 ++ [foot])) + Zlength junk) with (Zlength vret + 1 + Zlength junk).
    2: { rewrite Zlength_app. rewrite <- H16.  rewrite Zlength_cons, Zlength_one. rep_lia. }
    entailer!. simpl in *. clear H13 H14 H15.
    split.
    + apply linked_correctly'_shuffle with lookup_contents'; trivial.
      apply linked_correctly'_shuffle with lookup_contents; trivial.
      replace (Zlength vret + 1) with (Zlength (root :: h :: l)); trivial.
      rewrite <- H16. rewrite H8. do 2 rewrite Zlength_cons. rewrite Zlength_app, Zlength_one. lia.
      destruct H4; trivial. 2: destruct H9; trivial.
      - rewrite H8 in H4.
        replace (Zlength _) with (Zlength (root :: l0)) in H4.
        2: rewrite Zlength_app, Zlength_cons, Zlength_one; lia.
        rewrite app_comm_cons in H4.
        rewrite Zexchange_head_foot in H4.
        eapply relink_tail.
        3: apply H4. 
        do 2 rewrite app_comm_cons in Hz.
        apply Hz. rewrite H8.
        transitivity (root :: (foot :: l0)).
        2: apply Permutation_cons_append.
        constructor.
        transitivity ([foot] ++ l0).
        2: reflexivity.
        apply Permutation_app_comm.
      - rewrite H8 in H5.
        replace (Zlength _) with (Zlength (root :: l0)) in H5.
        2: rewrite Zlength_app, Zlength_cons, Zlength_one; lia.
        rewrite app_comm_cons in H5.
        rewrite Zexchange_head_foot in H5.
        intros.
        destruct H9.
        rewrite <- H14. trivial.
        repeat intro.
        destruct Hz.
        apply Permutation_Znth in Hq. 2: apply (0, Int.zero, Int.zero).
        destruct Hq as [? [f2 [? [? ?]]]].
        rewrite H23 in H17. 2: lia.
        generalize (H19 (Zlength (root :: h :: l) + i0)); intro Hqq.
        spec Hqq. do 2 rewrite app_comm_cons. rewrite Zlength_app. lia.
        do 2 rewrite app_comm_cons in Hqq. rewrite Znth_app2 in Hqq. 2: lia.
        replace (Zlength (root :: h :: l) + i0 - Zlength (root :: h :: l)) with i0 in Hqq by lia.
        destruct Hqq.
        assert (Z.of_nat (f2 (Z.to_nat j)) = 0 \/ Z.of_nat (f2 (Z.to_nat j)) > 0) by lia.
        rewrite H8 in H25.
        destruct H26.
        ** rewrite H26, Znth_0_cons in H17.
           specialize (H19 (Zlength (h :: l))). spec H19. repeat rewrite Zlength_cons. rewrite Zlength_app. rep_lia.
           destruct H19. rewrite app_comm_cons, H8 in H27. rewrite app_comm_cons in H27.
           rewrite Znth_app1 in H27. 2: rewrite Zlength_cons; rep_lia.
           rewrite app_comm_cons in H27. rewrite Znth_app2 in H27. 2: rewrite Zlength_cons, Zlength_app, Zlength_one; rep_lia.
           replace (Zlength (l0 ++ [foot]) - Zlength (root :: l0)) with 0 in H27 by (rewrite Zlength_cons, Zlength_app, Zlength_one; rep_lia).
           change (Znth 0 [foot]) with foot in H27.
           rewrite H17 in H27. rewrite H25 in H27. autorewrite with sublist in H27. lia.
        ** specialize (H21 (Z.to_nat j)). spec H21. lia.
           specialize (H19 (Z.of_nat (f2 (Z.to_nat j)))). spec H19. { rewrite app_comm_cons, H8.
           rewrite Zlength_cons, Zlength_app. rewrite Zlength_app, Zlength_one. rewrite Zlength_cons in H21. lia. }
           do 2 rewrite app_comm_cons in H19. rewrite H8 in H19. rewrite Znth_app1 in H19.
           2: autorewrite with sublist in *; rep_lia.
           rewrite app_comm_cons in H19.
           change (root :: l0) with ([root] ++ l0) in H19.
           rewrite <- app_assoc in H19.
           rewrite Znth_app2 in H19.
           2: rewrite Zlength_one; rep_lia.
           change (foot :: l0) with ([foot] ++ l0) in H17.
           rewrite Znth_app2 in H17. 2: rewrite Zlength_one; lia.
           rewrite Znth_app1 in H19. 2: autorewrite with sublist in *; rep_lia.
           rewrite Zlength_one in H17. rewrite Zlength_one in H19. destruct H19.
           rewrite H17 in H27. rewrite H25 in H27.
           autorewrite with sublist in H27, H21. lia.
    + rewrite H8 in H5.
      replace (Zlength _) with (Zlength (root :: l0)) in H5.
      2: rewrite Zlength_app, Zlength_cons, Zlength_one; lia.
      rewrite app_comm_cons in H5.
      rewrite Zexchange_head_foot in H5.
      split.
        { destruct H9. eapply Permutation_NoDup. apply H9. destruct H5. trivial. }
      intros. rewrite Zlength_one in H13. assert (i0 = 0) by lia. subst i0. subst loc.
      destruct H7. specialize (H14 _ H13). destruct H14.
      change (Znth 0 [root]) with root in *.
      destruct H9. split. { apply Permutation_Zlength in H9. lia. }
      destruct H5. generalize H18; intro Hqq. specialize (H18 (Zlength (foot :: l0))). spec H18. rewrite Zlength_app, Zlength_one. rep_lia.
      destruct H18. rewrite Znth_app2 in H19. 2: lia.
      replace (Zlength _ - Zlength _) with 0 in H19 by lia. change (Znth _ [root]) with root in H19.
      rewrite <- H17. lia.
      repeat intro.
      apply Permutation_Znth in Hq. 2: apply (0, Int.zero, Int.zero).
      destruct Hq as [? [f [? [? ?]]]].
      specialize (Hqq (Z.of_nat (f (Z.to_nat j)))). spec Hqq.
        { rewrite Zlength_app, Zlength_one. specialize (H23 (Z.to_nat j)). lia. }
      destruct Hqq. rewrite Znth_app1 in H27. 2: specialize (H23 (Z.to_nat j)); lia.
      rewrite <- H25 in H27. 2: lia.
      rewrite H21 in H27. rewrite H19 in H27. specialize (H23 (Z.to_nat j)); lia.
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
  forward. (* BUG, fst and snd are unfolded too far; array subscripting doesn't rewrite Znth_map *) 
    { rewrite Znth_map; trivial. entailer!. }
  forward. { rewrite Znth_map; trivial. entailer!. }
  forward. { repeat rewrite Znth_map; trivial. entailer!. }
  forward. { repeat rewrite Znth_map; trivial. entailer!. }
  forward. { repeat rewrite Znth_map; trivial. entailer!. }
  forward.
  forward. { repeat rewrite Znth_map; trivial. entailer!.
    (* We may be in another C-typing issue... *)
    case (eq_dec j k); intro.
    + subst k. rewrite upd_Znth_same. trivial. rewrite Zlength_map; auto.
    + rewrite upd_Znth_diff; auto. 2,3: rewrite Zlength_map; auto.
      (* BUG?  So ugly... is there no easier way? *)
      rewrite (surjective_pairing (heap_item_rep (Znth k arr_contents))) in H4.
      rewrite (surjective_pairing (snd (heap_item_rep (Znth k arr_contents)))) in H4.
      (* BUG? here is where I need to repack the unpacked rep... *)
      rewrite heap_item_rep_morph, upd_Znth_map in H4.
      apply Forall_map in H4.
      rewrite Forall_Znth in H4. specialize (H4 k).
      do 2 rewrite Zlength_map in H4. rewrite Zlength_upd_Znth in H4. specialize (H4 H0).
      do 2 rewrite Znth_map in H4. 2,3,4: autorewrite with sublist; trivial.
      rewrite upd_Znth_diff in H4; auto. rewrite Znth_map; trivial.
      (* Flailing around solves the goal... *)
      simplify_value_fits in H4. destruct H4 as [? [? ?]].
      apply H5. discriminate. }
  forward.
  forward.
  (* Fail forward. *) (* BUG, wrong error message here *)
  (* Some cleanup *)
  repeat rewrite upd_Znth_same, upd_Znth_overwrite.
  3,4: rewrite Zlength_upd_Znth. 2,3,4,5: rewrite Zlength_map; lia.
  repeat rewrite Znth_map. 2,3: lia.
  replace (let (x, _) := heap_item_rep (Znth k arr_contents) in x) with (fst (heap_item_rep (Znth k arr_contents))) by trivial.
  simpl fst. simpl snd.
  unfold lookup_array.
  (* HORRIBLE BUG, unsigned in C, signed data_at in VST, forward isn't working; and error message was terrible! *)
  forward. { entailer!. destruct H1. destruct (H9 k H0). apply H9. lia. }
  forward.
  forward.
  forward.
  repeat rewrite upd_Znth_overwrite. repeat rewrite upd_Znth_same.
  2,3,4,5,6: repeat rewrite Zlength_upd_Znth; rewrite Zlength_map; rep_lia.
  simpl snd.
  forward. { entailer!. destruct H1. destruct (H9 j H). apply H9. lia. }
  Exists (Zexchange lookup_contents (heap_item_key (Znth j arr_contents)) (heap_item_key (Znth k arr_contents))).
  autorewrite with sublist in *.
  unfold linked_heap_array, heap_array, lookup_array.
  repeat rewrite Zlength_Zexchange.
  entailer!; repeat rewrite Zlength_upd_Znth in *; rewrite Zlength_map in *.
  { split. apply lookup_oob_eq_Zexchange; auto. apply linked_correctly_Zexchange; auto. }
  { apply sepcon_derives; apply data_at_ext_derives; auto.
    * case (Z.eq_dec k j); intro.
      - subst k. rewrite upd_Znth_overwrite. 2: rewrite Zlength_map; rep_lia.
        change (Vint _, _) with (heap_item_rep (Znth j arr_contents)).
        rewrite upd_Znth_map, upd_Znth_same_Znth, Zexchange_eq. trivial. lia.
      - rewrite Znth_upd_Znth_diff; auto. clear H2 H5 H7 H8 H3 H6 H4.
        change (let (_, z) := let (_, y) :=
         @Znth (val * (val * val)) (Vundef, (Vundef, Vundef)) k
           (@map heap_item (@reptype CompSpecs t_item) heap_item_rep arr_contents) in y in z) with
         (snd (snd ((Znth k (map heap_item_rep arr_contents))))).
        rewrite Znth_map; auto. 
        change (Vint (Int.repr (fst (fst (Znth k arr_contents)))),
               (Vint (snd (fst (Znth k arr_contents))),
                snd (snd (heap_item_rep (Znth k arr_contents))))) with
          (heap_item_rep (Znth k arr_contents)).
        rewrite upd_Znth_map; auto.
        change (Vint (Int.repr (fst (fst (Znth j arr_contents)))),
               (Vint (snd (fst (Znth j arr_contents))), Vint (snd (Znth j arr_contents)))) with
          (heap_item_rep (Znth j arr_contents)).
        rewrite upd_Znth_map; auto. f_equal.
        rewrite upd_Znth_Zexchange; auto.
  * change (Vint (Int.repr j)) with ((fun z : Z => Vint (Int.repr z)) j).
    rewrite upd_Znth_map. 
    change (Vint (Int.repr k)) with ((fun z : Z => Vint (Int.repr z)) k).
    rewrite upd_Znth_map. 
    f_equal.
    change (fst (fst ?c)) with (heap_item_key c).
    destruct H1 as [Hx H1].
    destruct (H1 _ H).
    destruct (H1 _ H0).
    rewrite Zexchange_symm; auto.
    rewrite <- upd_Znth_Zexchange; auto.
    rewrite H10, H12.
    trivial. }
Time Qed.

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
      { forward.  entailer!. unfold cmp_rel in H0.
        subst j'. congruence. }
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

Lemma body_size: semax_body Vprog Gprog f_pq_size pq_size_spec.
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

Lemma body_insert_nc: semax_body Vprog Gprog f_pq_insert_nc pq_insert_nc_spec.
Proof.
  start_function.
  unfold valid_pq.
  Intros arr junk lookup lookup_contents.
  rename H0 into Hxx. rename H1 into H0. rename H2 into H1. rename H3 into H2.
  destruct junk. { exfalso. unfold heap_size, heap_capacity in *. rewrite Zlength_app, Zlength_nil in H2. lia. }
  change (h0 :: junk) with ([h0] ++ junk) in *. rewrite app_assoc in *.
  rewrite linked_heap_array_split. Intros.
  assert (0 <= heap_size h) by apply Zlength_nonneg.
  forward.
  forward. { unfold linked_heap_array, heap_array, heap_size in *. Intros. entailer!. }
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
      split. destruct H5; trivial.
      repeat intro. destruct H5 as [Hq H5]. specialize (H5 i).
      rewrite Zlength_app, Zlength_one in H15. rewrite Zlength_app, Zlength_one in H5.
      specialize (H5 H15). destruct H5. rewrite <- H16. subst loc. split.
        { assert (i < Zlength (heap_items h) \/ i = Zlength (heap_items h)) by lia.
          destruct H17. rewrite Znth_app1 in *; auto.
          rewrite Znth_app2 in *; try lia. subst i. rewrite Z.sub_diag in *.
          change (Znth _ [?c]) with c. change (Znth _ [?c]) with c in H5.
          destruct h0. destruct p. apply H5. }
      f_equal.
      assert (i < Zlength (heap_items h) \/ i = Zlength (heap_items h)) by lia.
      destruct H17. repeat rewrite Znth_app1. 2,3: lia. trivial.
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
    + split. { unfold heap_capacity in *. simpl. rewrite <- H2. repeat rewrite Zlength_app.
        apply Permutation_Zlength in H9. rewrite Zlength_app, Zlength_one in *. simpl fst in H9. lia. }
      destruct H7. apply Permutation_Zlength in H7. simpl snd in H7. rewrite <- H7.
      unfold heap_capacity in *. simpl in *. rewrite <- Hxx. trivial.
    + unfold heap_size, heap_capacity, heap_items. simpl fst in *. simpl snd in *.
      generalize (Permutation_Zlength _ _ _ H9); intro. rewrite <- H16.
      rewrite Zlength_app, Zlength_one in *. cancel.
      rewrite linked_heap_array_split. cancel.
      repeat rewrite Zlength_app. rewrite <- H16. unfold heap_array. entailer!.
      (* Show things are still linked correctly, a bit of a mess... *)
      eapply linked_correctly'_shuffle. apply H3.
        { destruct H7. trivial. }
      intros. apply H7. repeat intro.
      apply Permutation_Znth in H9; auto. destruct H9 as [? [f [? [? ?]]]].
      rewrite H23 in H20. 2: lia.
      red in H21. repeat rewrite Zlength_app, Zlength_one in *.
      specialize (H21 (Z.to_nat j)). spec H21. lia.
      remember (Z.of_nat (f (Z.to_nat j))) as j'.
      destruct H5 as [Hq H5].
      specialize (H5 j'). spec H5. autorewrite with sublist; lia. rewrite Z.add_0_l in H5.
      assert (0 <= j' < Zlength (heap_items h) \/ j' = Zlength (heap_items h)) by lia. destruct H24.
      - rewrite Znth_app1 in H20; rewrite Znth_app1 in H5; try lia.
        rewrite H20 in H5. destruct H3 as [Hqq H3]. specialize (H3 i H18). destruct H3. destruct H5. lia.
      - subst j'. rewrite Znth_app2 in H20; rewrite Znth_app2 in H5; try lia.
        rewrite H24, Z.sub_diag, Znth_0_cons in H20, H5.
        unfold heap_item_key in H20 at 1. simpl in H20.
        destruct H3 as [Hqq H3].
        specialize (H3 i H18). rewrite <- H20 in H3. destruct H5. unfold heap_item_key in H25.
        destruct H3. lia.
Time Qed.
