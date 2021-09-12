Require Import VST.floyd.proofauto.
Require Import CertiGraph.floyd_ext.share.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.unionfind.env_unionfind_arr. (*something here massages reptype (tarray...) into list (reptype ...)*)
(*edgelist*)

Require Import RelationClasses.
Require Import CertiGraph.binheap.binary_heap_model.
Require Import CertiGraph.binheap.binary_heap_Zmodel.
Require Import Sorting.

Require Import CertiGraph.kruskal.spatial_wedgearray_graph.
Require Import CertiGraph.kruskal.kruskal_specs.

Section VerifKrusSort.

Context {sz: Z}.

Definition rep2hi (r : reptype t_struct_edge) : heap_item :=
  match r with (v1, (v2, v3)) => (force_int v1, (force_int v2, force_int v3)) end.

Lemma rep2hi_ok: forall r, def_wedgerep r -> 
  heap_item_rep (rep2hi r) = r.
Proof.
  destruct r as [? [? ?]]. simpl in *. intros [? [? ?]]. simpl in *.
  destruct y; destruct y0; destruct c; try contradiction. trivial.
Qed.

Lemma rep2hi_map_ok: forall L,
  Forall def_wedgerep L ->
  map (heap_item_rep oo rep2hi) L = L.
Proof.
  induction L. trivial.
  simpl. intro. inversion H. rewrite IHL; auto. subst. f_equal.
  rewrite rep2hi_ok. trivial. rewrite Forall_forall in H. apply H. left. trivial.
Qed.

Set Nested Proofs Allowed.

Lemma Sorted_alt {A} : forall (cmp : A -> A -> Prop) (aI : Inhabitant A),
  forall L, (forall x, In x L -> cmp x x) -> (forall x y z, cmp x y -> cmp y z -> cmp x z) ->
    Sorted cmp L ->
    forall i j, 0 <= i -> i <= j -> j < Zlength L ->
    cmp (Znth i L) (Znth j L).
Proof.
  induction L; intros. rewrite Zlength_nil in H4. lia.
  inversion H1. subst l a0.
  assert (i = 0 \/ i > 0) by lia. destruct H5. subst i.
  rewrite Znth_0_cons.
  assert (j = 0 \/ j > 0) by lia. destruct H5. subst j.
  rewrite Znth_0_cons.
  apply H. left. trivial.
  change (a :: L) with ([a] ++ L).
  rewrite Znth_app2. rewrite Zlength_one. destruct L.
  rewrite Zlength_one in H4. lia.
  apply (H0 a a0). inversion H8. trivial.
  change a0 with (Znth 0 (a0 :: L)).
  apply IHL; auto; autorewrite with sublist in *; try lia.
  intros. apply H. right. trivial.
  rewrite Zlength_one. lia.
  change (a :: L) with ([a] ++ L).
  rewrite Znth_app2. 2: rewrite Zlength_one; lia. rewrite Zlength_one.
  rewrite Znth_app2. 2: rewrite Zlength_one; lia. rewrite Zlength_one.
  apply IHL; auto; try lia. 2: rewrite Zlength_cons in H4; lia.
  intros. apply H. right. trivial.
Qed.

Lemma sorted_wedge_le_flip_cmp_rel: forall L,
  Sorted (Basics.flip cmp_rel) L ->
  Sorted wedge_le (map heap_item_rep L).
Proof.
  induction 1. constructor. simpl.
  constructor. apply IHSorted.
  inversion H0; constructor.
  red in H1. unfold heap_item_rep. red.
  red in H1. unfold cmp in H1.
  assert (Int.lt (fst b) (fst a) = false). {
    rewrite <- (negb_involutive (Int.lt _ _)). rewrite H1. trivial. }
  apply lt_false_inv in H3. lia.
Qed.

Lemma body_heapsort: semax_body Vprog (@Gprog sz) f_heapsort heapsort_spec.
Proof.
  start_function. (* uint vs int *)
  remember (Zlength arr_contents) as size.
  forward_if (size > 0). {
    forward. Exists (@nil (reptype t_struct_edge)). destruct arr_contents.
    2: rewrite Zlength_cons in H1; rep_lia. rewrite Zlength_nil. entailer!. }
  forward. entailer!. Intros. rename H1 into Hsz.
  assert_PROP (2 * (size - 2) <= Int.max_unsigned). { 
    go_lower. unfold harray. saturate_local. apply prop_right.
    destruct H1 as [? [? [? [? ?]]]].
    destruct arr; try contradiction. simpl in H5. rep_lia. }
  forward.
  rename arr_contents into raw_arr_contents.
  set (arr_contents := map rep2hi raw_arr_contents).
  assert (Heqsize' : size = Zlength arr_contents). { subst arr_contents. rewrite Zlength_map. trivial. }
  apply (semax_pre (PROP ( ) LOCAL (temp _arr arr; temp _size (Vint (Int.repr size)))
                    SEP (harray sh arr_contents arr))). {
    unfold harray. entailer!. subst arr_contents. rewrite Zlength_map.
    rewrite map_map. rewrite rep2hi_map_ok; trivial. }
  forward_call (sh, arr, arr_contents, size).
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
                 SEP (harray sh (arr_contents1 ++ arr_contents2) arr)).
  { Exists size arr_contents' (@nil heap_item).
    rewrite app_nil_r. entailer!. split. rewrite Heqsize'. apply Permutation_Zlength. trivial.
    apply Forall_forall. constructor. }
  Intros s arrc1 arrc2.
  generalize (Permutation_Zlength _ _ _ H9); intro.
  rewrite Zlength_app in H10.
  forward_if.
  2: { (* This is the biggest change from the basic heap, to massage the postcondition. *)
       assert (s = 1) by rep_lia. subst s.
       destruct arrc1. rewrite Zlength_nil in H12; lia.
       destruct arrc1. 2: do 2 rewrite Zlength_cons in H12; rep_lia.
       rewrite H12.
       forward. Exists (map heap_item_rep (h :: arrc2)). entailer!. split.
       * change (heap_item_rep h :: map heap_item_rep arrc2) with (map heap_item_rep (h :: arrc2)).
         replace raw_arr_contents with (map (heap_item_rep oo rep2hi) raw_arr_contents).
         unfold Basics.compose. rewrite <- map_map.
         apply Permutation_map. subst arr_contents. trivial.
         apply rep2hi_map_ok. trivial.
       * intros. rewrite Zlength_cons, Zlength_map in H14.
         change (heap_item_rep h :: map heap_item_rep arrc2) with ([heap_item_rep h] ++ map heap_item_rep arrc2).
         apply Sorted_alt; auto. 4: simpl; rewrite Zlength_cons, Zlength_map; trivial.
         intros. apply wedge_le_refl. red.
         apply in_app_or in H15. destruct H15. inversion H15. subst x.
         unfold heap_item_rep. simpl. tauto. inversion H16.
         apply In_Znth_iff in H15. destruct H15 as [k [? ?]]. subst x.
         rewrite Znth_map. unfold heap_item_rep. simpl. tauto. rewrite Zlength_map in H15. lia.
         intros.
         unfold wedge_le in *. destruct x, y, z; try contradiction. simpl in *. destruct y0, y, y1; try contradiction. lia.
         change ([heap_item_rep h] ++ map heap_item_rep arrc2) with (map heap_item_rep (h :: arrc2)).
         apply sorted_wedge_le_flip_cmp_rel.
         constructor. trivial. rewrite Forall_forall in H8. apply H8. left. trivial.
       * unfold harray. rewrite Zlength_cons, Zlength_map, Zlength_app, Zlength_one.
         replace (Z.succ (Zlength arrc2)) with (1 + Zlength arrc2) by lia.
         apply derives_refl. }
  forward.
  rewrite harray_split. Intros.
  forward_call (sh, 0, s-1, arr, arrc1).
  destruct arrc1. rewrite Zlength_nil in H5. lia.
  generalize (foot_split_spec _ (h :: arrc1)). case foot_split. destruct o. 2: intros [? ?]; subst; discriminate.
  intros. destruct l. destruct arrc1. 2: discriminate. inversion H12. subst h0. clear H12.
  { (* Degenerate case: only one item, which simplies nicely after changing the bound! *)
    rewrite Zlength_one in H5. lia. }
  (* Main line *)
  assert (h1 = h) by (inversion H12; auto). subst h1.
  rewrite H12 in *. clear H12 arrc1.
  replace (s - 1) with (Zlength (h :: l)).
  2: autorewrite with sublist in *; rep_lia.
  rewrite Zexchange_head_foot.
  rewrite harray_split. Intros.
  forward_call (sh, 0, arr, (h0 :: l), s-1, 0).
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
      generalize (Permutation_in x H13 H5); intro.
      generalize (root_minimal _ cmp_rel cmp_po _ H6 h eq_refl); intro.
      rewrite Forall_forall in H15. apply H15.
      rewrite <- app_comm_cons. right.
      apply in_or_app.
      destruct H14. subst x. right. left. trivial. auto.
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
Time Qed.

(*
Lemma body_heapsort: semax_body Vprog (@Gprog sz) f_heapsort heapsort_spec.
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
  forward_call (0, s-1, arr, arrc1). rep_lia.
  destruct arrc1. rewrite Zlength_nil in H5. lia.
  generalize (foot_split_spec _ (h :: arrc1)). case foot_split. destruct o. 2: intros [? ?]; subst; discriminate.
  intros. destruct l. destruct arrc1. 2: discriminate. inversion H12. subst h0. clear H12.
  { (* Degenerate case: only one item, which simplies nicely after changing the bound! *)
    rewrite Zlength_one in H5. lia. }
  (* Main line *)
  assert (h1 = h) by (inversion H12; auto). subst h1.
  rewrite H12 in *. clear H12 arrc1.
  replace (s - 1) with (Zlength (h :: l)).
  2: autorewrite with sublist in *; rep_lia.
  rewrite Zexchange_head_foot.
  rewrite harray_split. Intros.
  forward_call (0, arr, (h0 :: l), s-1, 0).
  { split. rep_lia. split. autorewrite with sublist in *. rep_lia.
    split. rep_lia. split. intros _. rep_lia.
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
Time Qed.
*)

Lemma body_sink: semax_body Vprog (@Gprog sz) f_sink sink_spec.
Proof.
  start_function.
  assert (Hc : i = Zlength arr_contents \/ 0 <= i < Zlength arr_contents) by lia. destruct Hc as [Hc | Hc].
* (* Special case: oob sink, used when removing the last element of the heap. *)
  forward_loop ( PROP () LOCAL (temp _k (Vint (Int.repr i)); temp _first_available (Vint (Int.repr first_available))) SEP (harray sh arr_contents arr) ).
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
                 SEP (harray sh arr_contents' arr)).
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
                           SEP (harray sh arr_contents' arr)).
    { forward_call (sh, Zright_child i', Zleft_child i', arr, arr_contents').
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
              SEP (harray sh arr_contents' arr)).
    { forward. subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. entailer!. tauto. }
    { forward. entailer!. }
    Intros. (* Need to get the PROP above the bar... why doesn't forward_call do this for me? *)
    forward_call (sh, i', j', arr, arr_contents'). { subst j'. rewrite Zright_child_unfold, Zleft_child_unfold in *; try lia. destruct bo; lia. }
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
    forward_call (sh, i', j', arr, arr_contents').
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

Lemma body_build_heap: semax_body Vprog (@Gprog sz) f_build_heap build_heap_spec.
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
                 LOCAL (temp _arr arr; temp _size (Vint (Int.repr size)); temp _start (Vint (Int.repr s)))
                 SEP (harray sh arr_contents' arr)).
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
  forward_call (sh, s, arr, arr_contents', size, s).
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
Time Qed.

Lemma body_greater: semax_body Vprog (@Gprog sz) f_greater greater_spec.
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

Lemma heap_item_rep_morph: forall x y,
  (fst (heap_item_rep x), (snd (heap_item_rep y))) = 
  (heap_item_rep (fst x, snd y)).
Proof. unfold heap_item_rep. destruct x,y; reflexivity. Qed.

Lemma body_exch: semax_body Vprog (@Gprog sz) f_exch exch_spec.
Proof.
  start_function.
  unfold harray.
  forward. { rewrite Znth_map; trivial. entailer!. }
  forward. { rewrite Znth_map; trivial. entailer!. }
  forward. { rewrite Znth_map; trivial. entailer!. }
  forward. { repeat rewrite Znth_map; trivial. entailer!. }
  forward.
  forward. { repeat rewrite Znth_map; trivial. entailer!.
    clear H2.
    (* We may be in another C-typing issue... *)
    case (eq_dec i j); intro.
    + subst j. rewrite upd_Znth_same. trivial. rewrite Zlength_map; auto.
    + rewrite upd_Znth_diff; auto. 2,3: rewrite Zlength_map; auto.
      (* So ugly... is there no easier way? *)
      replace (let (x, _) := heap_item_rep _ in x) with (fst (heap_item_rep (Znth j arr_contents))) in H3 by trivial.
      rewrite heap_item_rep_morph, upd_Znth_map in H3.
      apply Forall_map in H3.
      rewrite Forall_Znth in H3. specialize (H3 j).
      do 2 rewrite Zlength_map in H3. rewrite Zlength_upd_Znth in H3. specialize (H3 H0).
      do 2 rewrite Znth_map in H3. 2,3,4: autorewrite with sublist; trivial.
      rewrite upd_Znth_diff in H3; auto. rewrite Znth_map; trivial.
      (* Flailing around solves the goal... *)
      simplify_value_fits in H3. destruct H3.
      apply H3. discriminate. }
  forward.
  rewrite upd_Znth_overwrite. rewrite upd_Znth_same.
  2,3: autorewrite with sublist; auto.
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
      rewrite Zlength_map in H4. rewrite Zlength_upd_Znth in H4. rewrite Zlength_map in H4.
      specialize (H4 H0).
      do 2 rewrite Znth_map in H4. 2,3,4: autorewrite with sublist; trivial.
      rewrite upd_Znth_diff in H4; auto. rewrite Znth_map; trivial.
      (* Flailing around solves the goal... *)
      simplify_value_fits in H4. rewrite Znth_map in H4. 2,3,4: autorewrite with sublist; trivial.
      destruct H4. apply H4. discriminate. }
  forward.
  rewrite upd_Znth_overwrite. rewrite upd_Znth_same.
  2,3: autorewrite with sublist; auto.
  forward.
  forward.
  rewrite upd_Znth_overwrite. rewrite upd_Znth_same.
  2,3: autorewrite with sublist; auto.
  forward.
  rewrite upd_Znth_overwrite. rewrite upd_Znth_same.
  2,3: autorewrite with sublist; auto.
  case (eq_dec i j); intro.
  + subst j. rewrite upd_Znth_overwrite, upd_Znth_same. 2,3: autorewrite with sublist; auto. simpl fst.
    unfold snd.
    replace (let (x, _) := Znth i (map heap_item_rep arr_contents) in x,
             let (_, y) := Znth i (map heap_item_rep arr_contents) in y)
            with (heap_item_rep (Znth i arr_contents)) by (rewrite Znth_map; auto).
    replace (let (x, _) := Znth i (map heap_item_rep arr_contents) in x,
             (let (x, _) := let (_, y) := Znth i (map heap_item_rep arr_contents) in y in x,
              let (_, y) := let (_, y) := Znth i (map heap_item_rep arr_contents) in y in y))
            with (heap_item_rep (Znth i arr_contents)) by (rewrite Znth_map; auto).
    rewrite upd_Znth_map, upd_Znth_same_Znth; trivial.
    rewrite Zexchange_eq. Intros. unfold harray. go_lower. cancel.
  + rewrite upd_Znth_diff; auto. 2,3: rewrite Zlength_map; auto.
    rewrite upd_Znth_diff; auto. 2,3: rewrite Zlength_map; auto.
    rewrite upd_Znth_diff; auto. 2,3: rewrite Zlength_map; auto.
    replace (let (x, _) := Znth j (map heap_item_rep arr_contents) in x,
             (let (x, _) := let (_, y) := Znth j (map heap_item_rep arr_contents) in y in x,
              let (_, y) := let (_, y) := Znth j (map heap_item_rep arr_contents) in y in y))
            with (heap_item_rep (Znth j arr_contents)) by (rewrite Znth_map; auto).
    simpl fst.
    replace (let (x, _) := Znth i (map heap_item_rep arr_contents) in x,
             (let (x, _) := let (_, y) := Znth i (map heap_item_rep arr_contents) in y in x,
              let (_, y) := let (_, y) := Znth i (map heap_item_rep arr_contents) in y in y))
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

End VerifKrusSort.
