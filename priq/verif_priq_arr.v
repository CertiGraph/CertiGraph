Require Import VST.floyd.proofauto.
Require Import CertiGraph.priq.priq_arr_specs.
Require Import CertiGraph.priq.priq_arr_utils.
Require Import VST.zlist.sublist.

Require Import CertiGraph.priq.priq_arr.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Local Open Scope Z_scope.
Instance Z_EqDec : EquivDec.EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Section PriqProof.

Definition size := 8.
Definition inf := 2147483646.

Lemma size_eq: size = 8.
Proof. auto. Qed.

Lemma inf_eq: inf = 2147483646.
Proof. auto. Qed.

Opaque size.
Opaque inf.

Lemma body_push: semax_body Vprog (@Gprog _ size inf) f_push (@push_spec _ size inf). 
Proof. start_function. forward. entailer!. Qed.

Lemma body_pq_emp: semax_body Vprog (@Gprog _ size inf) f_pq_emp (@pq_emp_spec _ size inf).
Proof.
  start_function.
  forward_for_simple_bound
    size
    (EX i : Z,
     PROP (@isEmpty inf (sublist 0 i priq_contents) = Vone)
     LOCAL (temp _pq pq)
     SEP (data_at Tsh (tarray tint size) (map Vint (map Int.repr priq_contents)) pq)).
  - rewrite size_eq; lia.
  - rewrite size_eq; rep_lia.
  - entailer!. 
  - simpl.
    assert_PROP (Zlength priq_contents = size). {
      entailer!. repeat rewrite Zlength_map in H3; auto.
    }
    forward; forward_if; forward; entailer!.
    + 
      rewrite (isEmpty_in priq_contents (Znth i priq_contents)); trivial.
      1: apply Znth_In; lia.
      rewrite <- H1 in H0.
      pose proof (Forall_Znth _ _ i H0 H).
      rewrite Int.signed_repr in H3.
      apply (Z.lt_stepr _ _ _ H3).
      rewrite inf_eq. compute; trivial.
      simpl in H7. split; [lia|].
      apply Z.le_trans with (m := inf + 1); [lia|].
      rewrite inf_eq; compute; inversion 1.
    + 
      rewrite (sublist_split 0 i (i+1)); try lia.
      unfold isEmpty.
      rewrite fold_right_app.
      rewrite sublist_one; try lia. Opaque inf. simpl.
      destruct (Z_lt_dec (Znth i priq_contents) (inf + 1)).
      2: unfold isEmpty in H2; trivial.
      assert (inf + 1 <= Int.max_signed). {
        rewrite inf_eq. set (j:=Int.max_signed); compute in j; subst j. lia. }
      rewrite Int.signed_repr in H3.
      2: { rewrite <- H1 in H0. apply (Forall_Znth _ _ i H0) in H; simpl in H. lia. }
      rewrite Int.signed_repr in H3.
      2: { 
           repeat rewrite Int.signed_repr;
             compute; split; inversion 1.
      }
      rewrite inf_eq in l. lia.
  - forward. entailer!.
    rewrite sublist_same in H0; trivial.
    2: { symmetry; repeat rewrite Zlength_map in H2.
         rewrite Zmax0r in H2. lia.
         rewrite size_eq; lia. }
    replace (Vint (Int.repr 1)) with Vone by now unfold Vone, Int.one.
    symmetry; trivial.
Qed.

Lemma body_adjustWeight: semax_body Vprog (@Gprog _ size inf) f_adjustWeight (@adjustWeight_spec _ size inf).
Proof. start_function. forward. entailer!. Qed.

Lemma body_popMin: semax_body Vprog (@Gprog _ size inf) f_popMin (@popMin_spec _ size inf).
Proof.
  start_function.
  assert_PROP (Zlength priq_contents = size). {
    entailer!. repeat rewrite Zlength_map in H2; auto.
  }
  assert (0 <= 0 < Zlength (map Int.repr priq_contents)) by
      (rewrite Zlength_map; rewrite H1; rewrite size_eq; lia).
  assert (0 <= 0 < Zlength priq_contents) by
      (rewrite H1; rewrite size_eq; lia).
  assert (Ha: inf + 1 <= Int.max_signed). {
    rewrite inf_eq; rep_lia.
  }

  forward. forward.
  forward_for_simple_bound
    size
    (EX i : Z,
     PROP ()
     LOCAL (temp _minWeight (Vint (Int.repr (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents))));
                        temp _minVertex (Vint (Int.repr (find priq_contents (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents)) 0)));
                        temp _pq pq)
                 SEP (data_at Tsh (tarray tint size) (map Vint (map Int.repr priq_contents)) pq)).
  - rewrite size_eq. rep_lia.
  - entailer!. simpl. rewrite find_index.
    trivial. lia. simpl. unfold not. lia.
  - forward.
    assert (0 <= i < Zlength priq_contents) by lia.
    assert (Int.min_signed <=
            fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents) <= Int.max_signed).
    { apply Forall_fold_min. apply Forall_Znth. lia.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H6.
      destruct H6 as [? [? ?]]. rewrite <- H7.
      pose proof (Forall_Znth _ _ x0 H6 H).
      simpl in H8.
      split; [lia|].
      apply Z.le_trans with (m := inf + 1); [lia|].
      rewrite inf_eq. rep_lia.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H6.
      destruct H6 as [? [? ?]]. rewrite <- H7.
      apply (Forall_sublist _ 0 i _) in H.
      apply (Forall_Znth _ _ _ H6) in H.
      simpl in H.
      split; [lia|].
      apply Z.le_trans with (m := inf + 1); [lia|].
      rewrite inf_eq; rep_lia.
    }
    assert (Int.min_signed <= Znth i priq_contents <= Int.max_signed). {
      apply (Forall_Znth _ _ _ H5) in H; simpl in H.

      rep_lia. }
    forward_if.
    + forward. forward. entailer!.
      rewrite (sublist_split 0 i (i+1)) by lia.
      rewrite (sublist_one i (i+1) priq_contents) by lia.
      rewrite fold_min_another.
      rewrite Z.min_r; [|lia].
      split; trivial. f_equal.
      rewrite find_index; trivial.
      apply min_not_in_prev; trivial.
    + forward. entailer!.
      rewrite (sublist_split 0 i (i+1)) by lia.
      rewrite (sublist_one i (i+1) priq_contents) by lia.
      rewrite fold_min_another.
      rewrite Z.min_l; [|lia]. split; trivial.
  - forward.
    + entailer!. rewrite <- H1.
      apply find_range.
      rewrite sublist_same; [|lia..].
      apply min_in_list; [apply incl_refl | apply Znth_In; lia].
    + forward.
      Exists (find priq_contents (fold_right Z.min (hd 0 priq_contents) (sublist 0 size priq_contents)) 0).
      rewrite sublist_same by lia. entailer!.
      destruct priq_contents; simpl; auto.
Qed.

End PriqProof.
