Require Import VST.floyd.proofauto.
Require Export CertiGraph.lib.find_lemmas.
Require Import CertiGraph.priq.priq_arr_specs.
Require Export CertiGraph.priq.is_empty_lemmas.
Require Import CertiGraph.priq.priq_arr.

Section PQProof.

Context {size : Z}.
Context {inf : Z}.
Context {Z_EqDec : EquivDec.EqDec Z eq}. 

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Local Open Scope Z_scope.

Lemma body_init: semax_body Vprog (@Gprog size inf _ _) f_init (@init_spec size _). 
Proof.
  start_function.
  assert (Int.max_signed < Int.max_unsigned) by now compute.
  forward_call (size * sizeof(tint)).
  1: simpl; split; Lia.lia.
  Intro pq. forward. Exists pq.
  rewrite Z_div_mult by (simpl; lia).
  entailer!.
  rewrite Z.mul_comm.
  apply derives_refl.
Qed.

Lemma body_push: semax_body Vprog (@Gprog size inf _ _) f_push (@push_spec size inf _). 
Proof. start_function. forward. entailer!. Qed.

Lemma body_pq_emp: semax_body Vprog (@Gprog size inf _ _) f_pq_emp (@pq_emp_spec size inf _).
Proof.
  start_function.
  forward_for_simple_bound
    size
    (EX i : Z,
     PROP (@isEmpty inf (sublist 0 i priq_contents) = Vone)
     LOCAL (temp _size (Vint (Int.repr size)); temp _inf (Vint (Int.repr inf));
     temp _pq pq)
     SEP (data_at Tsh (tarray tint size) (map Vint (map Int.repr priq_contents)) pq)).
  - entailer!. 
  - simpl.
    assert_PROP (Zlength priq_contents = size). {
      entailer!. repeat rewrite Zlength_map; auto.
    }
    forward; forward_if; forward; entailer!.
    + rewrite (isEmpty_in priq_contents (Znth i priq_contents)); trivial.
      1: apply Znth_In; lia.
      pose proof (sublist.Forall_Znth _ _ i H3 H); simpl in H9.
      rewrite Int.signed_repr in H6; lia.
    + rewrite (sublist_split 0 i (i+1)); try lia.
      rewrite isEmpty_Vone_app; split; trivial.
      rewrite sublist_one; try lia.
      simpl.
      destruct (Z_lt_dec (Znth i priq_contents) (inf + 1));
        trivial.
      exfalso.
      rewrite Int.signed_repr in H6; try lia.
      apply (sublist.Forall_Znth _ _ i H3) in H; simpl in H; rep_lia.
  - forward. entailer!.
    rewrite sublist_same in H3; trivial.
    2: repeat rewrite Zlength_map; trivial.
    replace (Vint (Int.repr 1)) with Vone by now unfold Vone, Int.one.
    symmetry; trivial.
Qed.

Lemma body_adjustWeight: semax_body Vprog (@Gprog size inf _ _) f_adjustWeight (@adjustWeight_spec size inf _).
Proof. start_function. forward. entailer!. Qed.

Lemma body_popMin: semax_body Vprog (@Gprog size inf _ _) f_popMin (@popMin_spec size inf _ _).
Proof.
  start_function.
  assert_PROP (Zlength priq_contents = size). {
    entailer!. repeat rewrite Zlength_map; auto.
  }
  assert (0 <= 0 < Zlength (map Int.repr priq_contents)). {
    rewrite Zlength_map. rewrite H4. lia.
  }
  forward. forward.
  forward_for_simple_bound
    size
    (EX i : Z,
     PROP ()
     LOCAL (temp _minWeight (Vint (Int.repr (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents))));
            temp _minVertex (Vint (Int.repr (find priq_contents (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents)) 0)));
            temp _size (Vint (Int.repr size));
            temp _inf (Vint (Int.repr inf));
            temp _pq pq)
     SEP (data_at Tsh (tarray tint size) (map Vint (map Int.repr priq_contents)) pq)).
  - entailer!. simpl.
    rewrite find_index. trivial. lia.
    simpl. unfold not. lia.
  - forward.
    assert (0 <= i < Zlength priq_contents) by lia.
    assert (Int.min_signed <=
            fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents) <= Int.max_signed).
    { apply Forall_fold_min.
      - apply sublist.Forall_Znth; [lia|].
        rewrite Forall_forall. intros. rewrite In_Znth_iff in H8.
        destruct H8 as [? [? ?]]. rewrite <- H9.
        pose proof (sublist.Forall_Znth _ _ x0 H8 H).
        simpl in H10.
        split; [lia|].
        apply Z.le_trans with (m := inf + 1); lia.
      - rewrite Forall_forall. intros. rewrite In_Znth_iff in H8.
        destruct H8 as [? [? ?]]. rewrite <- H9.
        apply (Forall_sublist _ 0 i _) in H.
        apply (sublist.Forall_Znth _ _ _ H8) in H.
        simpl in H.
        split; [lia|].
        apply Z.le_trans with (m := inf + 1); lia.
    }
    assert (Int.min_signed <= Znth i priq_contents <= Int.max_signed). {
      apply (sublist.Forall_Znth _ _ _ H7) in H; simpl in H.
      rep_lia.
    }
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
    + entailer!.
      apply find_range.
      rewrite sublist_same; [|lia..].
      apply min_in_list; [apply incl_refl | apply Znth_In; lia].
    + forward.
      Exists (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0).
      rewrite sublist_same by lia. entailer!.
      destruct priq_contents; simpl; auto.
Qed.

End PQProof.
