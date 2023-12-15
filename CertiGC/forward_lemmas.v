From CertiGraph.CertiGC Require Import env_graph_gc gc_spec.
Require Import CertiGraph.msl_ext.ramification_lemmas.
Require Import VST.concurrency.conclib.
Import graph_model List_ext.

Local Open Scope logic.

Lemma root_valid_int_or_ptr: forall g (roots: roots_t) root outlier,
    In root roots ->
    roots_compatible g outlier roots ->
    graph_rep g * outlier_rep outlier |-- !! (valid_int_or_ptr (root2val g root)).
Proof.
  intros. destruct H0. destruct root as [[? | ?] | ?].
  - simpl root2val. unfold odd_Z2val. replace (2 * z + 1) with (z + z + 1) by lia.
    apply prop_right, valid_int_or_ptr_ii1.
  - sep_apply (roots_outlier_rep_single_rep _ _ _ H H0).
    sep_apply (single_outlier_rep_valid_int_or_ptr g0). entailer!.
  - red in H1. rewrite Forall_forall in H1.
    rewrite (filter_sum_right_In_iff v roots) in H.
    apply H1 in H. simpl. sep_apply (graph_rep_valid_int_or_ptr _ _ H). entailer!.
Qed.

Lemma weak_derives_strong: forall (P Q: mpred),
    P |-- Q -> P |-- (weak_derives P Q && emp) * P.
Proof.
  intros. cancel. apply andp_right. 2: cancel.
  assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
  apply derives_weak. assumption.
Qed.

Lemma sapi_ptr_val: forall p m n,
    isptr p -> Int.min_signed <= n <= Int.max_signed ->
    (force_val
       (sem_add_ptr_int int_or_ptr_type Signed (offset_val (WORD_SIZE * m) p)
                        (vint n))) = offset_val (WORD_SIZE * (m + n)) p.
Proof.
  intros. rewrite sem_add_pi_ptr_special; [| easy | | easy].
  - simpl. rewrite offset_offset_val. f_equal. fold WORD_SIZE; rep_lia.
  - rewrite isptr_offset_val. assumption.
Qed.

Lemma sapil_ptr_val: forall p m n,
    isptr p ->
    if Archi.ptr64 then
      force_val
        (sem_add_ptr_long int_or_ptr_type (offset_val (WORD_SIZE * m) p)
                          (Vlong (Int64.repr n))) = offset_val (WORD_SIZE * (m + n)) p
    else
      force_val
        (sem_add_ptr_int int_or_ptr_type Signed (offset_val (WORD_SIZE * m) p)
                         (vint n)) = offset_val (WORD_SIZE * (m + n)) p.
Proof.
  intros. simpl.
  first [rewrite sem_add_pi_ptr_special' | rewrite sem_add_pl_ptr_special']; auto.
  simpl. fold WORD_SIZE. rewrite offset_offset_val. f_equal. lia.
Qed.

Lemma data_at_mfs_eq: forall g v i sh nv,
    field_compatible int_or_ptr_type [] (offset_val (WORD_SIZE * i) nv) ->
    0 <= i < Zlength (raw_fields (vlabel g v)) ->
    data_at sh (tarray int_or_ptr_type i) (sublist 0 i (make_fields_vals g v)) nv *
    field_at sh int_or_ptr_type [] (Znth i (make_fields_vals g v))
             (offset_val (WORD_SIZE * i) nv) =
    data_at sh (tarray int_or_ptr_type (i + 1))
            (sublist 0 (i + 1) (make_fields_vals g v)) nv.
Proof.
  intros. rewrite field_at_data_at. unfold field_address.
  rewrite if_true by assumption. simpl nested_field_type.
  simpl nested_field_offset. rewrite offset_offset_val.
  replace (WORD_SIZE * i + 0) with (WORD_SIZE * i)%Z by lia.
  rewrite <- (data_at_singleton_array_eq
                sh int_or_ptr_type _ [Znth i (make_fields_vals g v)]) by reflexivity.
  rewrite <- fields_eq_length in H0.
  rewrite (data_at_tarray_value
             sh (i + 1) i nv (sublist 0 (i + 1) (make_fields_vals g v))
             (make_fields_vals g v) (sublist 0 i (make_fields_vals g v))
             [Znth i (make_fields_vals g v)]).
  - replace (i + 1 - i) with 1 by lia. reflexivity.
  - lia.
  - lia.
  - autorewrite with sublist. reflexivity.
  - reflexivity.
  - rewrite sublist_one; [reflexivity | lia..].
Qed.

Lemma data_at__value_0_size: forall sh p,
    data_at_ sh (tarray int_or_ptr_type 0) p |-- emp.
Proof. intros. rewrite data_at__eq. apply data_at_zero_array_inv; reflexivity. Qed.

Lemma data_at_minus1_address: forall sh v p,
    data_at sh (if Archi.ptr64 then tulong else tuint)
            v (offset_val (- WORD_SIZE) p) |--
            !! (force_val (sem_add_ptr_int (if Archi.ptr64 then tulong else tuint)
                                           Signed p (eval_unop Oneg tint (vint 1))) =
                field_address (if Archi.ptr64 then tulong else tuint) []
                              (offset_val (- WORD_SIZE) p)).
Proof.
  intros. unfold eval_unop. simpl. entailer!.
  unfold field_address. rewrite if_true by assumption. rewrite offset_offset_val.
  simpl. reflexivity.
Qed.
