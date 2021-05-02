Require Import CertiGraph.CertiGC.gc_spec.

Local Open Scope logic.

Lemma data_at_heaptype_eq: forall (sh: share) v h,
    isptr h -> field_compatible heap_type [StructField _spaces] h ->
    data_at sh heap_type v h = data_at sh (tarray space_type 12) v h.
Proof.
  intros. unfold_data_at (data_at _ heap_type _ _). rewrite field_at_data_at. simpl nested_field_type.
  rewrite field_address_offset; auto. simpl nested_field_offset.
  rewrite isptr_offset_val_zero; auto.
Qed.

Lemma split2_data_at_Tarray_space_type:
  forall (sh: share) (n n1: Z) (v: list (val * (val * val))) (p: val),
    0 <= n1 <= n -> n = Zlength v ->
    data_at sh (tarray space_type n) v p =
    data_at sh (tarray space_type n1) (sublist 0 n1 v) p *
    data_at sh (tarray space_type (n - n1)) (sublist n1 n v)
            (field_address0 (tarray space_type n) [ArraySubsc n1] p).
Proof.
  intros. pose proof (split2_data_at_Tarray sh space_type n n1) as HS.
  apply HS with (v' := v); auto.
  - rewrite Z.le_lteq. right; auto.
  - rewrite sublist_all; [|apply Z.eq_le_incl; rewrite H0]; reflexivity.
Qed.

Lemma space_array_1_eq: forall (sh: share) (v: (val * (val * val))) (p: val),
    data_at sh (tarray space_type 1) [v] p = data_at sh space_type v p.
Proof.
  intros. pose proof (data_at_singleton_array_eq sh space_type). apply H. reflexivity.
Qed.

Lemma repeat_cons {t: Type}: forall i (v: t),
    1 <= i -> repeat v (Z.to_nat i) = v :: repeat v (Z.to_nat (i - 1)).
Proof.
  intros. replace (Z.to_nat i) with (S (Z.to_nat (i - 1))).
  - simpl. auto.
  - rewrite <- Z2Nat.inj_succ by lia. f_equal. lia.
Qed.

Lemma Znth_repeat_app {X: Type} {IX: Inhabitant X}: forall i (vh v0 vn: X) l,
    1 <= i -> Znth i (vh :: repeat v0 (Z.to_nat (i - 1)) ++ vn :: l) = vn.
Proof.
  intros. rewrite Znth_pos_cons by lia.
  rewrite app_Znth2 by (rewrite Zlength_repeat; lia).
  rewrite Zlength_repeat by lia.
  replace (i - 1 - (i - 1)) with 0 by lia. rewrite Znth_0_cons. reflexivity.
Qed.

Lemma upd_Znth_repeat_app {X: Type} {IX: Inhabitant X}:
  forall i (vh v0 v1 v2: X) l,
    1 <= i -> upd_Znth i (vh :: repeat v0 (Z.to_nat (i - 1)) ++ v1 :: l) v2 =
              vh :: repeat v0 (Z.to_nat (i - 1)) ++ v2 :: l.
Proof.
  intros. rewrite app_comm_cons, upd_Znth_app2.
  - rewrite app_comm_cons. f_equal.
    rewrite Zlength_cons, Zlength_repeat by lia.
    replace (i - Z.succ (i - 1)) with 0 by lia.
    rewrite upd_Znth0. f_equal.
  - rewrite Zlength_cons, !Zlength_repeat by lia.
    replace (Z.succ (i - 1)) with i by lia.
    pose proof (Zlength_nonneg (v1 :: l)). lia.
Qed.

Lemma body_create_heap: semax_body Vprog Gprog f_create_heap create_heap_spec.
Proof.
  start_function.
  forward_call (heap_type, gv).
  Intros h. if_tac.
  - subst h; forward_if False; [|inversion H].
    unfold all_string_constants; Intros;
      forward_call ((gv ___stringlit_8),
                    (map init_data2byte (gvar_init v___stringlit_8)), sh);
      exfalso; assumption.
  - Intros. forward_if True; [contradiction | forward; entailer! |]. Intros.
    (* make "data_at sh space_type v h " in SEP *)
    assert_PROP (isptr h) by entailer!. remember (Vundef, (Vundef, Vundef)) as vn.
    assert_PROP (field_compatible heap_type [StructField _spaces] h) by entailer!.
    replace_SEP 2 (data_at Ews heap_type (default_val heap_type) h) by entailer!.
    change (default_val heap_type) with
        (repeat (Vundef, (Vundef, Vundef)) (Z.to_nat 12)).
    rewrite <- Heqvn. rewrite data_at_heaptype_eq; auto.
    rewrite (split2_data_at_Tarray_space_type Ews 12 1);
      [| lia | rewrite Zlength_repeat; lia].
    rewrite sublist_repeat by lia. simpl repeat at 1.
    rewrite space_array_1_eq. Intros. forward_call (Ews, h, Z.shiftl 1 16, gv, sh).
    (* make succeed *)
    + rewrite MAX_SPACE_SIZE_eq. compute; split; [discriminate | reflexivity].
    + Intros p0. freeze [0;1;2;3;5] FR.
      (* change back to "data_at sh heap_type v h" *)
      rewrite <- space_array_1_eq. rewrite sublist_repeat by lia.
      change (12 - 1) with 11 at 2.
      gather_SEP (data_at Ews (tarray space_type 1) _ h)
                 (data_at Ews (tarray space_type (12 - 1)) _ _).
      remember (p0, (p0, offset_val (WORD_SIZE * Z.shiftl 1 16) p0)) as vh.
      remember (vh :: repeat vn (Z.to_nat 11)) as vl.
      replace [vh] with (sublist 0 1 vl). 2: {
        subst vl; rewrite sublist_one; try lia.
        - rewrite Znth_0_cons; auto.
        - rewrite Zlength_cons, Zlength_repeat; lia.
      } replace (repeat  vn (Z.to_nat 11)) with (sublist 1 12 vl) by
          (rewrite Heqvl, sublist_1_cons, sublist_repeat; [reflexivity|lia..]).
      rewrite <- split2_data_at_Tarray_space_type;
        [| lia | rewrite Heqvl, Zlength_cons, Zlength_repeat; lia].
      remember (Vint (Int.repr 0), (Vint (Int.repr 0), Vint (Int.repr 0))) as v0.
      (* change succeed *) subst vl. rewrite <- data_at_heaptype_eq; auto.
      forward_for_simple_bound
        12
        (EX i: Z,
         PROP ( )
         LOCAL (temp _h h; gvars gv)
         SEP (data_at Ews heap_type
                      (vh :: repeat v0 (Z.to_nat (i - 1)) ++
                          repeat vn (Z.to_nat (12 - i))) h; FRZL FR))%assert.
      * entailer!.
      * Opaque Znth. forward. rewrite (repeat_cons (12 - i)) at 2 by lia.
        rewrite Znth_repeat_app by apply (proj1 H2). rewrite Heqvn at 2.
        rewrite (repeat_cons (12 - i)) by lia.
        rewrite upd_Znth_repeat_app by apply (proj1 H2). forward.
        rewrite Znth_repeat_app by apply (proj1 H2).
        rewrite upd_Znth_repeat_app by apply (proj1 H2). forward.
        rewrite Znth_repeat_app by apply (proj1 H2).
        rewrite upd_Znth_repeat_app by apply (proj1 H2).
        simpl fst.
        replace (i + 1 - 1) with i by lia. rewrite <- Heqv0.
        replace (12 - i - 1) with (12 - (i + 1)) by lia.
        change (v0 :: repeat vn (Z.to_nat (12 - (i + 1))))
               with ([v0] ++ repeat vn (Z.to_nat (12 - (i + 1)))).
        rewrite app_assoc.
        replace (repeat v0 (Z.to_nat (i - 1)) ++ [v0]) with
            (repeat v0 (Z.to_nat i)). 1: entailer!.
        replace [v0] with (repeat v0 (Z.to_nat 1)) by (simpl; auto).
        rewrite <- repeat_app. f_equal. rewrite <- Z2Nat.inj_add by lia.
        f_equal. lia.
      * replace (12 - 12) with 0 by lia. simpl repeat at 2.
        rewrite app_nil_r. change 12 with MAX_SPACES at 2. thaw FR.
        change (Z.shiftl 1 16) with NURSERY_SIZE in *.
        assert (v0 = zero_triple) by (subst v0; unfold zero_triple; reflexivity).
        rewrite H2. forward. Exists h p0. entailer!. Transparent Znth.
Qed.
