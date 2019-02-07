Require Import VST.veric.compcert_rmaps.
Require Export VST.progs.conclib.
Require Import VST.msl.shares.
Require Export VST.msl.wand_frame.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.ramification_lemmas.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.CertiGC.GCGraph.
Require Export RamifyCoq.CertiGC.env_graph_gc.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import Coq.Lists.List.

Definition vertex_at (sh: share) (p: val) (header: Z) (lst_fields: list val) :=
  data_at sh tuint (Z2val header) (offset_val (- WORD_SIZE) p) *
  data_at sh (tarray int_or_ptr_type (Zlength lst_fields)) lst_fields p.

Definition vertex_rep (sh: share) (g: LGraph) (v: VType): mpred :=
  vertex_at sh (vertex_address g v) (make_header g v) (make_fields_vals g v).

Definition generation_rep (g: LGraph) (gen: nat): mpred :=
  iter_sepcon (map (fun x => (gen, x))
                   (nat_inc_list (nth_gen g gen).(number_of_vertices)))
              (vertex_rep (nth_sh g gen) g).

Definition graph_rep (g: LGraph): mpred :=
  iter_sepcon (nat_inc_list (length g.(glabel).(g_gen))) (generation_rep g).

Definition fun_info_rep (sh: share) (fi: fun_info) (p: val) : mpred :=
  let len := Zlength (live_roots_indices fi) in
  data_at
    sh (tarray tuint (len + 2))
    (map Z2val (fun_word_size fi :: len :: live_roots_indices fi)) p.

Definition space_rest_rep (sp: space): mpred :=
  if (Val.eq sp.(space_start) nullval)
  then emp
  else data_at_ (space_sh sp)
                (tarray int_or_ptr_type (sp.(total_space) - sp.(used_space)))
                (offset_val (WORD_SIZE * used_space sp) sp.(space_start)).

Definition heap_rest_rep (hp: heap): mpred :=
  iter_sepcon hp.(spaces) space_rest_rep.

Definition space_tri (sp: space): (reptype space_type) :=
  let s := sp.(space_start) in (s, (offset_val (WORD_SIZE * sp.(used_space)) s,
                                    offset_val (WORD_SIZE * sp.(total_space)) s)).

Definition heap_struct_rep (sh: share) (sp_reps: list (reptype space_type)) (h: val):
  mpred := data_at sh heap_type sp_reps h.

Definition before_gc_thread_info_rep (sh: share) (ti: thread_info) (t: val) :=
  let nursery := heap_head ti.(ti_heap) in
  let p := nursery.(space_start) in
  let n_lim := offset_val (WORD_SIZE * nursery.(total_space)) p in
  data_at sh thread_info_type
          (offset_val (WORD_SIZE * nursery.(used_space)) p,
           (n_lim, (ti.(ti_heap_p), ti.(ti_args)))) t *
  heap_struct_rep
    sh ((p, (Vundef, n_lim))
          :: map space_tri (tl ti.(ti_heap).(spaces))) ti.(ti_heap_p) *
  heap_rest_rep ti.(ti_heap).

Definition thread_info_rep (sh: share) (ti: thread_info) (t: val) :=
  data_at sh thread_info_type (Vundef, (Vundef, (ti.(ti_heap_p), ti.(ti_args)))) t *
  heap_struct_rep sh (map space_tri ti.(ti_heap).(spaces)) ti.(ti_heap_p) *
  heap_rest_rep ti.(ti_heap).

Definition single_outlier_rep (p: GC_Pointer) :=
  EX sh: share, !!(readable_share sh) &&
                  (data_at_ sh (tptr tvoid) (GC_Pointer2val p) * TT).

Definition outlier_rep (outlier: outlier_t) :=
  fold_right andp TT (map single_outlier_rep outlier).

Lemma vertex_head_address_eq: forall g gen num,
    offset_val (- WORD_SIZE) (vertex_address g (gen, num)) =
    offset_val (WORD_SIZE * (previous_vertices_size g gen num)) (gen_start g gen).
Proof.
  intros. unfold vertex_address, vertex_offset. simpl. rewrite offset_offset_val.
  f_equal. rewrite Z.add_opp_r, Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_simpl_r.
Qed.

Lemma vertex_rep_isptr: forall sh g v,
    vertex_rep sh g v |-- !! (isptr (gen_start g (vgeneration v))).
Proof.
  intros. destruct v as [gen num]. unfold vertex_rep, vertex_at.
  rewrite vertex_head_address_eq. simpl. rewrite data_at_isptr. Intros.
  apply prop_right. unfold offset_val in H.
  destruct (gen_start g gen); try contradiction. exact I.
Qed.

Lemma vertex_rep_memory_block: forall sh g v,
    vertex_rep sh g v |--
               memory_block sh (WORD_SIZE * vertex_size g v)
               (offset_val (- WORD_SIZE) (vertex_address g v)).
Proof.
  intros. sep_apply (vertex_rep_isptr sh g v). Intros.
  destruct v as [gen num]. unfold vertex_rep, vertex_at. simpl in H.
  rewrite vertex_head_address_eq. unfold vertex_address, vertex_offset. simpl.
  remember (gen_start g gen). destruct v; try contradiction.
  remember (previous_vertices_size g gen num).
  assert (0 <= z) by (rewrite Heqz; apply pvs_ge_zero).
  unfold vertex_size. entailer. rewrite <- fields_eq_length.
  destruct H1 as [_ [_ [? _]]]. simpl in H1.
  destruct H3 as [_ [_ [? _]]]. simpl in H3. rewrite <- H4 in H3.
  remember (previous_vertices_size g gen num).
  remember (Zlength (make_fields_vals g (gen, num))). rewrite (Z.add_comm z0).
  rewrite Z.mul_add_distr_l with (m := 1). rewrite Z.mul_1_r.
  simpl offset_val. remember (Ptrofs.add i (Ptrofs.repr (WORD_SIZE * z))).
  rewrite <- (Ptrofs.repr_unsigned i0). remember (Ptrofs.unsigned i0) as ofs.
  assert (Ptrofs.add i (Ptrofs.repr (WORD_SIZE * (z + 1))) = Ptrofs.repr (ofs + 4)). {
    rewrite WORD_SIZE_eq in *. rewrite Z.mul_add_distr_l, Z.mul_1_r.
    rewrite <- ptrofs_add_repr, <- Ptrofs.add_assoc.
    rewrite Ptrofs.add_unsigned. rewrite <- Heqi0. rewrite <- Heqofs. f_equal.
  } assert (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (WORD_SIZE * (z + 1)))) =
            ofs + 4). {
    rewrite H6, Ptrofs.unsigned_repr_eq. apply Z.mod_small.
    destruct (Ptrofs.unsigned_range i0). rewrite <- Heqofs in *. omega.
  } rewrite H6. assert (0 <= z0) by (subst z0; apply Zlength_nonneg).
  assert ((@Zlength (@reptype CompSpecs int_or_ptr_type)
                    (make_fields_vals g (gen, num))) =
          (@Zlength val (make_fields_vals g (gen, num)))) by reflexivity.
  rewrite H9 in H3. clear H9. rewrite <- Heqz0 in *.
  rewrite memory_block_split; [| rep_omega..].
  sep_apply (data_at_memory_block
               sh tuint (Vint (Int.repr (make_header g (gen, num))))
               (Vptr b (Ptrofs.repr ofs))).
  simpl sizeof. rewrite WORD_SIZE_eq. apply cancel_left.
  sep_apply (data_at_memory_block
               sh (tarray int_or_ptr_type z0) (make_fields_vals g (gen, num))
               (Vptr b (Ptrofs.repr (ofs + 4)))). simpl sizeof. rewrite Z.max_r; auto.
Qed.

Lemma iter_sepcon_vertex_rep_ptrofs: forall g gen b i sh num,
    Vptr b i = gen_start g gen ->
    iter_sepcon (map (fun x : nat => (gen, x)) (nat_inc_list num)) (vertex_rep sh g)
                |-- !! (WORD_SIZE * previous_vertices_size g gen num +
                        Ptrofs.unsigned i < Ptrofs.modulus).
Proof.
  intros. induction num. 1: entailer.
  rewrite nat_inc_list_S, map_app, iter_sepcon_app_sepcon.
  assert_PROP (WORD_SIZE * previous_vertices_size g gen num +
               Ptrofs.unsigned i < Ptrofs.modulus) by
      (unfold generation_rep in IHnum; sep_apply IHnum; entailer!). clear IHnum.
  simpl iter_sepcon. entailer. unfold vertex_rep at 2. unfold vertex_at.
  rewrite vertex_head_address_eq. unfold vertex_address, vertex_offset. simpl.
  rewrite <- H. inv_int i. entailer. destruct H1 as [_ [_ [? _]]]. simpl in H1.
  destruct H4 as [_ [_ [? _]]]. simpl in H4. rewrite <- H5 in H4. clear H3 H6 H5.
  rewrite ptrofs_add_repr in *. apply prop_right.
  pose proof (pvs_ge_zero g gen num). rewrite Ptrofs.unsigned_repr_eq in H1.
  rewrite Z.mod_small in H1 by rep_omega. rewrite pvs_S.
  unfold vertex_size. rewrite <- fields_eq_length. rewrite WORD_SIZE_eq in *.
  rewrite Z.mul_add_distr_l, Z.mul_1_r, Z.add_assoc in H4.
  rewrite Ptrofs.unsigned_repr_eq in H4. rewrite Z.mod_small in H4 by rep_omega.
  assert ((@Zlength (@reptype CompSpecs int_or_ptr_type)
                    (make_fields_vals g (gen, num))) =
          (@Zlength val (make_fields_vals g (gen, num)))) by reflexivity.
  rewrite H5 in *. rep_omega.
Qed.

Lemma generation_rep_ptrofs: forall g gen b i,
    Vptr b i = gen_start g gen ->
    generation_rep g gen |--
                   !! (WORD_SIZE * graph_gen_size g gen +
                       Ptrofs.unsigned i < Ptrofs.modulus).
Proof. intros. apply (iter_sepcon_vertex_rep_ptrofs g gen b i). assumption. Qed.

Lemma generation_rep_memory_block: forall g gen,
    graph_has_gen g gen ->
    generation_rep g gen |--
                   memory_block (nth_sh g gen) (WORD_SIZE * graph_gen_size g gen)
                   (gen_start g gen).
Proof.
  intros. apply graph_has_gen_start_isptr in H.
  remember (gen_start g gen). destruct v; try contradiction.
  unfold generation_rep, graph_gen_size.
  remember (number_of_vertices (nth_gen g gen)) as num. clear Heqnum.
  remember (nth_sh g gen) as sh. clear Heqsh. induction num.
  - simpl. rewrite memory_block_zero_Vptr. auto.
  - sep_apply (iter_sepcon_vertex_rep_ptrofs g gen b i sh (S num) Heqv). Intros.
    rename H0 into HS. simpl in HS. unfold generation_rep.
    rewrite nat_inc_list_S, map_app, iter_sepcon_app_sepcon.
    simpl. unfold generation_rep in IHnum. sep_apply IHnum. rewrite pvs_S, Z.add_comm.
    rewrite <- (Ptrofs.repr_unsigned i) at 2.
    remember (previous_vertices_size g gen num) as zp.
    assert (0 <= zp) by (rewrite Heqzp; apply pvs_ge_zero).
    pose proof (svs_gt_one g (gen, num)) as HS1.
    pose proof (Ptrofs.unsigned_range i) as HS2. rewrite pvs_S in HS.
    rewrite Z.add_comm, Z.mul_add_distr_l, memory_block_split; [|rep_omega..].
    rewrite (Ptrofs.repr_unsigned i). apply cancel_left.
    sep_apply (vertex_rep_memory_block sh g (gen, num)).
    rewrite vertex_head_address_eq, <- Heqzp, <- Heqv. simpl offset_val.
    rewrite <- ptrofs_add_repr, Ptrofs.repr_unsigned. auto.
Qed.

Lemma generation_rep_align_compatible: forall g gen,
    graph_has_gen g gen ->
    generation_rep g gen |--
                   !! (align_compatible (tarray int_or_ptr_type (graph_gen_size g gen))
                                        (gen_start g gen)).
Proof.
  intros. apply graph_has_gen_start_isptr in H.
  remember (gen_start g gen). destruct v; try contradiction.
  sep_apply (generation_rep_ptrofs g gen b i Heqv). Intros.
  unfold generation_rep, graph_gen_size in *.
  remember (number_of_vertices (nth_gen g gen)) as num. clear Heqnum.
  remember (nth_sh g gen) as sh. clear Heqsh. induction num.
  - unfold previous_vertices_size. simpl fold_left. apply prop_right.
    constructor. intros. omega.
  - unfold generation_rep. rewrite nat_inc_list_S, map_app, iter_sepcon_app_sepcon.
    simpl iter_sepcon. entailer. unfold vertex_rep at 2. unfold vertex_at.
    rename H0 into HS. rewrite vertex_head_address_eq. entailer!. clear H1 H2 H3 H4.
    destruct H0 as [_ [_ [_ [? _]]]]. rewrite <- Heqv in H0. inv_int i.
    hnf in H0. rewrite ptrofs_add_repr in H0. inv H0. simpl in H1. inv H1.
    simpl in H3. simpl in HS. pose proof (svs_gt_one g (gen, num)).
    pose proof (pvs_ge_zero g gen num). rewrite pvs_S in HS.
    rewrite Ptrofs.unsigned_repr_eq in H3. rewrite Z.mod_small in H3 by rep_omega.
    rewrite Z.add_comm in H3. apply Z.divide_add_cancel_r in H3.
    2: rewrite WORD_SIZE_eq; apply Z.divide_factor_l. constructor. intros.
    rewrite Ptrofs.unsigned_repr_eq. rewrite Z.mod_small by omega. simpl sizeof.
    apply align_compatible_rec_by_value with Mptr. 1: reflexivity. simpl.
    apply Z.divide_add_r; [assumption | apply Z.divide_factor_l].
Qed.

Lemma sizeof_tarray_int_or_ptr: forall n,
    0 <= n -> sizeof (tarray int_or_ptr_type n) = (WORD_SIZE * n)%Z.
Proof. intros. simpl. rewrite Z.max_r by assumption. rep_omega. Qed.

Lemma generation_rep_field_compatible: forall g gen,
    graph_has_gen g gen ->
    generation_rep g gen |--
                   !! (field_compatible (tarray int_or_ptr_type (graph_gen_size g gen))
                                        [] (gen_start g gen)).
Proof.
  intros. pose proof H. apply graph_has_gen_start_isptr in H.
  remember (gen_start g gen). destruct v; try contradiction.
  unfold field_compatible. entailer. unfold size_compatible.
  rewrite sizeof_tarray_int_or_ptr by apply pvs_ge_zero.
  sep_apply (generation_rep_ptrofs g gen b i Heqv). entailer. rewrite Heqv.
  sep_apply (generation_rep_align_compatible g gen H0). entailer!.
Qed.

Lemma generation_rep_data_at_: forall g gen,
    graph_has_gen g gen ->
    generation_rep g gen |--
                   data_at_ (nth_sh g gen)
                   (tarray int_or_ptr_type (graph_gen_size g gen))
                   (gen_start g gen).
Proof.
  intros. sep_apply (generation_rep_field_compatible g gen H). Intros.
  sep_apply (generation_rep_memory_block g gen H).
  rewrite <- sizeof_tarray_int_or_ptr by apply pvs_ge_zero.
  rewrite memory_block_data_at_; auto.
Qed.

Lemma field_compatible_tarray_join:
  forall (n n1 : Z) (p : val) (t: type),
    0 <= n1 <= n -> complete_legal_cosu_type t = true ->
    field_compatible (tarray t n1) [] p ->
    field_compatible (tarray t (n - n1)) []
                     (offset_val (sizeof t * n1) p) ->
    field_compatible (tarray t n) [] p.
Proof.
  intros. unfold field_compatible. simpl. destruct H1 as [? [_ [? [? _]]]].
  destruct H2 as [_ [_ [? [? _]]]]. destruct p; try contradiction. clear H1.
  simpl isptr. inv_int i. unfold size_compatible in *. simpl in H2.
  simpl sizeof in *. rewrite Z.max_r in * by omega. pose proof (sizeof_pos t).
  remember (sizeof t) as S. rewrite ptrofs_add_repr in H2.
  rewrite Ptrofs.unsigned_repr in * by rep_omega.
  assert (0 <= ofs + S * n1 <= Ptrofs.max_unsigned). {
    destruct H, H6. split. 2: rep_omega. apply Z.add_nonneg_nonneg. 1: omega.
    apply Z.mul_nonneg_nonneg; omega. }
  rewrite Ptrofs.unsigned_repr in * by assumption.
  assert (forall i, ofs + S * n1 + S * (i - n1) = ofs + S * i). {
    intros. rewrite <- Z.add_assoc. rewrite <- Z.mul_add_distr_l.
    do 2 f_equal. omega. } rewrite H8 in H2. do 4 (split; auto). constructor. intros.
  unfold tarray in *. inversion H4; subst. 1: simpl in H10; inversion H10.
  inversion H5; subst. 1: simpl in H10; inversion H10. remember (sizeof t) as S.
  rewrite ptrofs_add_repr in H15. rewrite Ptrofs.unsigned_repr in * by rep_omega.
  assert (0 <= i < n1 \/ n1 <= i < n) by omega. destruct H10.
  1: apply H14; assumption. assert (0 <= i - n1 < n - n1) by omega.
  specialize (H15 _ H11). rewrite H8 in H15. assumption.
Qed.

Lemma data_at_tarray_fold: forall sh n n1 p t (v v' v1 v2: list (reptype t)),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    complete_legal_cosu_type t = true ->
    data_at sh (tarray t n1) v1 p *
    data_at sh (tarray t (n - n1)) v2 (offset_val (sizeof t * n1) p) |--
            data_at sh (tarray t n) v p.
Proof.
  intros. rewrite (split2_data_at_Tarray sh t n n1 v v' v1 v2);
            [|assumption..]. entailer!. unfold field_address0. rewrite if_true.
  - simpl nested_field_offset. entailer!.
  - pose proof (field_compatible_tarray_join n _ p _ H H4 H5 H7). clear -H1 H.
    red in H1. red. simpl in *. intuition.
Qed.

Lemma data_at_tarray_unfold: forall sh n n1 p t (v v' v1 v2: list (reptype t)),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    data_at sh (tarray t n) v p |--
            data_at sh (tarray t n1) v1 p *
    data_at sh (tarray t (n - n1)) v2 (offset_val (sizeof t * n1) p).
Proof.
  intros. sep_apply (data_at_local_facts sh (tarray t n) v p).
  Intros. rewrite (split2_data_at_Tarray sh t n n1 v v' v1 v2);
            [|assumption..]. cancel. unfold field_address0. rewrite if_true.
  - simpl nested_field_offset. entailer!.
  - clear -H H4. red. red in H4. simpl in *. intuition.
Qed.

Lemma data_at_tarray_split: forall sh n n1 p t (v v' v1 v2: list (reptype t)),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    complete_legal_cosu_type t = true ->
    data_at sh (tarray t n) v p =
    data_at sh (tarray t n1) v1 p *
    data_at sh (tarray t (n - n1)) v2 (offset_val (sizeof t * n1) p).
Proof.
  intros. apply pred_ext.
  - apply data_at_tarray_unfold with v'; assumption.
  - apply data_at_tarray_fold with v'; assumption.
Qed.

Lemma data_at_tarray_value: forall sh n n1 p (v v' v1 v2: list val),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    data_at sh (tarray int_or_ptr_type n) v p =
    data_at sh (tarray int_or_ptr_type n1) v1 p *
    data_at sh (tarray int_or_ptr_type (n - n1)) v2 (offset_val (WORD_SIZE * n1) p).
Proof. intros. eapply data_at_tarray_split; eauto. Qed.

Lemma data_at_tarray_tuint: forall sh n n1 p (v v' v1 v2: list val),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    data_at sh (tarray tuint n) v p =
    data_at sh (tarray tuint n1) v1 p *
    data_at sh (tarray tuint (n - n1)) v2 (offset_val (WORD_SIZE * n1) p).
Proof. intros. eapply data_at_tarray_split; eauto. Qed.

Lemma data_at_tarray_space: forall sh n n1 p (v: list (reptype space_type)),
    0 <= n1 <= n ->
    n = Zlength v ->
    data_at sh (tarray space_type n) v p =
    data_at sh (tarray space_type n1) (sublist 0 n1 v) p *
    data_at sh (tarray space_type (n - n1)) (sublist n1 n v)
            (offset_val (SPACE_STRUCT_SIZE * n1) p).
Proof.
  intros. eapply data_at_tarray_split; eauto. 1: omega.
  autorewrite with sublist. reflexivity.
Qed.

Lemma data_at__tarray_value: forall sh n n1 p,
    0 <= n1 <= n ->
    data_at_ sh (tarray int_or_ptr_type n) p =
    data_at_ sh (tarray int_or_ptr_type n1) p *
    data_at_ sh (tarray int_or_ptr_type (n - n1)) (offset_val (WORD_SIZE * n1) p).
Proof.
  intros. rewrite !data_at__eq.
  apply data_at_tarray_value with (default_val (tarray int_or_ptr_type n));
    [assumption | unfold default_val; simpl; autorewrite with sublist..];
    [omega | reflexivity..].
Qed.

Definition valid_int_or_ptr (x: val) :=
  match x with
  | Vint i => Int.testbit i 0 = true
  | Vptr _ z => Ptrofs.testbit z 0 = false /\ Ptrofs.testbit z 1 = false
  | _ => False
  end.

Lemma valid_int_or_ptr_ii1:
  forall i, valid_int_or_ptr (Vint (Int.repr (i + i + 1))).
Proof.
  intros.
  simpl.
  rewrite Int.unsigned_repr_eq.
  rewrite Zodd_mod.
  apply Zeq_is_eq_bool.
  replace (i+i) with (2*i)%Z by omega.
  rewrite <- Zmod_div_mod; try omega.
  - rewrite Z.mul_comm, Z.add_comm, Z_mod_plus_full. reflexivity.
  - compute; reflexivity.
  - exists (Z.div Int.modulus 2). reflexivity.
Qed.

Lemma four_divided_odd_false: forall z, (4 | z) -> Z.odd z = false.
Proof.
  intros. rewrite Zodd_mod. inversion H.
  replace (x * 4)%Z with (2 * x * 2)%Z in H0 by omega. subst.
  rewrite Z_mod_mult; unfold Zeq_bool; reflexivity.
Qed.

Lemma four_divided_tenth_pl_false: forall i,
    (4 | Ptrofs.unsigned i) -> Ptrofs.testbit i 1 = false.
Proof.
  intros. unfold Ptrofs.testbit. inversion H.
  replace (x * 4)%Z with (2 * (x * 2))%Z in H0 by omega.
  rewrite H0. rewrite Z.double_bits. simpl.
  rewrite Zodd_mod; rewrite Z_mod_mult;
  unfold Zeq_bool; reflexivity.
Qed.

Lemma vertex_rep_valid_int_or_ptr: forall sh g v,
    vertex_rep sh g v |-- !! (valid_int_or_ptr (vertex_address g v)).
Proof.
  intros. sep_apply (vertex_rep_isptr sh g v). Intros.
  unfold vertex_rep, vertex_at, vertex_address.
  remember (gen_start g (vgeneration v)) as vv. destruct vv; try contradiction.
  inv_int i. entailer!.
  destruct H3 as [_ [_ [_ [? _]]]]. clear -H3. hnf in H3. inv H3.
  1: simpl in H; inversion H. assert (0 <= 0 < Zlength (make_fields_vals g v)). {
    split; [omega|]. rewrite fields_eq_length.
    destruct (raw_fields_head_cons (vlabel g v)) as [r [l [? _]]]. rewrite H.
    rewrite Zlength_cons. pose proof (Zlength_nonneg l). omega.
  } apply H4 in H. rewrite Z.mul_0_r, Z.add_0_r in H. clear H4. inv H. inv H0.
  simpl in H1. split.
  - simpl; rewrite !ptrofs_add_repr in *; apply four_divided_odd_false; assumption.
  - rewrite !ptrofs_add_repr in *; apply four_divided_tenth_pl_false; assumption.
Qed.

Lemma graph_rep_generation_rep: forall g gen,
    graph_has_gen g gen -> graph_rep g |-- generation_rep g gen * TT.
Proof.
  intros. unfold graph_rep. red in H. rewrite <- nat_inc_list_In_iff in H.
  sep_apply (iter_sepcon_in_true (generation_rep g) _ _ H). apply derives_refl.
Qed.

Lemma generation_rep_vertex_rep: forall g gen index,
    gen_has_index g gen index ->
    generation_rep g gen |--
                   vertex_rep (nth_sh g gen) g (gen, index) * TT.
Proof.
  intros. unfold generation_rep. remember (number_of_vertices (nth_gen g gen)) as num.
  assert (nth index (map (fun x : nat => (gen, x)) (nat_inc_list num))
              (gen, O) = (gen, index)). {
    change (gen, O) with ((fun x: nat => (gen, x)) O). rewrite map_nth. red in H.
    rewrite nat_inc_list_nth by omega. reflexivity.
  } assert (In (gen, index) (map (fun x : nat => (gen, x)) (nat_inc_list num))). {
    rewrite <- H0. apply nth_In. rewrite map_length, nat_inc_list_length.
    red in H. subst num. assumption.
  } apply (iter_sepcon_in_true (vertex_rep _ g) _ _ H1).
Qed.

Lemma graph_rep_vertex_rep: forall g v,
    graph_has_v g v -> graph_rep g |-- EX sh: share, !!(writable_share sh) &&
                                                       vertex_rep sh g v * TT.
Proof.
  intros. destruct H. sep_apply (graph_rep_generation_rep g (vgeneration v) H).
  red in H0. sep_apply (generation_rep_vertex_rep g (vgeneration v) _ H0).
  Exists (nth_sh g (vgeneration v)). destruct v. simpl. entailer!.
  apply generation_share_writable.
Qed.

Lemma graph_rep_valid_int_or_ptr: forall g v,
    graph_has_v g v -> graph_rep g |-- !! (valid_int_or_ptr (vertex_address g v)).
Proof.
  intros. sep_apply (graph_rep_vertex_rep g v H). Intros sh.
  sep_apply (vertex_rep_valid_int_or_ptr sh g v). entailer!.
Qed.

(* weak derives for use in funspecs *)
Program Definition weak_derives (P Q: mpred): mpred :=
  fun w => predicates_hered.derives (approx (S (level w)) P) (approx (S (level w)) Q).
Next Obligation.
  repeat intro.
  destruct H1.
  apply age_level in H.
  lapply (H0 a0); [|split; auto; omega].
  intro HQ; destruct HQ.
  eexists; eauto.
Defined.

Lemma derives_nonexpansive: forall P Q n,
    approx n (weak_derives P Q) = approx n (weak_derives (approx n P) (approx n Q)).
Proof.
  apply nonexpansive2_super_non_expansive; repeat intro.
  - split; intros ??%necR_level Hshift ? HP;
      destruct (Hshift _ HP); destruct HP; eexists;  eauto; eapply H; auto; omega.
  - split; intros ??%necR_level Hshift ? []; apply Hshift;
      split; auto; apply (H a0); auto; omega.
Qed.

Lemma derives_nonexpansive_l: forall P Q n,
    approx n (weak_derives P Q) = approx n (weak_derives (approx n P) Q).
Proof.
  repeat intro.
  apply (nonexpansive_super_non_expansive (fun P => weak_derives P Q)); repeat intro.
  split; intros ??%necR_level Hshift ? [];
    apply Hshift; split; auto; apply (H a0); auto; omega.
Qed.

Lemma derives_nonexpansive_r: forall P Q n,
    approx n (weak_derives P Q) = approx n (weak_derives P (approx n Q)).
Proof.
  repeat intro.
  apply (nonexpansive_super_non_expansive (fun Q => weak_derives P Q)); repeat intro.
  split; intros ??%necR_level Hshift ? HP;
    destruct (Hshift _ HP); destruct HP;
      eexists;  eauto;
        eapply H; auto; omega.
Qed.

Lemma derives_weak: forall P Q, P |-- Q -> TT |-- weak_derives P Q.
Proof.
  intros.
  change (predicates_hered.derives TT (weak_derives P Q)).
  intros w _ ? [? HP].
  specialize (H _ HP).
  eexists; eauto.
Qed.

Lemma apply_derives: forall P Q, (weak_derives P Q && emp) * P |-- Q.
Proof.
  intros.
  change (predicates_hered.derives ((weak_derives P Q && emp) * P) Q).
  intros ? (? & ? & ? & [Hderives Hemp] & HP).
  destruct (join_level _ _ _ H).
  apply Hemp in H; subst.
  lapply (Hderives a); [|split; auto; omega].
  intro X; destruct X; eauto 7.
Qed.

Definition heap_rest_gen_data_at_ (g: LGraph) (t_info: thread_info) (gen: nat) :=
  data_at_ (nth_sh g gen)
           (tarray int_or_ptr_type
                   (total_space (nth_space t_info gen) - graph_gen_size g gen))
           (offset_val (WORD_SIZE * graph_gen_size g gen) (gen_start g gen)).

Lemma heap_rest_rep_iter_sepcon: forall g t_info,
    graph_thread_info_compatible g t_info ->
    heap_rest_rep (ti_heap t_info) =
    iter_sepcon (nat_inc_list (length (g_gen (glabel g))))
                (heap_rest_gen_data_at_ g t_info).
Proof.
  intros. unfold heap_rest_rep.
  pose proof (gt_gs_compatible _ _ H). destruct H as [? [? ?]].
  rewrite <- (firstn_skipn (length (g_gen (glabel g))) (spaces (ti_heap t_info))).
  rewrite iter_sepcon_app_sepcon. rewrite <- map_skipn in H1.
  remember (skipn (length (g_gen (glabel g))) (spaces (ti_heap t_info))).
  assert (iter_sepcon l space_rest_rep = emp). {
    clear Heql. induction l; simpl. 1: reflexivity.
    rewrite IHl by (simpl in H1; apply Forall_tl in H1; assumption).
    rewrite Forall_forall in H1. simpl in H1. unfold space_rest_rep. rewrite if_true.
    - rewrite emp_sepcon; reflexivity.
    - symmetry. apply H1. left; reflexivity.
  } rewrite H3.
  replace (firstn (length (g_gen (glabel g))) (spaces (ti_heap t_info)))
    with (map (nth_space t_info) (nat_inc_list (length (g_gen (glabel g))))).
  - rewrite <- iter_sepcon_map, sepcon_emp.
    apply iter_sepcon_func_strong. intros gen ?.
    unfold space_rest_rep, heap_rest_gen_data_at_. rewrite nat_inc_list_In_iff in H4.
    specialize (H0 _ H4). destruct H0 as [? [? ?]]. rewrite <- H0, if_false.
    + unfold gen_start. rewrite if_true. 2: assumption. rewrite <- H5, <- H6. f_equal.
    + pose proof (start_isptr (nth_gen g gen)).
      destruct (start_address (nth_gen g gen)); try contradiction. intro. inversion H8.
  - unfold nth_space. remember (spaces (ti_heap t_info)) as ls.
    remember (length (g_gen (glabel g))) as m. clear -H2. revert ls H2.
    induction m; intros. 1: simpl; reflexivity. rewrite nat_inc_list_S, map_app.
    rewrite IHm by omega. simpl map. clear IHm. revert ls H2. induction m; intros.
    + destruct ls. 1: simpl in H2; exfalso; omega. simpl. reflexivity.
    + destruct ls. 1: simpl in H2; exfalso; omega.
      simpl firstn at 1. simpl nth. Opaque firstn. simpl. Transparent firstn.
      rewrite IHm by (simpl in H2; omega). simpl. destruct ls; reflexivity.
Qed.

Lemma heap_rest_rep_data_at_: forall (g: LGraph) (t_info: thread_info) gen,
    graph_has_gen g gen ->
    graph_thread_info_compatible g t_info ->
    heap_rest_rep (ti_heap t_info) |-- heap_rest_gen_data_at_ g t_info gen * TT.
Proof.
  intros. rewrite (heap_rest_rep_iter_sepcon g) by assumption.
  sep_apply (iter_sepcon_in_true (heap_rest_gen_data_at_ g t_info)
                                 (nat_inc_list (length (g_gen (glabel g)))) gen).
  - rewrite nat_inc_list_In_iff. assumption.
  - apply derives_refl.
Qed.

Definition generation_data_at_ g t_info gen :=
  data_at_ (nth_sh g gen)
           (tarray int_or_ptr_type (gen_size t_info gen)) (gen_start g gen).

Lemma gr_hrgda_data_at_: forall g t_info gen,
    graph_has_gen g gen ->
    graph_thread_info_compatible g t_info ->
    generation_rep g gen *
    heap_rest_gen_data_at_ g t_info gen |-- generation_data_at_ g t_info gen.
Proof.
  intros. sep_apply (generation_rep_data_at_ g gen H).
  unfold heap_rest_gen_data_at_, generation_data_at_.
  remember (nth_sh g gen) as sh.
  rewrite <- (data_at__tarray_value sh _ _ (gen_start g gen)).
  - unfold gen_size. entailer!.
  - unfold graph_gen_size. destruct (gt_gs_compatible _ _ H0 _ H) as [_ [_ ?]].
    rewrite H1. apply space_order.
Qed.

Lemma graph_heap_rest_iter_sepcon: forall g t_info,
    graph_thread_info_compatible g t_info ->
    graph_rep g * heap_rest_rep (ti_heap t_info) |--
                                iter_sepcon (nat_inc_list (length (g_gen (glabel g))))
                                (generation_data_at_ g t_info).
Proof.
  intros. unfold graph_rep. rewrite (heap_rest_rep_iter_sepcon _ _ H).
  assert (forall gen,
             In gen (nat_inc_list (length (g_gen (glabel g)))) -> graph_has_gen g gen)
    by (intros; rewrite nat_inc_list_In_iff in H0; assumption).
  remember (length (g_gen (glabel g))). clear Heqn. revert H0. induction n; intros.
  - simpl. rewrite emp_sepcon. apply derives_refl.
  - rewrite nat_inc_list_S. rewrite !iter_sepcon_app_sepcon. simpl.
    rewrite !sepcon_emp. pull_left (generation_rep g n). rewrite <- sepcon_assoc.
    rewrite (sepcon_assoc (generation_rep g n)). sep_apply IHn.
    + intros. apply H0. rewrite nat_inc_list_S, in_app_iff. left; assumption.
    + cancel. sep_apply (gr_hrgda_data_at_ g t_info n); auto.
      apply H0. rewrite nat_inc_list_S, in_app_iff. right. left. reflexivity.
Qed.

Lemma graph_and_heap_rest_data_at_: forall (g: LGraph) (t_info: thread_info) gen,
    graph_has_gen g gen ->
    graph_thread_info_compatible g t_info ->
    graph_rep g * heap_rest_rep (ti_heap t_info) |--
                                generation_data_at_ g t_info gen * TT.
Proof.
  intros. sep_apply (graph_heap_rest_iter_sepcon _ _ H0).
  sep_apply (iter_sepcon_in_true (generation_data_at_ g t_info)
                                 (nat_inc_list (length (g_gen (glabel g)))) gen);
    [rewrite nat_inc_list_In_iff; assumption | apply derives_refl].
Qed.

Lemma graph_and_heap_rest_valid_ptr: forall (g: LGraph) (t_info: thread_info) gen,
    graph_has_gen g gen -> ti_size_spec t_info ->
    graph_thread_info_compatible g t_info ->
    graph_rep g * heap_rest_rep (ti_heap t_info) |--
                                valid_pointer (space_start (nth_space t_info gen)).
Proof.
  intros. sep_apply (graph_and_heap_rest_data_at_ _ _ _ H H1).
  unfold generation_data_at_. destruct (gt_gs_compatible _ _ H1 _ H) as [? [? ?]].
  sep_apply (data_at__memory_block_cancel
               (nth_sh g gen)
               (tarray int_or_ptr_type (gen_size t_info gen)) (gen_start g gen)).
  simpl sizeof. rewrite Z.max_r by
      (unfold gen_size; apply (proj1 (total_space_range (nth_space t_info gen)))).
  unfold gen_start. if_tac. 2: contradiction.
  rewrite H2. sep_apply (memory_block_valid_ptr
                           (nth_sh g gen) (4 * gen_size t_info gen)
                           (space_start (nth_space t_info gen)));
                [|pose proof (ti_size_gt_0 g t_info gen H1 H5 H0); omega | entailer!].
  - unfold nth_sh. apply readable_nonidentity, writable_readable,
                   generation_share_writable.
Qed.

Lemma generation_data_at__ptrofs: forall g t_info gen b i,
    Vptr b i = gen_start g gen ->
    generation_data_at_ g t_info gen |--
                        !! (WORD_SIZE * gen_size t_info gen + Ptrofs.unsigned i <=
                            Ptrofs.max_unsigned).
Proof.
  intros. unfold generation_data_at_. rewrite <- H. entailer!.
  destruct H0 as [_ [_ [? _]]]. red in H0. simpl sizeof in H0.
  rewrite Z.max_r in H0; [rep_omega |
                          unfold gen_size; apply (proj1 (total_space_range _))].
Qed.

Lemma outlier_rep_single_rep: forall outlier p,
    In p outlier ->
    outlier_rep outlier |-- single_outlier_rep p * TT.
Proof.
  intros. unfold outlier_rep. apply (in_map single_outlier_rep) in H.
  apply fold_right_andp in H. destruct H as [Q ?]. rewrite H.
  apply andp_left1. cancel.
Qed.

Lemma roots_outlier_rep_single_rep: forall (roots: roots_t) outlier p,
    In (inl (inr p)) roots ->
    incl (filter_sum_right (filter_sum_left roots)) outlier ->
    outlier_rep outlier |-- single_outlier_rep p * TT.
Proof. intros. apply outlier_rep_single_rep. eapply root_in_outlier; eauto. Qed.

Lemma single_outlier_rep_valid_pointer: forall p,
    single_outlier_rep p |-- valid_pointer (GC_Pointer2val p) * TT.
Proof.
  intros. unfold single_outlier_rep. Intros sh. remember (GC_Pointer2val p) as pp.
  sep_apply (data_at__memory_block_cancel sh (tptr tvoid) pp). simpl sizeof.
  sep_apply (memory_block_valid_ptr sh 4 pp);
    [apply readable_nonidentity; assumption | apply derives_refl].
Qed.

Lemma outlier_rep_valid_pointer: forall outlier p,
    In p outlier ->
    outlier_rep outlier |-- valid_pointer (GC_Pointer2val p) * TT.
Proof.
  intros. sep_apply (outlier_rep_single_rep _ _ H).
  sep_apply (single_outlier_rep_valid_pointer p). cancel.
Qed.

Lemma roots_outlier_rep_valid_pointer: forall (roots: roots_t) outlier p,
    In (inl (inr p)) roots ->
    incl (filter_sum_right (filter_sum_left roots)) outlier ->
    outlier_rep outlier |-- valid_pointer (GC_Pointer2val p) * TT.
Proof. intros. apply outlier_rep_valid_pointer. eapply root_in_outlier; eauto. Qed.

Lemma single_outlier_rep_valid_int_or_ptr: forall p,
    single_outlier_rep p |-- !! (valid_int_or_ptr (GC_Pointer2val p)).
Proof.
  intros. unfold single_outlier_rep. Intros sh. remember (GC_Pointer2val p) as pp.
  clear Heqpp. entailer!. destruct H0 as [? [_ [_ [? _]]]].
  destruct pp; try contradiction. unfold align_compatible in H1. inv H1.
  inv H2. simpl in H3. split.
  - simpl; apply four_divided_odd_false; assumption.
  - apply four_divided_tenth_pl_false; assumption.
Qed.

Import Share.

Lemma writable_readable_share_common: forall rsh wsh,
    readable_share rsh -> writable_share wsh ->
    exists sh, nonunit sh /\ join_sub sh rsh /\ join_sub sh wsh.
Proof.
  intros. assert (join (glb Lsh rsh) (glb Rsh rsh) rsh). {
    apply (comp_parts_join comp_Lsh_Rsh).
    - rewrite glb_twice, <- glb_assoc, glb_Lsh_Rsh, (glb_commute bot), glb_bot.
      apply join_comm, bot_join_eq.
    - rewrite <- glb_assoc, (glb_commute Rsh), glb_Lsh_Rsh,
      (glb_commute bot), glb_bot, glb_twice. apply bot_join_eq.
  } assert (join (glb Rsh rsh) (glb Rsh (comp rsh)) Rsh). {
    rewrite !(glb_commute Rsh). apply (@comp_parts_join rsh (comp rsh)); auto.
    - rewrite glb_twice, <- glb_assoc, comp2, (glb_commute bot), glb_bot.
      apply join_comm, bot_join_eq.
    - rewrite <- glb_assoc, (glb_commute (comp _)), comp2, (glb_commute bot), glb_bot,
      glb_twice. apply bot_join_eq.
  } exists (glb Rsh rsh). split; [|split].
  - red in H. apply nonidentity_nonunit, H.
  - apply join_comm in H1. exists (glb Lsh rsh). assumption.
  - apply join_sub_trans with Rsh; [exists (glb Rsh (comp rsh))|destruct H0];
      assumption.
Qed.

Lemma readable_writable_memory_block_FF: forall rsh wsh m1 m2 p,
    readable_share rsh -> writable_share wsh ->
    0 < m1 <= Ptrofs.max_unsigned -> 0 < m2 <= Ptrofs.max_unsigned ->
    memory_block rsh m1 p * memory_block wsh m2 p |-- FF.
Proof.
  intros.
  destruct (writable_readable_share_common _ _ H H0) as [sh [? [[shr ?] [shw ?]]]].
  rewrite <- (memory_block_share_join _ _ _ _ _ H4).
  rewrite <- (memory_block_share_join _ _ _ _ _ H5).
  rewrite <- sepcon_assoc, (sepcon_comm (memory_block sh m1 p)),
  (sepcon_assoc (memory_block shr m1 p)).
  sep_apply (memory_block_conflict sh _ _ p H3 H1 H2). entailer!.
Qed.

Lemma v_in_range_data_at_: forall v p n sh,
    v_in_range v p (WORD_SIZE * n) ->
    data_at_ sh (tarray int_or_ptr_type n) p |--
             EX m: Z, !!(0 < m <= Ptrofs.max_unsigned) && memory_block sh m v * TT.
Proof.
  intros. destruct H as [o [? ?]]. rewrite data_at__memory_block. Intros.
  destruct H1 as [? [_ [? _]]]. destruct p; try contradiction. inv_int i.
  simpl offset_val in H0. rewrite ptrofs_add_repr in H0.
  assert (0 <= n)%Z by rep_omega. rewrite sizeof_tarray_int_or_ptr by assumption.
  simpl in H2. rewrite Ptrofs.unsigned_repr in H2 by rep_omega.
  rewrite Z.max_r in H2 by assumption. rewrite WORD_SIZE_eq in *.
  assert (4 * n = o + (4 * n - o))%Z by omega. remember (4 * n - o) as m.
  rewrite H5 in *. rewrite (memory_block_split sh b ofs o m) by omega.
  clear Heqm n H5 H3. assert (0 < m <= Ptrofs.max_unsigned) by rep_omega.
  rewrite <- H0. Exists m. entailer!.
Qed.

Lemma single_outlier_rep_memory_block_FF: forall gp p n wsh,
    writable_share wsh -> v_in_range (GC_Pointer2val gp) p (WORD_SIZE * n) ->
    single_outlier_rep gp * data_at_ wsh (tarray int_or_ptr_type n) p |-- FF.
Proof.
  intros. unfold single_outlier_rep. Intros rsh. remember (GC_Pointer2val gp) as ggp.
  clear gp Heqggp. rename ggp into gp.
  sep_apply (v_in_range_data_at_ _ _ _ wsh H0). Intros m.
  sep_apply (data_at__memory_block_cancel rsh (tptr tvoid) gp). simpl sizeof.
  rewrite <- sepcon_assoc.
  sep_apply (readable_writable_memory_block_FF _ _ 4 m gp H1 H); auto;
    [rep_omega | entailer].
Qed.

Lemma graph_and_heap_rest_v_in_range_iff: forall g t_info gen v,
    graph_thread_info_compatible g t_info ->
    graph_has_gen g gen -> graph_has_v g v ->
    graph_rep g * heap_rest_rep (ti_heap t_info) |--
                                !! (v_in_range (vertex_address g v) (gen_start g gen)
                                               (WORD_SIZE * gen_size t_info gen) <-> vgeneration v = gen).
Proof.
  intros. unfold iff. rewrite and_comm. apply prop_and_right.
  - intros. rewrite <- H2. apply graph_thread_v_in_range; assumption.
  - rewrite prop_impl, <- imp_andp_adjoint; Intros.
    destruct (Nat.eq_dec (vgeneration v) gen). 1: apply prop_right; assumption.
    sep_apply (graph_heap_rest_iter_sepcon _ _ H).
    pose proof (graph_thread_v_in_range _ _ _ H H1). destruct H1.
    assert (NoDup [vgeneration v; gen]) by
        (constructor; [|constructor; [|constructor]]; intro HS;
         simpl in HS; destruct HS; auto).
    assert (incl [vgeneration v; gen] (nat_inc_list (length (g_gen (glabel g))))) by
        (apply incl_cons; [|apply incl_cons];
         [rewrite nat_inc_list_In_iff; assumption..| apply incl_nil]).
    sep_apply (iter_sepcon_incl_true (generation_data_at_ g t_info) H5 H6); simpl.
    rewrite sepcon_emp. unfold generation_data_at_.
    remember (nth_sh g (vgeneration v)) as sh1. remember (nth_sh g gen) as sh2.
    sep_apply (v_in_range_data_at_ _ _ _ sh1 H3). Intros m1.
    sep_apply (v_in_range_data_at_ _ _ _ sh2 H2). Intros m2.
    remember (vertex_address g v) as p.
    rewrite <- sepcon_assoc, (sepcon_comm (memory_block sh2 m2 p)),
    (sepcon_assoc TT).
    sep_apply (readable_writable_memory_block_FF sh2 sh1 m2 m1 p); auto.
    + apply writable_readable. subst. apply generation_share_writable.
    + subst. apply generation_share_writable.
    + entailer!.
Qed.

Lemma graph_gen_ramif_stable: forall g gen,
    graph_has_gen g gen ->
    graph_rep g |-- generation_rep g gen * (generation_rep g gen -* graph_rep g).
Proof.
  intros. unfold graph_rep. remember (nat_inc_list (length (g_gen (glabel g)))).
  apply iter_sepcon_ramif_stable_1. subst l. rewrite nat_inc_list_In_iff. assumption.
Qed.

Lemma gen_vertex_ramif_stable: forall g gen index,
    gen_has_index g gen index ->
    generation_rep g gen |--
                   vertex_rep (nth_sh g gen) g (gen, index) *
    (vertex_rep (nth_sh g gen) g (gen, index) -* generation_rep g gen).
Proof.
  intros. unfold generation_rep. remember (nth_sh g gen) as sh.
  apply iter_sepcon_ramif_stable_1.
  change (gen, index) with ((fun x : nat => (gen, x)) index). apply in_map.
  rewrite nat_inc_list_In_iff. assumption.
Qed.

Lemma graph_vertex_ramif_stable: forall g v,
    graph_has_v g v ->
    graph_rep g |-- vertex_rep (nth_sh g (vgeneration v)) g v *
    (vertex_rep (nth_sh g (vgeneration v)) g v -* graph_rep g).
Proof.
  intros. destruct H. sep_apply (graph_gen_ramif_stable _ _ H).
  sep_apply (gen_vertex_ramif_stable _ _ _ H0). destruct v as [gen index].
  simpl. cancel. apply wand_frame_ver.
Qed.

Lemma heap_rest_rep_cut: forall (h: heap) i s (H1: 0 <= i < Zlength (spaces h))
                                (H2: has_space (Znth i (spaces h)) s),
    space_start (Znth i (spaces h)) <> nullval ->
    heap_rest_rep h =
    data_at_ (space_sh (Znth i (spaces h))) (tarray int_or_ptr_type s)
             (offset_val (WORD_SIZE * used_space (Znth i (spaces h)))
                         (space_start (Znth i (spaces h)))) *
    heap_rest_rep (cut_heap h i s H1 H2).
Proof.
  intros. unfold heap_rest_rep.
  pose proof (split3_full_length_list
                0 i _ _ H1 (Zminus_0_l_reverse (Zlength (spaces h)))).
  replace (i - 0) with i in H0 by omega. simpl in *.
  remember (firstn (Z.to_nat i) (spaces h)) as l1.
  remember (skipn (Z.to_nat (i + 1)) (spaces h)) as l2.
  assert (Zlength l1 = i). {
    rewrite Zlength_length by omega. subst l1. apply firstn_length_le.
    rewrite Zlength_correct in H1. rep_omega. }
  rewrite H0 at 5. rewrite (upd_Znth_char _ _ _ _ _ H3).
  rewrite H0 at 1. rewrite !iter_sepcon_app_sepcon. simpl.
  remember (data_at_ (space_sh (Znth i (spaces h))) (tarray int_or_ptr_type s)
                     (offset_val (WORD_SIZE * used_space (Znth i (spaces h)))
                                 (space_start (Znth i (spaces h))))) as P.
  rewrite (sepcon_comm P), sepcon_assoc. f_equal.
  rewrite (sepcon_comm _ P), <- sepcon_assoc. f_equal.
  unfold space_rest_rep. simpl. do 2 rewrite if_false by assumption.
  red in H2. subst P. remember (Znth i (spaces h)) as sp.
  rewrite (data_at__tarray_value _ _ _ _ H2). rewrite offset_offset_val.
  replace (total_space sp - used_space sp - s) with
      (total_space sp - (used_space sp + s)) by omega.
  replace (WORD_SIZE * used_space sp + WORD_SIZE * s) with
      (WORD_SIZE * (used_space sp + s))%Z by rep_omega. reflexivity.
Qed.

Lemma data_at__singleton_array_eq:
  forall sh tp p, data_at_ sh (tarray tp 1) p = data_at_ sh tp p.
Proof.
  intros. rewrite data_at__tarray. simpl.
  rewrite data_at__eq, (data_at_singleton_array_eq _ _ (default_val tp)); reflexivity.
Qed.

Lemma field_compatible_int_or_ptr_tuint_iff: forall p,
    field_compatible int_or_ptr_type [] p <-> field_compatible tuint [] p.
Proof.
  intros. unfold field_compatible. simpl.
  intuition; unfold align_compatible in *; destruct p; try constructor; inv H2;
    inv H3; apply align_compatible_rec_by_value with (ch := Mint32); try reflexivity;
      simpl in *; assumption.
Qed.

Lemma data_at__int_or_ptr_tuint: forall sh p,
    data_at_ sh (tarray int_or_ptr_type 1) p = data_at_ sh tuint p.
Proof.
  intros. rewrite data_at__singleton_array_eq, !data_at__memory_block,
          field_compatible_int_or_ptr_tuint_iff. reflexivity.
Qed.

Lemma lacv_generation_rep_not_eq: forall g v to n,
    n <> to -> graph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    generation_rep (lgraph_add_copied_v g v to) n = generation_rep g n.
Proof.
  intros. unfold generation_rep. rewrite lacv_nth_gen by assumption.
  apply iter_sepcon_func_strong. intros. apply list_in_map_inv in H3.
  destruct H3 as [m [? ?]]. unfold nth_sh. rewrite lacv_nth_gen by assumption.
  remember (generation_sh (nth_gen g n)) as sh. unfold vertex_rep. subst x.
  assert (graph_has_v g (n, m)). {
    rewrite nat_inc_list_In_iff in H4.
    destruct (Nat.lt_ge_cases n (length (g_gen (glabel g)))).
    - split; simpl; assumption.
    - exfalso. unfold nth_gen in H4. rewrite nth_overflow in H4 by assumption.
      simpl in H4. omega. } f_equal.
  - apply lacv_vertex_address_old; assumption.
  - apply lacv_make_header_old. intro S; inversion S. contradiction.
  - apply lacv_make_fields_vals_old; assumption.
Qed.

Lemma lacv_icgr_not_eq: forall l g v to,
    ~ In to l -> graph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    iter_sepcon l (generation_rep (lgraph_add_copied_v g v to)) =
    iter_sepcon l (generation_rep g).
Proof.
  intros. induction l; simpl. 1: reflexivity. rewrite IHl.
  - f_equal. apply lacv_generation_rep_not_eq; [|assumption..].
    intro. apply H. left. assumption.
  - intro. apply H. right. assumption.
Qed.

Lemma lacv_generation_rep_eq: forall g v to,
    graph_has_v g v -> graph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    generation_rep (lgraph_add_copied_v g v to) to =
    vertex_at (nth_sh g to) (vertex_address g (new_copied_v g to))
              (make_header g v) (make_fields_vals g v) * generation_rep g to.
Proof.
  intros. unfold generation_rep. rewrite lacv_nth_sh by assumption.
  remember (number_of_vertices (nth_gen g to)).
  unfold lgraph_add_copied_v at 1. unfold nth_gen. simpl.
  rewrite cvmgil_eq by assumption. simpl. unfold nth_gen in Heqn. rewrite <- Heqn.
  rewrite nat_inc_list_app, map_app, iter_sepcon_app_sepcon, sepcon_comm.
  simpl nat_seq. change (nth to (g_gen (glabel g)) null_info) with
                     (nth_gen g to) in Heqn. f_equal.
  - simpl. normalize. replace (to, n) with (new_copied_v g to) by
        (unfold new_copied_v; subst n; reflexivity). unfold vertex_rep. f_equal.
    + apply lacv_vertex_address_new. assumption.
    + apply lacv_make_header_new.
    + apply lacv_make_fields_vals_new; assumption.
  - apply iter_sepcon_func_strong. intros. destruct x as [m x].
    apply list_in_map_inv in H3. destruct H3 as [? [? ?]]. inversion H3. subst x0.
    subst m. clear H3. remember (nth_sh g to) as sh. subst n.
    rewrite nat_inc_list_In_iff in H4. unfold vertex_rep.
    assert (graph_has_v g (to, x)) by (split; simpl; assumption).
    rewrite lacv_vertex_address_old, lacv_make_header_old, lacv_make_fields_vals_old;
      [reflexivity | try assumption..].
    unfold new_copied_v. intro. inversion H5. omega.
Qed.

Lemma copied_v_derives_new_g: forall g v to,
    graph_has_gen g to -> no_dangling_dst g -> copy_compatible g -> graph_has_v g v ->
    vertex_at (nth_sh g to) (vertex_address g (new_copied_v g to))
              (make_header g v) (make_fields_vals g v) *
    graph_rep g = graph_rep (lgraph_add_copied_v g v to).
Proof.
  intros. unfold graph_rep. unfold lgraph_add_copied_v at 1. simpl. red in H.
  rewrite cvmgil_length by assumption. remember (length (g_gen (glabel g))).
  assert (n = to + (n - to))%nat by omega. assert (0 < n - to)%nat by omega.
  remember (n - to)%nat as m. rewrite H3, nat_inc_list_app, !iter_sepcon_app_sepcon.
  rewrite (lacv_icgr_not_eq (nat_inc_list to) g v to); try assumption.
  3: subst n; apply H. 2: intro; rewrite nat_inc_list_In_iff in H5; omega.
  rewrite sepcon_comm, sepcon_assoc. f_equal. assert (m = 1 + (m - 1))%nat by omega.
  rewrite H5, nat_seq_app, !iter_sepcon_app_sepcon.
  assert (nat_seq to 1 = [to]) by reflexivity. rewrite H6. clear H6.
  rewrite (lacv_icgr_not_eq (nat_seq (to + 1) (m - 1)) g v to); try assumption.
  3: subst n; apply H. 2: intro; rewrite nat_seq_In_iff in H6; omega.
  rewrite sepcon_assoc, sepcon_comm, sepcon_assoc, sepcon_comm. f_equal.
  simpl iter_sepcon. normalize. clear m Heqm H3 H4 H5. subst n.
  rewrite <- lacv_generation_rep_eq; [reflexivity | assumption..].
Qed.

Lemma data_at_tarray_split_1:
  forall sh p (tt: type) (v: reptype tt) (l: list (reptype tt)),
    complete_legal_cosu_type tt = true ->
    data_at sh (tarray tt (Zlength l + 1)) (v :: l) p =
    data_at sh tt v p *
    data_at sh (tarray tt (Zlength l)) l (offset_val (sizeof tt) p).
Proof.
  intros.
  rewrite (data_at_tarray_split sh (Zlength l + 1) 1 p tt (v :: l) (v :: l) [v] l).
  - replace (sizeof tt * 1)%Z with (sizeof tt) by omega.
    replace (Zlength l + 1 - 1) with (Zlength l) by omega. f_equal.
    rewrite (data_at_singleton_array_eq _ tt v); reflexivity.
  - rep_omega.
  - rewrite Zlength_cons. omega.
  - autorewrite with sublist; reflexivity.
  - simpl. vm_compute. reflexivity.
  - simpl. rewrite sublist_1_cons.
    replace (Zlength l + 1 - 1) with (Zlength l) by omega.
    autorewrite with sublist. reflexivity.
  - assumption.
Qed.

Lemma data_at_tarray_value_split_1: forall sh p (l: list val),
    0 < Zlength l ->
    data_at sh (tarray int_or_ptr_type (Zlength l)) l p =
    data_at sh int_or_ptr_type (hd nullval l) p *
    data_at sh (tarray int_or_ptr_type (Zlength l-1)) (tl l) (offset_val WORD_SIZE p).
Proof.
  intros. destruct l. 1: rewrite Zlength_nil in H; omega. clear H. simpl hd.
  simpl tl. rewrite Zlength_cons.
  replace (Z.succ (Zlength l)) with (Zlength l + 1) by omega.
  replace (Zlength l + 1 - 1) with (Zlength l) by omega.
  eapply data_at_tarray_split_1; eauto.
Qed.

Lemma data_at_tarray_tuint_split_1: forall sh p (l: list val),
    0 < Zlength l ->
    data_at sh (tarray tuint (Zlength l)) l p =
    data_at sh tuint (hd nullval l) p *
    data_at sh (tarray tuint (Zlength l-1)) (tl l) (offset_val WORD_SIZE p).
Proof.
  intros. destruct l. 1: rewrite Zlength_nil in H; omega. clear H. simpl hd.
  simpl tl. rewrite Zlength_cons.
  replace (Z.succ (Zlength l)) with (Zlength l + 1) by omega.
  replace (Zlength l + 1 - 1) with (Zlength l) by omega.
  eapply data_at_tarray_split_1; eauto.
Qed.

Lemma lmc_vertex_rep_eq: forall sh g v new_v,
    vertex_rep sh (lgraph_mark_copied g v new_v) v =
    data_at sh tuint (Vint (Int.repr 0))
            (offset_val (- WORD_SIZE) (vertex_address g v)) *
    data_at sh int_or_ptr_type (vertex_address g new_v)
            (vertex_address g v) *
    data_at sh (tarray int_or_ptr_type (Zlength (make_fields_vals g v) - 1))
            (tl (make_fields_vals g v)) (offset_val WORD_SIZE (vertex_address g v)).
Proof.
  intros. unfold vertex_rep. rewrite lmc_vertex_address. unfold vertex_at.
  rewrite sepcon_assoc. f_equal.
  - f_equal. unfold make_header. simpl vlabel at 1.
    unfold update_copied_old_vlabel, graph_gen.update_vlabel.
    rewrite if_true by reflexivity. simpl. unfold Z2val. reflexivity.
  - rewrite lmc_make_fields_vals_eq, data_at_tarray_value_split_1.
    + simpl hd. f_equal. simpl tl.
      replace (Zlength (vertex_address g new_v :: tl (make_fields_vals g v)) - 1)
        with (Zlength (make_fields_vals g v) - 1). 1: reflexivity.
      transitivity (Zlength (tl (make_fields_vals g v))).
      2: rewrite Zlength_cons; rep_omega.
      assert (0 < Zlength (make_fields_vals g v)) by
          (rewrite fields_eq_length; apply (proj1 (raw_fields_range (vlabel g v)))).
      remember (make_fields_vals g v). destruct l.
      1: rewrite Zlength_nil in H; omega. rewrite Zlength_cons. simpl. omega.
    + rewrite Zlength_cons. rep_omega.
Qed.

Lemma lmc_vertex_rep_not_eq: forall sh g v new_v x,
    x <> v -> vertex_rep sh (lgraph_mark_copied g v new_v) x = vertex_rep sh g x.
Proof.
  intros. unfold vertex_rep. rewrite lmc_vertex_address, lmc_make_fields_vals_not_eq.
  2: assumption. f_equal. unfold make_header. rewrite lmc_vlabel_not_eq by assumption.
  reflexivity.
Qed.

Lemma lmc_generation_rep_not_eq: forall (g : LGraph) (v new_v : VType) (x : nat),
    x <> vgeneration v ->
    generation_rep g x = generation_rep (lgraph_mark_copied g v new_v) x.
Proof.
  intros. unfold generation_rep. unfold nth_sh, nth_gen. simpl.
  remember (nat_inc_list (number_of_vertices (nth x (g_gen (glabel g)) null_info))).
  apply iter_sepcon_func_strong. intros. destruct x0 as [n m].
  apply list_in_map_inv in H0. destruct H0 as [x0 [? ?]]. inversion H0. subst n x0.
  clear H0. remember (generation_sh (nth x (g_gen (glabel g)) null_info)) as sh.
  rewrite lmc_vertex_rep_not_eq. 1: reflexivity. intro. destruct v. simpl in *.
  inversion H0. subst. contradiction.
Qed.

Lemma graph_gen_lmc_ramif: forall g v new_v,
    graph_has_gen g (vgeneration v) ->
    graph_rep g |-- generation_rep g (vgeneration v) *
    (generation_rep (lgraph_mark_copied g v new_v) (vgeneration v) -*
                    graph_rep (lgraph_mark_copied g v new_v)).
Proof.
  intros. unfold graph_rep. simpl. apply iter_sepcon_ramif_pred_1.
  red in H. rewrite <- nat_inc_list_In_iff in H. apply In_Permutation_cons in H.
  destruct H as [f ?]. exists f. split. 1: assumption. intros.
  assert (NoDup (vgeneration v :: f)) by
      (apply (Permutation_NoDup H), nat_inc_list_NoDup). apply NoDup_cons_2 in H1.
  rewrite <- lmc_generation_rep_not_eq. 1: reflexivity. intro. subst. contradiction.
Qed.

Lemma gen_vertex_lmc_ramif: forall g gen index new_v,
    gen_has_index g gen index ->
    generation_rep g gen |-- vertex_rep (nth_sh g gen) g (gen, index) *
    (vertex_rep (nth_sh g gen) (lgraph_mark_copied g (gen, index) new_v)
                (gen, index) -*
                generation_rep (lgraph_mark_copied g (gen, index) new_v) gen).
Proof.
  intros. unfold generation_rep. unfold nth_gen. simpl. apply iter_sepcon_ramif_pred_1.
  change (nth gen (g_gen (glabel g)) null_info) with (nth_gen g gen).
  remember (map (fun x : nat => (gen, x))
                (nat_inc_list (number_of_vertices (nth_gen g gen)))).
  assert (In (gen, index) l) by
      (subst l; apply in_map; rewrite nat_inc_list_In_iff; assumption).
  apply In_Permutation_cons in H0. destruct H0 as [f ?]. exists f. split.
  1: assumption. intros. unfold nth_sh, nth_gen. simpl. rewrite lmc_vertex_rep_not_eq.
  1: reflexivity. assert (NoDup l). {
    subst l. apply FinFun.Injective_map_NoDup. 2: apply nat_inc_list_NoDup.
    red. intros. inversion H2. reflexivity. }
  apply (Permutation_NoDup H0), NoDup_cons_2 in H2. intro. subst. contradiction.
Qed.

Lemma graph_vertex_lmc_ramif: forall g v new_v,
    graph_has_v g v ->
    graph_rep g |-- vertex_rep (nth_sh g (vgeneration v)) g v *
    (vertex_rep (nth_sh g (vgeneration v))
                (lgraph_mark_copied g v new_v) v -*
                graph_rep (lgraph_mark_copied g v new_v)).
Proof.
  intros. destruct H. sep_apply (graph_gen_lmc_ramif g v new_v H).
  destruct v as [gen index]. simpl vgeneration in *. simpl vindex in *.
  sep_apply (gen_vertex_lmc_ramif g gen index new_v H0). cancel. apply wand_frame_ver.
Qed.

Lemma lgd_vertex_rep_eq_in_diff_vert: forall sh g v' v v1 e n,
    0 <= n < Zlength (make_fields g v) ->
    Znth n (make_fields g v) = inr e ->
    v1 <> v ->
    vertex_rep sh g v1 = vertex_rep sh (labeledgraph_gen_dst g e v') v1.
Proof.
  intros. unfold vertex_rep.
  rewrite lgd_vertex_address_eq, <- lgd_make_header_eq.
  f_equal. unfold make_fields_vals.
  rewrite <- lgd_raw_mark_eq.
  simple_if_tac; [f_equal |];
    rewrite (lgd_map_f2v_diff_vert_eq g v v' v1 e n);
    try reflexivity; assumption.
Qed.

Lemma lgd_gen_rep_eq_in_diff_gen: forall (g : LGraph) (v v' : VType) (x : nat) e n,
    0 <= n < Zlength (make_fields g v) ->
    Znth n (make_fields g v) = inr e ->
    x <> vgeneration v ->
     generation_rep g x = generation_rep (labeledgraph_gen_dst g e v') x.
Proof.
  intros. unfold generation_rep.
  unfold nth_sh, nth_gen. simpl.
  remember (nat_inc_list (number_of_vertices
                            (nth x (g_gen (glabel g)) null_info))).
  apply iter_sepcon_func_strong. intros v1 H2.
  apply list_in_map_inv in H2.
  destruct H2 as [x1 [? ?]].
  remember (generation_sh (nth x (g_gen (glabel g)) null_info)) as sh.
  assert (v1 <> v). {
    intro. unfold vgeneration in H1.
    rewrite H4 in H2. rewrite H2 in H1. unfold not in H1.
    simpl in H1. omega. }
  apply (lgd_vertex_rep_eq_in_diff_vert sh g v' v v1 e n); assumption.
Qed.

Lemma graph_gen_lgd_ramif: forall g v v' e n,
    0 <= n < Zlength (make_fields g v) ->
    Znth n (make_fields g v) = inr e ->
    graph_has_gen g (vgeneration v) ->
    graph_rep g |-- generation_rep g (vgeneration v) *
    (generation_rep (labeledgraph_gen_dst g e v') (vgeneration v) -*
                    graph_rep (labeledgraph_gen_dst g e v')).
Proof.
  intros. unfold graph_rep. simpl.
  apply iter_sepcon_ramif_pred_1.
  red in H1. rewrite <- nat_inc_list_In_iff in H1.
  apply In_Permutation_cons in H1.
  destruct H1 as [f ?]. exists f. split. 1: assumption. intros.
  assert (NoDup (vgeneration v :: f)) by
      (apply (Permutation_NoDup H1), nat_inc_list_NoDup).
  apply NoDup_cons_2 in H3.
  assert (x <> vgeneration v) by
      (unfold not; intro; subst; contradiction).
  apply (lgd_gen_rep_eq_in_diff_gen g v v' x e n); assumption.
Qed.

Lemma gen_vertex_lgd_ramif: forall g gen index new_v v n e,
    gen_has_index g gen index ->
0 <= n < Zlength (make_fields g v) ->
       Znth n (make_fields g v) = inr e ->
       v = (gen, index) ->
    generation_rep g gen |-- vertex_rep (nth_sh g gen) g (gen, index) *
    (vertex_rep (nth_sh g gen) (labeledgraph_gen_dst g e new_v)
                (gen, index) -*
                generation_rep (labeledgraph_gen_dst g e new_v) gen).
Proof.
  intros. unfold generation_rep. unfold nth_gen.
  simpl. apply iter_sepcon_ramif_pred_1.
  change (nth gen (g_gen (glabel g)) null_info) with (nth_gen g gen).
  remember (map (fun x : nat => (gen, x))
                (nat_inc_list (number_of_vertices (nth_gen g gen)))).
  assert (In (gen, index) l) by
      (subst l; apply in_map; rewrite nat_inc_list_In_iff; assumption).
  apply In_Permutation_cons in H3. destruct H3 as [f ?]. exists f. split.
  1: assumption. intros. unfold nth_sh, nth_gen. simpl.
  remember (generation_sh (nth gen (g_gen (glabel g)) null_info)) as sh.
  rewrite (lgd_vertex_rep_eq_in_diff_vert sh g new_v v x e n);
    try reflexivity; try assumption.
  assert (NoDup l). {
    subst l. apply FinFun.Injective_map_NoDup. 2: apply nat_inc_list_NoDup.
    red. intros. inversion H5. reflexivity. }
  apply (Permutation_NoDup H3), NoDup_cons_2 in H5. intro.
  rewrite H2 in H6. rewrite H6 in H4. intuition.
Qed.

Lemma graph_vertex_lgd_ramif: forall g v e v' n,
    0 <= n < Zlength (make_fields g v) ->
    Znth n (make_fields g v) = inr e ->
    graph_has_v g v ->
    graph_rep g |-- vertex_rep (nth_sh g (vgeneration v)) g v *
    (vertex_rep (nth_sh g (vgeneration v))
                (labeledgraph_gen_dst g e v') v -*
                graph_rep (labeledgraph_gen_dst g e v')).
Proof.
  intros. destruct H1. sep_apply (graph_gen_lgd_ramif g v v' e n);
                         try assumption.
  destruct v as [gen index] eqn:?. simpl vgeneration in *.
  simpl vindex in *. rewrite <- Heqv0 in H, H0.
  sep_apply (gen_vertex_lgd_ramif g gen index v' v n e);
    try assumption.
  cancel. apply wand_frame_ver.
Qed.

Definition space_struct_rep (sh: share) (tinfo: thread_info) (gen: nat) :=
  data_at sh space_type (space_tri (nth_space tinfo gen)) (space_address tinfo gen).

Lemma heap_struct_rep_eq: forall sh l p,
    heap_struct_rep sh l p = data_at sh (tarray space_type 12) l p.
Proof.
  intros. unfold heap_struct_rep. apply pred_ext; rewrite data_at_isptr; Intros.
  - unfold_data_at (data_at _ heap_type _ _).
    entailer!. clear H0. rewrite field_at_data_at.
    unfold field_address. rewrite if_true by assumption. simpl.
    entailer!.
  - unfold_data_at (data_at _ heap_type _ _). entailer!. clear H0 H1. rewrite field_at_data_at.
    unfold field_address. rewrite if_true.
    + simpl. rewrite isptr_offset_val_zero by assumption. entailer!.
    + unfold field_compatible in *. simpl in *. intuition.
      * destruct p; try contradiction. clear -H2. unfold align_compatible in *.
        unfold heap_type.
        remember {|
            co_su := Struct;
            co_members := [(_spaces, tarray (Tstruct _space noattr) 12)];
            co_attr := noattr;
            co_sizeof := 144;
            co_alignof := 4;
            co_rank := 2;
            co_sizeof_pos := Zgeb0_ge0 144 eq_refl;
            co_alignof_two_p := prove_alignof_two_p 4 eq_refl;
            co_sizeof_alignof := prove_Zdivide 4 144 eq_refl |}.
        apply (align_compatible_rec_Tstruct cenv_cs _heap noattr c _); subst c.
        1: reflexivity. simpl co_members. intros. simpl in H.
        if_tac in H; inversion H. subst. clear H. inversion H0. subst z0.
        rewrite Z.add_0_r. apply H2.
      * red. simpl. left; reflexivity.
Qed.

Lemma heap_struct_rep_split_lt: forall sh l tinfo i1 i2,
    i1 < MAX_SPACES -> i2 < MAX_SPACES -> 0 <= i1 < i2 -> Zlength l = MAX_SPACES ->
    exists B,
      heap_struct_rep sh l (ti_heap_p tinfo) =
      data_at sh space_type (Znth i1 l) (space_address tinfo (Z.to_nat i1)) *
      data_at sh space_type (Znth i2 l) (space_address tinfo (Z.to_nat i2)) * B.
Proof.
  intros.
  exists (@data_at CompSpecs sh
                   (tarray space_type
                           (@Zlength (@reptype CompSpecs space_type)
                                     (@sublist (@reptype CompSpecs space_type)
                                               (i2 + 1) 12 l)))
                   (@sublist (@reptype CompSpecs space_type) (i2 + 1) 12 l)
                   (offset_val (SPACE_STRUCT_SIZE * (i2 + 1)) (ti_heap_p tinfo)) *
          @data_at CompSpecs sh (tarray space_type i1)
                   (@sublist (@reptype CompSpecs space_type) 0 i1 l)
                   (ti_heap_p tinfo) *
          @data_at CompSpecs sh (tarray space_type (i2 - i1 - 1))
                   (@sublist (@reptype CompSpecs space_type) (i1 + 1) i2 l)
                   (offset_val (SPACE_STRUCT_SIZE * (i1 + 1)) (ti_heap_p tinfo))).
  rewrite heap_struct_rep_eq. rewrite (data_at_tarray_space sh 12 i1) by rep_omega.
  rewrite (sublist_next i1 12 l) by rep_omega.
  replace (12 - i1) with (Zlength (sublist (i1 + 1) 12 l) + 1) by
      (rewrite Zlength_sublist; rep_omega).
  rewrite data_at_tarray_split_1 by reflexivity. unfold space_address.
  rewrite Z2Nat.id by omega. rewrite sepcon_comm, !sepcon_assoc. f_equal.
  rewrite offset_offset_val. rewrite Z2Nat.id by omega.
  replace (SPACE_STRUCT_SIZE * i1 + sizeof space_type) with
      (SPACE_STRUCT_SIZE * (i1 + 1))%Z by (simpl sizeof; rep_omega).
  assert (Zlength (sublist (i1 + 1) 12 l) = 11 - i1) by
      (rewrite Zlength_sublist; rep_omega). rewrite H3.
  rewrite (data_at_tarray_space sh (11 - i1) (i2 - i1 - 1)).
  3: rewrite H3; reflexivity. 2: rep_omega. rewrite !sublist_sublist by rep_omega.
  replace (0 + (i1 + 1)) with (i1 + 1) by omega.
  replace (i2 - i1 - 1 + (i1 + 1)) with i2 by omega.
  replace (11 - i1 - (i2 - i1 - 1)) with (12 - i2) by omega.
  replace (11 - i1 + (i1 + 1)) with 12 by omega.
  rewrite offset_offset_val, <- Z.mul_add_distr_l.
  replace (i1 + 1 + (i2 - i1 - 1)) with i2 by omega.
  rewrite (sublist_next i2 12 l) by rep_omega.
  replace (12 - i2) with (Zlength (sublist (i2 + 1) 12 l) + 1) by
      (rewrite Zlength_sublist; rep_omega).
  rewrite data_at_tarray_split_1 by reflexivity.
  rewrite sepcon_assoc, sepcon_comm, !sepcon_assoc. f_equal.
  rewrite <- !sepcon_assoc. rewrite offset_offset_val. simpl sizeof.
  replace (SPACE_STRUCT_SIZE * i2 + 12) with (SPACE_STRUCT_SIZE * (i2 + 1))%Z by
      rep_omega. reflexivity.
Qed.

Lemma heap_struct_rep_split: forall sh l tinfo i1 i2,
    0 <= i1 < MAX_SPACES -> 0 <= i2 < MAX_SPACES ->
    i1 <> i2 -> Zlength l = MAX_SPACES -> exists B,
        heap_struct_rep sh l (ti_heap_p tinfo) =
        data_at sh space_type (Znth i1 l) (space_address tinfo (Z.to_nat i1)) *
        data_at sh space_type (Znth i2 l) (space_address tinfo (Z.to_nat i2)) * B.
Proof.
  intros. destruct H, H0. destruct (Z_dec i1 i2) as [[? | ?] | ?]. 3: contradiction.
  - destruct (heap_struct_rep_split_lt sh l tinfo i1 i2) as [B ?]; try rep_omega.
    exists B. assumption.
  - destruct (heap_struct_rep_split_lt sh l tinfo i2 i1) as [B ?]; try rep_omega.
    exists B. rewrite H5. f_equal. rewrite sepcon_comm. reflexivity.
Qed.

Lemma thread_info_rep_ramif_stable: forall sh tinfo ti gen1 gen2,
    gen1 <> gen2 -> Z.of_nat gen1 < MAX_SPACES -> Z.of_nat gen2 < MAX_SPACES ->
    thread_info_rep sh tinfo ti |--
                         (space_struct_rep sh tinfo gen1 *
                          space_struct_rep sh tinfo gen2) *
    ((space_struct_rep sh tinfo gen1 * space_struct_rep sh tinfo gen2)
       -* thread_info_rep sh tinfo ti).
Proof.
  intros. unfold thread_info_rep.
  remember (@data_at
              CompSpecs sh thread_info_type
              (@pair val (prod val (prod val (list val))) Vundef
                     (@pair val (prod val (list val)) Vundef
                            (@pair val (list val)
                                   (ti_heap_p tinfo) (ti_args tinfo)))) ti) as P.
  remember (heap_rest_rep (ti_heap tinfo)) as Q.
  rewrite (sepcon_comm P), sepcon_assoc. remember (P * Q) as R.
  clear P HeqP Q HeqQ HeqR. remember (map space_tri (spaces (ti_heap tinfo))).
  assert (0 <= Z.of_nat gen1 < MAX_SPACES) by rep_omega.
  assert (0 <= Z.of_nat gen2 < MAX_SPACES) by rep_omega.
  assert (Z.of_nat gen1 <> Z.of_nat gen2) by omega.
  assert (Zlength l = MAX_SPACES) by (subst; rewrite Zlength_map; apply spaces_size).
  destruct (heap_struct_rep_split sh l tinfo _ _ H2 H3 H4 H5) as [B ?].
  rewrite H6, !Nat2Z.id.
  assert (forall i, 0 <= Z.of_nat i < MAX_SPACES ->
                    data_at sh space_type (Znth (Z.of_nat i) l)
                            (space_address tinfo i) = space_struct_rep sh tinfo i). {
    intros. unfold space_struct_rep. subst l. rewrite Zlength_map in H5.
    rewrite nth_space_Znth, Znth_map by rep_omega. reflexivity. }
  rewrite !H7 by rep_omega. rewrite (sepcon_assoc _ B R).
  cancel. apply wand_frame_intro.
Qed.

Lemma hsr_single_explicit: forall sh l tinfo i,
    0 <= i < MAX_SPACES -> Zlength l = MAX_SPACES ->
      heap_struct_rep sh l (ti_heap_p tinfo) =
      data_at sh space_type (Znth i l) (space_address tinfo (Z.to_nat i)) *
      (@data_at
         CompSpecs sh
         (tarray space_type
                 (@Zlength (@reptype CompSpecs space_type)
                           (@sublist (@reptype CompSpecs space_type) (i + 1) 12 l)))
         (@sublist (@reptype CompSpecs space_type) (i + 1) 12 l)
         (offset_val (@sizeof (@cenv_cs CompSpecs) space_type)
                     (offset_val (SPACE_STRUCT_SIZE * i) (ti_heap_p tinfo))) *
       @data_at CompSpecs sh (tarray space_type i)
                (@sublist (@reptype CompSpecs space_type) 0 i l) (ti_heap_p tinfo)).
Proof.
  intros. rewrite heap_struct_rep_eq.
  rewrite (data_at_tarray_space sh 12 i) by rep_omega.
  rewrite (sublist_next i 12 l) by rep_omega.
  replace (12 - i) with (Zlength (sublist (i + 1) 12 l) + 1) by
      (rewrite Zlength_sublist; rep_omega).
  rewrite data_at_tarray_split_1 by reflexivity. unfold space_address.
  rewrite Z2Nat.id by omega. rewrite sepcon_comm, !sepcon_assoc. reflexivity.
Qed.

Lemma heap_struct_rep_split_single: forall sh l tinfo i,
    0 <= i < MAX_SPACES -> Zlength l = MAX_SPACES ->
    exists B,
      heap_struct_rep sh l (ti_heap_p tinfo) =
      data_at sh space_type (Znth i l) (space_address tinfo (Z.to_nat i)) * B.
Proof.
  intros.
  exists (@data_at
            CompSpecs sh
            (tarray space_type
                    (@Zlength (@reptype CompSpecs space_type)
                              (@sublist (@reptype CompSpecs space_type) (i + 1) 12 l)))
            (@sublist (@reptype CompSpecs space_type) (i + 1) 12 l)
            (offset_val (@sizeof (@cenv_cs CompSpecs) space_type)
                        (offset_val (SPACE_STRUCT_SIZE * i) (ti_heap_p tinfo))) *
          @data_at CompSpecs sh (tarray space_type i)
                   (@sublist (@reptype CompSpecs space_type) 0 i l) (ti_heap_p tinfo)).
  erewrite hsr_single_explicit; eauto.
Qed.

Lemma thread_info_rep_ramif_stable_1: forall sh tinfo ti gen,
    Z.of_nat gen < MAX_SPACES ->
    thread_info_rep sh tinfo ti |--
                    space_struct_rep sh tinfo gen *
    (space_struct_rep sh tinfo gen -* thread_info_rep sh tinfo ti).
Proof.
  intros. unfold thread_info_rep.
  remember (@data_at
              CompSpecs sh thread_info_type
              (@pair val (prod val (prod val (list val))) Vundef
                     (@pair val (prod val (list val)) Vundef
                            (@pair val (list val)
                                   (ti_heap_p tinfo) (ti_args tinfo)))) ti) as P.
  remember (heap_rest_rep (ti_heap tinfo)) as Q.
  rewrite (sepcon_comm P), sepcon_assoc. remember (P * Q) as R.
  clear P HeqP Q HeqQ HeqR. remember (map space_tri (spaces (ti_heap tinfo))).
  assert (Zlength l = MAX_SPACES) by (subst; rewrite Zlength_map; apply spaces_size).
  destruct (heap_struct_rep_split_single sh l tinfo (Z.of_nat gen))
    as [B ?]; try rep_omega; try assumption. rewrite H1, !Nat2Z.id. clear H1.
  assert (data_at sh space_type
                  (@Znth _ (@Inhabitant_reptype CompSpecs space_type)
                         (Z.of_nat gen) l) (space_address tinfo gen) =
          space_struct_rep sh tinfo gen). {
    intros. unfold space_struct_rep. subst l. rewrite Zlength_map in H0.
    rewrite Znth_map by rep_omega. rewrite nth_space_Znth. reflexivity. } rewrite !H1.
  rewrite (sepcon_assoc _ B R). cancel. apply wand_frame_intro.
Qed.

Lemma vertex_rep_reset: forall g i j x sh,
    vertex_rep sh (reset_graph j g) (i, x) = vertex_rep sh g (i, x).
Proof.
  intros. unfold vertex_rep.
  rewrite vertex_address_reset, make_header_reset, make_fields_reset. reflexivity.
Qed.

Lemma generation_rep_reset_diff: forall (g: LGraph) i j,
    i <> j -> generation_rep (reset_graph j g) i = generation_rep g i.
Proof.
  intros. unfold generation_rep. rewrite <- !iter_sepcon_map.
  rewrite reset_nth_gen_diff, reset_nth_sh_diff by assumption.
  apply iter_sepcon_func; intros. apply vertex_rep_reset.
Qed.

Lemma generation_rep_reset_same: forall (g: LGraph) i,
    graph_has_gen g i -> generation_rep (reset_graph i g) i = emp.
Proof.
  intros. unfold generation_rep. rewrite <- !iter_sepcon_map.
  unfold nth_gen, reset_graph at 1. simpl.
  rewrite reset_nth_gen_info_same. simpl. reflexivity.
Qed.

Lemma graph_rep_reset: forall (g: LGraph) (gen: nat),
    graph_has_gen g gen ->
    graph_rep g = graph_rep (reset_graph gen g) * generation_rep g gen.
Proof.
  intros. unfold graph_rep. simpl.
  rewrite reset_nth_gen_info_length, remove_ve_glabel_unchanged.
  remember (length (g_gen (glabel g))). pose proof H as HS. red in H.
  rewrite <- Heqn in H. destruct (nat_inc_list_Permutation_cons _ _ H) as [l ?].
  rewrite !(iter_sepcon_permutation _ H0). simpl.
  assert (iter_sepcon l (generation_rep (reset_graph gen g)) =
          iter_sepcon l (generation_rep g)). {
    apply iter_sepcon_func_strong. intros. rewrite generation_rep_reset_diff.
    1: reflexivity. pose proof (nat_inc_list_NoDup n).
    apply (Permutation_NoDup H0) in H2. apply NoDup_cons_2 in H2.
    intro. subst. contradiction. } rewrite H1. clear H1.
  rewrite generation_rep_reset_same by assumption.
  rewrite emp_sepcon, sepcon_comm. reflexivity.
Qed.

Lemma heap_rest_rep_reset: forall (g: LGraph) t_info gen,
    graph_thread_info_compatible g t_info -> graph_has_gen g gen ->
    heap_rest_rep (ti_heap t_info) *
    generation_rep g gen |-- heap_rest_rep
                   (ti_heap (reset_nth_heap_thread_info gen t_info)).
Proof.
  intros. unfold heap_rest_rep. simpl.
  assert (gen < length (spaces (ti_heap t_info)))%nat by
      (red in H0; destruct H as [_ [_ ?]]; omega).
  destruct (reset_nth_space_Permutation _ _ H1) as [l [? ?]].
  rewrite (iter_sepcon_permutation _ H3). rewrite (iter_sepcon_permutation _ H2).
  simpl. cancel. destruct (gt_gs_compatible _ _ H _ H0) as [? [? ?]].
  fold (nth_space t_info gen). unfold space_rest_rep. unfold reset_space at 1.
  assert (isptr (space_start (nth_space t_info gen))) by
      (rewrite <- H4; apply start_isptr).
  assert (space_start (nth_space t_info gen) <> nullval). {
    destruct (space_start (nth_space t_info gen)); try contradiction.
    intro; inversion H8. } simpl space_start. rewrite !if_false by assumption.
  sep_apply (generation_rep_data_at_ g gen H0). unfold graph_gen_size. rewrite H6.
  unfold gen_start. rewrite if_true by assumption. rewrite H4. unfold nth_sh.
  rewrite H5. simpl. remember (nth_space t_info gen).
  replace (WORD_SIZE * 0)%Z with 0 by omega.
  rewrite isptr_offset_val_zero by assumption.
  replace (total_space s - 0) with (total_space s) by omega.
  rewrite <- data_at__tarray_value by apply space_order. cancel.
Qed.

Definition space_token_rep (sp: space): mpred :=
  if Val.eq (space_start sp) nullval then emp
  else malloc_token Ews (tarray int_or_ptr_type (total_space sp)) (space_start sp).

Definition ti_token_rep (ti: thread_info): mpred :=
  malloc_token Ews heap_type (ti_heap_p ti) *
  iter_sepcon (spaces (ti_heap ti)) space_token_rep.

Lemma ti_rel_token_the_same: forall (t1 t2: thread_info),
    thread_info_relation t1 t2 -> ti_token_rep t1 = ti_token_rep t2.
Proof.
  intros. destruct H as [? [? ?]]. unfold ti_token_rep. rewrite H. f_equal.
  apply (iter_sepcon_pointwise_eq _ _ _ _ null_space null_space).
  - rewrite <- !ZtoNat_Zlength, !spaces_size. reflexivity.
  - intros. fold (nth_space t1 i). fold (nth_space t2 i). unfold gen_size in H0.
    unfold space_token_rep. rewrite H0, H1. reflexivity.
Qed.

Lemma ti_token_rep_add: forall ti sp i (Hs: 0 <= i < MAX_SPACES),
    space_start (Znth i (spaces (ti_heap ti))) = nullval ->
    space_start sp <> nullval ->
    malloc_token Ews (tarray int_or_ptr_type (total_space sp)) (space_start sp) *
    ti_token_rep ti |-- ti_token_rep (ti_add_new_space ti sp i Hs).
Proof.
  intros. unfold ti_token_rep. simpl. cancel. remember (spaces (ti_heap ti)).
  rewrite <- (sublist_all (Zlength l) l) at 1 by omega. unfold upd_Znth.
  assert (Zlength l = MAX_SPACES) by (subst; rewrite spaces_size; reflexivity).
  rewrite <- (sublist_rejoin 0 i) by omega. rewrite !iter_sepcon_app_sepcon. cancel.
  rewrite (sublist_next i) by omega. simpl. cancel. subst l.
  unfold space_token_rep at 1. rewrite H. rewrite if_true by reflexivity.
  unfold space_token_rep. rewrite if_false by assumption. cancel.
Qed.

Lemma heap_struct_rep_add: forall tinfo sh sp i (Hs: 0 <= i < MAX_SPACES),
    data_at sh space_type (space_tri sp) (space_address tinfo (Z.to_nat i)) *
    (@data_at
       CompSpecs sh
       (tarray space_type
               (@Zlength (@reptype CompSpecs space_type)
                         (@sublist (@reptype CompSpecs space_type) (i + 1) 12
                                   (map space_tri (spaces (ti_heap tinfo))))))
       (@sublist (@reptype CompSpecs space_type) (i + 1) 12
                 (map space_tri (spaces (ti_heap tinfo))))
       (offset_val (@sizeof (@cenv_cs CompSpecs) space_type)
                   (offset_val (SPACE_STRUCT_SIZE * i) (ti_heap_p tinfo))) *
     @data_at CompSpecs sh (tarray space_type i)
              (@sublist (@reptype CompSpecs space_type) 0 i
                        (map space_tri (spaces (ti_heap tinfo)))) (ti_heap_p tinfo)) =
    (heap_struct_rep
       sh (map space_tri (spaces (ti_heap (ti_add_new_space tinfo sp i Hs))))
       (ti_heap_p (ti_add_new_space tinfo sp i Hs))).
Proof.
  intros. assert (Zlength (map space_tri (spaces (ti_heap tinfo))) = MAX_SPACES) by
      (rewrite Zlength_map, spaces_size; reflexivity).
  assert (Zlength (map space_tri (spaces (ti_heap (ti_add_new_space tinfo sp i Hs)))) =
          MAX_SPACES) by (rewrite Zlength_map, spaces_size; reflexivity).
  rewrite hsr_single_explicit with (i := i) by assumption. simpl.
  rewrite <- !upd_Znth_map, upd_Znth_same, ans_space_address by omega.
  rewrite sublist_upd_Znth_r; [| omega | pose proof Hs; rep_omega].
  rewrite sublist_upd_Znth_l by omega. reflexivity.
Qed.

Lemma heap_rest_rep_add: forall tinfo sp i (Hs: 0 <= i < MAX_SPACES),
    space_start (Znth i (spaces (ti_heap tinfo))) = nullval ->
    heap_rest_rep (ti_heap tinfo) * space_rest_rep sp =
    heap_rest_rep (ti_heap (ti_add_new_space tinfo sp i Hs)).
Proof.
  intros. unfold heap_rest_rep. simpl. remember (spaces (ti_heap tinfo)).
  rewrite <- (sublist_all (Zlength l) l) at 1 by omega. unfold upd_Znth.
  assert (Zlength l = MAX_SPACES) by (subst; rewrite spaces_size; reflexivity).
  rewrite <- (sublist_rejoin 0 i) by omega. rewrite !iter_sepcon_app_sepcon.
  rewrite sepcon_assoc. f_equal. rewrite (sublist_next i) by omega. simpl.
  rewrite sepcon_comm. f_equal. subst l. unfold space_rest_rep at 1.
  rewrite if_true by assumption. rewrite emp_sepcon. reflexivity.
Qed.

Lemma vertex_rep_add: forall (g : LGraph) (gi : generation_info) v sh,
    graph_has_v g v -> copy_compatible g -> no_dangling_dst g ->
    vertex_rep sh g v = vertex_rep sh (lgraph_add_new_gen g gi) v.
Proof.
  intros. unfold vertex_rep. rewrite ang_vertex_address_old; auto.
  rewrite <- ang_make_header, <- ang_make_fields_vals_old; auto.
Qed.

Lemma graph_rep_add: forall (g : LGraph) (gi : generation_info),
    number_of_vertices gi = O -> copy_compatible g -> no_dangling_dst g ->
    graph_rep g = graph_rep (lgraph_add_new_gen g gi).
Proof.
  intros. unfold graph_rep. simpl. rewrite app_length. simpl.
  rewrite Nat.add_1_r, nat_inc_list_S, iter_sepcon_app_sepcon. simpl.
  unfold generation_rep at 3. unfold nth_gen. simpl. rewrite app_nth2 by omega.
  replace (length (g_gen (glabel g)) - length (g_gen (glabel g)))%nat with O by omega.
  simpl. rewrite H. simpl. rewrite !sepcon_emp. apply iter_sepcon_func_strong. intros.
  rewrite nat_inc_list_In_iff in H2. unfold generation_rep. unfold nth_sh.
  rewrite !ang_nth_old by assumption. apply iter_sepcon_func_strong. intros v ?.
  rewrite in_map_iff in H3. destruct H3 as [idx [? ?]].
  rewrite nat_inc_list_In_iff in H4. apply vertex_rep_add; auto.
  split; subst; simpl; assumption.
Qed.
