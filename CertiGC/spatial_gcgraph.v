Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.CertiGC.GCGraph.
Require Export RamifyCoq.CertiGC.env_graph_gc.

Definition vertex_at (sh: share) (p: val) (header: Z) (lst_fields: list val) :=
  data_at sh tint (Z2val header) (offset_val (- WORD_SIZE) p) *
  data_at sh (tarray int_or_ptr_type (Zlength lst_fields)) lst_fields p.

Definition vertex_rep (sh: share) (g: LGraph) (v: VType): mpred :=
  vertex_at sh (vertex_address g v) (make_header g v) (make_fields g v).

Definition generation_rep (g: LGraph) (gen_num_sh_triple: nat * nat * share): mpred :=
  match gen_num_sh_triple with
  | (gen, num, sh) =>
    iter_sepcon (map (fun x => (gen, x)) (nat_inc_list num)) (vertex_rep sh g)
  end.

Definition graph_rep (g: LGraph): mpred :=
  let up := map number_of_vertices g.(glabel).(g_gen) in
  let shs := map generation_sh g.(glabel).(g_gen) in
  iter_sepcon (combine (combine (nat_inc_list (length up)) up) shs) (generation_rep g).

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

Definition thread_info_rep (sh: share) (ti: thread_info) (t: val) :=
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

Definition outlier_rep (outlier: outlier_t) :=
  fold_right andp TT (map (compose valid_pointer GC_Pointer2val) outlier).

Lemma vertex_head_address_eq: forall g gen num,
  offset_val (- WORD_SIZE) (vertex_address g (gen, num)) =
  offset_val (WORD_SIZE * (previous_vertices_size g gen num)) (gen_start g gen).
Proof.
  intros. unfold vertex_address, vertex_offset. simpl. rewrite offset_offset_val.
  f_equal. rewrite Z.add_opp_r, Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_simpl_r.
Qed.

Lemma vertex_rep_memory_block: forall sh g v,
    vertex_rep sh g v |--
               memory_block sh (WORD_SIZE * single_vertex_size g v)
               (offset_val (- WORD_SIZE) (vertex_address g v)).
Proof.
  intros. destruct v as [gen num]. unfold vertex_rep, vertex_at.
  rewrite vertex_head_address_eq. unfold vertex_address, vertex_offset. simpl.
  assert (isptr (gen_start g gen)) by (apply start_isptr).
  remember (gen_start g gen). destruct v; try contradiction.
  remember (previous_vertices_size g gen num).
  assert (0 <= z) by (rewrite Heqz; apply previous_size_ge_zero).
  unfold single_vertex_size. entailer. rewrite <- fields_eq_length.
  destruct H1 as [_ [_ [? _]]]. simpl in H1.
  destruct H3 as [_ [_ [? _]]]. simpl in H3. rewrite <- H4 in H3.
  remember (previous_vertices_size g gen num).
  remember (Zlength (make_fields g (gen, num))). rewrite (Z.add_comm z0).
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
  rewrite memory_block_split; [| rep_omega..].
  sep_apply (data_at_memory_block
               sh tint (Vint (Int.repr (make_header g (gen, num))))
               (Vptr b (Ptrofs.repr ofs))).
  simpl sizeof. rewrite WORD_SIZE_eq. apply cancel_left.
  sep_apply (data_at_memory_block
               sh (tarray int_or_ptr_type z0) (make_fields g (gen, num))
               (Vptr b (Ptrofs.repr (ofs + 4)))). simpl sizeof. rewrite Z.max_r; auto.
Qed.

Lemma generation_rep_ptrofs: forall sh g gen num b i,
    Vptr b i = gen_start g gen ->
    generation_rep g (gen, num, sh) |--
                   !! (WORD_SIZE * previous_vertices_size g gen num +
                       Ptrofs.unsigned i < Ptrofs.modulus).
Proof.
  intros. induction num. 1: entailer. unfold generation_rep.
  rewrite nat_inc_list_S, map_app, iter_sepcon_app_sepcon.
  assert_PROP (WORD_SIZE * previous_vertices_size g gen num +
               Ptrofs.unsigned i < Ptrofs.modulus) by
      (unfold generation_rep in IHnum; sep_apply IHnum; entailer!). clear IHnum.
  simpl iter_sepcon. entailer. unfold vertex_rep at 2. unfold vertex_at.
  rewrite vertex_head_address_eq. unfold vertex_address, vertex_offset. simpl.
  rewrite <- H. inv_int i. entailer. destruct H1 as [_ [_ [? _]]]. simpl in H1.
  destruct H4 as [_ [_ [? _]]]. simpl in H4. rewrite <- H5 in H4. clear H3 H6 H5.
  rewrite ptrofs_add_repr in *. apply prop_right.
  pose proof (previous_size_ge_zero g gen num).
  rewrite Ptrofs.unsigned_repr_eq in H1. rewrite Z.mod_small in H1 by rep_omega.
  unfold single_vertex_size. rewrite <- fields_eq_length. rewrite WORD_SIZE_eq in *.
  rewrite Z.mul_add_distr_l, Z.mul_1_r, Z.add_assoc in H4.
  rewrite Ptrofs.unsigned_repr_eq in H4. rewrite Z.mod_small in H4 by rep_omega.
  rep_omega.
Qed.

Lemma generation_rep_memory_block: forall sh g gen num,
    generation_rep g (gen, num, sh) |--
    memory_block sh (WORD_SIZE * (previous_vertices_size g gen num)) (gen_start g gen).
Proof.
  intros. assert (isptr (gen_start g gen)) by (apply start_isptr).
  remember (gen_start g gen). destruct v; try contradiction.
  induction num.
  - simpl. rewrite memory_block_zero_Vptr. auto.
  - sep_apply (generation_rep_ptrofs sh g gen (S num) b i Heqv). Intros.
    rename H0 into HS. simpl in HS. unfold generation_rep.
    rewrite nat_inc_list_S, map_app, iter_sepcon_app_sepcon.
    simpl. unfold generation_rep in IHnum. sep_apply IHnum. rewrite Z.add_comm.
    rewrite <- (Ptrofs.repr_unsigned i) at 2.
    remember (previous_vertices_size g gen num) as zp.
    assert (0 <= zp) by (rewrite Heqzp; apply previous_size_ge_zero).
    pose proof (single_vertex_size_gt_zero g (gen, num)) as HS1.
    pose proof (Ptrofs.unsigned_range i) as HS2.
    rewrite Z.mul_add_distr_l, memory_block_split; [|rep_omega..].
    rewrite (Ptrofs.repr_unsigned i). apply cancel_left.
    sep_apply (vertex_rep_memory_block sh g (gen, num)).
    rewrite vertex_head_address_eq, <- Heqzp, <- Heqv. simpl offset_val.
    rewrite <- ptrofs_add_repr, Ptrofs.repr_unsigned. auto.
Qed.

Lemma generation_rep_align_compatible: forall sh g gen num,
    generation_rep g (gen, num, sh) |--
    !! (align_compatible (tarray int_or_ptr_type (previous_vertices_size g gen num))
                         (gen_start g gen)).
Proof.
  intros.  assert (isptr (gen_start g gen)) by (apply start_isptr).
  remember (gen_start g gen). destruct v; try contradiction.
  sep_apply (generation_rep_ptrofs sh g gen num b i Heqv). Intros. induction num.
  - simpl previous_vertices_size. apply prop_right. constructor. intros. omega.
  - unfold generation_rep. rewrite nat_inc_list_S, map_app, iter_sepcon_app_sepcon.
    simpl iter_sepcon. entailer. unfold vertex_rep at 2. unfold vertex_at.
    rename H0 into HS. rewrite vertex_head_address_eq. entailer!. clear H1 H2 H3 H4.
    destruct H0 as [_ [_ [_ [? _]]]]. rewrite <- Heqv in H0. inv_int i.
    hnf in H0. rewrite ptrofs_add_repr in H0. inv H0. simpl in H1. inv H1.
    simpl in H3. simpl in HS. pose proof (single_vertex_size_gt_zero g (gen, num)).
    pose proof (previous_size_ge_zero g gen num).
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

Lemma generation_rep_field_compatible: forall sh g gen num,
    generation_rep g (gen, num, sh) |--
    !! (field_compatible (tarray int_or_ptr_type (previous_vertices_size g gen num))
                         [] (gen_start g gen)).
Proof.
  intros. assert (isptr (gen_start g gen)) by (apply start_isptr).
  remember (gen_start g gen). destruct v; try contradiction.
  unfold field_compatible. entailer. unfold size_compatible.
  rewrite sizeof_tarray_int_or_ptr by apply previous_size_ge_zero.
  sep_apply (generation_rep_ptrofs sh g gen num b i Heqv). entailer. rewrite Heqv.
  sep_apply (generation_rep_align_compatible sh g gen num). entailer!.
Qed.

Lemma generation_rep_data_at_: forall sh g gen num,
    generation_rep g (gen, num, sh) |--
    data_at_ sh (tarray int_or_ptr_type (previous_vertices_size g gen num))
             (gen_start g gen).
Proof.
  intros. sep_apply (generation_rep_field_compatible sh g gen num). Intros.
  sep_apply (generation_rep_memory_block sh g gen num).
  rewrite <- sizeof_tarray_int_or_ptr by apply previous_size_ge_zero.
  rewrite memory_block_data_at_; auto.
Qed.

Lemma data_at__tarray_value_join_local_fact: forall sh n n1 p,
    0 <= n1 <= n ->
    data_at_ sh (tarray int_or_ptr_type n1) p *
    data_at_ sh (tarray int_or_ptr_type (n - n1)) (offset_val (WORD_SIZE * n1) p) |--
             !!(field_compatible (tarray int_or_ptr_type n) [] p).
Proof.
  intros. entailer!. unfold field_compatible. simpl. destruct H0 as [? [_ [? [? _]]]].
  destruct H1 as [_ [_ [? [? _]]]]. destruct p; try contradiction. clear H0.
  simpl isptr. inv_int i. unfold size_compatible in *. simpl in H1.
  rewrite sizeof_tarray_int_or_ptr in * by omega. rewrite WORD_SIZE_eq in *.
  rewrite ptrofs_add_repr in H1. do 2 rewrite Ptrofs.unsigned_repr in * by rep_omega.
  replace (Z.max 0 (n - n1)) with (n - n1) in H1 by (rewrite Z.max_r; omega).
  assert (ofs + 4 * n < Ptrofs.modulus) by omega. intuition. constructor. intros.
  simpl sizeof. rewrite Ptrofs.unsigned_repr by rep_omega.
  apply align_compatible_rec_by_value with Mptr. 1: reflexivity. simpl.
  apply Z.divide_add_r. 2: apply Z.divide_factor_l. simpl offset_val in H4.
  rewrite ptrofs_add_repr in H4. unfold align_compatible in *.
  rewrite Ptrofs.unsigned_repr in * by rep_omega.
  pose proof (align_compatible_rec_Tarray_inv _ _ _ _ _ H3).
  pose proof (align_compatible_rec_Tarray_inv _ _ _ _ _ H4). simpl sizeof in *.
  rewrite Z.le_lteq in H6. destruct H6.
  - assert (0 <= 0 < n1) by omega. specialize (H9 _ H11).
    apply (align_compatible_rec_by_value_inv _ _ Mptr) in H9. 2: reflexivity.
    simpl in H9. rewrite Z.add_0_r in H9. assumption.
  - subst n1. rewrite Z.sub_0_r in H10. specialize (H10 _ H5).
    apply (align_compatible_rec_by_value_inv _ _ Mptr) in H10. 2: reflexivity.
    simpl in H10. rewrite Z.add_0_r, Z.add_comm in H10.
    apply Z.divide_add_cancel_r in H10; [assumption | apply Z.divide_factor_l].
Qed.

Lemma data_at__tarray_value_join: forall sh n n1 p,
    0 <= n1 <= n ->
    data_at_ sh (tarray int_or_ptr_type n1) p *
    data_at_ sh (tarray int_or_ptr_type (n - n1)) (offset_val (WORD_SIZE * n1) p) |--
             data_at_ sh (tarray int_or_ptr_type n) p.
Proof.
  intros. unfold data_at_ at 3; unfold field_at_. rewrite field_at_data_at.
  erewrite (@split2_data_at_Tarray CompSpecs sh int_or_ptr_type n n1).
  - instantiate (1:= list_repeat (Z.to_nat (n-n1)) Vundef).
    instantiate (1:= list_repeat (Z.to_nat n1) Vundef). unfold field_address. simpl.
    sep_apply (data_at__tarray_value_join_local_fact sh n n1 p H). Intros.
    rewrite if_true; trivial. entailer!. unfold data_at_. unfold field_at_.
    rewrite field_at_data_at. unfold field_address0. rewrite if_true.
    + simpl. unfold field_address. rewrite if_true; trivial. simpl.
      rewrite offset_offset_val. entailer!.
    + unfold field_compatible0. simpl. destruct H0. intuition.
  - assumption.
  - instantiate (1:=list_repeat (Z.to_nat n) Vundef). list_solve.
  - unfold default_val. simpl. autorewrite with sublist. apply JMeq_refl.
  - unfold default_val. simpl. autorewrite with sublist. apply JMeq_refl.
  - unfold default_val. simpl. autorewrite with sublist. apply JMeq_refl.
Qed.
