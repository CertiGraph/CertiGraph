Require Import VST.veric.compcert_rmaps.
Require Export VST.progs.conclib.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.CertiGC.GCGraph.
Require Export RamifyCoq.CertiGC.env_graph_gc.

Definition vertex_at (sh: share) (p: val) (header: Z) (lst_fields: list val) :=
  data_at sh tint (Z2val header) (offset_val (- WORD_SIZE) p) *
  data_at sh (tarray int_or_ptr_type (Zlength lst_fields)) lst_fields p.

Definition vertex_rep (sh: share) (g: LGraph) (v: VType): mpred :=
  vertex_at sh (vertex_address g v) (make_header g v) (make_fields_vals g v).

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
  fold_right andp TT (map (valid_pointer oo GC_Pointer2val) outlier).

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
               memory_block sh (WORD_SIZE * single_vertex_size g v)
               (offset_val (- WORD_SIZE) (vertex_address g v)).
Proof.
  intros. sep_apply (vertex_rep_isptr sh g v). Intros.
  destruct v as [gen num]. unfold vertex_rep, vertex_at. simpl in H.
  rewrite vertex_head_address_eq. unfold vertex_address, vertex_offset. simpl.
  remember (gen_start g gen). destruct v; try contradiction.
  remember (previous_vertices_size g gen num).
  assert (0 <= z) by (rewrite Heqz; apply previous_size_ge_zero).
  unfold single_vertex_size. entailer. rewrite <- fields_eq_length.
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
  rewrite memory_block_split; [| rep_omega..].
  sep_apply (data_at_memory_block
               sh tint (Vint (Int.repr (make_header g (gen, num))))
               (Vptr b (Ptrofs.repr ofs))).
  simpl sizeof. rewrite WORD_SIZE_eq. apply cancel_left.
  sep_apply (data_at_memory_block
               sh (tarray int_or_ptr_type z0) (make_fields_vals g (gen, num))
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
    graph_has_gen g gen ->
    generation_rep g (gen, num, sh) |--
    memory_block sh (WORD_SIZE * (previous_vertices_size g gen num)) (gen_start g gen).
Proof.
  intros. apply graph_has_gen_start_isptr in H.
  remember (gen_start g gen). destruct v; try contradiction. induction num.
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
    graph_has_gen g gen ->
    generation_rep g (gen, num, sh) |--
    !! (align_compatible (tarray int_or_ptr_type (previous_vertices_size g gen num))
                         (gen_start g gen)).
Proof.
  intros. apply graph_has_gen_start_isptr in H.
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
    graph_has_gen g gen ->
    generation_rep g (gen, num, sh) |--
    !! (field_compatible (tarray int_or_ptr_type (previous_vertices_size g gen num))
                         [] (gen_start g gen)).
Proof.
  intros. pose proof H. apply graph_has_gen_start_isptr in H.
  remember (gen_start g gen). destruct v; try contradiction.
  unfold field_compatible. entailer. unfold size_compatible.
  rewrite sizeof_tarray_int_or_ptr by apply previous_size_ge_zero.
  sep_apply (generation_rep_ptrofs sh g gen num b i Heqv). entailer. rewrite Heqv.
  sep_apply (generation_rep_align_compatible sh g gen num H0). entailer!.
Qed.

Lemma generation_rep_data_at_: forall sh g gen num,
    graph_has_gen g gen ->
    generation_rep g (gen, num, sh) |--
    data_at_ sh (tarray int_or_ptr_type (previous_vertices_size g gen num))
             (gen_start g gen).
Proof.
  intros. sep_apply (generation_rep_field_compatible sh g gen num H). Intros.
  sep_apply (generation_rep_memory_block sh g gen num H).
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
  - unfold default_val. simpl. autorewrite with sublist. reflexivity. 
  - unfold default_val. simpl. autorewrite with sublist. reflexivity.
  - unfold default_val. simpl. autorewrite with sublist. reflexivity.
Qed.

Definition valid_int_or_ptr (x: val) :=
 match x with
 | Vint i => Int.testbit i 0 = true
 | Vptr b z => Ptrofs.testbit z 0 = false
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

Lemma vertex_rep_valid_int_or_ptr: forall sh g v,
    vertex_rep sh g v |-- !! (valid_int_or_ptr (vertex_address g v)).
Proof.
  intros. sep_apply (vertex_rep_isptr sh g v). Intros.
  unfold vertex_rep, vertex_at, vertex_address.
  remember (gen_start g (vgeneration v)) as vv. destruct vv; try contradiction.
  inv_int i. simpl. rewrite !ptrofs_add_repr. entailer!.
  destruct H3 as [_ [_ [_ [? _]]]]. clear -H3. hnf in H3. inv H3.
  1: simpl in H; inversion H. assert (0 <= 0 < Zlength (make_fields_vals g v)). {
    split; [omega|]. rewrite fields_eq_length.
    destruct (raw_fields_head_cons (vlabel g v)) as [r [l [? _]]]. rewrite H.
    rewrite Zlength_cons. pose proof (Zlength_nonneg l). omega.
  } apply H4 in H. rewrite Z.mul_0_r, Z.add_0_r in H. clear H4. inv H. inv H0.
  simpl in H1. rewrite Zodd_mod. apply Zdivide_mod in H1.
  remember (Ptrofs.unsigned (Ptrofs.repr (ofs + WORD_SIZE * vertex_offset g v))).
  clear Heqz. rewrite Zmod_divides in H1 by omega. destruct H1.
  replace (4 * x)%Z with (2 * x * 2)%Z in H by omega. subst. rewrite Z_mod_mult.
  unfold Zeq_bool. simpl. reflexivity.
Qed.

Lemma graph_rep_generation_rep: forall g gen,
    graph_has_gen g gen ->
    graph_rep g |-- generation_rep g (gen, (nth_gen g gen).(number_of_vertices),
                                      (nth_gen g gen).(generation_sh)) * TT.
Proof.
  intros. unfold graph_rep. hnf in H. remember (g_gen (glabel g)).
  rewrite map_length. remember (nat_inc_list (length l)).
  remember (map number_of_vertices l). remember (map generation_sh l).
  assert (length l0 = length l1) by
      (subst; rewrite nat_inc_list_length, map_length; reflexivity).
  assert (length (combine l0 l1) = length l) by
      (subst; rewrite combine_length, H0, Nat.min_id, map_length; reflexivity).
  assert (length (combine l0 l1) = length l2) by
      (subst; rewrite combine_length, H0, Nat.min_id, !map_length; reflexivity).
  assert (length (combine (combine l0 l1) l2) = length l). {
    rewrite combine_length, H1. subst l2. rewrite map_length, Nat.min_id. reflexivity.
  } apply (combine_nth _ _ gen (O, O) Tsh) in H2.
  apply (combine_nth _ _ gen O O) in H0. rewrite H0 in H2. clear H0.
  assert (In (nth gen (combine (combine l0 l1) l2) (0%nat, 0%nat, Tsh))
             (combine (combine l0 l1) l2)) by (apply nth_In; rewrite H3; omega).
  sep_apply (iter_sepcon_in_true (generation_rep g) _ _ H0). rewrite H2. subst.
  clear -H. unfold nth_gen. rewrite nat_inc_list_nth by omega.
  change O with (number_of_vertices null_info).
  change Tsh with (generation_sh null_info). rewrite !map_nth. cancel.
Qed.

Lemma generation_rep_vertex_rep: forall g gen index num sh,
    (index < num)%nat ->
    generation_rep g (gen, num, sh) |-- vertex_rep sh g (gen, index) * TT.
Proof.
  intros. unfold generation_rep.
  assert (nth index (map (fun x : nat => (gen, x)) (nat_inc_list num))
              (gen, O) = (gen, index)). {
    change (gen, O) with ((fun x: nat => (gen, x)) O). rewrite map_nth.
    rewrite nat_inc_list_nth by omega. reflexivity.
  } assert (In (gen, index) (map (fun x : nat => (gen, x)) (nat_inc_list num))). {
    rewrite <- H0. apply nth_In. rewrite map_length, nat_inc_list_length. assumption.
  } apply (iter_sepcon_in_true (vertex_rep sh g) _ _ H1).
Qed.

Lemma graph_rep_vertex_rep: forall g v,
    graph_has_v g v -> graph_rep g |-- EX sh: share, vertex_rep sh g v * TT.
Proof.
  intros. destruct H. sep_apply (graph_rep_generation_rep g (vgeneration v) H).
  unfold gen_has_index in H0. remember (generation_sh (nth_gen g (vgeneration v))).
  sep_apply (generation_rep_vertex_rep g (vgeneration v) _ _ s H0).
  Exists s. destruct v. simpl. cancel.
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

Lemma heap_rest_rep_data_at_: forall (g: LGraph) (t_info: thread_info) gen n1,
    graph_has_gen g gen ->
    graph_thread_info_compatible g t_info ->
    n1 = previous_vertices_size g gen (number_of_vertices (nth_gen g gen)) ->
    0 <= n1 <= total_space (nth_space t_info gen) /\
    heap_rest_rep (ti_heap t_info) |--
                  data_at_ (generation_sh (nth_gen g gen))
                  (tarray int_or_ptr_type (total_space (nth_space t_info gen) - n1))
                  (offset_val (WORD_SIZE * n1) (gen_start g gen)) * TT.
Proof.
  intros. subst n1. destruct H0 as [? [? ?]]. unfold graph_has_gen in H.
  rewrite Forall_forall in H0. remember (g_gen (glabel g)).
  remember (nat_inc_list (length l)). remember (spaces (ti_heap t_info)).
  assert (length (combine l0 l) = length l) by
      (subst; rewrite combine_length, nat_inc_list_length, Nat.min_id; reflexivity).
  assert (length (combine (combine l0 l) l1) = length l) by
      (rewrite combine_length, H3, min_l by assumption; reflexivity).
  assert (generation_space_compatible
            g (nth gen (combine (combine l0 l) l1) (O, null_info, null_space))) by
      (apply H0, nth_In; rewrite H4; assumption).
  rewrite combine_nth_lt in H5; [|rewrite H3; omega | omega].
  rewrite combine_nth in H5 by (subst l0; rewrite nat_inc_list_length; reflexivity).
  rewrite Heql0 in H5. rewrite nat_inc_list_nth in H5 by assumption.
  unfold heap_rest_rep. rewrite <- Heql1. assert (In (nth gen l1 null_space) l1). {
    apply nth_In, Nat.lt_le_trans with (length l); assumption.
  } rewrite Heql in H5.
  change (nth gen (g_gen (glabel g)) null_info) with (nth_gen g gen) in H5.
  subst l1. change (nth gen (spaces (ti_heap t_info)) null_space) with
                (nth_space t_info gen) in *. destruct H5 as [? [? ?]]. split.
  - rewrite H8. apply space_order.
  - sep_apply (iter_sepcon_in_true space_rest_rep _ (nth_space t_info gen) H6).
    unfold space_rest_rep. rewrite <- H5. if_tac.
    + pose proof (start_isptr (nth_gen g gen)). rewrite H9 in H10. inversion H10.
    + rewrite <- H7, <- H8.
      replace (start_address (nth_gen g gen)) with (gen_start g gen).
      * cancel.
      * unfold gen_start. if_tac. reflexivity. unfold graph_has_gen in H10.
        subst l; exfalso; omega.
Qed.

Lemma graph_and_heap_rest_memory_block: forall (g: LGraph) (t_info: thread_info) gen,
    graph_has_gen g gen ->
    graph_thread_info_compatible g t_info ->
    graph_rep g * heap_rest_rep
                    (ti_heap t_info) |--
                    memory_block (generation_sh (nth_gen g gen))
                    (WORD_SIZE * gen_size t_info gen) (gen_start g gen) * TT.
Proof.
  intros. sep_apply (graph_rep_generation_rep g gen H).
  remember (previous_vertices_size g gen (number_of_vertices (nth_gen g gen))) as n1.
  destruct (heap_rest_rep_data_at_ g t_info gen n1 H H0 Heqn1). sep_apply H2. clear H2.
  remember (number_of_vertices (nth_gen g gen)) as num.
  remember (generation_sh (nth_gen g gen)) as sh.
  sep_apply (generation_rep_data_at_ sh g gen num H). rewrite <- Heqn1.
  remember (total_space (nth_space t_info gen)) as n.
  sep_apply (data_at__tarray_value_join sh n n1 (gen_start g gen) H1).
    sep_apply (data_at__memory_block_cancel
                 sh (tarray int_or_ptr_type n) (gen_start g gen)).
  rewrite sizeof_tarray_int_or_ptr by omega. subst n. unfold gen_size. cancel.
Qed.

Lemma outlier_rep_valid_pointer: forall (roots: roots_t) outlier p,
    In (inl (inr p)) roots ->
    incl (filter_sum_right (filter_sum_left roots)) outlier ->
    outlier_rep outlier |-- valid_pointer (GC_Pointer2val p) * TT.
Proof.
  intros. assert (In p outlier). {
    apply H0. rewrite <- filter_sum_right_In_iff, <- filter_sum_left_In_iff.
    assumption. } unfold outlier_rep.
  apply (in_map (valid_pointer oo GC_Pointer2val)) in H1. apply fold_right_andp in H1.
  destruct H1 as [Q ?]. rewrite H1. simpl. apply andp_left1.
  rewrite <- (sepcon_emp (valid_pointer (GC_Pointer2val p))) at 1. cancel.
Qed.
