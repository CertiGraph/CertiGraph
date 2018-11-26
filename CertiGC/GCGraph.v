Require Import Coq.ZArith.ZArith.
Require Export Coq.Program.Basics.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import VST.veric.base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.val_lemmas.
Require Import VST.veric.shares.
Require Import VST.msl.seplog.
Require Import VST.msl.shares.
Require Import VST.floyd.sublist.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.functional_base.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Export RamifyCoq.graph.graph_gen.
Import ListNotations.

Local Open Scope Z_scope.

Definition MAX_SPACES: Z := 12.
Lemma MAX_SPACES_eq: MAX_SPACES = 12. Proof. reflexivity. Qed.
Hint Rewrite MAX_SPACES_eq: rep_omega.
Global Opaque MAX_SPACES.

Definition NURSERY_SIZE: Z := Z.shiftl 1 16.
Lemma NURSERY_SIZE_eq: NURSERY_SIZE = Z.shiftl 1 16. Proof. reflexivity. Qed.
Hint Rewrite NURSERY_SIZE_eq: rep_omega.
Global Opaque NURSERY_SIZE.

Definition MAX_ARGS: Z := 1024.
Lemma MAX_ARGS_eq: MAX_ARGS = 1024. Proof. reflexivity. Qed.
Hint Rewrite MAX_ARGS_eq: rep_omega.
Global Opaque MAX_ARGS.

Definition WORD_SIZE: Z := 4.
Lemma WORD_SIZE_eq: WORD_SIZE = 4. Proof. reflexivity. Qed.
Hint Rewrite WORD_SIZE_eq: rep_omega.
Global Opaque WORD_SIZE.

Definition MAX_SPACE_SIZE: Z := Z.shiftl 1 29.
Lemma MAX_SPACE_SIZE_eq: MAX_SPACE_SIZE = Z.shiftl 1 29. Proof. reflexivity. Qed.
Hint Rewrite MAX_SPACE_SIZE_eq: rep_omega.
Global Opaque MAX_SPACE_SIZE.

Definition NO_SCAN_TAG: Z := 251.
Lemma NO_SCAN_TAG_eq: NO_SCAN_TAG = 251. Proof. reflexivity. Qed.
Hint Rewrite NO_SCAN_TAG_eq: rep_omega.
Global Opaque NO_SCAN_TAG.

Definition SPACE_STRUCT_SIZE: Z := 12.
Lemma SPACE_STRUCT_SIZE_eq: SPACE_STRUCT_SIZE = 12. Proof. reflexivity. Qed.
Hint Rewrite SPACE_STRUCT_SIZE_eq: rep_omega.
Global Opaque SPACE_STRUCT_SIZE.

Lemma MSS_eq_unsigned:
  Int.unsigned (Int.shl (Int.repr 1) (Int.repr 29)) = MAX_SPACE_SIZE.
Proof.
  rewrite Int.shl_mul_two_p.
  rewrite (Int.unsigned_repr 29) by (compute; split; discriminate).
  rewrite mul_repr, MAX_SPACE_SIZE_eq. rewrite Int.Zshiftl_mul_two_p by omega.
  rewrite !Z.mul_1_l, Int.unsigned_repr;
    [reflexivity | compute; split; intro S; discriminate].
Qed.

Lemma MSS_max_unsigned_range: forall n,
    0 <= n < MAX_SPACE_SIZE -> 0 <= n <= Int.max_unsigned.
Proof.
  intros. destruct H. split. 1: assumption. rewrite Z.lt_eq_cases. left.
  transitivity MAX_SPACE_SIZE. 1: assumption.  rewrite MAX_SPACE_SIZE_eq.
  compute; reflexivity.
Qed.

Lemma MSS_max_4_unsigned_range: forall n,
    0 <= n < MAX_SPACE_SIZE -> 0 <= 4 * n <= Int.max_unsigned.
Proof.
  intros. destruct H. split. 1: omega.
  rewrite Z.lt_eq_cases. left. transitivity (4 * MAX_SPACE_SIZE). 1: omega.
  rewrite MAX_SPACE_SIZE_eq. compute; reflexivity.
Qed.

Lemma MSS_max_4_signed_range: forall n,
    0 <= n < MAX_SPACE_SIZE -> Ptrofs.min_signed <= WORD_SIZE * n <= Ptrofs.max_signed.
Proof.
  intros. destruct H. rewrite WORD_SIZE_eq. split.
  - transitivity 0. 2: omega. rewrite Z.le_lteq. left. apply Ptrofs.min_signed_neg.
  - rewrite Z.lt_le_pred in H0. rewrite Z.le_lteq. left.
    apply Z.le_lt_trans with (4 * Z.pred MAX_SPACE_SIZE). 1: omega.
    rewrite Z.mul_pred_r, MAX_SPACE_SIZE_eq.
    unfold Ptrofs.max_signed, Ptrofs.half_modulus, Ptrofs.modulus, Ptrofs.wordsize,
    Wordsize_Ptrofs.wordsize. destruct Archi.ptr64 eqn:? .
    inversion Heqb. simpl. omega.
Qed.

Definition VType: Type := nat * nat.
Definition EType: Type := VType * nat.
Definition vgeneration: VType -> nat := fst.
Definition vindex: VType -> nat := snd.

Instance V_EqDec: EqDec VType eq.
Proof.
  hnf. intros [x] [y]. destruct (Nat.eq_dec x y).
  - destruct (Nat.eq_dec n n0); subst.
    + left. reflexivity.
    + right. intro. apply n1. inversion H. reflexivity.
  - right. intro. apply n1. inversion H. reflexivity.
Defined.

Instance E_EqDec: EqDec EType eq.
Proof.
  hnf. intros [x] [y]. destruct (equiv_dec x y).
  - hnf in e. destruct (Nat.eq_dec n n0); subst.
    + left; reflexivity.
    + right; intro; apply n1; inversion H; reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

Inductive GC_Pointer := | GCPtr: block -> ptrofs -> GC_Pointer.

Definition raw_field: Type := option (Z + GC_Pointer).

Instance raw_field_inhabitant: Inhabitant raw_field := None.

Definition odd_Z2val (x: Z) : val := Vint (Int.repr (2 * x + 1)%Z).

Definition Z2val (x: Z) : val := Vint (Int.repr x).

Definition GC_Pointer2val (x: GC_Pointer) : val :=
  match x with | GCPtr b z => Vptr b z end.

Record raw_vertex_block : Type :=
  {
    raw_mark: bool;
    copied_vertex: VType;
    raw_fields: list raw_field;
    raw_color: Z;
    raw_tag: Z;
    raw_tag_range: 0 <= raw_tag < 256;
    raw_color_range: 0 <= raw_color < 4;
    raw_fields_range: 0 < Zlength raw_fields < two_power_nat 22;
    tag_no_scan: NO_SCAN_TAG <= raw_tag -> ~ In None raw_fields;
  }.

Local Close Scope Z_scope.

Lemma raw_fields_not_nil: forall rvb, raw_fields rvb <> nil.
Proof.
  intros. pose proof (raw_fields_range rvb). destruct (raw_fields rvb).
  - simpl in H. rewrite Zlength_nil in H. exfalso; omega.
  - intro. inversion H0.
Qed.

Definition raw_fields_head (rvb: raw_vertex_block): raw_field :=
  match rvb.(raw_fields) as l return (raw_fields rvb = l -> raw_field) with
  | nil => fun m => False_rect _ (raw_fields_not_nil _ m)
  | r :: _ => fun _ => r
  end eq_refl.

Lemma raw_fields_head_cons:
  forall rvb, exists r l, raw_fields rvb = r :: l /\ raw_fields_head rvb = r.
Proof.
  intros. destruct rvb eqn:? . simpl. unfold raw_fields_head; simpl.
  destruct raw_fields0.
  - exfalso. clear Heqr. rewrite Zlength_nil in raw_fields_range0. omega.
  - exists r, raw_fields0. split; reflexivity.
Qed.

Local Open Scope Z_scope.

Record generation_info: Type :=
  {
    start_address: val;
    number_of_vertices: nat;
    generation_sh: share;
    start_isptr: isptr start_address;
    generation_share_writable: writable_share generation_sh;
  }.

Definition IMPOSSIBLE_VAL := Vptr xH Ptrofs.zero.
Lemma IMPOSSIBLE_ISPTR: isptr IMPOSSIBLE_VAL. Proof. exact I. Qed.
Global Opaque IMPOSSIBLE_VAL.

Definition null_info: generation_info :=
  Build_generation_info IMPOSSIBLE_VAL O Tsh IMPOSSIBLE_ISPTR writable_share_top.

Instance gen_info_inhabitant: Inhabitant generation_info := null_info.

Record graph_info : Type :=
  {
    g_gen: list generation_info;
    g_gen_not_nil: g_gen <> nil;
  }.

Definition graph_info_head (gi: graph_info): generation_info :=
  match gi.(g_gen) as l return (g_gen gi = l -> generation_info) with
  | nil => fun m => False_rect _ (g_gen_not_nil _ m)
  | s :: _ => fun _ => s
  end eq_refl.

Lemma graph_info_head_cons:
  forall gi, exists s l, g_gen gi = s :: l /\ graph_info_head gi = s.
Proof.
  intros. destruct gi eqn:? . simpl. unfold graph_info_head. simpl. destruct g_gen0.
  1: contradiction. exists g, g_gen0. split; reflexivity.
Qed.

Definition LGraph := LabeledGraph VType EType raw_vertex_block unit graph_info.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Record space: Type :=
  {
    space_start: val;
    used_space: Z;
    total_space: Z;
    space_sh: share;
    space_order: 0 <= used_space <= total_space;
    space_upper_bound: total_space < MAX_SPACE_SIZE;
  }.

Definition null_space: space.
Proof.
  refine (Build_space nullval 0 0 emptyshare _ _).
  - split; apply Z.le_refl.
  - rewrite MAX_SPACE_SIZE_eq. compute; reflexivity.
Defined.

Instance space_inhabitant: Inhabitant space := null_space.

Lemma total_space_tight_range: forall sp, 0 <= total_space sp < MAX_SPACE_SIZE.
Proof.
  intros. split.
  - destruct (space_order sp). transitivity (used_space sp); assumption.
  - apply space_upper_bound.
Qed.

Lemma total_space_range: forall sp, 0 <= total_space sp <= Int.max_unsigned.
Proof. intros. apply MSS_max_unsigned_range, total_space_tight_range. Qed.

Lemma total_space_signed_range: forall sp,
    Ptrofs.min_signed <= WORD_SIZE * total_space sp <= Ptrofs.max_signed.
Proof. intros. apply MSS_max_4_signed_range, total_space_tight_range. Qed.

Lemma used_space_signed_range: forall sp,
    Ptrofs.min_signed <= WORD_SIZE * used_space sp <= Ptrofs.max_signed.
Proof.
  intros. apply MSS_max_4_signed_range. destruct (space_order sp). split.
  1: assumption. apply Z.le_lt_trans with (total_space sp). 1: assumption.
  apply (proj2 (total_space_tight_range sp)).
Qed.

Lemma rest_space_signed_range: forall sp,
    Ptrofs.min_signed <=
    WORD_SIZE * total_space sp - WORD_SIZE * used_space sp <=
    Ptrofs.max_signed.
Proof.
  intros. rewrite <- Z.mul_sub_distr_l. apply MSS_max_4_signed_range.
  destruct (space_order sp). pose proof (total_space_tight_range sp). omega.
Qed.

Lemma signed_range_repable_signed: forall z,
    Ptrofs.min_signed <= z <= Ptrofs.max_signed <-> repable_signed z.
Proof.
  intros. unfold repable_signed.
  replace Ptrofs.max_signed with Int.max_signed by (vm_compute; reflexivity).
  replace Ptrofs.min_signed with Int.min_signed by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma used_space_repable_signed: forall sp, repable_signed (used_space sp).
Proof.
  intros. rewrite <- signed_range_repable_signed.
  pose proof (used_space_signed_range sp). rep_omega.
Qed.

Lemma total_space_repable_signed: forall sp, repable_signed (total_space sp).
Proof.
  intros. rewrite <- signed_range_repable_signed.
  pose proof (total_space_signed_range sp). rep_omega.
Qed.

Lemma rest_space_repable_signed: forall sp,
    repable_signed (total_space sp - used_space sp).
Proof.
  intros. rewrite <- signed_range_repable_signed.
  pose proof (rest_space_signed_range sp). rep_omega.
Qed.

Record heap: Type :=
  {
    spaces: list space;
    spaces_size: Zlength spaces = MAX_SPACES;
  }.

Lemma heap_spaces_nil: forall h: heap, nil = spaces h -> False.
Proof.
  intros. pose proof (spaces_size h). rewrite <- H, Zlength_nil in H0. discriminate.
Qed.

Definition heap_head (h: heap) : space :=
  match h.(spaces) as l return (l = spaces h -> space) with
  | nil => fun m => False_rect space (heap_spaces_nil h m)
  | s :: _ => fun _ => s
  end eq_refl.

Lemma heap_head_cons: forall h, exists s l, spaces h = s :: l /\ heap_head h = s.
Proof.
  intros. destruct h eqn:? . simpl. unfold heap_head. simpl. destruct spaces0.
  1: inversion spaces_size0. exists s, spaces0. split; reflexivity.
Qed.

Record thread_info: Type :=
  {
    ti_heap_p: val;
    ti_heap: heap;
    ti_args: list val;
    arg_size: Zlength ti_args = MAX_ARGS;
  }.

Definition vertex_size (g: LGraph) (v: VType): Z :=
  Zlength (vlabel g v).(raw_fields) + 1.

Lemma svs_gt_one: forall g v, 1 < vertex_size g v.
Proof.
  intros. unfold vertex_size. pose proof (raw_fields_range (vlabel g v)). omega.
Qed.

Fixpoint nat_seq (s: nat) (total: nat): list nat :=
  match total with
  | O => nil
  | S n => s :: nat_seq (S s) n
  end.

Lemma nat_seq_length: forall s n, length (nat_seq s n) = n.
Proof. intros. revert s. induction n; intros; simpl; [|rewrite IHn]; reflexivity. Qed.

Lemma nat_seq_S: forall i num, nat_seq i (S num) = nat_seq i num ++ [(num + i)%nat].
Proof.
  intros. revert i. induction num; intros. 1: simpl; reflexivity.
  remember (S num). simpl. rewrite (IHnum (S i)). subst. simpl. repeat f_equal. omega.
Qed.

Lemma nat_seq_In_iff: forall s n i, In i (nat_seq s n) <-> (s <= i < s + n)%nat.
Proof. intros. revert s. induction n; intros; simpl; [|rewrite IHn]; omega. Qed.

Lemma nat_seq_NoDup: forall s n, NoDup (nat_seq s n).
Proof.
  intros. revert s. induction n; intros; simpl; constructor. 2: apply IHn.
  intro. rewrite nat_seq_In_iff in H. omega.
Qed.

Local Close Scope Z_scope.

Lemma nat_seq_nth: forall s num n a, n < num -> nth n (nat_seq s num) a = s + n.
Proof.
  intros. revert s n H. induction num; intros. 1: exfalso; omega. simpl. destruct n.
  1: omega. specialize (IHnum (S s) n). replace (s + S n) with (S s + n) by omega.
  rewrite IHnum; [reflexivity | omega].
Qed.

Lemma nat_seq_app: forall s n m, nat_seq s (n + m) = nat_seq s n ++ nat_seq (s + n) m.
Proof.
  intros. revert s; induction n; simpl; intros.
  - rewrite Nat.add_0_r. reflexivity.
  - f_equal. rewrite IHn. replace (S s + n) with (s + S n) by omega. reflexivity.
Qed.

Lemma nat_seq_Permutation_cons: forall s i n,
    i < n -> exists l, Permutation (nat_seq s n) (s + i :: l).
Proof.
  intros. induction n. 1: omega. replace (S n) with (n + 1) by omega.
  rewrite nat_seq_app. simpl. destruct (Nat.eq_dec i n).
  - subst i. exists (nat_seq s n). symmetry. apply Permutation_cons_append.
  - assert (i < n) by omega. apply IHn in H0. destruct H0 as [l ?].
    exists (l +:: (s + n)). rewrite app_comm_cons. apply Permutation_app_tail.
    assumption.
Qed.

Definition nat_inc_list (n: nat) : list nat := nat_seq O n.

Lemma nat_inc_list_length: forall num, length (nat_inc_list num) = num.
Proof. intros. unfold nat_inc_list. rewrite nat_seq_length. reflexivity. Qed.

Lemma nat_inc_list_S: forall num, nat_inc_list (S num) = nat_inc_list num ++ [num].
Proof. intros. unfold nat_inc_list. rewrite nat_seq_S. repeat f_equal. omega. Qed.

Lemma nat_inc_list_In_iff: forall i n, In i (nat_inc_list n) <-> i < n.
Proof. intros. unfold nat_inc_list. rewrite nat_seq_In_iff. intuition. Qed.

Lemma nat_inc_list_nth: forall i n a, i < n -> nth i (nat_inc_list n) a = i.
Proof. intros. unfold nat_inc_list. rewrite nat_seq_nth; [omega | assumption]. Qed.

Lemma nat_inc_list_app: forall n m,
    nat_inc_list (n + m) = nat_inc_list n ++ nat_seq n m.
Proof. intros. unfold nat_inc_list. rewrite nat_seq_app. reflexivity. Qed.

Lemma nat_inc_list_NoDup: forall n, NoDup (nat_inc_list n).
Proof. intros. unfold nat_inc_list. apply nat_seq_NoDup. Qed.

Lemma nat_inc_list_Permutation_cons: forall i n,
    i < n -> exists l, Permutation (nat_inc_list n) (i :: l).
Proof.
  intros. unfold nat_inc_list. replace i with (O + i) by omega.
  apply nat_seq_Permutation_cons. assumption.
Qed.

Local Open Scope Z_scope.

Definition vertex_size_accum g gen (s: Z) (n: nat) := s + vertex_size g (gen, n).

Definition previous_vertices_size (g: LGraph) (gen i: nat): Z :=
  fold_left (vertex_size_accum g gen) (nat_inc_list i) 0.

Lemma vsa_mono: forall g gen s n, s < vertex_size_accum g gen s n.
Proof.
  intros. unfold vertex_size_accum. pose proof (svs_gt_one g (gen, n)). omega.
Qed.

Lemma vsa_comm: forall g gen s n1 n2,
    vertex_size_accum g gen (vertex_size_accum g gen s n1) n2 =
    vertex_size_accum g gen (vertex_size_accum g gen s n2) n1.
Proof. intros. unfold vertex_size_accum. omega. Qed.

Lemma vs_accum_list_lt: forall g gen s l,
    l <> nil -> s < fold_left (vertex_size_accum g gen) l s.
Proof.
  intros; apply (fold_left_Z_mono_strict (vertex_size_accum g gen) nil l l);
    [apply vsa_mono | apply vsa_comm | assumption | apply Permutation_refl].
Qed.

Lemma vs_accum_list_le: forall g gen s l, s <= fold_left (vertex_size_accum g gen) l s.
Proof.
  intros. destruct l. 1: simpl; omega. rename l into l1. remember (n :: l1).
  assert (l <> nil) by (subst; intro S; inversion S). rewrite Z.le_lteq. left.
  apply vs_accum_list_lt. assumption.
Qed.

Lemma pvs_S: forall g gen i,
    previous_vertices_size g gen (S i) =
    previous_vertices_size g gen i + vertex_size g (gen, i).
Proof.
  intros. unfold previous_vertices_size at 1. rewrite nat_inc_list_S, fold_left_app.
  fold (previous_vertices_size g gen i). simpl. reflexivity.
Qed.

Lemma pvs_ge_zero: forall g gen i, 0 <= previous_vertices_size g gen i.
Proof. intros. unfold previous_vertices_size. apply vs_accum_list_le. Qed.

Definition generation_space_compatible (g: LGraph)
           (tri: nat * generation_info * space) : Prop :=
  match tri with
  | (gen, gi, sp) =>
    gi.(start_address) = sp.(space_start) /\
    gi.(generation_sh) = sp.(space_sh) /\
    previous_vertices_size g gen gi.(number_of_vertices) = sp.(used_space)
  end.

Local Close Scope Z_scope.

Definition graph_thread_info_compatible (g: LGraph) (ti: thread_info): Prop :=
  Forall (generation_space_compatible g)
         (combine (combine (nat_inc_list (length g.(glabel).(g_gen)))
                           g.(glabel).(g_gen)) ti.(ti_heap).(spaces)) /\
  Forall (eq nullval)
         (skipn (length g.(glabel).(g_gen)) (map space_start ti.(ti_heap).(spaces))) /\
  length g.(glabel).(g_gen) <= length ti.(ti_heap).(spaces).

Record fun_info : Type :=
  {
    fun_word_size: Z;
    live_roots_indices: list Z;
    fi_index_range: forall i, In i live_roots_indices -> (0 <= i < MAX_ARGS)%Z;
    lri_range: (Zlength (live_roots_indices) <= Int.max_unsigned - 2)%Z;
    word_size_range: (0 <= fun_word_size <= Int.max_unsigned)%Z;
  }.

Definition vertex_offset (g: LGraph) (v: VType): Z :=
  previous_vertices_size g (vgeneration v) (vindex v) + 1.

Definition nth_gen (g: LGraph) (gen: nat): generation_info :=
  nth gen g.(glabel).(g_gen) null_info.

Definition graph_gen_size g gen :=
  previous_vertices_size g gen (number_of_vertices (nth_gen g gen)).

Definition graph_has_gen (g: LGraph) (n: nat): Prop := n < length g.(glabel).(g_gen).

Definition gen_has_index (g: LGraph) (gen index: nat): Prop :=
  index < number_of_vertices (nth_gen g gen).

Definition graph_has_v (g: LGraph) (v: VType): Prop :=
  graph_has_gen g (vgeneration v) /\ gen_has_index g (vgeneration v) (vindex v).

Lemma graph_has_gen_O: forall g, graph_has_gen g O.
Proof.
  intros. hnf. destruct (g_gen (glabel g)) eqn:? ; simpl; try omega.
  pose proof (g_gen_not_nil (glabel g)). contradiction.
Qed.

Definition graph_has_gen_dec g n: {graph_has_gen g n} + {~ graph_has_gen g n} :=
  lt_dec n (length (g_gen (glabel g))).

Definition gen_start (g: LGraph) (gen: nat): val :=
  if graph_has_gen_dec g gen then start_address (nth_gen g gen) else Vundef.

Lemma graph_has_gen_start_isptr: forall g n,
    graph_has_gen g n -> isptr (gen_start g n).
Proof. intros. unfold gen_start. if_tac; [apply start_isptr | contradiction]. Qed.

Definition vertex_address (g: LGraph) (v: VType): val :=
  offset_val (WORD_SIZE * vertex_offset g v) (gen_start g (vgeneration v)).

Definition root_t: Type := Z + GC_Pointer + VType.

Instance root_t_inhabitant: Inhabitant root_t := inl (inl Z.zero).

Definition root2val (g: LGraph) (fd: root_t) : val :=
  match fd with
  | inl (inl z) => odd_Z2val z
  | inl (inr p) => GC_Pointer2val p
  | inr v => vertex_address g v
  end.

Definition roots_t: Type := list root_t.

Definition outlier_t: Type := list GC_Pointer.

Definition fun_thread_arg_compatible
           (g: LGraph) (ti: thread_info) (fi: fun_info) (roots: roots_t) : Prop :=
  map (root2val g) roots = map ((flip Znth) ti.(ti_args)) fi.(live_roots_indices).

Definition roots_outlier_compatible (roots: roots_t) (outlier: outlier_t): Prop :=
  incl (filter_sum_right (filter_sum_left roots)) outlier.

Definition roots_graph_compatible (roots: roots_t) (g: LGraph): Prop :=
  Forall (graph_has_v g) (filter_sum_right roots).

Definition roots_compatible (g: LGraph) (outlier: outlier_t) (roots: roots_t): Prop :=
  roots_outlier_compatible roots outlier /\ roots_graph_compatible roots g.

Definition outlier_compatible (g: LGraph) (outlier: outlier_t): Prop :=
  forall v,
    graph_has_v g v ->
    incl (filter_sum_right (filter_option (vlabel g v).(raw_fields))) outlier.

Definition copy_compatible (g: LGraph): Prop :=
  forall v, graph_has_v g v -> (vlabel g v).(raw_mark) = true ->
            graph_has_v g (vlabel g v).(copied_vertex) /\
            vgeneration v <> vgeneration (vlabel g v).(copied_vertex).
Definition
  super_compatible
  (g_ti_r: LGraph * thread_info * roots_t) (fi: fun_info) (out: outlier_t) : Prop :=
  let (g_ti, r) := g_ti_r in
  let (g, ti) := g_ti in
  graph_thread_info_compatible g ti /\
  fun_thread_arg_compatible g ti fi r /\
  roots_compatible g out r /\
  outlier_compatible g out.

Definition reset_gen_info (gi: generation_info) : generation_info :=
  Build_generation_info (start_address gi) O (generation_sh gi) (start_isptr gi)
                        (generation_share_writable gi).

Fixpoint reset_nth_gen_info
         (n: nat) (gi: list generation_info) : list generation_info :=
  match n with
  | O => match gi with
         | nil => nil
         | g :: l => reset_gen_info g :: l
         end
  | S m => match gi with
           | nil => nil
           | g :: l => g :: reset_nth_gen_info m l
           end
  end.

Lemma reset_nth_gen_info_length: forall n gl,
    length (reset_nth_gen_info n gl) = length gl.
Proof.
  intros. revert n. induction gl; simpl; intros; destruct n; simpl;
                      [| | | rewrite IHgl]; reflexivity.
Qed.

Lemma reset_nth_gen_info_not_nil: forall n g, reset_nth_gen_info n (g_gen g) <> nil.
Proof.
  intros. pose proof (g_gen_not_nil g). destruct (g_gen g).
  - contradiction.
  - destruct n; simpl; discriminate.
Qed.

Lemma reset_nth_gen_info_diff: forall gl i j a,
    i <> j -> nth i (reset_nth_gen_info j gl) a = nth i gl a.
Proof.
  intros ? ? ?. revert gl i. induction j; intros; simpl; destruct gl; try reflexivity.
  - destruct i. 1: contradiction. simpl. reflexivity.
  - destruct i. 1: reflexivity. simpl. apply IHj. omega.
Qed.

Lemma reset_nth_gen_info_same: forall gl i,
    nth i (reset_nth_gen_info i gl) null_info = reset_gen_info (nth i gl null_info).
Proof.
  intros. revert gl. induction i; intros; destruct gl; simpl in *; try reflexivity.
  apply IHi.
Qed.

Lemma reset_nth_gen_info_overflow: forall gl i,
    length gl <= i -> reset_nth_gen_info i gl = gl.
Proof.
  intros ? ?. revert gl. induction i; intros; destruct gl; simpl in *; try reflexivity.
  1: omega. rewrite IHi; [reflexivity | omega].
Qed.

Lemma sublist_pos_cons: forall {A: Type} (lo hi: Z) (al: list A) v,
    (0 < lo)%Z -> sublist lo hi (v :: al) = sublist (lo - 1) (hi - 1) al.
Proof.
  intros. unfold sublist. f_equal. 1: f_equal; omega.
  replace (Z.to_nat lo) with (S (Z.to_nat (lo - 1))) by
      (zify; rewrite !Z2Nat.id; omega). simpl. reflexivity.
Qed.

Lemma upd_Znth_pos_cons: forall {A: Type} (i: Z) (l: list A) v x,
    (0 < i <= Zlength l)%Z -> upd_Znth i (v :: l) x = v :: upd_Znth (i - 1) l x.
Proof.
  intros. unfold upd_Znth.
  rewrite (sublist_split 0 1 i); [| |rewrite Zlength_cons]; [| omega..].
  unfold sublist at 1. simpl. rewrite !sublist_pos_cons by omega. do 4 f_equal.
  1: omega. rewrite Zlength_cons; omega.
Qed.

Definition reset_nth_graph_info (n: nat) (g: graph_info) : graph_info :=
  Build_graph_info (reset_nth_gen_info n g.(g_gen)) (reset_nth_gen_info_not_nil n g).

Lemma reset_space_order: forall sp, (0 <= 0 <= total_space sp)%Z.
Proof. intros. pose proof (space_order sp). omega. Qed.

Definition reset_space (sp: space) : space :=
  Build_space (space_start sp) 0 (total_space sp) (space_sh sp) (reset_space_order sp)
              (space_upper_bound sp).

Fixpoint reset_nth_space (n: nat) (s: list space): list space :=
  match n with
  | O => match s with
         | nil => nil
         | sp :: l => reset_space sp :: l
         end
  | S m => match s with
           | nil => nil
           | sp :: l => sp :: reset_nth_space m l
           end
  end.

Lemma reset_nth_space_length: forall n s, length (reset_nth_space n s) = length s.
Proof.
  induction n; intros; simpl.
  - destruct s; simpl; reflexivity.
  - destruct s; [|simpl; rewrite (IHn s0)]; reflexivity.
Qed.

Lemma reset_nth_space_Zlength: forall n s, Zlength s = Zlength (reset_nth_space n s).
Proof. intros. rewrite !Zlength_correct, reset_nth_space_length. reflexivity. Qed.

Lemma reset_nth_heap_Zlength: forall n h,
    Zlength (reset_nth_space n (spaces h)) = MAX_SPACES.
Proof. intros. rewrite <- reset_nth_space_Zlength. apply spaces_size. Qed.

Lemma reset_nth_space_Permutation: forall n s,
    n < length s -> exists l, Permutation (reset_nth_space n s)
                                          (reset_space (nth n s null_space) :: l) /\
                              Permutation s (nth n s null_space :: l).
Proof.
  induction n; intros; destruct s; simpl in *; try omega.
  - exists s0. split; constructor; reflexivity.
  - assert (n < length s0) by omega. destruct (IHn _ H0) as [ll [? ?]].
    exists (s :: ll). split.
    + transitivity (s :: reset_space (nth n s0 null_space) :: ll).
      1: constructor; assumption. apply perm_swap.
    + transitivity (s :: nth n s0 null_space :: ll).
      1: constructor; assumption. apply perm_swap.
Qed.

Lemma reset_nth_space_Znth: forall s i,
    i < length s ->
    reset_nth_space i s = upd_Znth (Z.of_nat i) s (reset_space (Znth (Z.of_nat i) s)).
Proof.
  intros ? ?. revert s. induction i; intros; destruct s; simpl in H; try omega.
  - simpl.
    rewrite upd_Znth0, Znth_0_cons, sublist_1_cons, sublist_same; try reflexivity.
    rewrite Zlength_cons. omega.
  - replace (Z.of_nat (S i)) with (Z.of_nat i + 1)%Z by (zify; omega).
    rewrite Znth_pos_cons by omega.
    replace (Z.of_nat i + 1 - 1)%Z with (Z.of_nat i) by omega. simpl.
    rewrite upd_Znth_pos_cons.
    + replace (Z.of_nat i + 1 - 1)%Z with (Z.of_nat i) by omega.
      rewrite <- IHi; [reflexivity | omega].
    + rewrite Zlength_correct. omega.
Qed.

Lemma reset_nth_space_overflow: forall s i, length s <= i -> reset_nth_space i s = s.
Proof.
  intros ? ?. revert s.
  induction i; intros; destruct s; simpl in *; try omega; try reflexivity.
  rewrite IHi; [reflexivity | omega].
Qed.

Lemma reset_nth_space_diff: forall gl i j a,
    i <> j -> nth i (reset_nth_space j gl) a = nth i gl a.
Proof.
  intros ? ? ?. revert gl i. induction j; intros; simpl; destruct gl; try reflexivity.
  - destruct i. 1: contradiction. simpl. reflexivity.
  - destruct i. 1: reflexivity. simpl. apply IHj. omega.
Qed.

Lemma reset_nth_space_same: forall gl i a,
    i < length gl -> nth i (reset_nth_space i gl) a = reset_space (nth i gl a).
Proof.
  intros. revert gl H. induction i; intros; destruct gl; simpl in *; try omega.
  - reflexivity.
  - apply IHi. omega.
Qed.

Definition reset_nth_heap (n: nat) (h: heap) : heap :=
  Build_heap (reset_nth_space n (spaces h)) (reset_nth_heap_Zlength n h).

Definition reset_nth_heap_thread_info (n: nat) (ti: thread_info) :=
  Build_thread_info (ti_heap_p ti) (reset_nth_heap n (ti_heap ti))
                    (ti_args ti) (arg_size ti).

Lemma reset_thread_info_overflow: forall n ti,
    length (spaces (ti_heap ti)) <= n -> reset_nth_heap_thread_info n ti = ti.
Proof.
  intros. unfold reset_nth_heap_thread_info. destruct ti. f_equal.
  simpl. unfold reset_nth_heap. destruct ti_heap0. simpl in *.
  assert (spaces0 = reset_nth_space n spaces0) by
      (rewrite reset_nth_space_overflow; [reflexivity | assumption]).
  apply EqdepFacts.f_eq_dep_non_dep, EqdepFacts.eq_dep1_dep.
  apply (EqdepFacts.eq_dep1_intro _ _ _ _ _ _ H0). apply proof_irr.
Qed.

Definition make_header (g: LGraph) (v: VType): Z:=
  let vb := vlabel g v in if vb.(raw_mark)
                          then 0 else
                            vb.(raw_tag) + (Z.shiftl vb.(raw_color) 8) +
                            (Z.shiftl (Zlength vb.(raw_fields)) 10).

Local Open Scope Z_scope.

Lemma make_header_mark_iff: forall g v,
    make_header g v = 0 <-> raw_mark (vlabel g v) = true.
Proof.
  intros. unfold make_header. destruct (raw_mark (vlabel g v)). 1: intuition.
  split; intros. 2: inversion H. exfalso.
  destruct (raw_tag_range (vlabel g v)) as [? _].
  assert (0 <= Z.shiftl (raw_color (vlabel g v)) 8). {
    rewrite Z.shiftl_nonneg. apply (proj1 (raw_color_range (vlabel g v))).
  } assert (Z.shiftl (Zlength (raw_fields (vlabel g v))) 10 <= 0) by omega.
  clear -H2. assert (0 <= Z.shiftl (Zlength (raw_fields (vlabel g v))) 10) by
      (rewrite Z.shiftl_nonneg; apply Zlength_nonneg).
  assert (Z.shiftl (Zlength (raw_fields (vlabel g v))) 10 = 0) by omega. clear -H0.
  rewrite Z.shiftl_eq_0_iff in H0 by omega.
  pose proof (proj1 (raw_fields_range (vlabel g v))). omega.
Qed.

Lemma make_header_range: forall g v, 0 <= make_header g v < two_power_nat 32.
Proof.
  intros. unfold make_header. destruct (raw_mark (vlabel g v)).
  - pose proof (two_power_nat_pos 32). omega.
  - pose proof (raw_tag_range (vlabel g v)). pose proof (raw_color_range (vlabel g v)).
    pose proof (raw_fields_range (vlabel g v)). remember (raw_tag (vlabel g v)) as z1.
    clear Heqz1. remember (raw_color (vlabel g v)) as z2. clear Heqz2.
    remember (Zlength (raw_fields (vlabel g v))) as z3. clear Heqz3.
    assert (0 <= 8) by omega. apply (Int.Zshiftl_mul_two_p z2) in H2. rewrite H2.
    clear H2. assert (0 <= 10) by omega. apply (Int.Zshiftl_mul_two_p z3) in H2.
    rewrite H2. clear H2. rewrite two_power_nat_two_p in *. simpl Z.of_nat in *.
    assert (two_p 10 > 0) by (apply two_p_gt_ZERO; omega).
    assert (two_p 8 > 0) by (apply two_p_gt_ZERO; omega). split.
    + assert (0 <= z2 * two_p 8) by (apply Z.mul_nonneg_nonneg; omega).
      assert (0 <= z3 * two_p 10) by (apply Z.mul_nonneg_nonneg; omega). omega.
    + destruct H as [_ ?]. destruct H0 as [_ ?]. destruct H1 as [_ ?].
      change 256 with (two_p 8) in H. change 4 with (two_p 2) in H0.
      assert (z1 <= two_p 8 - 1) by omega. clear H.
      assert (z2 <= two_p 2 - 1) by omega. clear H0.
      assert (z3 <= two_p 22 - 1) by omega. clear H1.
      apply Z.mul_le_mono_nonneg_r with (p := two_p 8) in H. 2: omega.
      apply Z.mul_le_mono_nonneg_r with (p := two_p 10) in H0. 2: omega.
      rewrite Z.mul_sub_distr_r in H, H0.
      rewrite <- two_p_is_exp in H, H0 by omega. simpl Z.add in H, H0. omega.
Qed.

Lemma make_header_int_rep_mark_iff: forall g v,
    Int.repr (make_header g v) = Int.repr 0 <-> raw_mark (vlabel g v) = true.
Proof.
  intros. rewrite <- make_header_mark_iff. split; intros; [|rewrite H; reflexivity].
  Transparent Int.repr. inversion H. Opaque Int.repr. clear H. rewrite H1.
  rewrite Int.Z_mod_modulus_eq, Z.mod_small in H1 by apply make_header_range.
  assumption.
Qed.

Lemma make_header_Wosize: forall g v,
    raw_mark (vlabel g v) = false ->
    Int.shru (Int.repr (make_header g v)) (Int.repr 10) =
    Int.repr (Zlength (raw_fields (vlabel g v))).
Proof.
  intros. rewrite Int.shru_div_two_p, !Int.unsigned_repr.
  - f_equal. unfold make_header. remember (vlabel g v). clear Heqr.
    rewrite H, !Int.Zshiftl_mul_two_p by omega. rewrite Z.div_add. 2: compute; omega.
    pose proof (raw_tag_range r). pose proof (raw_color_range r).
    cut ((raw_tag r + raw_color r * two_p 8) / two_p 10 = 0). 1: intros; omega.
    apply Z.div_small. change 256 with (two_p 8) in H0. change 4 with (two_p 2) in H1.
    assert (0 <= raw_tag r <= two_p 8 - 1) by omega. clear H0. destruct H2.
    assert (0 <= raw_color r <= two_p 2 - 1) by omega. clear H1. destruct H3.
    assert (two_p 8 > 0) by (apply two_p_gt_ZERO; omega). split.
    + assert (0 <= raw_color r * two_p 8) by (apply Z.mul_nonneg_nonneg; omega). omega.
    + apply Z.mul_le_mono_nonneg_r with (p := two_p 8) in H3. 2: omega.
      rewrite Z.mul_sub_distr_r, <- two_p_is_exp in H3 by omega. simpl Z.add in H3.
      omega.
  - rep_omega.
  - pose proof (make_header_range g v). unfold Int.max_unsigned, Int.modulus.
    rep_omega.
Qed.

Definition field_t: Type := Z + GC_Pointer + EType.

Instance field_t_inhabitant: Inhabitant field_t := inl (inl Z.zero).

Definition field2val (g: LGraph) (fd: field_t) : val :=
  match fd with
  | inl (inl z) => odd_Z2val z
  | inl (inr p) => GC_Pointer2val p
  | inr e => vertex_address g (dst g e)
  end.

Fixpoint make_fields' (l_raw: list raw_field) (v: VType) (n: nat): list field_t :=
  match l_raw with
  | nil => nil
  | Some (inl z) :: l => inl (inl z) :: make_fields' l v (n + 1)
  | Some (inr ptr) :: l => inl (inr ptr) :: make_fields' l v (n + 1)
  | None :: l => inr (v, n) :: make_fields' l v (n + 1)
  end.

Lemma make_fields'_eq_length: forall l v n, length (make_fields' l v n) = length l.
Proof.
  intros. revert n. induction l; intros; simpl. 1: reflexivity.
  destruct a; [destruct s|]; simpl; rewrite IHl; reflexivity.
Qed.

Lemma make_fields'_eq_Zlength: forall l v n, Zlength (make_fields' l v n) = Zlength l.
Proof.
  intros. rewrite !Zlength_correct. rewrite make_fields'_eq_length. reflexivity.
Qed.

Lemma make_fields'_edge_depends_on_index:
  forall n l_raw i v e,
    0 <= Z.of_nat n < Zlength l_raw ->
    nth n (make_fields' l_raw v i) field_t_inhabitant = inr e ->
    e = (v, n+i)%nat.
Proof.
  induction n as [|n' IHn'].
  - intros. destruct l_raw; try inversion H0.
    destruct r; [destruct s|]; simpl in H0; inversion H0;
      reflexivity.
  - intro. destruct l_raw; try inversion 2.
    replace (S n' + i)%nat with (n' + S i)%nat by omega.
    specialize (IHn' l_raw (S i) v e).
    assert (0 <= Z.of_nat n' < Zlength l_raw) by
          (rewrite Zlength_cons, Nat2Z.inj_succ in H; omega).
      assert (nth n' (make_fields' l_raw v (S i)) field_t_inhabitant = inr e) by
        (destruct r; [destruct s|]; simpl in H2;
        replace (i + 1)%nat with (S i) in H2 by omega; assumption).
      destruct r; [destruct s|]; simpl; apply IHn'; assumption.
Qed.

Definition make_fields (g: LGraph) (v: VType): list field_t :=
  make_fields' (vlabel g v).(raw_fields) v O.

Definition get_edges (g: LGraph) (v: VType): list EType :=
  filter_sum_right (make_fields g v).

Definition pregraph_remove_vertex_and_edges
           (g: LGraph) (v: VType): PreGraph VType EType :=
  fold_left pregraph_remove_edge (get_edges g v) (pregraph_remove_vertex g v).

Definition lgraph_remove_vertex_and_edges (g: LGraph) (v: VType): LGraph :=
  Build_LabeledGraph _ _ _ (pregraph_remove_vertex_and_edges g v)
                     (vlabel g) (elabel g) (glabel g).

Definition remove_nth_gen_ve (g: LGraph) (gen: nat): LGraph :=
  let all_nv := map (fun idx => (gen, idx))
                    (nat_inc_list (number_of_vertices (nth_gen g gen))) in
  fold_left lgraph_remove_vertex_and_edges all_nv g.

Lemma remove_ve_glabel_unchanged: forall g gen,
    glabel (remove_nth_gen_ve g gen) = glabel g.
Proof.
  intros. unfold remove_nth_gen_ve.
  remember (map (fun idx : nat => (gen, idx))
                (nat_inc_list (number_of_vertices (nth_gen g gen)))). clear Heql.
  revert g. induction l; intros; simpl. 1: reflexivity. rewrite IHl. reflexivity.
Qed.

Lemma remove_ve_vlabel_unchanged: forall g gen v,
    vlabel (remove_nth_gen_ve g gen) v = vlabel g v.
Proof.
  intros. unfold remove_nth_gen_ve.
  remember (map (fun idx : nat => (gen, idx))
                (nat_inc_list (number_of_vertices (nth_gen g gen)))). clear Heql.
  revert g v. induction l; intros; simpl. 1: reflexivity. rewrite IHl. reflexivity.
Qed.

Lemma remove_ve_dst_unchanged: forall g gen e,
    dst (remove_nth_gen_ve g gen) e = dst g e.
Proof.
  intros. unfold remove_nth_gen_ve.
  remember (map (fun idx : nat => (gen, idx))
                (nat_inc_list (number_of_vertices (nth_gen g gen)))). clear Heql.
  revert g e. induction l; intros; simpl. 1: reflexivity. rewrite IHl.
  clear. simpl. unfold pregraph_remove_vertex_and_edges.
  transitivity (dst (pregraph_remove_vertex g a) e). 2: reflexivity.
  remember (pregraph_remove_vertex g a) as g'. remember (get_edges g a) as l.
  clear a g Heqg' Heql. rename g' into g. revert g e. induction l; intros; simpl.
  1: reflexivity. rewrite IHl. reflexivity.
Qed.

Definition reset_nth_glabel (n: nat) (g: LGraph) : LGraph :=
  Build_LabeledGraph _ _ _ (pg_lg g) (vlabel g) (elabel g)
                     (reset_nth_graph_info n (glabel g)).

Definition reset_graph (n: nat) (g: LGraph) : LGraph :=
  reset_nth_glabel n (remove_nth_gen_ve g n).

Lemma graph_has_gen_reset: forall (g: LGraph) gen1 gen2,
    graph_has_gen (reset_graph gen1 g) gen2 <-> graph_has_gen g gen2.
Proof.
  intros. unfold graph_has_gen. simpl. rewrite reset_nth_gen_info_length.
  rewrite remove_ve_glabel_unchanged. reflexivity.
Qed.

Lemma reset_nth_gen_diff: forall g i j,
    i <> j -> nth_gen (reset_graph j g) i = nth_gen g i.
Proof.
  intros. unfold nth_gen, reset_graph. simpl.
  rewrite remove_ve_glabel_unchanged.
  apply reset_nth_gen_info_diff. assumption.
Qed.

Definition make_fields_vals (g: LGraph) (v: VType): list val :=
  let vb := vlabel g v in
  let original_fields_val := map (field2val g) (make_fields g v) in
  if vb.(raw_mark)
  then vertex_address g vb.(copied_vertex) :: tl original_fields_val
  else original_fields_val.

Lemma fields_eq_length: forall g v,
    Zlength (make_fields_vals g v) = Zlength (raw_fields (vlabel g v)).
Proof.
  intros. rewrite !Zlength_correct. f_equal. unfold make_fields_vals, make_fields.
  destruct (raw_mark (vlabel g v)).
  - destruct (raw_fields_head_cons (vlabel g v)) as [r [l [? ?]]].
    rewrite H; simpl; destruct r; [destruct s|]; simpl;
      rewrite map_length, make_fields'_eq_length; reflexivity.
  - rewrite map_length, make_fields'_eq_length. reflexivity.
Qed.

Lemma make_fields_eq_length: forall g v,
    Zlength (make_fields g v) = Zlength (raw_fields (vlabel g v)).
Proof.
  unfold make_fields. intros.
  rewrite !Zlength_correct, make_fields'_eq_length. reflexivity.
Qed.

Lemma make_fields_Znth_edge: forall g v n e,
    0 <= n < Zlength (raw_fields (vlabel g v)) ->
    Znth n (make_fields g v) = inr e -> e = (v, Z.to_nat n).
Proof.
  intros. rewrite <- nth_Znth in H0. 2: rewrite make_fields_eq_length; assumption.
  apply make_fields'_edge_depends_on_index in H0.
  - rewrite Nat.add_0_r in H0; assumption.
  - rewrite Z2Nat.id; [assumption | omega].
Qed.

Lemma Znth_skip_hd_same: forall A (d: Inhabitant A) (l: list A) a n,
    n > 0 ->
    Zlength l > 0 ->
    Znth n (a :: tl l) = Znth n l.
Proof.
  intros. destruct l.
  - rewrite Zlength_nil in H0; inversion H0.
  - repeat rewrite Znth_pos_cons by omega. reflexivity.
Qed.

Lemma make_fields'_n_doesnt_matter: forall i l v n m gcptr,
    nth i (make_fields' l v n) field_t_inhabitant = inl (inr gcptr) ->
    nth i (make_fields' l v m) field_t_inhabitant = inl (inr gcptr).
Proof.
  intros.
  unfold make_fields' in *.
  generalize dependent i.
  generalize dependent n.
  generalize dependent m.
  induction l.
  + intros; assumption.
  + induction i.
    - destruct a; [destruct s|]; simpl; intros; try assumption; try inversion H.
    - destruct a; [destruct s|]; simpl; intro;
        apply IHl with (m:=(m+1)%nat) in H; assumption.
Qed.

Lemma make_fields'_item_was_in_list: forall l v n gcptr,
    0 <= n < Zlength l ->
    Znth n (make_fields' l v 0) = inl (inr gcptr) ->
    Znth n l = Some (inr gcptr).
Proof.
  intros.
  rewrite <- nth_Znth; rewrite <- nth_Znth in H0; [| rewrite Zlength_correct in *..];
    try rewrite make_fields'_eq_length; [|assumption..].
  generalize dependent n.
  induction l.
  - intros. rewrite nth_Znth in H0; try assumption.
    unfold make_fields' in H0; rewrite Znth_nil in H0; inversion H0.
  - intro n. induction (Z.to_nat n) eqn:?.
    + intros. destruct a; [destruct s|]; simpl in *; try inversion H0; try reflexivity.
    + intros. simpl in *. clear IHn0.
      replace n0 with (Z.to_nat (Z.of_nat n0)) by apply Nat2Z.id.
      assert (0 <= Z.of_nat n0 < Zlength l). {
        split; try omega.
        destruct H; rewrite Zlength_cons in H1.
        apply Zsucc_lt_reg; rewrite <- Nat2Z.inj_succ.
        rewrite <- Heqn0; rewrite Z2Nat.id; assumption.
      }
      destruct a; [destruct s|]; simpl in H0; apply IHl;
        try assumption; apply make_fields'_n_doesnt_matter with (n:=1%nat);
        rewrite Nat2Z.id; assumption.
Qed.

Lemma make_fields_edge_unique: forall g e v1 v2 n m,
    0 <= n < Zlength (make_fields g v1) ->
    0 <= m < Zlength (make_fields g v2) ->
    Znth n (make_fields g v1) = inr e ->
    Znth m (make_fields g v2) = inr e ->
    n = m /\ v1 = v2.
Proof.
  intros. unfold make_fields in *.
  rewrite make_fields'_eq_Zlength in *.
  assert (0 <= Z.of_nat (Z.to_nat n) < Zlength (raw_fields (vlabel g v1))) by
      (destruct H; split; rewrite Z2Nat.id; assumption).
  rewrite <- nth_Znth in H1 by
      (rewrite make_fields'_eq_Zlength; assumption).
  assert (0 <= Z.of_nat (Z.to_nat m) < Zlength (raw_fields (vlabel g v2))) by
       (destruct H0; split; rewrite Z2Nat.id; assumption).
  rewrite <- nth_Znth in H2 by
      (rewrite make_fields'_eq_Zlength; assumption).
  pose proof (make_fields'_edge_depends_on_index
                (Z.to_nat n) (raw_fields (vlabel g v1)) 0 v1 e H3 H1).
  pose proof (make_fields'_edge_depends_on_index
                (Z.to_nat m) (raw_fields (vlabel g v2)) 0 v2 e H4 H2).
  rewrite H5 in H6. inversion H6.
  rewrite Nat.add_cancel_r, Z2Nat.inj_iff in H9 by omega.
  split; [assumption | reflexivity].
Qed.

Lemma in_gcptr_outlier: forall g gcptr outlier n v,
    graph_has_v g v ->
    outlier_compatible g outlier ->
    0 <= n < Zlength (raw_fields (vlabel g v)) ->
    Znth n (make_fields g v) = inl (inr gcptr) ->
    In gcptr outlier.
Proof.
  intros.
  apply H0 in H; apply H; clear H; clear H0.
  unfold make_fields in H2.
  apply make_fields'_item_was_in_list in H2; try assumption.
  rewrite <- filter_sum_right_In_iff, <- filter_option_In_iff.
  rewrite <- H2; apply Znth_In; assumption.
Qed.

Lemma vertex_address_the_same: forall (g1 g2: LGraph) v,
    (forall v, g1.(vlabel) v = g2.(vlabel) v) ->
    map start_address g1.(glabel).(g_gen) = map start_address g2.(glabel).(g_gen) ->
    vertex_address g1 v = vertex_address g2 v.
Proof.
  intros. unfold vertex_address. f_equal.
  - f_equal. unfold vertex_offset. f_equal. remember (vindex v). clear Heqn.
    induction n; simpl; auto. rewrite !pvs_S, IHn. f_equal. unfold vertex_size.
    rewrite H. reflexivity.
  - assert (forall gen, graph_has_gen g1 gen <-> graph_has_gen g2 gen). {
      intros. unfold graph_has_gen.
      cut (length (g_gen (glabel g1)) = length (g_gen (glabel g2))).
      - intros. rewrite H1. reflexivity.
      - do 2 rewrite <- (map_length start_address). rewrite H0. reflexivity.
    } unfold gen_start. do 2 if_tac; [|rewrite H1 in H2; contradiction.. |reflexivity].
    unfold nth_gen. rewrite <- !(map_nth start_address), H0. reflexivity.
Qed.

Lemma make_fields_the_same: forall (g1 g2: LGraph) v,
    (forall e, dst g1 e = dst g2 e) ->
    (forall v, g1.(vlabel) v = g2.(vlabel) v) ->
    map start_address g1.(glabel).(g_gen) = map start_address g2.(glabel).(g_gen) ->
    make_fields_vals g1 v = make_fields_vals g2 v.
Proof.
  intros. unfold make_fields_vals, make_fields. remember O. clear Heqn. rewrite H0.
  remember (raw_fields (vlabel g2 v)) as l. clear Heql.
  cut (forall fl, map (field2val g1) fl = map (field2val g2) fl).
  - intros. rewrite H2. rewrite (vertex_address_the_same g1 g2) by assumption.
    reflexivity.
  - apply map_ext. intros. unfold field2val. destruct a. 1: reflexivity.
    rewrite H. apply vertex_address_the_same; assumption.
Qed.

Lemma start_address_reset: forall n l,
   map start_address (reset_nth_gen_info n l) = map start_address l.
Proof.
  intros. revert n.
  induction l; intros; simpl; destruct n; simpl; [| | | rewrite IHl]; reflexivity.
Qed.

Lemma vertex_address_reset: forall (g: LGraph) v n,
    vertex_address (reset_graph n g) v = vertex_address g v.
Proof.
  intros. apply vertex_address_the_same; unfold reset_graph; simpl.
  - intros. rewrite remove_ve_vlabel_unchanged. reflexivity.
  - rewrite remove_ve_glabel_unchanged, start_address_reset. reflexivity.
Qed.

Lemma make_fields_reset: forall (g: LGraph) v n,
    make_fields_vals (reset_graph n g) v = make_fields_vals g v.
Proof.
  intros. apply make_fields_the_same; unfold reset_graph; simpl; intros.
  - apply remove_ve_dst_unchanged.
  - apply remove_ve_vlabel_unchanged.
  - rewrite remove_ve_glabel_unchanged. apply start_address_reset.
Qed.

Lemma make_header_reset: forall (g: LGraph) v n,
    make_header (reset_graph n g) v = make_header g v.
Proof.
  intros. unfold make_header. simpl vlabel. rewrite remove_ve_vlabel_unchanged.
  reflexivity.
Qed.

Definition copy_v_add_edge
           (s: VType) (g: PreGraph VType EType) (p: EType * VType):
  PreGraph VType EType := pregraph_add_edge g (fst p) s (snd p).

Definition pregraph_copy_v (g: LGraph) (old_v new_v: VType) : PreGraph VType EType :=
  let old_edges := get_edges g old_v in
  let new_edges := combine (repeat new_v (length old_edges)) (map snd old_edges) in
  let new_edge_dst_l := combine new_edges (map (dst g) old_edges) in
  fold_left (copy_v_add_edge new_v) new_edge_dst_l (pregraph_add_vertex g new_v).

Definition copy_v_mod_rvb (rvb: raw_vertex_block) (new_v: VType) : raw_vertex_block :=
  Build_raw_vertex_block
    true new_v (raw_fields rvb) (raw_color rvb) (raw_tag rvb) (raw_tag_range rvb)
    (raw_color_range rvb) (raw_fields_range rvb) (tag_no_scan rvb).

Definition update_copied_new_vlabel (g: LGraph) (old_v new_v: VType) :=
  update_vlabel (vlabel g) new_v (vlabel g old_v).

Definition update_copied_old_vlabel (g: LGraph) (old_v new_v: VType) :=
  update_vlabel (vlabel g) old_v (copy_v_mod_rvb (vlabel g old_v) new_v).

Definition copy_v_mod_gen_info (gi: generation_info) : generation_info :=
  Build_generation_info (start_address gi) (number_of_vertices gi + 1)
                        (generation_sh gi) (start_isptr gi)
                        (generation_share_writable gi).

Definition copy_v_mod_gen_info_list
           (l: list generation_info) (to: nat) : list generation_info :=
  firstn to l ++ copy_v_mod_gen_info (nth to l null_info) :: skipn (to + 1) l.

Lemma copy_v_mod_gen_no_nil: forall l to, copy_v_mod_gen_info_list l to <> nil.
Proof.
  repeat intro. unfold copy_v_mod_gen_info_list in H. apply app_eq_nil in H.
  destruct H. inversion H0.
Qed.

Definition copy_v_update_glabel (gi: graph_info) (to: nat): graph_info :=
  Build_graph_info (copy_v_mod_gen_info_list (g_gen gi) to)
                   (copy_v_mod_gen_no_nil (g_gen gi) to).

Definition new_copied_v (g: LGraph) (to: nat): VType :=
  (to, number_of_vertices (nth_gen g to)).

Definition lgraph_add_copied_v (g: LGraph) (v: VType) (to: nat): LGraph :=
  let new_v := new_copied_v g to in
  Build_LabeledGraph _ _ _ (pregraph_copy_v g v new_v)
                     (update_copied_new_vlabel g v new_v)
                     (elabel g) (copy_v_update_glabel (glabel g) to).

Definition lgraph_mark_copied (g: LGraph) (old new: VType): LGraph :=
  Build_LabeledGraph _ _ _ (pg_lg g)
                     (update_copied_old_vlabel g old new) (elabel g) (glabel g).

Definition lgraph_copy_v (g: LGraph) (v: VType) (to: nat): LGraph :=
  lgraph_mark_copied (lgraph_add_copied_v g v to) v (new_copied_v g to).

Definition forward_t: Type := Z + GC_Pointer + VType + EType.

Definition root2forward (r: root_t): forward_t :=
  match r with
  | inl (inl z) => inl (inl (inl z))
  | inl (inr p) => inl (inl (inr p))
  | inr v => inl (inr v)
  end.

Definition field2forward (f: field_t): forward_t :=
  match f with
  | inl (inl z) => inl (inl (inl z))
  | inl (inr p) => inl (inl (inr p))
  | inr e => inr e
  end.

Definition forward_p_type: Type := Z + (VType * Z).

Definition forward_p2forward_t
           (p: forward_p_type) (roots: roots_t) (g: LGraph): forward_t :=
  match p with
  | inl root_index => root2forward (Znth root_index roots)
  | inr (v, n) => if (vlabel g v).(raw_mark) && (n =? 0)
                  then (inl (inr (vlabel g v).(copied_vertex)))
                  else field2forward (Znth n (make_fields g v))
  end.

Definition vertex_pos_pairs (g: LGraph) (v: VType) : list (forward_p_type) :=
  map (fun x => inr (v, Z.of_nat x))
      (nat_inc_list (length (raw_fields (vlabel g v)))).

Inductive forward_relation (from to: nat):
  nat -> forward_t -> LGraph -> LGraph -> Prop :=
| fr_z: forall depth z g, forward_relation from to depth (inl (inl (inl z))) g g
| fr_p: forall depth p g, forward_relation from to depth (inl (inl (inr p))) g g
| fr_v_not_in: forall depth v g,
    vgeneration v <> from -> forward_relation from to depth (inl (inr v)) g g
| fr_v_in_forwarded: forall depth v g,
    vgeneration v = from -> (vlabel g v).(raw_mark) = true ->
    forward_relation from to depth (inl (inr v)) g g
| fr_v_in_not_forwarded_O: forall v g,
    vgeneration v = from -> (vlabel g v).(raw_mark) = false ->
    forward_relation from to O (inl (inr v)) g (lgraph_copy_v g v to)
| fr_v_in_not_forwarded_Sn: forall depth v g g',
    vgeneration v = from -> (vlabel g v).(raw_mark) = false ->
    let new_g := lgraph_copy_v g v to in
    forward_loop from to depth (vertex_pos_pairs new_g (new_copied_v g to)) new_g g' ->
    forward_relation from to (S depth) (inl (inr v)) g g'
| fr_e_not_to: forall depth e (g: LGraph),
    vgeneration (dst g e) <> from -> forward_relation from to depth (inr e) g g
| fr_e_to_forwarded: forall depth e (g: LGraph),
    vgeneration (dst g e) = from -> (vlabel g (dst g e)).(raw_mark) = true ->
    let new_g := labeledgraph_gen_dst g e (vlabel g (dst g e)).(copied_vertex) in
    forward_relation from to depth (inr e) g new_g
| fr_e_to_not_forwarded_O: forall e (g: LGraph),
    vgeneration (dst g e) = from -> (vlabel g (dst g e)).(raw_mark) = false ->
    let new_g := labeledgraph_gen_dst (lgraph_copy_v g (dst g e) to) e
                                      (new_copied_v g to) in
    forward_relation from to O (inr e) g new_g
| fr_e_to_not_forwarded_Sn: forall depth e (g g': LGraph),
    vgeneration (dst g e) = from -> (vlabel g (dst g e)).(raw_mark) = false ->
    let new_g := labeledgraph_gen_dst (lgraph_copy_v g (dst g e) to) e
                                      (new_copied_v g to) in
    forward_loop from to depth (vertex_pos_pairs new_g (new_copied_v g to)) new_g g' ->
    forward_relation from to (S depth) (inr e) g g'
with
forward_loop (from to: nat): nat -> list forward_p_type -> LGraph -> LGraph -> Prop :=
| fl_nil: forall depth g, forward_loop from to depth nil g g
| fl_cons: forall depth g1 g2 g3 f fl,
    forward_relation from to depth (forward_p2forward_t f nil g1) g1 g2 ->
    forward_loop from to depth fl g2 g3 -> forward_loop from to depth (f :: fl) g1 g3.

Definition forward_p_compatible
           (p: forward_p_type) (roots: roots_t) (g: LGraph) (from: nat): Prop :=
  match p with
  | inl root_index => 0 <= root_index < Zlength roots
  | inr (v, n) => graph_has_v g v /\ 0 <= n < Zlength (vlabel g v).(raw_fields) /\
                  (vlabel g v).(raw_mark) = false /\ vgeneration v <> from
  end.

Fixpoint collect_Z_indices {A} (eqdec: forall (a b: A), {a = b} + {a <> b})
         (target: A) (l: list A) (ind: Z) : list Z :=
  match l with
  | nil => nil
  | li :: l => if eqdec target li
               then ind :: collect_Z_indices eqdec target l (ind + 1)
               else collect_Z_indices eqdec target l (ind + 1)
  end.

Lemma collect_Z_indices_spec:
  forall {A} {d: Inhabitant A} eqdec (target: A) (l: list A) (ind: Z) c,
    l = skipn (Z.to_nat ind) c -> 0 <= ind ->
    forall j, In j (collect_Z_indices eqdec target l ind) <->
              ind <= j < Zlength c /\ Znth j c = target.
Proof.
  intros. revert ind H H0 j. induction l; intros.
  - simpl. split; intros. 1: exfalso; assumption. pose proof (Zlength_skipn ind c).
    destruct H1. rewrite <- H, Zlength_nil, (Z.max_r _ _ H0) in H2. symmetry in H2.
    rewrite Z.max_l_iff in H2. omega.
  - assert (l = skipn (Z.to_nat (ind + 1)) c). {
      clear -H H0. rewrite Z2Nat.inj_add by omega. simpl Z.to_nat at 2.
      remember (Z.to_nat ind). clear ind Heqn H0.
      replace (n + 1)%nat with (S n) by omega. revert a l c H.
      induction n; intros; simpl in H; destruct c; [inversion H | | inversion H|].
      - simpl. inversion H; reflexivity.
      - apply IHn in H. rewrite H. simpl. destruct c; reflexivity. }
    assert (0 <= ind + 1) by omega. specialize (IHl _ H1 H2). simpl.
    assert (Znth ind c = a). {
      clear -H H0. apply Z2Nat.id in H0. remember (Z.to_nat ind). rewrite <- H0.
      clear ind Heqn H0. revert a l c H.
      induction n; intros; simpl in H; destruct c; [inversion H | | inversion H|].
      - simpl. inversion H. rewrite Znth_0_cons. reflexivity.
      - rewrite Nat2Z.inj_succ, Znth_pos_cons by omega. apply IHn in H.
        replace (Z.succ (Z.of_nat n) - 1) with (Z.of_nat n) by omega.
        assumption. }
    destruct (eqdec target a).
    + simpl. rewrite IHl. clear IHl. split; intros; destruct H4; [|intuition|].
      * subst j. split; [split|]; [omega | | rewrite <- e in H3; assumption].
        pose proof (Zlength_skipn ind c). rewrite <- H in H4.
        rewrite Zlength_cons in H4. pose proof (Zlength_nonneg l).
        destruct (Z.max_spec 0 (Zlength c - Z.max 0 ind)). 2: exfalso; omega.
        destruct H6 as [? _]. rewrite Z.max_r in H6; omega.
      * assert (ind = j \/ ind + 1 <= j < Zlength c) by omega.
        destruct H6; [left | right; split]; assumption.
    + rewrite IHl; split; intros; destruct H4; split;
        [omega | assumption | | assumption].
      assert (ind = j \/ ind + 1 <= j < Zlength c) by omega. clear H4. destruct H6.
      2: assumption. exfalso; subst j. rewrite H5 in H3. rewrite H3 in n.
      apply n; reflexivity.
Qed.

Definition get_indices (index: Z) (live_indices: list Z) :=
  collect_Z_indices Z.eq_dec (Znth index live_indices) live_indices 0.

Definition upd_bunch (index: Z) (f_info: fun_info)
           (roots: roots_t) (v: root_t): roots_t :=
  fold_right (fun i rs => upd_Znth i rs v) roots
             (get_indices index (live_roots_indices f_info)).

Lemma fold_right_upd_Znth_Zlength {A}: forall (l: list Z) (roots: list A) (v: A),
    (forall j, In j l -> 0 <= j < Zlength roots) ->
    Zlength (fold_right (fun (i : Z) (rs : list A) => upd_Znth i rs v) roots l) =
    Zlength roots.
Proof.
  induction l; intros; simpl. 1: reflexivity. rewrite upd_Znth_Zlength.
  - apply IHl. intros. apply H. right. assumption.
  - rewrite IHl; intros; apply H; [left; reflexivity | right; assumption].
Qed.

Lemma get_indices_spec: forall (l: list Z) (z j : Z),
    In j (get_indices z l) <-> 0 <= j < Zlength l /\ Znth j l = Znth z l.
Proof.
  intros. unfold get_indices. remember (Znth z l) as p. clear Heqp z.
  apply collect_Z_indices_spec. 2: omega. rewrite skipn_0. reflexivity.
Qed.

Lemma upd_bunch_Zlength: forall (f_info : fun_info) (roots : roots_t) (z : Z),
    Zlength roots = Zlength (live_roots_indices f_info) ->
    forall r : root_t, Zlength (upd_bunch z f_info roots r) = Zlength roots.
Proof.
  intros. unfold upd_bunch. apply fold_right_upd_Znth_Zlength.
  intros. rewrite H. rewrite get_indices_spec in H0. destruct H0; assumption.
Qed.

Lemma fold_right_upd_Znth_same {A} {d: Inhabitant A}:
  forall (l: list Z) (roots: list A) (v: A),
    (forall j, In j l -> 0 <= j < Zlength roots) ->
    forall j,
      In j l ->
      Znth j (fold_right (fun (i : Z) (rs : list A) => upd_Znth i rs v) roots l) = v.
Proof.
  intros. induction l; simpl in H0. 1: exfalso; assumption.
  assert (Zlength (fold_right (fun (i : Z) (rs : list A) => upd_Znth i rs v) roots l) =
          Zlength roots) by
      (apply fold_right_upd_Znth_Zlength; intros; apply H; right; assumption).
  simpl. destruct H0.
  - subst a. rewrite upd_Znth_same. reflexivity. rewrite H1. apply H.
    left; reflexivity.
  - destruct (Z.eq_dec j a).
    + subst a. rewrite upd_Znth_same. reflexivity. rewrite H1. apply H.
      left; reflexivity.
    + rewrite upd_Znth_diff; [|rewrite H1; apply H; intuition..| assumption].
      apply IHl; [intros; apply H; right |]; assumption.
Qed.

Lemma upd_bunch_same: forall f_info roots z j r,
    0 <= j < Zlength roots ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    Znth j (live_roots_indices f_info) = Znth z (live_roots_indices f_info) ->
    Znth j (upd_bunch z f_info roots r) = r.
Proof.
  intros. unfold upd_bunch. apply fold_right_upd_Znth_same.
  - intros. rewrite get_indices_spec in H2. destruct H2. rewrite H0; assumption.
  - rewrite get_indices_spec. split; [rewrite <- H0|]; assumption.
Qed.

Lemma fold_right_upd_Znth_diff {A} {d: Inhabitant A}:
  forall (l: list Z) (roots: list A) (v: A),
    (forall j, In j l -> 0 <= j < Zlength roots) ->
    forall j,
      ~ In j l -> 0 <= j < Zlength roots ->
      Znth j (fold_right (fun (i : Z) (rs : list A) => upd_Znth i rs v) roots l) =
      Znth j roots.
Proof.
  intros. induction l; simpl. 1: reflexivity.
  assert (Zlength (fold_right (fun (i : Z) (rs : list A) => upd_Znth i rs v) roots l) =
          Zlength roots) by
      (apply fold_right_upd_Znth_Zlength; intros; apply H; right; assumption).
  assert (j <> a) by (intro; apply H0; left; rewrite H3; reflexivity).
  rewrite upd_Znth_diff; [ | rewrite H2.. | assumption];
    [|assumption | apply H; intuition].
  apply IHl; repeat intro; [apply H | apply H0]; right; assumption.
Qed.

Lemma upd_bunch_diff: forall f_info roots z j r,
    0 <= j < Zlength roots ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    Znth j (live_roots_indices f_info) <> Znth z (live_roots_indices f_info) ->
    Znth j (upd_bunch z f_info roots r) = Znth j roots.
Proof.
  intros. unfold upd_bunch. apply fold_right_upd_Znth_diff. 3: assumption.
  - intros. rewrite get_indices_spec in H2. destruct H2. rewrite H0; assumption.
  - rewrite get_indices_spec. intro. destruct H2. apply H1. assumption.
Qed.

Lemma Znth_list_eq {X: Type} {d: Inhabitant X}: forall (l1 l2: list X),
    l1 = l2 <-> (Zlength l1 = Zlength l2 /\
                 forall j, 0 <= j < Zlength l1 -> Znth j l1 = Znth j l2).
Proof.
  induction l1; destruct l2; split; intros.
  - split; intros; reflexivity.
  - reflexivity.
  - inversion H.
  - destruct H. rewrite Zlength_nil, Zlength_cons in H. exfalso; rep_omega.
  - inversion H.
  - destruct H. rewrite Zlength_nil, Zlength_cons in H. exfalso; rep_omega.
  - inversion H. subst a. subst l1. split; intros; reflexivity.
  - destruct H. assert (0 <= 0 < Zlength (a :: l1)) by
        (rewrite Zlength_cons; rep_omega). apply H0 in H1. rewrite !Znth_0_cons in H1.
    subst a. rewrite !Zlength_cons in H. f_equal. rewrite IHl1. split. 1: rep_omega.
    intros. assert (0 < j + 1) by omega.
    assert (0 <= j + 1 < Zlength (x :: l1)) by (rewrite Zlength_cons; rep_omega).
    specialize (H0 _ H3). rewrite !Znth_pos_cons in H0 by assumption.
    replace (j + 1 - 1) with j in H0 by omega. assumption.
Qed.

Lemma upd_thread_info_Zlength: forall (t: thread_info) (i: Z) (v: val),
    0 <= i < MAX_ARGS -> Zlength (upd_Znth i (ti_args t) v) = MAX_ARGS.
Proof.
  intros. rewrite upd_Znth_Zlength; [apply arg_size | rewrite arg_size; assumption].
Qed.

Definition upd_thread_info_arg
           (t: thread_info) (i: Z) (v: val) (H: 0 <= i < MAX_ARGS) : thread_info :=
  Build_thread_info (ti_heap_p t) (ti_heap t) (upd_Znth i (ti_args t) v)
                    (upd_thread_info_Zlength t i v H).

Lemma upd_fun_thread_arg_compatible: forall g t_info f_info roots z,
    fun_thread_arg_compatible g t_info f_info roots ->
    forall (v : VType) (HB : 0 <= Znth z (live_roots_indices f_info) < MAX_ARGS),
      fun_thread_arg_compatible
        g (upd_thread_info_arg t_info (Znth z (live_roots_indices f_info))
                               (vertex_address g v) HB) f_info
        (upd_bunch z f_info roots (inr v)).
Proof.
  intros. red in H |-* . unfold upd_thread_info_arg. simpl. rewrite Znth_list_eq in H.
  destruct H. rewrite !Zlength_map in H. rewrite Zlength_map in H0.
  assert (Zlength (upd_bunch z f_info roots (inr v)) = Zlength roots) by
      (rewrite upd_bunch_Zlength; [reflexivity | assumption]).
  rewrite Znth_list_eq. split. 1: rewrite !Zlength_map, H1; assumption. intros.
  rewrite Zlength_map, H1 in H2.
  rewrite !Znth_map; [|rewrite <- H | rewrite H1]; [|assumption..].
  specialize (H0 _ H2). rewrite !Znth_map in H0; [|rewrite <- H| ]; [|assumption..].
  unfold flip in *.
  destruct (Z.eq_dec (Znth j (live_roots_indices f_info))
                     (Znth z (live_roots_indices f_info))).
  - rewrite e, upd_Znth_same. 2: rewrite arg_size; rep_omega.
    rewrite upd_bunch_same; [|assumption..]. reflexivity.
  - rewrite upd_Znth_diff. 4: assumption. 3: rewrite arg_size; rep_omega.
    + rewrite <- H0. rewrite upd_bunch_diff; [|assumption..]. reflexivity.
    + rewrite arg_size. apply (fi_index_range f_info), Znth_In.
      rewrite <- H. assumption.
Qed.

Lemma In_Znth {A} {d: Inhabitant A}: forall (e: A) l,
    In e l -> exists i, 0 <= i < Zlength l /\ Znth i l = e.
Proof.
  intros. apply In_nth with (d := d) in H. destruct H as [n [? ?]].
  exists (Z.of_nat n). assert (0 <= Z.of_nat n < Zlength l) by
      (rewrite Zlength_correct; omega). split. 1: assumption.
  rewrite <- nth_Znth by assumption. rewrite Nat2Z.id. assumption.
Qed.

Lemma upd_Znth_In {A}: forall (e: A) l i v, In v (upd_Znth i l e) -> In v l \/ v = e.
Proof.
  intros. unfold upd_Znth in H. rewrite in_app_iff in H. simpl in H.
  destruct H as [? | [? | ?]]; [|right; rewrite H; reflexivity|];
    apply sublist_In in H; left; assumption.
Qed.

Lemma fold_right_upd_Znth_In {A}: forall (l: list Z) (roots: list A) (v: A) e,
      In e (fold_right (fun (i : Z) (rs : list A) => upd_Znth i rs v) roots l) ->
      In e roots \/ e = v.
Proof.
  induction l; intros; simpl in H. 1: left; assumption.
  apply upd_Znth_In in H. destruct H; [apply IHl | right]; assumption.
Qed.

Lemma upd_roots_outlier_compatible: forall f_info roots outlier z v,
    roots_outlier_compatible roots outlier ->
    (* forall v : VType, *)
    (*   graph_has_v g v -> *)
    roots_outlier_compatible (upd_bunch z f_info roots (inr v)) outlier.
Proof.
  intros. do 2 red in H |-* . intros.
  rewrite <- filter_sum_right_In_iff, <- filter_sum_left_In_iff in H0.
  unfold upd_bunch in H0. apply fold_right_upd_Znth_In in H0. destruct H0.
  2: inversion H0. apply H.
  rewrite <- filter_sum_right_In_iff, <- filter_sum_left_In_iff. assumption.
Qed.

Lemma upd_bunch_graph_compatible: forall g f_info roots z,
    roots_graph_compatible roots g ->
    forall v : VType,
      graph_has_v g v ->
      roots_graph_compatible (upd_bunch z f_info roots (inr v)) g.
Proof.
  intros. red in H |-* . rewrite Forall_forall in H |-* . intros.
  rewrite <- filter_sum_right_In_iff in H1. unfold upd_bunch in H1.
  apply fold_right_upd_Znth_In in H1. destruct H1. 2: inversion H1; assumption.
  apply H. rewrite <- filter_sum_right_In_iff. assumption.
Qed.

Lemma upd_roots_compatible: forall g f_info roots outlier z,
    roots_compatible g outlier roots ->
    forall v : VType, graph_has_v g v ->
                      roots_compatible g outlier (upd_bunch z f_info roots (inr v)).
Proof.
  intros. destruct H. split.
  - apply upd_roots_outlier_compatible; assumption.
  - apply upd_bunch_graph_compatible; assumption.
Qed.

Local Close Scope Z_scope.

Definition upd_roots (from to: nat) (forward_p: forward_p_type)
           (g: LGraph) (roots: roots_t) (f_info: fun_info): roots_t :=
  match forward_p with
  | inr _ => roots
  | inl index => match Znth index roots with
                 | inl (inl z) => roots
                 | inl (inr p) => roots
                 | inr v => if Nat.eq_dec (vgeneration v) from
                            then if (vlabel g v).(raw_mark)
                                 then upd_bunch index f_info roots
                                                (inr (vlabel g v).(copied_vertex))
                                 else upd_bunch index f_info roots
                                                (inr (new_copied_v g to))
                            else roots
                 end
  end.

Inductive forward_roots_loop (from to: nat) (f_info: fun_info):
  list nat -> roots_t -> LGraph -> roots_t -> LGraph -> Prop :=
| frl_nil: forall g roots, forward_roots_loop from to f_info nil roots g roots g
| frl_cons: forall g1 g2 g3 i il roots1 roots3,
    forward_relation from to O (root2forward (Znth (Z.of_nat i) roots1)) g1 g2 ->
    forward_roots_loop from to f_info il
                       (upd_roots from to (inl (Z.of_nat i)) g1 roots1 f_info)
                       g2 roots3 g3 ->
    forward_roots_loop from to f_info (i :: il) roots1 g1 roots3 g3.

Definition forward_roots_relation from to f_info roots1 g1 roots2 g2 :=
  forward_roots_loop from to f_info (nat_inc_list (length roots1)) roots1 g1 roots2 g2.

Definition nth_space (t_info: thread_info) (n: nat): space :=
  nth n t_info.(ti_heap).(spaces) null_space.

Lemma nth_space_Znth: forall t n,
    nth_space t n = Znth (Z.of_nat n) (spaces (ti_heap t)).
Proof.
  intros. unfold nth_space, Znth. rewrite if_false. 2: omega.
  rewrite Nat2Z.id. reflexivity.
Qed.

Definition gen_size t_info n := total_space (nth_space t_info n).

Lemma gsc_iff: forall (g: LGraph) t_info,
    length (g_gen (glabel g)) <= length (spaces (ti_heap t_info)) ->
    Forall (generation_space_compatible g)
           (combine (combine (nat_inc_list (length (g_gen (glabel g))))
                             (g_gen (glabel g))) (spaces (ti_heap t_info))) <->
    forall gen,
      graph_has_gen g gen ->
      generation_space_compatible g (gen, nth_gen g gen, nth_space t_info gen).
Proof.
  intros. rewrite Forall_forall. remember (g_gen (glabel g)).
  remember (nat_inc_list (length l)). remember (spaces (ti_heap t_info)).
  assert (length (combine l0 l) = length l) by
      (subst; rewrite combine_length, nat_inc_list_length, Nat.min_id; reflexivity).
  assert (length (combine (combine l0 l) l1) = length l) by
      (rewrite combine_length, H0, min_l by assumption; reflexivity).
  cut (forall x, In x (combine (combine l0 l) l1) <->
                    exists gen, graph_has_gen g gen /\
                                x = (gen, nth_gen g gen, nth_space t_info gen)).
  - intros. split; intros.
    + apply H3. rewrite H2. exists gen. intuition.
    + rewrite H2 in H4. destruct H4 as [gen [? ?]]. subst x. apply H3. assumption.
  - intros.
    assert (forall gen,
               graph_has_gen g gen ->
               nth gen (combine (combine l0 l) l1) (0, null_info, null_space) =
               (gen, nth_gen g gen, nth_space t_info gen)). {
      intros. red in H2. rewrite <- Heql in H2.
      rewrite combine_nth_lt; [|rewrite H0; omega | omega].
      rewrite combine_nth by (subst l0; rewrite nat_inc_list_length; reflexivity).
      rewrite Heql0. rewrite nat_inc_list_nth by assumption.
      rewrite Heql. unfold nth_gen, nth_space. rewrite Heql1. reflexivity. }
    split; intros.
    + apply (In_nth (combine (combine l0 l) l1) x (O, null_info, null_space)) in H3.
      destruct H3 as [gen [? ?]]. exists gen. rewrite H1 in H3.
      assert (graph_has_gen g gen) by (subst l; assumption). split. 1: assumption.
      rewrite H2 in H4 by assumption. subst x. reflexivity.
    + destruct H3 as [gen [? ?]]. rewrite <- H2 in H4 by assumption. subst x.
      apply nth_In. rewrite H1. subst l. assumption.
Qed.

Lemma gt_gs_compatible:
  forall (g: LGraph) (t_info: thread_info),
    graph_thread_info_compatible g t_info ->
    forall gen,
      graph_has_gen g gen ->
      generation_space_compatible g (gen, nth_gen g gen, nth_space t_info gen).
Proof.
  intros. destruct H as [? [_ ?]]. rewrite gsc_iff in H by assumption.
  apply H. assumption.
Qed.

Lemma pvs_mono_strict: forall g gen i j,
    i < j -> (previous_vertices_size g gen i < previous_vertices_size g gen j)%Z.
Proof.
  intros. assert (j = i + (j - i)) by omega. rewrite H0. remember (j - i). subst j.
  unfold previous_vertices_size. rewrite nat_inc_list_app, fold_left_app.
  apply vs_accum_list_lt. pose proof (nat_seq_length i n). destruct (nat_seq i n).
  - simpl in H0. omega.
  - intro S; inversion S.
Qed.

Lemma pvs_mono: forall g gen i j,
    i <= j -> (previous_vertices_size g gen i <= previous_vertices_size g gen j)%Z.
Proof.
  intros. rewrite Nat.le_lteq in H. destruct H. 2: subst; omega.
  rewrite Z.le_lteq. left. apply pvs_mono_strict. assumption.
Qed.

Lemma pvs_lt_rev: forall g gen i j,
    (previous_vertices_size g gen i < previous_vertices_size g gen j)%Z -> i < j.
Proof.
  intros. destruct (le_lt_dec j i).
  - apply (pvs_mono g gen) in l. exfalso. omega.
  - assumption.
Qed.

Local Open Scope Z_scope.

Definition forward_roots_compatible
           (from to: nat) (g: LGraph) (ti : thread_info): Prop :=
  (nth_space ti from).(used_space) <= (nth_space ti to).(total_space) -
                                      (nth_space ti to).(used_space).

Lemma vo_lt_gs: forall g v,
    gen_has_index g (vgeneration v) (vindex v) ->
    vertex_offset g v < graph_gen_size g (vgeneration v).
Proof.
  intros. unfold vertex_offset, graph_gen_size. red in H.
  remember (number_of_vertices (nth_gen g (vgeneration v))). remember (vgeneration v).
  assert (S (vindex v) <= n)%nat by omega.
  apply Z.lt_le_trans with (previous_vertices_size g n0 (S (vindex v))).
  - rewrite pvs_S. apply Zplus_lt_compat_l, svs_gt_one.
  - apply pvs_mono; assumption.
Qed.

Definition v_in_range (v: val) (start: val) (n: Z): Prop :=
  exists i, 0 <= i < n /\ v = offset_val i start.

Lemma graph_thread_v_in_range: forall g t_info v,
    graph_thread_info_compatible g t_info -> graph_has_v g v ->
    v_in_range (vertex_address g v) (gen_start g (vgeneration v))
               (WORD_SIZE * gen_size t_info (vgeneration v)).
Proof.
  intros. red. unfold vertex_address. exists (WORD_SIZE * vertex_offset g v).
  split. 2: reflexivity. unfold gen_size. destruct H0. remember (vgeneration v). split.
  - unfold vertex_offset.
    pose proof (pvs_ge_zero g (vgeneration v) (vindex v)). rep_omega.
  - apply Zmult_lt_compat_l. 1: rep_omega.
    apply Z.lt_le_trans with (used_space (nth_space t_info n)).
    2: apply (proj2 (space_order (nth_space t_info n))).
    destruct (gt_gs_compatible _ _ H _ H0) as [? [? ?]].
    rewrite <- H4, Heqn. apply vo_lt_gs. subst n. assumption.
Qed.

Definition nth_sh g gen := generation_sh (nth_gen g gen).

Lemma reset_nth_sh_diff: forall g i j,
    i <> j -> nth_sh (reset_graph j g) i = nth_sh g i.
Proof. intros. unfold nth_sh. rewrite reset_nth_gen_diff; auto. Qed.

Lemma reset_nth_sh: forall g i j,
    nth_sh (reset_graph j g) i = nth_sh g i.
Proof.
  intros. destruct (Nat.eq_dec i j).
  - subst. unfold reset_graph, nth_sh, nth_gen. simpl.
    rewrite reset_nth_gen_info_same, remove_ve_glabel_unchanged. reflexivity.
  - apply reset_nth_sh_diff. assumption.
Qed.

Lemma Znth_tl {A} {d: Inhabitant A}: forall (l: list A) i,
    0 <= i -> Znth i (tl l) = Znth (i + 1) l.
Proof.
  intros. destruct l; simpl.
  - unfold Znth; if_tac; if_tac; try omega; destruct (Z.to_nat (i + 1));
      destruct (Z.to_nat i); simpl; reflexivity.
  - rewrite Znth_pos_cons by omega. replace (i + 1 - 1) with i by omega. reflexivity.
Qed.

Definition unmarked_gen_size (g: LGraph) (gen: nat) :=
  fold_left (vertex_size_accum g gen)
            (filter (fun i => negb (vlabel g (gen, i)).(raw_mark))
                    (nat_inc_list (number_of_vertices (nth_gen g gen)))) 0.

Lemma unmarked_gen_size_le: forall g n, unmarked_gen_size g n <= graph_gen_size g n.
Proof.
  intros g gen. unfold unmarked_gen_size, graph_gen_size, previous_vertices_size.
  apply fold_left_mono_filter;
    [intros; rewrite Z.le_lteq; left; apply vsa_mono | apply vsa_comm].
Qed.

Lemma single_unmarked_le: forall g v,
    graph_has_v g v -> raw_mark (vlabel g v) = false ->
    vertex_size g v <= unmarked_gen_size g (vgeneration v).
Proof.
  intros. unfold unmarked_gen_size.
  remember (filter (fun i : nat => negb (raw_mark (vlabel g (vgeneration v, i))))
                   (nat_inc_list (number_of_vertices (nth_gen g (vgeneration v))))).
  assert (In (vindex v) l). {
    subst l. rewrite filter_In. split.
    - rewrite nat_inc_list_In_iff. apply (proj2 H).
    - destruct v; simpl. rewrite negb_true_iff. apply H0. }
  apply In_Permutation_cons in H1. destruct H1 as [l1 ?]. symmetry in H1.
  change (vindex v :: l1) with ([vindex v] ++ l1) in H1.
  transitivity (fold_left (vertex_size_accum g (vgeneration v)) [vindex v] 0).
  - simpl. destruct v; simpl. apply Z.le_refl.
  - apply (fold_left_Z_mono (vertex_size_accum g (vgeneration v)) [vindex v] l1 l 0);
      [intros; apply Z.le_lteq; left; apply vsa_mono | apply vsa_comm | apply H1].
Qed.

Definition rest_gen_size (t_info: thread_info) (gen: nat): Z :=
  total_space (nth_space t_info gen) - used_space (nth_space t_info gen).

Definition enough_space_to_copy g t_info from to: Prop :=
  unmarked_gen_size g from <= rest_gen_size t_info to.

Definition no_dangling_dst (g: LGraph): Prop :=
  forall v, graph_has_v g v ->
            forall e, In e (get_edges g v) -> graph_has_v g (dst g e).

Definition forward_condition g t_info from to: Prop :=
  enough_space_to_copy g t_info from to /\
  graph_has_gen g from /\ graph_has_gen g to /\
  copy_compatible g /\ no_dangling_dst g.

Definition has_space (sp: space) (s: Z): Prop :=
  0 <= s <= total_space sp - used_space sp.

Lemma cut_space_order: forall (sp : space) (s : Z),
    has_space sp s -> 0 <= used_space sp + s <= total_space sp.
Proof. intros. pose proof (space_order sp). red in H. omega. Qed.

Definition cut_space (sp: space) (s: Z) (H: has_space sp s): space :=
  Build_space (space_start sp) (used_space sp + s) (total_space sp)
              (space_sh sp) (cut_space_order sp s H) (space_upper_bound sp).

Lemma cut_heap_size:
  forall (h : heap) (i s : Z) (H : has_space (Znth i (spaces h)) s),
    0 <= i < Zlength (spaces h) ->
    Zlength (upd_Znth i (spaces h) (cut_space (Znth i (spaces h)) s H)) = MAX_SPACES.
Proof. intros. rewrite upd_Znth_Zlength; [apply spaces_size | assumption]. Qed.

Definition cut_heap (h: heap) (i s: Z) (H1: 0 <= i < Zlength (spaces h))
           (H2: has_space (Znth i (spaces h)) s): heap :=
  Build_heap (upd_Znth i (spaces h) (cut_space (Znth i (spaces h)) s H2))
             (cut_heap_size h i s H2 H1).

Lemma heap_head_cut_thread_info: forall
    h i s (H1: 0 <= i < Zlength (spaces h)) (H2: has_space (Znth i (spaces h)) s),
    i <> 0 -> heap_head (cut_heap h i s H1 H2) = heap_head h.
Proof.
  intros. destruct (heap_head_cons h) as [hs1 [l1 [? ?]]].
  destruct (heap_head_cons (cut_heap h i s H1 H2)) as [hs2 [l2 [? ?]]].
  rewrite H3, H5. simpl in H4.
  pose proof (split3_full_length_list
                0 i _ _ H1 (Zminus_0_l_reverse (Zlength (spaces h)))).
  replace (i - 0) with i in H6 by omega. simpl in H6.
  remember (firstn (Z.to_nat i) (spaces h)) as ls1.
  remember (skipn (Z.to_nat (i + 1)) (spaces h)) as ls2.
  assert (Zlength ls1 = i). {
    rewrite Zlength_length by omega. subst ls1. apply firstn_length_le.
    clear H5. rewrite Zlength_correct in H1. rep_omega. }
  rewrite H6 in H4 at 1. rewrite (upd_Znth_char _ _ _ _ _ H7) in H4.
  rewrite H6 in H0. clear -H0 H4 H H7. destruct ls1.
  - rewrite Zlength_nil in H7. exfalso. apply H. subst i. reflexivity.
  - simpl in H0, H4. inversion H0. subst hs1. inversion H4. reflexivity.
Qed.

Definition cut_thread_info (t: thread_info) (i s: Z)
           (H1: 0 <= i < Zlength (spaces (ti_heap t)))
           (H2: has_space (Znth i (spaces (ti_heap t))) s) : thread_info :=
  Build_thread_info (ti_heap_p t) (cut_heap (ti_heap t) i s H1 H2) (ti_args t)
                    (arg_size t).

Lemma cti_eq: forall t i s1 s2 (H1: 0 <= i < Zlength (spaces (ti_heap t)))
                     (Hs1: has_space (Znth i (spaces (ti_heap t))) s1)
                     (Hs2: has_space (Znth i (spaces (ti_heap t))) s2),
    s1 = s2 -> cut_thread_info t i s1 H1 Hs1 = cut_thread_info t i s2 H1 Hs2.
Proof.
  intros. unfold cut_thread_info. f_equal. subst s1. f_equal. apply proof_irr.
Qed.

Lemma upd_Znth_tl {A}: forall (i: Z) (l: list A) (x: A),
    0 <= i -> l <> nil -> tl (upd_Znth (i + 1) l x) = upd_Znth i (tl l) x.
Proof.
  intros. destruct l; simpl. 1: contradiction.
  unfold upd_Znth. unfold sublist. replace (i - 0) with i by omega.
  replace (i + 1 - 0) with (i + 1) by omega. simpl.
  assert (forall j, 0 <= j -> Z.to_nat (j + 1) = S (Z.to_nat j)) by
      (intros; rewrite <- Z2Nat.inj_succ; rep_omega).
  rewrite (H1 _ H). simpl tl. do 3 f_equal.
  - f_equal. rewrite Zlength_cons. omega.
  - remember (S (Z.to_nat i)). replace (Z.to_nat (i + 1 + 1)) with (S n).
    + simpl. reflexivity.
    + do 2 rewrite H1 by omega. subst n. reflexivity.
Qed.

Lemma isptr_is_pointer_or_integer: forall p, isptr p -> is_pointer_or_integer p.
Proof. intros. destruct p; try contradiction. exact I. Qed.

Lemma mfv_unmarked_all_is_ptr_or_int: forall (g : LGraph) (v : VType),
    no_dangling_dst g -> graph_has_v g v ->
    Forall is_pointer_or_integer (map (field2val g) (make_fields g v)).
Proof.
  intros. rewrite Forall_forall. intros f ?. apply list_in_map_inv in H1.
  destruct H1 as [x [? ?]]. destruct x as [[? | ?] | ?]; simpl in H1; subst.
  - unfold odd_Z2val. exact I.
  - destruct g0. exact I.
  - apply isptr_is_pointer_or_integer. unfold vertex_address.
    rewrite isptr_offset_val. apply graph_has_gen_start_isptr.
    apply filter_sum_right_In_iff, H in H2; [destruct H2|]; assumption.
Qed.

Lemma mfv_all_is_ptr_or_int: forall g v,
    copy_compatible g -> no_dangling_dst g -> graph_has_v g v ->
    Forall is_pointer_or_integer (make_fields_vals g v).
Proof.
  intros. rewrite Forall_forall. intros f ?. unfold make_fields_vals in H2.
  pose proof (mfv_unmarked_all_is_ptr_or_int _ _ H0 H1). rewrite Forall_forall in H3.
  specialize (H3 f). destruct (raw_mark (vlabel g v)) eqn:? . 2: apply H3; assumption.
  simpl in H2. destruct H2. 2: apply H3, In_tail; assumption.
  subst f. unfold vertex_address. apply isptr_is_pointer_or_integer.
  rewrite isptr_offset_val. apply graph_has_gen_start_isptr, (proj1 (H _ H1 Heqb)).
Qed.

Lemma upd_tf_arg_Zlength: forall (t: thread_info) (index: Z) (v: val),
    0 <= index < MAX_ARGS -> Zlength (upd_Znth index (ti_args t) v) = MAX_ARGS.
Proof.
  intros. rewrite upd_Znth_Zlength; [apply arg_size | rewrite arg_size; assumption].
Qed.

Definition update_thread_info_arg (t: thread_info) (index: Z)
           (v: val) (H: 0 <= index < MAX_ARGS): thread_info :=
  Build_thread_info (ti_heap_p t) (ti_heap t) (upd_Znth index (ti_args t) v)
                    (upd_tf_arg_Zlength t index v H).

Local Close Scope Z_scope.

Lemma cvmgil_length: forall l to,
    to < length l -> length (copy_v_mod_gen_info_list l to) = length l.
Proof.
  intros. unfold copy_v_mod_gen_info_list. rewrite app_length. simpl.
  rewrite firstn_length_le by omega. rewrite skipn_length. omega.
Qed.

Lemma cvmgil_not_eq: forall to n l,
    n <> to -> to < length l ->
    nth n (copy_v_mod_gen_info_list l to) null_info = nth n l null_info.
Proof.
  intros. unfold copy_v_mod_gen_info_list.
  assert (length (firstn to l) = to) by (rewrite firstn_length_le; omega).
  destruct (Nat.lt_ge_cases n to).
  - rewrite app_nth1 by omega. apply nth_firstn. assumption.
  - rewrite Nat.lt_eq_cases in H2. destruct H2. 2: exfalso; intuition.
    rewrite <- (firstn_skipn (to + 1) l) at 4. rewrite app_cons_assoc, !app_nth2.
    + do 2 f_equal. rewrite app_length, H1, firstn_length_le by omega. reflexivity.
    + rewrite firstn_length_le; omega.
    + rewrite app_length, H1. simpl. omega.
Qed.

Lemma cvmgil_eq: forall to l,
    to < length l -> nth to (copy_v_mod_gen_info_list l to) null_info =
                     copy_v_mod_gen_info (nth to l null_info).
Proof.
  intros. unfold copy_v_mod_gen_info_list.
  assert (length (firstn to l) = to) by (rewrite firstn_length_le; omega).
  rewrite app_nth2 by omega. rewrite H0. replace (to - to) with O by omega.
  simpl. reflexivity.
Qed.

Lemma lacv_nth_gen: forall g v to n,
    n <> to -> graph_has_gen g to ->
    nth_gen (lgraph_add_copied_v g v to) n = nth_gen g n.
Proof.
  intros. unfold lgraph_add_copied_v, nth_gen. simpl. remember (g_gen (glabel g)).
  apply cvmgil_not_eq; [|subst l]; assumption.
Qed.

Lemma lacv_graph_has_gen: forall g v to n,
    graph_has_gen g to ->
    graph_has_gen (lgraph_add_copied_v g v to) n <-> graph_has_gen g n.
Proof.
  intros. unfold graph_has_gen. simpl.
  rewrite cvmgil_length by assumption. reflexivity.
Qed.

Lemma lacv_gen_start: forall g v to n,
    graph_has_gen g to -> gen_start (lgraph_add_copied_v g v to) n = gen_start g n.
Proof.
  intros. unfold gen_start. do 2 if_tac.
  - destruct (Nat.eq_dec n to).
    + subst n. unfold nth_gen. simpl. rewrite cvmgil_eq by assumption.
      simpl. reflexivity.
    + rewrite lacv_nth_gen by assumption. reflexivity.
  - rewrite lacv_graph_has_gen in H0 by assumption. contradiction.
  - exfalso. apply H0. rewrite lacv_graph_has_gen; assumption.
  - reflexivity.
Qed.

Lemma lacv_vlabel_old: forall (g : LGraph) (v : VType) (to: nat) x,
    x <> new_copied_v g to -> vlabel (lgraph_add_copied_v g v to) x = vlabel g x.
Proof.
  intros. simpl.
  unfold update_copied_new_vlabel, graph_gen.update_vlabel.
  rewrite if_false. 1: reflexivity. unfold Equivalence.equiv; intro S; apply H.
  inversion S; reflexivity.
Qed.

Definition closure_has_index (g: LGraph) (gen index: nat) :=
  index <= number_of_vertices (nth_gen g gen).

Definition closure_has_v (g: LGraph) (v: VType): Prop :=
  graph_has_gen g (vgeneration v) /\ closure_has_index g (vgeneration v) (vindex v).

Lemma lacv_vertex_address: forall (g : LGraph) (v : VType) (to: nat) x,
    closure_has_v g x -> graph_has_gen g to ->
    vertex_address (lgraph_add_copied_v g v to) x = vertex_address g x.
Proof.
  intros. destruct x as [n m]. destruct H. simpl in *. unfold vertex_address. f_equal.
  - f_equal. unfold vertex_offset. f_equal. unfold previous_vertices_size.
    simpl. apply fold_left_ext. intros. unfold vertex_size_accum. f_equal.
    unfold vertex_size. f_equal. rewrite lacv_vlabel_old. 1: reflexivity.
    intro. unfold new_copied_v in H3. inversion H3.
    rewrite nat_inc_list_In_iff in H2. subst n. red in H1. omega.
  - simpl. apply lacv_gen_start. assumption.
Qed.

Lemma graph_has_v_in_closure: forall g v, graph_has_v g v -> closure_has_v g v.
Proof.
  intros g v. destruct v as [gen index].
  unfold graph_has_v, closure_has_v, closure_has_index, gen_has_index.
  simpl. intros. intuition.
Qed.

Lemma lacv_vertex_address_old: forall (g : LGraph) (v : VType) (to: nat) x,
    graph_has_v g x -> graph_has_gen g to ->
    vertex_address (lgraph_add_copied_v g v to) x = vertex_address g x.
Proof.
  intros. apply lacv_vertex_address; [apply graph_has_v_in_closure |]; assumption.
Qed.

Lemma lacv_vertex_address_new: forall (g : LGraph) (v : VType) (to: nat),
    graph_has_gen g to ->
    vertex_address (lgraph_add_copied_v g v to) (new_copied_v g to) =
    vertex_address g (new_copied_v g to).
Proof.
  intros. unfold new_copied_v. apply lacv_vertex_address. 2: assumption.
  red. simpl.  split; [assumption | apply Nat.le_refl].
Qed.

Lemma lacv_make_header_old: forall (g : LGraph) (v : VType) (to : nat) x,
    x <> new_copied_v g to ->
    make_header (lgraph_add_copied_v g v to) x = make_header g x.
Proof.
  intros. unfold make_header. rewrite lacv_vlabel_old by assumption. reflexivity.
Qed.

Lemma e_in_make_fields': forall l v n e,
    In (inr e) (make_fields' l v n) -> exists s, e = (v, s).
Proof.
  induction l; intros; simpl in *. 1: exfalso; assumption. destruct a; [destruct s|].
  - simpl in H. destruct H. 1: inversion H. apply IHl with (n + 1). assumption.
  - simpl in H. destruct H. 1: inversion H. apply IHl with (n + 1). assumption.
  - simpl in H. destruct H.
    + inversion H. exists n. reflexivity.
    + apply IHl with (n + 1). assumption.
Qed.

Lemma flcvae_dst_old: forall g new (l: list (EType * VType)) e,
    ~ In e (map fst l) -> dst (fold_left (copy_v_add_edge new) l g) e = dst g e.
Proof.
  intros. revert g H. induction l; intros; simpl. 1: reflexivity.
  rewrite IHl. 2: intro; apply H; simpl; right; assumption. simpl.
  unfold updateEdgeFunc. rewrite if_false. 1: reflexivity. unfold equiv. intro.
  apply H. simpl. left; assumption.
Qed.

Lemma flcvae_dst_new: forall g new (l: list (EType * VType)) e v,
    NoDup (map fst l) -> In (e, v) l ->
    dst (fold_left (copy_v_add_edge new) l g) e = v.
Proof.
  intros. revert g. induction l. 1: simpl in H; exfalso; assumption.
  intros. simpl in *. destruct H0.
  - subst a. rewrite flcvae_dst_old.
    + simpl. unfold updateEdgeFunc. rewrite if_true; reflexivity.
    + simpl in H. apply NoDup_cons_2 in H. assumption.
  - apply IHl; [apply NoDup_cons_1 in H|]; assumption.
Qed.

Lemma pcv_dst_old: forall g old new e,
    fst e <> new -> dst (pregraph_copy_v g old new) e = dst g e.
Proof.
  intros. unfold pregraph_copy_v. rewrite flcvae_dst_old. 1: simpl; reflexivity.
  intro. apply H. rewrite map_fst_combine in H0.
  - destruct e. simpl in *. apply in_combine_l, repeat_spec in H0. assumption.
  - unfold EType. rewrite combine_length, repeat_length, !map_length, Nat.min_id.
    reflexivity.
Qed.

Lemma pcv_dst_new: forall g old new n,
    In n (map snd (get_edges g old)) ->
    dst (pregraph_copy_v g old new) (new, n) = dst g (old, n).
Proof.
  intros. unfold pregraph_copy_v. rewrite flcvae_dst_new with (v := dst g (old, n)).
  - reflexivity.
  - rewrite map_fst_combine.
    + apply NoDup_combine_r. clear H. unfold get_edges. unfold make_fields.
      remember (raw_fields (vlabel g old)). clear Heql. remember 0 as m. clear Heqm.
      revert m. induction l; intros. simpl. 1: constructor.
      simpl. destruct a; [destruct s|]; simpl; try apply IHl. constructor.
      2: apply IHl. clear.
      cut (forall a b,
              In a (map snd (filter_sum_right (make_fields' l old b))) -> b <= a).
      * repeat intro. apply H in H0. omega.
      * induction l; intros; simpl in H. 1: exfalso; assumption.
        destruct a; [destruct s|]; simpl in H; try (apply IHl in H; omega).
        destruct H; [|apply IHl in H]; omega.
    + unfold EType. rewrite combine_length, repeat_length, !map_length, Nat.min_id.
      reflexivity.
  - apply list_in_map_inv in H. destruct H as [[x ?] [? ?]]. simpl in H. subst n0.
    assert (x = old). {
      unfold get_edges in H0. rewrite <- filter_sum_right_In_iff in H0.
      unfold make_fields in H0. apply e_in_make_fields' in H0. destruct H0 as [s ?].
      inversion H. reflexivity. } subst x. remember (get_edges g old). clear Heql.
    induction l; simpl in *. 1: assumption. destruct H0.
    + subst a. simpl. left; reflexivity.
    + right. apply IHl. assumption.
Qed.

Lemma graph_has_v_not_eq: forall g to x,
    graph_has_v g x -> x <> new_copied_v g to.
Proof.
  intros. destruct H. unfold new_copied_v. destruct x as [gen idx]. simpl in *.
  destruct (Nat.eq_dec gen to).
  - subst gen. intro S; inversion S. red in H0. omega.
  - intro S; inversion S. apply n; assumption.
Qed.

Lemma lacv_make_fields_not_eq: forall (g : LGraph) (v : VType) (to : nat) x,
    x <> new_copied_v g to ->
    make_fields (lgraph_add_copied_v g v to) x = make_fields g x.
Proof.
  intros. unfold make_fields. simpl. unfold update_copied_new_vlabel, update_vlabel.
  rewrite if_false. 1: reflexivity. intuition.
Qed.

Lemma lacv_field2val_make_fields_old:  forall (g : LGraph) (v : VType) (to : nat) x,
    graph_has_v g x -> graph_has_gen g to -> no_dangling_dst g ->
    map (field2val (lgraph_add_copied_v g v to))
        (make_fields (lgraph_add_copied_v g v to) x) =
    map (field2val g) (make_fields g x).
Proof.
  intros. unfold make_fields. pose proof (graph_has_v_not_eq _ to _ H).
  rewrite lacv_vlabel_old by assumption. apply map_ext_in.
  intros [[? | ?] | ?] ?; simpl; try reflexivity. unfold new_copied_v.
  rewrite pcv_dst_old.
  - apply lacv_vertex_address_old. 2: assumption. specialize (H1 _ H). apply H1.
    unfold get_edges. rewrite <- filter_sum_right_In_iff. assumption.
  - apply e_in_make_fields' in H3. destruct H3 as [s ?]. subst e. simpl. intro.
    unfold new_copied_v in H2. contradiction.
Qed.

Lemma lacv_make_fields_vals_old: forall (g : LGraph) (v : VType) (to: nat) x,
    graph_has_v g x -> graph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    make_fields_vals (lgraph_add_copied_v g v to) x = make_fields_vals g x.
Proof.
  intros. pose proof (lacv_field2val_make_fields_old _ v _ _ H H0 H1).
  unfold make_fields_vals. pose proof (graph_has_v_not_eq g to x H).
  rewrite lacv_vlabel_old by assumption. rewrite H3.
  destruct (raw_mark (vlabel g x)) eqn:? ; [f_equal | reflexivity].
  apply lacv_vertex_address_old; [apply H2|]; assumption.
Qed.

Lemma lacv_nth_sh: forall (g : LGraph) (v : VType) (to : nat) n,
    graph_has_gen g to -> nth_sh (lgraph_add_copied_v g v to) n = nth_sh g n.
Proof.
  intros. unfold nth_sh, nth_gen. simpl. destruct (Nat.eq_dec n to).
  - subst n. rewrite cvmgil_eq by assumption. simpl. reflexivity.
  - rewrite cvmgil_not_eq by assumption. reflexivity.
Qed.

Lemma lacv_vlabel_new: forall g v to,
    vlabel (lgraph_add_copied_v g v to) (new_copied_v g to) = vlabel g v.
Proof.
  intros. simpl. unfold update_copied_new_vlabel, graph_gen.update_vlabel.
  rewrite if_true; reflexivity.
Qed.

Lemma lacv_make_header_new: forall g v to,
    make_header (lgraph_add_copied_v g v to) (new_copied_v g to) = make_header g v.
Proof. intros. unfold make_header. rewrite lacv_vlabel_new. reflexivity. Qed.

Lemma lacv_field2val_make_fields_new: forall g v to,
    graph_has_v g v -> graph_has_gen g to -> no_dangling_dst g ->
    map (field2val (lgraph_add_copied_v g v to))
        (make_fields (lgraph_add_copied_v g v to) (new_copied_v g to)) =
    map (field2val g) (make_fields g v).
Proof.
  intros. unfold make_fields. rewrite lacv_vlabel_new.
  remember (raw_fields (vlabel g v)). remember 0 as n.
  assert (forall m, In m (map snd (filter_sum_right (make_fields' l v n))) ->
                    In m (map snd (get_edges g v))). {
    unfold get_edges, make_fields. subst. intuition. }
  clear Heql Heqn. revert n H2. induction l; intros; simpl. 1: reflexivity.
  destruct a; [destruct s|].
  - simpl in *. rewrite IHl; [reflexivity | assumption].
  - simpl in *. rewrite IHl; [reflexivity | assumption].
  - simpl in *. rewrite IHl.
    + assert (In n (map snd (get_edges g v))) by (apply H2; left; reflexivity).
      f_equal. rewrite pcv_dst_new by assumption. apply lacv_vertex_address_old.
      2: assumption. red in H1. apply (H1 v). 1: assumption. apply in_map_iff in H3.
      destruct H3 as [[x ?] [? ?]]. simpl in H3. subst n0. clear -H4. pose proof H4.
      unfold get_edges in H4. rewrite <- filter_sum_right_In_iff in H4.
      unfold make_fields in H4. apply e_in_make_fields' in H4. destruct H4 as [s ?].
      inversion H0. subst. assumption.
    + intros. apply H2. right; assumption.
Qed.

Lemma lacv_make_fields_vals_new: forall g v to,
    graph_has_v g v -> graph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    make_fields_vals (lgraph_add_copied_v g v to) (new_copied_v g to) =
    make_fields_vals g v.
Proof.
  intros. unfold make_fields_vals. rewrite lacv_vlabel_new.
  rewrite (lacv_field2val_make_fields_new _ _ _ H H0 H1).
  destruct (raw_mark (vlabel g v)) eqn:? . 2: reflexivity. f_equal.
  apply lacv_vertex_address_old. 2: assumption. apply H2; assumption.
Qed.

Lemma lacv_graph_has_v_old: forall g v to x,
    graph_has_gen g to -> graph_has_v g x ->
    graph_has_v (lgraph_add_copied_v g v to) x.
Proof.
  intros. destruct H0. split.
  - rewrite lacv_graph_has_gen; assumption.
  - red. destruct (Nat.eq_dec (vgeneration x) to).
    + rewrite e in *. unfold nth_gen. simpl. rewrite cvmgil_eq by assumption.
      simpl. red in H1. unfold nth_gen in H1. omega.
    + rewrite lacv_nth_gen; assumption.
Qed.

Lemma lacv_graph_has_v_new: forall g v to,
    graph_has_gen g to -> graph_has_v (lgraph_add_copied_v g v to) (new_copied_v g to).
Proof.
  intros. split; simpl.
  - red. simpl. rewrite cvmgil_length; assumption.
  - red. unfold nth_gen. simpl. rewrite cvmgil_eq by assumption. simpl. omega.
Qed.

Lemma lmc_vertex_address: forall g v new_v x,
    vertex_address (lgraph_mark_copied g v new_v) x = vertex_address g x.
Proof.
  intros. unfold vertex_address. f_equal.
  f_equal. unfold vertex_offset. f_equal. unfold previous_vertices_size.
  apply fold_left_ext. intros. unfold vertex_size_accum. f_equal. unfold vertex_size.
  f_equal. simpl. unfold update_copied_old_vlabel, graph_gen.update_vlabel.
  destruct (EquivDec.equiv_dec v (vgeneration x, y)).
  - unfold Equivalence.equiv in e. rewrite <- e. simpl. reflexivity.
  - reflexivity.
Qed.

Lemma lmc_make_fields: forall (g : LGraph) (old new v: VType),
    make_fields (lgraph_mark_copied g old new) v = make_fields g v.
Proof.
  intros. unfold make_fields. simpl. unfold update_copied_old_vlabel, update_vlabel.
  if_tac; [unfold equiv in H; subst v |]; reflexivity.
Qed.

Lemma lmc_field2val_make_fields: forall (g : LGraph) (v new_v x: VType),
    map (field2val (lgraph_mark_copied g v new_v))
        (make_fields (lgraph_mark_copied g v new_v) x) =
    map (field2val g) (make_fields g x).
Proof.
  intros. rewrite lmc_make_fields. apply map_ext; intros.
  destruct a; [destruct s|]; simpl; [| |rewrite lmc_vertex_address]; reflexivity.
Qed.

Lemma lmc_vlabel_not_eq: forall g v new_v x,
    x <> v -> vlabel (lgraph_mark_copied g v new_v) x = vlabel g x.
Proof.
  intros. unfold lgraph_mark_copied, update_copied_old_vlabel, update_vlabel. simpl.
  rewrite if_false. 1: reflexivity. unfold equiv. intuition.
Qed.

Lemma lmc_make_fields_vals_not_eq: forall (g : LGraph) (v new_v : VType) x,
    x <> v -> make_fields_vals (lgraph_mark_copied g v new_v) x = make_fields_vals g x.
Proof.
  intros. unfold make_fields_vals.
  rewrite lmc_field2val_make_fields, lmc_vlabel_not_eq, lmc_vertex_address;
    [reflexivity | assumption].
Qed.

Lemma lmc_make_fields_vals_eq: forall (g : LGraph) (v new_v : VType),
    make_fields_vals (lgraph_mark_copied g v new_v) v =
    vertex_address g new_v :: tl (make_fields_vals g v).
Proof.
  intros. unfold make_fields_vals at 1. simpl.
  unfold update_copied_old_vlabel, graph_gen.update_vlabel.
  rewrite if_true by reflexivity. simpl. rewrite lmc_vertex_address.
  assert (tl (make_fields_vals g v) = tl (map (field2val g) (make_fields g v))) by
      (unfold make_fields_vals; destruct (raw_mark (vlabel g v)); simpl; reflexivity).
  rewrite H. clear H. do 2 f_equal. apply lmc_field2val_make_fields.
Qed.

Lemma lcv_graph_has_gen: forall g v to x,
    graph_has_gen g to -> graph_has_gen g x <-> graph_has_gen (lgraph_copy_v g v to) x.
Proof. unfold graph_has_gen. intros. simpl. rewrite cvmgil_length; intuition. Qed.

Lemma lmc_graph_has_v: forall g old new x,
    graph_has_v g x <-> graph_has_v (lgraph_mark_copied g old new) x.
Proof.
  intros. unfold graph_has_v, graph_has_gen, gen_has_index, nth_gen. reflexivity.
Qed.

Lemma lmc_copy_compatible: forall g old new,
    graph_has_v g new -> vgeneration old <> vgeneration new -> copy_compatible g ->
    copy_compatible (lgraph_mark_copied g old new).
Proof.
  repeat intro. destruct (V_EqDec old v).
  - compute in e. subst old. rewrite <- lmc_graph_has_v. simpl.
    unfold update_copied_old_vlabel, update_vlabel. rewrite if_true by reflexivity.
    simpl. split; assumption.
  - assert (v <> old) by intuition. clear c.
    rewrite lmc_vlabel_not_eq, <- lmc_graph_has_v in * by assumption.
    apply H1; assumption.
Qed.

Lemma lacv_graph_has_v_inv: forall (g : LGraph) (v : VType) (to : nat) (x : VType),
    graph_has_gen g to -> graph_has_v (lgraph_add_copied_v g v to) x ->
    graph_has_v g x \/ x = new_copied_v g to.
Proof.
  intros. destruct (V_EqDec x (new_copied_v g to)).
  - unfold equiv in e; right; assumption.
  - left. destruct H0. split.
    + rewrite lacv_graph_has_gen in H0; assumption.
    + assert (x <> (new_copied_v g to)) by intuition. clear c H0.
      unfold gen_has_index in *. unfold nth_gen, lgraph_add_copied_v in H1.
      simpl in H1. destruct x as [gen index]. simpl in *. unfold new_copied_v in H2.
      destruct (Nat.eq_dec gen to).
      * subst gen. rewrite cvmgil_eq in H1 by assumption. simpl in H1.
        change (nth to (g_gen (glabel g)) null_info) with (nth_gen g to) in H1.
        remember (number_of_vertices (nth_gen g to)).
        assert (index <> n) by (intro; apply H2; f_equal; assumption). omega.
      * rewrite cvmgil_not_eq in H1; assumption.
Qed.

Lemma lacv_copy_compatible: forall (g : LGraph) (v : VType) (to : nat),
    raw_mark (vlabel g v) = false -> graph_has_gen g to ->
    copy_compatible g -> copy_compatible (lgraph_add_copied_v g v to).
Proof.
  repeat intro. destruct (V_EqDec v0 (new_copied_v g to)).
  - unfold equiv in e. subst v0. rewrite lacv_vlabel_new in *.
    rewrite H3 in H. inversion H.
  - assert (v0 <> (new_copied_v g to)) by intuition. clear c.
    rewrite lacv_vlabel_old in * by assumption.
    assert (graph_has_v g v0). {
      apply lacv_graph_has_v_inv in H2. 2: assumption. destruct H2. 1: assumption.
      contradiction. } split.
    + apply lacv_graph_has_v_old; [|apply H1]; assumption.
    + apply H1; assumption.
Qed.

Lemma lcv_copy_compatible: forall g v to,
    raw_mark (vlabel g v) = false -> graph_has_gen g to ->
    vgeneration v <> to -> copy_compatible g -> copy_compatible (lgraph_copy_v g v to).
Proof.
  intros. unfold lgraph_copy_v. apply lmc_copy_compatible. 2: simpl; assumption.
  - apply lacv_graph_has_v_new. assumption.
  - apply lacv_copy_compatible; assumption.
Qed.

Lemma get_edges_In: forall g v s,
    In (v, s) (get_edges g v) <-> In s (map snd (get_edges g v)).
Proof.
  intros. unfold get_edges, make_fields. remember (raw_fields (vlabel g v)).
  remember 0 as n. clear Heqn Heql. revert n. induction l; intros; simpl.
  1: reflexivity. destruct a; [destruct s0 |]; simpl; rewrite IHl; try reflexivity.
  intuition. inversion H0. left; reflexivity.
Qed.

Lemma get_edges_fst: forall g v e, In e (get_edges g v) -> fst e = v.
Proof.
  intros g v e. unfold get_edges, make_fields. remember (raw_fields (vlabel g v)).
  remember 0 as n. clear Heqn Heql. revert n. induction l; intros; simpl in *.
  - exfalso; assumption.
  - destruct a; [destruct s|]; simpl in *;
      [| | destruct H; [subst e; simpl; reflexivity|]]; apply IHl in H; assumption.
Qed.

Lemma lmc_no_dangling_dst: forall g old new,
    no_dangling_dst g -> no_dangling_dst (lgraph_mark_copied g old new).
Proof.
  repeat intro. simpl. rewrite <- lmc_graph_has_v in *.
  unfold get_edges in H1. rewrite lmc_make_fields in H1. apply (H v); assumption.
Qed.

Lemma lacv_get_edges_new: forall g v to,
  map snd (get_edges (lgraph_add_copied_v g v to) (new_copied_v g to)) =
  map snd (get_edges g v).
Proof.
  intros. unfold get_edges, make_fields. rewrite lacv_vlabel_new.
  remember (raw_fields (vlabel g v)). remember 0. clear Heql Heqn. revert n.
  induction l; intros; simpl. 1: reflexivity.
  destruct a; [destruct s|]; simpl; rewrite IHl; reflexivity.
Qed.

Lemma lacv_no_dangling_dst: forall (g : LGraph) (v : VType) (to : nat),
    no_dangling_dst g -> graph_has_gen g to -> graph_has_v g v ->
    no_dangling_dst (lgraph_add_copied_v g v to).
Proof.
  intros; intro x; intros. simpl. destruct (V_EqDec x (new_copied_v g to)).
  - unfold equiv in e0. subst x. pose proof H3. remember (new_copied_v g to) as new.
    apply get_edges_fst in H3. destruct e as [? s]. simpl in H3. subst v0.
    rewrite get_edges_In, Heqnew, lacv_get_edges_new in H4. rewrite pcv_dst_new.
    2: assumption. apply lacv_graph_has_v_old. 1: assumption.
    apply (H v); [|rewrite get_edges_In]; assumption.
  - assert (x <> new_copied_v g to) by intuition. clear c. rewrite pcv_dst_old.
    + apply lacv_graph_has_v_old. 1: assumption. apply lacv_graph_has_v_inv in H2.
      2: assumption. destruct H2. 2: contradiction. apply (H x). 1: assumption.
      unfold get_edges in *. rewrite lacv_make_fields_not_eq in H3; assumption.
    + unfold get_edges in H3. rewrite <- filter_sum_right_In_iff in H3.
      apply e_in_make_fields' in H3. destruct H3 as [s ?]. subst e. simpl. assumption.
Qed.

Lemma lcv_no_dangling_dst: forall g v to,
    no_dangling_dst g -> graph_has_gen g to -> graph_has_v g v ->
    no_dangling_dst (lgraph_copy_v g v to).
Proof.
  intros. unfold lgraph_copy_v.
  apply lmc_no_dangling_dst, lacv_no_dangling_dst; assumption.
Qed.

Lemma lmc_outlier_compatible: forall g outlier old new,
    outlier_compatible g outlier ->
    outlier_compatible (lgraph_mark_copied g old new) outlier.
Proof.
  intros. intro v. intros. rewrite <- lmc_graph_has_v in H0.
  unfold lgraph_mark_copied, update_copied_old_vlabel, update_vlabel; simpl.
  if_tac; simpl; apply H; [unfold equiv in H1; subst|]; assumption.
Qed.

Lemma lacv_outlier_compatible: forall (g : LGraph) outlier (v : VType) (to : nat),
    graph_has_gen g to -> graph_has_v g v -> outlier_compatible g outlier ->
    outlier_compatible (lgraph_add_copied_v g v to) outlier.
Proof.
  intros. intros x ?. apply lacv_graph_has_v_inv in H2. 2: assumption. destruct H2.
  - rewrite lacv_vlabel_old; [apply H1 | apply graph_has_v_not_eq]; assumption.
  - subst x. rewrite lacv_vlabel_new. apply H1; assumption.
Qed.

Lemma lcv_outlier_compatible: forall g outlier v to,
    graph_has_gen g to -> graph_has_v g v -> outlier_compatible g outlier ->
    outlier_compatible (lgraph_copy_v g v to) outlier.
Proof. intros. apply lmc_outlier_compatible, lacv_outlier_compatible; assumption. Qed.

Local Open Scope Z_scope.

Lemma utia_estc: forall g t_info from to index v (H : 0 <= index < MAX_ARGS),
    enough_space_to_copy g t_info from to ->
    enough_space_to_copy g (update_thread_info_arg t_info index v H) from to.
Proof.
  unfold enough_space_to_copy. intros. unfold rest_gen_size, nth_space in *. apply H0.
Qed.

Lemma lacv_unmarked_gen_size: forall g v to from,
    from <> to -> graph_has_gen g to ->
    unmarked_gen_size g from = unmarked_gen_size (lgraph_add_copied_v g v to) from.
Proof.
  intros. unfold unmarked_gen_size. rewrite lacv_nth_gen by assumption.
  remember (nat_inc_list (number_of_vertices (nth_gen g from))) as l.
  assert (forall i, (from, i) <> new_copied_v g to). {
    intros. intro. inversion H1. apply H. assumption. }
  assert (filter (fun i : nat => negb (raw_mark (vlabel g (from, i)))) l =
          filter (fun i : nat =>
                    negb(raw_mark(vlabel(lgraph_add_copied_v g v to) (from,i)))) l). {
    apply filter_ext. intros. rewrite lacv_vlabel_old by apply H1. reflexivity. }
  rewrite <- H2. apply fold_left_ext. intros. unfold vertex_size_accum. f_equal.
  unfold vertex_size. rewrite lacv_vlabel_old by apply H1. reflexivity.
Qed.

Lemma lacv_estc: forall g t_info from to v,
    from <> to -> graph_has_gen g to ->
    enough_space_to_copy g t_info from to ->
    enough_space_to_copy (lgraph_add_copied_v g v to) t_info from to.
Proof.
  unfold enough_space_to_copy. intros. rewrite <- lacv_unmarked_gen_size; assumption.
Qed.

Lemma vsa_fold_left:
  forall (g : LGraph) (gen : nat) (l : list nat) (z1 z2 : Z),
    fold_left (vertex_size_accum g gen) l (z2 + z1) =
    fold_left (vertex_size_accum g gen) l z2 + z1.
Proof.
  intros. revert z1 z2. induction l; intros; simpl. 1: reflexivity.
  rewrite <- IHl. f_equal. unfold vertex_size_accum. omega.
Qed.

Lemma lmc_unmarked_gen_size: forall g v v',
    graph_has_v g v -> raw_mark (vlabel g v) = false ->
    unmarked_gen_size g (vgeneration v) =
    unmarked_gen_size (lgraph_mark_copied g v v') (vgeneration v) +
     vertex_size g v.
Proof.
  intros. unfold unmarked_gen_size. unfold nth_gen. simpl glabel.
  destruct v as [gen index]. simpl vgeneration.
  change (nth gen (g_gen (glabel g)) null_info) with (nth_gen g gen).
  remember (nat_inc_list (number_of_vertices (nth_gen g gen))).
  rewrite (fold_left_ext (vertex_size_accum (lgraph_mark_copied g (gen, index) v') gen)
                         (vertex_size_accum g gen)).
  - simpl. remember (fun i : nat => negb (raw_mark (vlabel g (gen, i)))) as f1.
    remember (fun i : nat =>
                negb (raw_mark (update_copied_old_vlabel g (gen, index) v' (gen, i))))
      as f2. cut (Permutation (filter f1 l) (index :: filter f2 l)).
    + intros. rewrite (fold_left_comm _ _ (index :: filter f2 l)). 3: assumption.
      * simpl. rewrite <- vsa_fold_left. f_equal.
      * apply vsa_comm.
    + apply filter_singular_perm; subst.
      * intros. unfold update_copied_old_vlabel, update_vlabel.
        rewrite if_false. 1: reflexivity. unfold equiv. intro. apply H2.
        inversion H3. reflexivity.
      * rewrite nat_inc_list_In_iff. destruct H. simpl in *. assumption.
      * unfold update_copied_old_vlabel, update_vlabel. rewrite if_true; reflexivity.
      * rewrite H0. reflexivity.
      * apply nat_inc_list_NoDup.
  - intros. unfold vertex_size_accum. f_equal. unfold vertex_size. f_equal.
    simpl. unfold update_copied_old_vlabel, update_vlabel. if_tac. 2: reflexivity.
    simpl. unfold equiv in H2. rewrite H2. reflexivity.
Qed.

Lemma cti_rest_gen_size:
  forall t_info to s
         (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info)))
         (Hh : has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info))) s),
  rest_gen_size t_info to =
  rest_gen_size (cut_thread_info t_info (Z.of_nat to) s Hi Hh) to + s.
Proof.
  intros. unfold rest_gen_size. rewrite !nth_space_Znth. unfold cut_thread_info. simpl.
  rewrite upd_Znth_same by assumption. simpl. omega.
Qed.

Lemma lmc_estc:
  forall (g : LGraph) (t_info : thread_info) (v v': VType) (to : nat)
         (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info))),
    enough_space_to_copy g t_info (vgeneration v) to ->
    graph_has_v g v -> raw_mark (vlabel g v) = false ->
    forall
      Hh : has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info))) (vertex_size g v),
      enough_space_to_copy (lgraph_mark_copied g v v')
                           (cut_thread_info
                              t_info (Z.of_nat to) (vertex_size g v) Hi Hh)
                           (vgeneration v) to.
Proof.
  unfold enough_space_to_copy. intros.
  rewrite (lmc_unmarked_gen_size g v v') in H by assumption.
  rewrite (cti_rest_gen_size _ _ (vertex_size g v) Hi Hh) in H. omega.
Qed.

Lemma forward_estc_unchanged: forall
    g t_info v to
    (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info))) (vertex_size g v)),
    vgeneration v <> to -> graph_has_gen g to ->
    graph_has_v g v -> raw_mark (vlabel g v) = false ->
    enough_space_to_copy g t_info (vgeneration v) to ->
    enough_space_to_copy (lgraph_copy_v g v to)
         (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh)
      (vgeneration v) to.
Proof.
  intros. unfold lgraph_copy_v.
  apply (lacv_estc _ _ _ _ v) in H3; [| assumption..].
  assert (vertex_size g v = vertex_size (lgraph_add_copied_v g v to) v). {
    unfold vertex_size. rewrite lacv_vlabel_old. 1: reflexivity.
    intro. destruct v as [gen index]. simpl in H. unfold new_copied_v in H4.
    inversion H4. apply H. assumption. }
  remember (lgraph_add_copied_v g v to) as g'.
  pose proof Hh as Hh'. rewrite H4 in Hh'.
  replace (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh) with
      (cut_thread_info t_info (Z.of_nat to) (vertex_size g' v) Hi Hh') by
      (apply cti_eq; symmetry; assumption).
  apply lmc_estc.
  - assumption.
  - subst g'. apply lacv_graph_has_v_old; assumption.
  - subst g'. rewrite lacv_vlabel_old; [| apply graph_has_v_not_eq]; assumption.
Qed.

Lemma forward_estc: forall
    g t_info v to index uv
    (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info))) (vertex_size g v))
    (Hm : 0 <= index < MAX_ARGS),
    vgeneration v <> to -> graph_has_gen g to ->
    graph_has_v g v -> raw_mark (vlabel g v) = false ->
    enough_space_to_copy g t_info (vgeneration v) to ->
    enough_space_to_copy
      (lgraph_copy_v g v to)
      (update_thread_info_arg
         (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh) index uv Hm)
      (vgeneration v) to.
Proof.
  intros. apply utia_estc. clear index uv Hm.
  apply forward_estc_unchanged; assumption.
Qed.

Lemma lcv_forward_condition: forall
    g t_info v to index uv
    (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info))) (vertex_size g v))
    (Hm : 0 <= index < MAX_ARGS),
    vgeneration v <> to -> graph_has_v g v -> raw_mark (vlabel g v) = false ->
    forward_condition g t_info (vgeneration v) to ->
    forward_condition
      (lgraph_copy_v g v to)
      (update_thread_info_arg
         (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh) index uv Hm)
      (vgeneration v) to.
Proof.
  intros. destruct H2 as [? [? [? [? ?]]]]. split; [|split; [|split; [|split]]].
  - apply forward_estc; assumption.
  - apply lcv_graph_has_gen; assumption.
  - apply lcv_graph_has_gen; assumption.
  - apply lcv_copy_compatible; assumption.
  - apply lcv_no_dangling_dst; assumption.
Qed.

Lemma lcv_forward_condition_unchanged: forall
    g t_info v to
    (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info))) (vertex_size g v)),
    vgeneration v <> to -> graph_has_v g v -> raw_mark (vlabel g v) = false ->
    forward_condition g t_info (vgeneration v) to ->
    forward_condition (lgraph_copy_v g v to)
         (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh)
      (vgeneration v) to.
Proof.
  intros. destruct H2 as [? [? [? [? ?]]]]. split; [|split; [|split; [|split]]].
  - apply forward_estc_unchanged; assumption.
  - apply lcv_graph_has_gen; assumption.
  - apply lcv_graph_has_gen; assumption.
  - apply lcv_copy_compatible; assumption.
  - apply lcv_no_dangling_dst; assumption.
Qed.

Lemma lcv_graph_has_v_new: forall g v to,
    graph_has_gen g to -> graph_has_v (lgraph_copy_v g v to) (new_copied_v g to).
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_graph_has_v.
  apply lacv_graph_has_v_new. assumption.
Qed.

Lemma lcv_graph_has_v_old: forall g v to x,
    graph_has_gen g to -> graph_has_v g x -> graph_has_v (lgraph_copy_v g v to) x.
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_graph_has_v.
  apply lacv_graph_has_v_old; assumption.
Qed.

Lemma lcv_rgc_unchanged: forall g roots v to,
    graph_has_gen g to ->
    roots_graph_compatible roots g ->
    roots_graph_compatible roots (lgraph_copy_v g v to).
Proof.
  intros. red in H0 |-*. rewrite Forall_forall in *. intros.
  apply lcv_graph_has_v_old; [|apply H0]; assumption.
Qed.

Lemma lcv_roots_compatible_unchanged: forall g roots outlier v to,
    graph_has_gen g to ->
    roots_compatible g outlier roots ->
    roots_compatible (lgraph_copy_v g v to) outlier roots.
Proof. intros. destruct H0. split; [|apply lcv_rgc_unchanged]; assumption. Qed.

Lemma lcv_roots_graph_compatible: forall g roots v to f_info z,
    graph_has_gen g to ->
    roots_graph_compatible roots g ->
    roots_graph_compatible (upd_bunch z f_info roots (inr (new_copied_v g to)))
                           (lgraph_copy_v g v to).
Proof.
  intros. apply upd_bunch_graph_compatible.
  - apply lcv_rgc_unchanged; assumption.
  - unfold lgraph_copy_v; rewrite <- lmc_graph_has_v;
      apply lacv_graph_has_v_new; assumption.
Qed.

Lemma lcv_roots_compatible: forall g roots outlier v to f_info z,
    graph_has_gen g to ->
    roots_compatible g outlier roots ->
    roots_compatible (lgraph_copy_v g v to) outlier
                     (upd_bunch z f_info roots (inr (new_copied_v g to))).
Proof.
  intros. destruct H0. split.
  - apply upd_roots_outlier_compatible; assumption.
  - apply lcv_roots_graph_compatible; assumption.
Qed.

Lemma lcv_vertex_address: forall g v to x,
    graph_has_gen g to -> closure_has_v g x ->
    vertex_address (lgraph_copy_v g v to) x = vertex_address g x.
Proof.
  intros. unfold lgraph_copy_v.
  rewrite lmc_vertex_address, lacv_vertex_address; [reflexivity | assumption..].
Qed.

Lemma lcv_vertex_address_new: forall g v to,
    graph_has_gen g to ->
    vertex_address (lgraph_copy_v g v to) (new_copied_v g to) =
    vertex_address g (new_copied_v g to).
Proof.
  intros.
  apply lcv_vertex_address;  [| red; simpl; split]; [assumption..| apply Nat.le_refl].
Qed.

Lemma lcv_vertex_address_old: forall g v to x,
    graph_has_gen g to -> graph_has_v g x ->
    vertex_address (lgraph_copy_v g v to) x = vertex_address g x.
Proof.
  intros. apply lcv_vertex_address; [|apply graph_has_v_in_closure]; assumption.
Qed.

Lemma lcv_fun_thread_arg_compatible_unchanged: forall
    g t_info f_info roots v to i s
    (Hi : 0 <= i < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (spaces (ti_heap t_info))) s),
    graph_has_gen g to ->
    roots_graph_compatible roots g ->
    fun_thread_arg_compatible g t_info f_info roots ->
    fun_thread_arg_compatible (lgraph_copy_v g v to)
         (cut_thread_info t_info i s Hi Hh) f_info roots.
Proof.
  intros.
  unfold fun_thread_arg_compatible in *. simpl. rewrite <- H1. apply map_ext_in.
  intros. destruct a; [destruct s0|]; [reflexivity..| simpl].
  apply lcv_vertex_address_old. 1: assumption. red in H0. rewrite Forall_forall in H0.
  apply H0. rewrite <- filter_sum_right_In_iff. assumption.
Qed.

Lemma lcv_fun_thread_arg_compatible: forall
    g t_info f_info roots z v to i s
    (Hi : 0 <= i < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (spaces (ti_heap t_info))) s)
    (Hm : 0 <= Znth z (live_roots_indices f_info) < MAX_ARGS),
    graph_has_gen g to -> roots_graph_compatible roots g ->
    fun_thread_arg_compatible g t_info f_info roots ->
    fun_thread_arg_compatible
      (lgraph_copy_v g v to)
      (update_thread_info_arg
         (cut_thread_info t_info i s Hi Hh) (Znth z (live_roots_indices f_info))
         (vertex_address g (new_copied_v g to)) Hm)
      f_info (upd_bunch z f_info roots (inr (new_copied_v g to))).
Proof.
  intros. rewrite <- (lcv_vertex_address_new g v to H).
  apply upd_fun_thread_arg_compatible with (HB := Hm).
    apply lcv_fun_thread_arg_compatible_unchanged; assumption.
Qed.

Lemma upd_Znth_unchanged: forall {A : Type} {d : Inhabitant A} (i : Z) (l : list A),
    0 <= i < Zlength l -> upd_Znth i l (Znth i l) = l.
Proof.
  intros. assert (Zlength (upd_Znth i l (Znth i l)) = Zlength l) by
      (rewrite upd_Znth_Zlength; [reflexivity | assumption]). rewrite Znth_list_eq.
  split. 1: assumption. intros. rewrite H0 in H1. destruct (Z.eq_dec j i).
  - subst j. rewrite upd_Znth_same; [reflexivity | assumption].
  - rewrite upd_Znth_diff; [reflexivity | assumption..].
Qed.

Instance share_inhabitant: Inhabitant share := emptyshare.

Lemma lcv_nth_gen: forall g v to n,
    n <> to -> graph_has_gen g to -> nth_gen (lgraph_copy_v g v to) n = nth_gen g n.
Proof.
  intros. unfold lgraph_copy_v, nth_gen. simpl.
  rewrite cvmgil_not_eq; [reflexivity | assumption..].
Qed.

Lemma lcv_vertex_size_new: forall (g : LGraph) (v : VType) (to : nat),
    vertex_size (lgraph_copy_v g v to) (new_copied_v g to) = vertex_size g v.
Proof.
  intros. unfold vertex_size, lgraph_copy_v. simpl.
  unfold update_copied_old_vlabel, update_vlabel. if_tac.
  - simpl. unfold update_copied_new_vlabel, update_vlabel. if_tac; reflexivity.
  - rewrite lacv_vlabel_new. reflexivity.
Qed.

Lemma lcv_vertex_size_old: forall (g : LGraph) (v : VType) (to : nat) x,
        graph_has_gen g to -> graph_has_v g x ->
        vertex_size (lgraph_copy_v g v to) x = vertex_size g x.
Proof.
  intros. unfold vertex_size, lgraph_copy_v. simpl.
  unfold update_copied_old_vlabel, update_vlabel. if_tac.
  - simpl. unfold update_copied_new_vlabel, update_vlabel. unfold equiv in H1. subst.
    if_tac; reflexivity.
  - rewrite lacv_vlabel_old. 1: reflexivity. apply graph_has_v_not_eq. assumption.
Qed.

Lemma lcv_pvs_same: forall g v to,
    graph_has_gen g to ->
    previous_vertices_size (lgraph_copy_v g v to) to
                           (number_of_vertices (nth_gen (lgraph_copy_v g v to) to)) =
    previous_vertices_size g to (number_of_vertices (nth_gen g to)) + vertex_size g v.
Proof.
  intros. unfold nth_gen. simpl. rewrite cvmgil_eq by assumption. simpl.
  remember (number_of_vertices (nth to (g_gen (glabel g)) null_info)).
  replace (n + 1)%nat with (S n) by omega. rewrite pvs_S. f_equal.
  - unfold previous_vertices_size. apply fold_left_ext. intros.
    unfold vertex_size_accum. f_equal. apply lcv_vertex_size_old. 1: assumption.
    rewrite nat_inc_list_In_iff in H0; subst; split; simpl; assumption.
  - assert ((to, n) = new_copied_v g to) by
        (unfold new_copied_v, nth_gen; subst n; reflexivity). rewrite H0.
    apply lcv_vertex_size_new.
Qed.

Lemma lcv_pvs_old: forall g v to gen,
    gen <> to -> graph_has_gen g to -> graph_has_gen g gen ->
    previous_vertices_size (lgraph_copy_v g v to) gen
                           (number_of_vertices (nth_gen (lgraph_copy_v g v to) gen)) =
    previous_vertices_size g gen (number_of_vertices (nth_gen g gen)).
Proof.
  intros. unfold nth_gen. simpl. rewrite cvmgil_not_eq by assumption.
  remember (number_of_vertices (nth gen (g_gen (glabel g)) null_info)).
  unfold previous_vertices_size. apply fold_left_ext. intros.
  unfold vertex_size_accum. f_equal. apply lcv_vertex_size_old. 1: assumption.
  rewrite nat_inc_list_In_iff in H2. subst. split; simpl; assumption.
Qed.

Lemma lcv_graph_thread_info_compatible: forall
    g t_info v to
    (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info))) (vertex_size g v)),
    graph_has_gen g to ->
    graph_thread_info_compatible g t_info ->
    graph_thread_info_compatible (lgraph_copy_v g v to)
      (cut_thread_info t_info (Z.of_nat to) (vertex_size g v)
                       Hi Hh).
Proof.
  unfold graph_thread_info_compatible. intros. destruct H0 as [? [? ?]].
  assert (map space_start (spaces (ti_heap t_info)) =
          map space_start
              (upd_Znth (Z.of_nat to) (spaces (ti_heap t_info))
                        (cut_space
                           (Znth (Z.of_nat to) (spaces (ti_heap t_info)))
                           (vertex_size g v) Hh))). {
    rewrite <- upd_Znth_map. simpl. rewrite <- Znth_map by assumption.
    rewrite upd_Znth_unchanged; [reflexivity | rewrite Zlength_map; assumption]. }
  split; [|split]; [|simpl; rewrite cvmgil_length by assumption..].
  - rewrite gsc_iff in *; simpl. 2: assumption.
    + intros. unfold nth_space. simpl.
      rewrite <- lcv_graph_has_gen in H4 by assumption. specialize (H0 _ H4).
      simpl in H0. destruct H0 as [? [? ?]]. split; [|split].
      * clear -H0 H3 H. rewrite <- map_nth, <- H3, map_nth. clear H3.
        unfold nth_gen, nth_space in *. simpl. destruct (Nat.eq_dec gen to).
        -- subst gen. rewrite cvmgil_eq; simpl; assumption.
        -- rewrite cvmgil_not_eq; assumption.
      * assert (map space_sh
                    (upd_Znth (Z.of_nat to) (spaces (ti_heap t_info))
                              (cut_space
                                 (Znth (Z.of_nat to) (spaces (ti_heap t_info)))
                                 (vertex_size g v) Hh)) =
                map space_sh (spaces (ti_heap t_info))). {
          rewrite <- upd_Znth_map. simpl. rewrite <- Znth_map by assumption.
          rewrite upd_Znth_unchanged; [reflexivity|rewrite Zlength_map; assumption]. }
        rewrite <- map_nth, H7, map_nth. clear -H5 H. unfold nth_gen, nth_space in *.
        simpl. destruct (Nat.eq_dec gen to).
        -- subst gen. rewrite cvmgil_eq; simpl; assumption.
        -- rewrite cvmgil_not_eq; assumption.
      * assert (0 <= Z.of_nat gen < Zlength (spaces (ti_heap t_info))). {
          split. 1: apply Nat2Z.is_nonneg. rewrite Zlength_correct.
          apply inj_lt. red in H4. omega. }
        rewrite <- (Nat2Z.id gen) at 3. rewrite nth_Znth.
        2: rewrite upd_Znth_Zlength; assumption. destruct (Nat.eq_dec gen to).
        -- subst gen. rewrite upd_Znth_same by assumption. simpl.
           rewrite lcv_pvs_same by assumption.
           rewrite H6, nth_space_Znth. reflexivity.
        -- assert (Z.of_nat gen <> Z.of_nat to) by
              (intro; apply n, Nat2Z.inj; assumption).
           rewrite upd_Znth_diff, <- nth_space_Znth, lcv_pvs_old; assumption.
    + rewrite cvmgil_length, <- !ZtoNat_Zlength, upd_Znth_Zlength, !ZtoNat_Zlength;
        assumption.
  - intros. rewrite <- H3. assumption.
  - rewrite <- !ZtoNat_Zlength, upd_Znth_Zlength, !ZtoNat_Zlength; assumption.
Qed.

Lemma lcv_super_compatible_unchanged: forall
    g t_info roots f_info outlier to v
    (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info))) (vertex_size g v)),
    graph_has_gen g to -> graph_has_v g v ->
    super_compatible (g, t_info, roots) f_info outlier ->
    super_compatible
      (lgraph_copy_v g v to,
       (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh),
       roots) f_info outlier.
Proof.
  intros. destruct H1 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply lcv_graph_thread_info_compatible; assumption.
  - destruct H3. apply lcv_fun_thread_arg_compatible_unchanged; assumption.
  - apply lcv_roots_compatible_unchanged; assumption.
  - apply lcv_outlier_compatible; assumption.
Qed.

Lemma lcv_super_compatible: forall
    g t_info roots f_info outlier to v z
    (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info))) (vertex_size g v))
    (Hm : 0 <= Znth z (live_roots_indices f_info) < MAX_ARGS),
    graph_has_gen g to -> graph_has_v g v ->
    super_compatible (g, t_info, roots) f_info outlier ->
    super_compatible
      (lgraph_copy_v g v to,
       update_thread_info_arg
         (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh)
         (Znth z (live_roots_indices f_info))
         (vertex_address g (new_copied_v g to)) Hm,
       upd_bunch z f_info roots (inr (new_copied_v g to))) f_info outlier.
Proof.
  intros. destruct H1 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply lcv_graph_thread_info_compatible; assumption.
  - destruct H3. apply lcv_fun_thread_arg_compatible; assumption.
  - apply lcv_roots_compatible; assumption.
  - apply lcv_outlier_compatible; assumption.
Qed.

Lemma lmc_gen_start: forall g old new n,
    gen_start (lgraph_mark_copied g old new) n = gen_start g n.
Proof.
  intros. unfold gen_start. do 2 if_tac.
  - unfold nth_gen. simpl. reflexivity.
  - unfold graph_has_gen in *. simpl in *. contradiction.
  - unfold graph_has_gen in *. simpl in *. contradiction.
  - reflexivity.
Qed.

Lemma lcv_gen_start: forall g v to n,
    graph_has_gen g to -> gen_start (lgraph_copy_v g v to) n = gen_start g n.
Proof.
  intros. unfold lgraph_copy_v.
  rewrite lmc_gen_start, lacv_gen_start; [reflexivity | assumption].
Qed.

Lemma utia_ti_heap: forall t_info i ad (Hm : 0 <= i < MAX_ARGS),
    ti_heap (update_thread_info_arg t_info i ad Hm) = ti_heap t_info.
Proof. intros. simpl. reflexivity. Qed.

Lemma cti_space_not_eq: forall t_info i s n
    (Hi : 0 <= i < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (spaces (ti_heap t_info))) s),
    (Z.of_nat n) <> i ->
    nth_space (cut_thread_info t_info i s Hi Hh) n = nth_space t_info n.
Proof.
  intros. rewrite !nth_space_Znth. simpl.
  pose proof (Nat2Z.is_nonneg n). remember (Z.of_nat n). clear Heqz.
  remember (spaces (ti_heap t_info)). destruct (Z_lt_le_dec z (Zlength l)).
  - assert (0 <= z < Zlength l) by omega.
    rewrite upd_Znth_diff; [reflexivity |assumption..].
  - rewrite !Znth_overflow;
      [reflexivity | | rewrite upd_Znth_Zlength by assumption]; omega.
Qed.

Lemma cti_space_eq: forall t_info i s
    (Hi : 0 <= Z.of_nat i < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat i) (spaces (ti_heap t_info))) s),
    nth_space (cut_thread_info t_info (Z.of_nat i) s Hi Hh) i =
    cut_space (Znth (Z.of_nat i) (spaces (ti_heap t_info))) s Hh.
Proof.
  intros. rewrite nth_space_Znth. simpl. rewrite upd_Znth_same by assumption.
  reflexivity.
Qed.

Lemma cti_gen_size: forall t_info i s n
    (Hi : 0 <= i < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (spaces (ti_heap t_info))) s),
    gen_size (cut_thread_info t_info i s Hi Hh) n =
    gen_size t_info n.
Proof.
  intros. unfold gen_size. destruct (Z.eq_dec (Z.of_nat n) i).
  - subst i. rewrite cti_space_eq. simpl. rewrite nth_space_Znth. reflexivity.
  - rewrite cti_space_not_eq; [reflexivity | assumption].
Qed.

Lemma cti_space_start: forall t_info i s  n
    (Hi : 0 <= i < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (spaces (ti_heap t_info))) s),
    space_start (nth_space (cut_thread_info t_info i s Hi Hh) n) =
    space_start (nth_space t_info n).
Proof.
  intros. destruct (Z.eq_dec (Z.of_nat n) i).
  - subst i. rewrite cti_space_eq. simpl. rewrite nth_space_Znth. reflexivity.
  - rewrite cti_space_not_eq; [reflexivity | assumption].
Qed.

Lemma utiacti_gen_size: forall t_info i1 i2 s ad n
    (Hi : 0 <= i1 < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth i1 (spaces (ti_heap t_info))) s)
    (Hm : 0 <= i2 < MAX_ARGS),
    gen_size (update_thread_info_arg (cut_thread_info t_info i1 s Hi Hh) i2 ad Hm) n =
    gen_size t_info n.
Proof.
  intros. unfold gen_size, nth_space. rewrite utia_ti_heap. apply cti_gen_size.
Qed.

Lemma utiacti_space_start: forall t_info i1 i2 s ad n
    (Hi : 0 <= i1 < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth i1 (spaces (ti_heap t_info))) s)
    (Hm : 0 <= i2 < MAX_ARGS),
    space_start
      (nth_space (update_thread_info_arg (cut_thread_info t_info i1 s Hi Hh) i2 ad Hm)
                 n) = space_start (nth_space t_info n).
Proof. intros. unfold nth_space. rewrite utia_ti_heap. apply cti_space_start. Qed.

Definition thread_info_relation t t':=
  ti_heap_p t = ti_heap_p t' /\ (forall n, gen_size t n = gen_size t' n) /\
  forall n, space_start (nth_space t n) = space_start (nth_space t' n).

Lemma tir_id: forall t, thread_info_relation t t.
Proof. intros. red. split; [|split]; reflexivity. Qed.

Lemma upd_Znth_diff_strong : forall {A}{d: Inhabitant A} i j l (u : A),
    0 <= j < Zlength l -> i <> j ->
  Znth i (upd_Znth j l u) = Znth i l.
Proof.
  intros.
  destruct (zlt i 0).
  { rewrite !Znth_underflow; auto. }
  destruct (zlt i (Zlength l)).
  apply upd_Znth_diff; auto; omega.
  { rewrite !Znth_overflow; auto.
    rewrite upd_Znth_Zlength; auto. }
Qed.

Lemma lgd_graph_has_v: forall g e v v',
    graph_has_v g v <-> graph_has_v (labeledgraph_gen_dst g e v') v.
Proof. reflexivity. Qed.

Lemma lgd_graph_has_gen: forall g e v x,
    graph_has_gen (labeledgraph_gen_dst g e v) x <-> graph_has_gen g x.
Proof. intros; unfold graph_has_gen; intuition. Qed.

Lemma lgd_raw_fld_length_eq: forall (g: LGraph) v e v',
    Zlength (raw_fields (vlabel g v)) =
    Zlength (raw_fields (vlabel (labeledgraph_gen_dst g e v') v)).
Proof. reflexivity. Qed.

Lemma lgd_vertex_address_eq: forall g e v' x,
    vertex_address (labeledgraph_gen_dst g e v') x = vertex_address g x.
Proof. reflexivity. Qed.

Lemma lgd_make_fields_eq: forall (g : LGraph) (v v': VType) e,
    make_fields (labeledgraph_gen_dst g e v') v = make_fields g v.
Proof. reflexivity. Qed.

Lemma lgd_make_header_eq: forall g e v' x,
    make_header g x = make_header (labeledgraph_gen_dst g e v') x.
Proof. reflexivity. Qed.

Lemma lgd_raw_mark_eq: forall (g: LGraph) e (v v' : VType),
    raw_mark (vlabel g v) = raw_mark (vlabel (labeledgraph_gen_dst g e v') v).
Proof. reflexivity. Qed.

Lemma lgd_dst_old: forall (g: LGraph) e v e',
    e <> e' -> dst (labeledgraph_gen_dst g e v) e' = dst g e'.
Proof.
  intros. simpl. unfold updateEdgeFunc. rewrite if_false. 1: reflexivity. auto.
Qed.

Lemma lgd_dst_new: forall (g: LGraph) e v,
    dst (labeledgraph_gen_dst g e v) e = v.
Proof. intros. simpl. unfold updateEdgeFunc. rewrite if_true; reflexivity. Qed.

Lemma lgd_f2v_eq_except_one: forall g fd e v',
    fd <> (inr e) ->
    field2val g fd = field2val (labeledgraph_gen_dst g e v') fd.
Proof.
  intros; unfold field2val; simpl.
  destruct fd; [destruct s|]; try reflexivity.
  unfold updateEdgeFunc; if_tac; [exfalso; apply H; rewrite H0|]; reflexivity.
Qed.

Lemma lgd_map_f2v_diff_vert_eq: forall g v v' v1 e n,
    0 <= n < Zlength (make_fields g v) ->
    Znth n (make_fields g v) = inr e ->
    v1 <> v ->
    map (field2val g) (make_fields g v1) =
    map (field2val (labeledgraph_gen_dst g e v'))
        (make_fields (labeledgraph_gen_dst g e v') v1).
Proof.
    intros.
    rewrite lgd_make_fields_eq.
    apply Znth_list_eq. split.
    1: repeat rewrite Zlength_map; reflexivity.
    intros. rewrite Zlength_map in H2.
    repeat rewrite Znth_map by assumption.
    apply lgd_f2v_eq_except_one. intro.
    pose proof (make_fields_edge_unique g e v
                                        v1 n j H H2 H0 H3).
    destruct H4. unfold not in H1. symmetry in H5.
    apply (H1 H5).
Qed.

Lemma lgd_f2v_eq_after_update: forall g v v' e n j,
  0 <= n < Zlength (make_fields g v) ->
  0 <= j < Zlength (make_fields g v) ->
  Znth n (make_fields g v) = inr e ->
  Znth j (upd_Znth n (map (field2val g)
                          (make_fields g v)) (vertex_address g v')) =
  Znth j
    (map (field2val (labeledgraph_gen_dst g e v'))
         (make_fields (labeledgraph_gen_dst g e v') v)).
Proof.
  intros.
  rewrite Znth_map.
  2: rewrite lgd_make_fields_eq; assumption.
  assert (j = n \/ j <> n) by omega; destruct H2.
  + subst j; rewrite upd_Znth_same.
    2: rewrite Zlength_map; assumption.
    replace (make_fields (labeledgraph_gen_dst g e v') v)
      with (make_fields g v) by reflexivity.
    rewrite H1; simpl field2val.
    unfold updateEdgeFunc; if_tac; try reflexivity.
    unfold complement in H2; assert (e = e) by reflexivity.
    apply H2 in H3; exfalso; assumption.
  + rewrite upd_Znth_diff_strong; [|rewrite Zlength_map|]; try assumption.
    rewrite Znth_map by assumption.
    apply (lgd_f2v_eq_except_one g (Znth j (make_fields g v))).
    intro. pose proof (make_fields_edge_unique g e v v n j H H0 H1 H3).
    omega.
Qed.

Lemma lgd_mfv_change_in_one_spot: forall g v e v' n,
    0 <= n < Zlength (make_fields g v) ->
    raw_mark (vlabel g v) = false ->
    Znth n (make_fields g v) = inr e ->
    upd_Znth n (make_fields_vals g v) (vertex_address g v') =
    (make_fields_vals (labeledgraph_gen_dst g e v') v).
Proof.
  intros.
  rewrite (Znth_list_eq (upd_Znth n (make_fields_vals g v)
               (vertex_address g v')) (make_fields_vals
                     (labeledgraph_gen_dst g e v') v)).
  rewrite upd_Znth_Zlength, fields_eq_length.
  2: rewrite fields_eq_length; rewrite make_fields_eq_length in H; assumption.
  split. 1: rewrite fields_eq_length; reflexivity.
  intros.
  unfold make_fields_vals.
  replace (raw_mark (vlabel (labeledgraph_gen_dst g e v') v))
    with (raw_mark (vlabel g v)) by reflexivity.
  rewrite H0; rewrite <- make_fields_eq_length in H2.
  apply lgd_f2v_eq_after_update; assumption.
Qed.

Lemma lgd_no_dangling_dst: forall g e v',
    graph_has_v g v' ->
    no_dangling_dst g ->
     no_dangling_dst (labeledgraph_gen_dst g e v').
Proof.
  intros. unfold no_dangling_dst in *.
  intros. rewrite <- lgd_graph_has_v.
  simpl. unfold updateEdgeFunc; if_tac; [assumption | apply (H0 v)]; assumption.
Qed.

Lemma lgd_no_dangling_dst_copied_vert: forall g e v,
    copy_compatible g ->
    graph_has_v g v ->
    raw_mark (vlabel g v) = true ->
    no_dangling_dst g ->
    no_dangling_dst (labeledgraph_gen_dst g e (copied_vertex (vlabel g v))).
Proof.
  intros.
  assert (graph_has_v g (copied_vertex (vlabel g v))) by apply (H v H0 H1).
  apply lgd_no_dangling_dst; assumption.
Qed.

Lemma lgd_enough_space_to_copy: forall g e v' t_info gen sp,
    enough_space_to_copy g t_info gen sp ->
    enough_space_to_copy (labeledgraph_gen_dst g e v') t_info gen sp.
Proof.
  intros. unfold enough_space_to_copy in *. intuition. Qed.

Lemma lgd_copy_compatible: forall g v' e,
    copy_compatible g ->
    copy_compatible (labeledgraph_gen_dst g e v').
Proof.
  intros. unfold copy_compatible in *. intuition. Qed.

Lemma lgd_forward_condition: forall g t_info v to v' e,
    vgeneration v <> to ->
    graph_has_v g v ->
    graph_has_v g v' ->
    forward_condition g t_info (vgeneration v) to ->
    forward_condition (labeledgraph_gen_dst g e v') t_info (vgeneration v) to.
Proof.
  intros. destruct H2 as [? [? [? [? ?]]]]. split; [|split; [|split; [|split]]].
  - apply lgd_enough_space_to_copy; assumption.
  - apply lgd_graph_has_gen; assumption.
  - apply lgd_graph_has_gen; assumption.
  - apply lgd_copy_compatible; assumption.
  - apply lgd_no_dangling_dst; assumption.
Qed.

Lemma lgd_rgc: forall g roots e v,
    roots_graph_compatible roots g ->
    roots_graph_compatible roots (labeledgraph_gen_dst g e v).
Proof.
  intros. red in H |-*. rewrite Forall_forall in *. intros.
  rewrite <- lgd_graph_has_v. apply H. assumption.
Qed.

Lemma lgd_roots_compatible: forall g outlier roots e v,
    roots_compatible g outlier roots ->
    roots_compatible (labeledgraph_gen_dst g e v) outlier roots.
Proof. intros. destruct H. split; [|apply lgd_rgc]; assumption. Qed.

Lemma lgd_graph_thread_info_compatible:
  forall (g : LGraph) (t_info : thread_info) e (v' : VType),
  graph_thread_info_compatible g t_info ->
  graph_thread_info_compatible (labeledgraph_gen_dst g e v') t_info.
Proof.
  intros; destruct H; split; assumption. Qed.

Lemma lgd_fun_thread_arg_compatible:
  forall (g : LGraph) (t_info : thread_info) e (v' : VType) f_info roots,
    fun_thread_arg_compatible g t_info f_info roots ->
    fun_thread_arg_compatible (labeledgraph_gen_dst g e v') t_info f_info roots.
Proof.
  intros. unfold fun_thread_arg_compatible in *.
  rewrite <- H. apply map_ext_in. intros. destruct a; [destruct s|]; reflexivity.
Qed.

Lemma lgd_outlier_compatible:
  forall (g : LGraph) (t_info : thread_info) e (v' : VType) outlier,
    outlier_compatible g outlier ->
    outlier_compatible (labeledgraph_gen_dst g e v') outlier.
Proof.
  intros. intro v. intros.
  rewrite <- lgd_graph_has_v in H0.
  unfold labeledgraph_gen_dst, pregraph_gen_dst, updateEdgeFunc; simpl.
  apply (H v H0).
Qed.

Lemma lgd_super_compatible: forall g t_info roots f_info outlier v' e,
    super_compatible (g, t_info, roots) f_info outlier ->
    super_compatible ((labeledgraph_gen_dst g e v'), t_info, roots) f_info outlier.
Proof.
  intros. destruct H as [? [? [? ?]]]. split; [|split; [|split]].
  - apply lgd_graph_thread_info_compatible; assumption.
  - destruct H1. apply lgd_fun_thread_arg_compatible; assumption.
  - apply lgd_roots_compatible; assumption.
  - apply lgd_outlier_compatible; assumption.
Qed.

Lemma fr_general_prop_bootstrap: forall depth from to p g g'
                                        (P: nat -> LGraph -> LGraph -> Prop),
    (forall to g, P to g g) ->
    (forall to g1 g2 g3, P to g1 g2 -> P to g2 g3 -> P to g1 g3) ->
    (forall to g e v, P to g (labeledgraph_gen_dst g e v)) ->
    (forall to g v, P to g (lgraph_copy_v g v to)) ->
    forward_relation from to depth p g g' -> P to g g'.
Proof.
  induction depth; intros.
  - inversion H3; subst; try (specialize (H to g'); assumption).
    + apply H2.
    + subst new_g. apply H1.
    + subst new_g. remember (lgraph_copy_v g (dst g e) to) as g1.
      remember (labeledgraph_gen_dst g1 e (new_copied_v g to)) as g2.
      cut (P to g1 g2). 2: subst; apply H1. intros. apply (H0 to g g1 g2).
      2: assumption. subst g1. apply H2.
  - assert (forall l from to g1 g2,
                 forward_loop from to depth l g1 g2 -> P to g1 g2). {
    induction l; intros; inversion H4. 1: apply H. subst.
    specialize (IHl _ _ _ _ H11). specialize (IHdepth _ _ _ _ _ _ H H0 H1 H2 H8).
    apply (H0 _ _ _ _ IHdepth IHl). }
    clear IHdepth. inversion H3; subst; try (specialize (H to g'); assumption).
    + cut (P to g new_g).
      * intros. apply (H0 to g new_g g'). 1: assumption. apply (H4 _ _ _ _ _ H8).
      * subst new_g. apply H2.
    + subst new_g. apply H1.
    + cut (P to g new_g).
      * intros. apply (H0 to g new_g g'). 1: assumption. apply (H4 _ _ _ _ _ H8).
      * subst new_g. remember (lgraph_copy_v g (dst g e) to) as g1.
        remember (labeledgraph_gen_dst g1 e (new_copied_v g to)) as g2.
        cut (P to g1 g2). 2: subst; apply H1. intros. apply (H0 to g g1 g2).
        2: assumption. subst g1. apply H2.
Qed.

Lemma fr_graph_has_gen: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall x, graph_has_gen g x <-> graph_has_gen g' x.
Proof.
  intros. remember (fun to g1 g2 =>
                      graph_has_gen g1 to ->
                      forall x, graph_has_gen g1 x <-> graph_has_gen g2 x) as P.
  pose proof (fr_general_prop_bootstrap depth from to p g g' P). subst P.
  apply H1; clear H1; intros; try assumption; try reflexivity.
  - rewrite H1 by assumption. apply H2. rewrite <- H1; assumption.
  - apply lcv_graph_has_gen. assumption.
Qed.

Lemma fl_graph_has_gen: forall from to depth l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall x, graph_has_gen g x <-> graph_has_gen g' x.
Proof.
  intros. revert g g' H H0 x. induction l; intros; inversion H0. 1: reflexivity.
  subst. assert (forall y, graph_has_gen g y <-> graph_has_gen g2 y) by
      (intros; apply (fr_graph_has_gen _ _ _ _ _ _ H H4)).
  transitivity (graph_has_gen g2 x). 1: apply H1. rewrite H1 in H.
  apply IHl; assumption.
Qed.

Lemma fr_general_prop:
  forall depth from to p g g' A (Q: LGraph -> A -> nat -> Prop)
         (P: LGraph -> LGraph -> A -> Prop) (R: nat -> nat -> Prop),
    R from to -> graph_has_gen g to -> (forall g v, P g g v) ->
    (forall g1 g2 g3 v, P g1 g2 v -> P g2 g3 v -> P g1 g3 v) ->
    (forall g e v x, P g (labeledgraph_gen_dst g e v) x) ->
    (forall from g v to x,
        graph_has_gen g to -> Q g x from -> (vlabel g v).(raw_mark) = false ->
        R from to -> vgeneration v = from -> P g (lgraph_copy_v g v to) x) ->
    (forall depth from to p g g',
        graph_has_gen g to -> forward_relation from to depth p g g' ->
        forall v, Q g v from -> Q g' v from) ->
    (forall g v to x from, graph_has_gen g to -> Q g x from ->
                           Q (lgraph_copy_v g v to) x from) ->
    (forall g e v x from, Q g x from -> Q (labeledgraph_gen_dst g e v) x from) ->
    forward_relation from to depth p g g' ->
    forall v, Q g v from -> P g g' v.
Proof.
  induction depth; intros.
  - inversion H8; subst; try (specialize (H1 g' v); assumption).
    + apply (H4 (vgeneration v0)); [assumption.. | reflexivity].
    + subst new_g. apply H3.
    + subst new_g. remember (lgraph_copy_v g (dst g e) to) as g1.
      remember (labeledgraph_gen_dst g1 e (new_copied_v g to)) as g2.
      cut (P g1 g2 v). 2: subst; apply H3. intros. apply (H2 g g1 g2).
      2: assumption. subst g1.
      apply (H4 (vgeneration (dst g e))); [assumption.. | reflexivity].
  - assert (forall l from to g1 g2,
               graph_has_gen g1 to -> forward_loop from to depth l g1 g2 ->
               R from to -> forall v, Q g1 v from -> P g1 g2 v). {
      induction l; intros; inversion H11. 1: apply H1. subst.
      specialize (IHdepth _ _ _ _ _ _ _ _ _ H12 H10 H1 H2 H3 H4 H5 H6 H7 H17 _ H13).
      apply (H5 _ _ _ _ _ _ H10 H17) in H13.
      rewrite (fr_graph_has_gen _ _ _ _ _ _ H10 H17) in H10.
      specialize (IHl _ _ _ _ H10 H20 H12 _ H13). apply (H2 _ _ _ _ IHdepth IHl). }
    clear IHdepth. inversion H8; subst; try (specialize (H1 g' v); assumption).
    + cut (P g new_g v).
      * intros. apply (H2 g new_g g'). 1: assumption.
        assert (graph_has_gen new_g to) by
            (subst new_g; rewrite <- lcv_graph_has_gen; assumption).
        apply (H10 _ _ _ _ _ H12 H14 H). subst new_g. apply H6; assumption.
      * subst new_g. apply (H4 (vgeneration v0)); [assumption.. | reflexivity].
    + subst new_g. apply H3.
    + cut (P g new_g v).
      * intros. apply (H2 g new_g g'). 1: assumption.
        assert (graph_has_gen new_g to) by
            (subst new_g; rewrite lgd_graph_has_gen, <- lcv_graph_has_gen; assumption).
        apply (H10 _ _ _ _ _ H12 H14 H). subst new_g. apply H7, H6; assumption.
      * subst new_g. remember (lgraph_copy_v g (dst g e) to) as g1.
        remember (labeledgraph_gen_dst g1 e (new_copied_v g to)) as g2.
        cut (P g1 g2 v). 2: subst; apply H3. intros. apply (H2 g g1 g2).
        2: assumption. subst g1.
        apply (H4 (vgeneration (dst g e))); [assumption.. | reflexivity].
Qed.

Lemma fr_gen_start: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall x, gen_start g x = gen_start g' x.
Proof.
  intros. remember (fun (g: LGraph) (v: nat) (x: nat) => True) as Q.
  remember (fun g1 g2 x => gen_start g1 x = gen_start g2 x) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H1; clear H1; intros; try assumption; try reflexivity.
  - rewrite H1. assumption.
  - rewrite lcv_gen_start; [reflexivity | assumption].
Qed.

Lemma fl_gen_start: forall from to depth l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall x, gen_start g x = gen_start g' x.
Proof.
  intros. revert g g' H H0 x. induction l; intros; inversion H0. 1: reflexivity.
  subst. transitivity (gen_start g2 x).
  - apply (fr_gen_start _ _ _ _ _ _ H H4).
  - assert (graph_has_gen g2 to) by
        (rewrite <- (fr_graph_has_gen _ _ _ _ _ _ H H4); assumption).
    apply IHl; assumption.
Qed.

Lemma lcv_closure_has_v: forall g v to x,
    graph_has_gen g to -> closure_has_v g x -> closure_has_v (lgraph_copy_v g v to) x.
Proof.
  intros. unfold closure_has_v in *. destruct x as [gen index]. simpl in *.
  destruct H0. split. 1: rewrite <- lcv_graph_has_gen; assumption.
  destruct (Nat.eq_dec gen to).
  - subst gen. red. unfold nth_gen. simpl. rewrite cvmgil_eq by assumption.
    simpl. red in H1. unfold nth_gen in H1. omega.
  - red. rewrite lcv_nth_gen; assumption.
Qed.

Lemma fr_closure_has_v: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, closure_has_v g v -> closure_has_v g' v.
Proof.
  intros. remember (fun (g: LGraph) (v: VType) (x: nat) => True) as Q.
  remember (fun g1 g2 v => closure_has_v g1 v -> closure_has_v g2 v) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H2; clear H2; intros; try assumption; try reflexivity.
  - apply H3, H2. assumption.
  - apply lcv_closure_has_v; assumption.
Qed.

Lemma fr_graph_has_v: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, graph_has_v g v -> graph_has_v g' v.
Proof.
  intros. remember (fun (g: LGraph) (v: VType) (x: nat) => True) as Q.
  remember (fun g1 g2 v => graph_has_v g1 v -> graph_has_v g2 v) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H2; clear H2; intros; try assumption; try reflexivity.
  - apply H3, H2. assumption.
  - unfold lgraph_copy_v. rewrite <- lmc_graph_has_v.
    apply lacv_graph_has_v_old; assumption.
Qed.

Lemma fl_graph_has_v: forall from to depth l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, graph_has_v g v -> graph_has_v g' v.
Proof.
  intros. revert g g' H H0 v H1. induction l; intros; inversion H0; subst.
  1: assumption. cut (graph_has_v g2 v).
  - intros. assert (graph_has_gen g2 to) by
        (apply (fr_graph_has_gen _ _ _ _ _ _ H H5); assumption).
    apply (IHl _ _ H3 H8 _ H2).
  - apply (fr_graph_has_v _ _ _ _ _ _ H H5 _ H1).
Qed.

Lemma fr_vertex_address: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, closure_has_v g v -> vertex_address g v = vertex_address g' v.
Proof.
  intros. remember (fun g v (x: nat) => closure_has_v g v) as Q.
  remember (fun g1 g2 v => vertex_address g1 v = vertex_address g2 v) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H2; clear H2; intros; try assumption; try reflexivity.
  - rewrite H2. assumption.
  - rewrite lcv_vertex_address; [reflexivity | assumption..].
  - apply (fr_closure_has_v _ _ _ _ _ _ H2 H3 _ H4).
  - apply lcv_closure_has_v; assumption.
Qed.

Lemma fl_vertex_address: forall from to depth l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, closure_has_v g v -> vertex_address g v = vertex_address g' v.
Proof.
  intros. revert g g' H H0 v H1. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (vertex_address g2 v).
  - apply (fr_vertex_address _ _ _ _ _ _ H H5 _ H1).
  - apply IHl; [|assumption|].
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_closure_has_v; eauto.
Qed.

Lemma lmc_raw_fields: forall g old new x,
    raw_fields (vlabel g x) = raw_fields (vlabel (lgraph_mark_copied g old new) x).
Proof.
  intros. destruct (V_EqDec old x).
  - unfold equiv in e. subst. simpl. unfold update_copied_old_vlabel, update_vlabel.
    rewrite if_true by reflexivity. simpl. reflexivity.
  - assert (x <> old) by intuition.
    rewrite lmc_vlabel_not_eq; [reflexivity | assumption].
Qed.

Lemma lcv_raw_fields: forall g v to x,
    graph_has_gen g to -> graph_has_v g x ->
    raw_fields (vlabel g x) = raw_fields (vlabel (lgraph_copy_v g v to) x).
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_raw_fields, lacv_vlabel_old.
  1: reflexivity. apply graph_has_v_not_eq; assumption.
Qed.

Lemma lcv_mfv_Zlen_eq: forall g v v' to,
    graph_has_gen g to ->
    graph_has_v g v ->
    Zlength (make_fields_vals g v) =
    Zlength (make_fields_vals (lgraph_copy_v g v' to) v).
Proof.
  intros. repeat rewrite fields_eq_length.
  rewrite <- lcv_raw_fields by assumption; reflexivity.
Qed.

Lemma fr_raw_fields: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, graph_has_v g v -> raw_fields (vlabel g v) = raw_fields (vlabel g' v).
Proof.
  intros. remember (fun (g: LGraph) (v: VType) (x: nat) => graph_has_v g v) as Q.
  remember (fun (g1 g2: LGraph) v =>
              raw_fields (vlabel g1 v) = raw_fields (vlabel g2 v)) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H2; clear H2; intros; try assumption; try reflexivity.
  - rewrite H2. apply H3.
  - rewrite <- lcv_raw_fields; [reflexivity | assumption..].
  - apply (fr_graph_has_v _ _ _ _ _ _ H2 H3 _ H4).
  - apply lcv_graph_has_v_old; assumption.
Qed.

Lemma fl_raw_fields: forall from to depth l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, graph_has_v g v -> raw_fields (vlabel g v) = raw_fields (vlabel g' v).
Proof.
  intros. revert g g' H H0 v H1. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (raw_fields (vlabel g2 v)).
  - apply (fr_raw_fields _ _ _ _ _ _ H H5 _ H1).
  - apply IHl; [|assumption|].
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_graph_has_v; eauto.
Qed.

Lemma lmc_raw_mark: forall g old new x,
    x <> old -> raw_mark (vlabel g x) =
                raw_mark (vlabel (lgraph_mark_copied g old new) x).
Proof.
  intros. destruct (V_EqDec x old).
  - unfold equiv in e. contradiction.
  - rewrite lmc_vlabel_not_eq; [reflexivity | assumption].
Qed.

Lemma lcv_raw_mark: forall g v to x,
    x <> v -> graph_has_gen g to -> graph_has_v g x ->
    raw_mark (vlabel g x) = raw_mark (vlabel (lgraph_copy_v g v to) x).
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_raw_mark by assumption.
  rewrite lacv_vlabel_old. 1: reflexivity. apply graph_has_v_not_eq; assumption.
Qed.

Lemma fr_raw_mark: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, graph_has_v g v -> vgeneration v <> from ->
              raw_mark (vlabel g v) = raw_mark (vlabel g' v).
Proof.
  intros. remember (fun (g: LGraph) (v: VType) (x: nat) =>
                      graph_has_v g v /\ vgeneration v <> x) as Q.
  remember (fun (g1 g2: LGraph) v =>
              raw_mark (vlabel g1 v) = raw_mark (vlabel g2 v)) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H3; clear H3; intros; try assumption; try reflexivity.
  - rewrite H3. apply H4.
  - destruct H4. rewrite <- lcv_raw_mark; [reflexivity | try assumption..].
    destruct x, v0. simpl in *. intro. inversion H9. subst. contradiction.
  - destruct H5. split. 2: assumption.
    apply (fr_graph_has_v _ _ _ _ _ _ H3 H4 _ H5).
  - destruct H4. split. 2: assumption. apply lcv_graph_has_v_old; assumption.
  - split; assumption.
Qed.

Lemma fl_raw_mark: forall depth from to l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, graph_has_v g v -> vgeneration v <> from ->
              raw_mark (vlabel g v) = raw_mark (vlabel g' v).
Proof.
  intros. revert g g' H H0 v H1 H2. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (raw_mark (vlabel g2 v)).
  - apply (fr_raw_mark _ _ _ _ _ _ H H6 _ H1 H2).
  - apply IHl; [|assumption| |assumption].
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_graph_has_v; eauto.
Qed.

Lemma tir_trans: forall t1 t2 t3,
    thread_info_relation t1 t2 -> thread_info_relation t2 t3 ->
    thread_info_relation t1 t3.
Proof.
  intros. destruct H as [? [? ?]], H0 as [? [? ?]].
  split; [|split]; [rewrite H; assumption | intros; rewrite H1; apply H3|
                   intros; rewrite H2; apply H4].
Qed.

Lemma forward_loop_add_tail: forall from to depth l x g1 g2 g3 roots,
    forward_loop from to depth l g1 g2 ->
    forward_relation from to depth (forward_p2forward_t (inr x) roots g2) g2 g3 ->
    forward_loop from to depth (l +:: (inr x)) g1 g3.
Proof.
  intros. revert x g1 g2 g3 H H0. induction l; intros.
  - simpl. inversion H. subst. apply fl_cons with g3. 2: constructor. apply H0.
  - inversion H. subst. clear H. simpl app. apply fl_cons with g4. 1: assumption.
    apply IHl with g2; assumption.
Qed.

Lemma vpp_Zlength: forall g x,
    Zlength (vertex_pos_pairs g x) = Zlength (raw_fields (vlabel g x)).
Proof.
  intros. unfold vertex_pos_pairs.
  rewrite Zlength_map, !Zlength_correct, nat_inc_list_length. reflexivity.
Qed.

Instance forward_p_type_Inhabitant: Inhabitant forward_p_type := inl 0.

Lemma vpp_Znth: forall (x : VType) (g : LGraph) (i : Z),
    0 <= i < Zlength (raw_fields (vlabel g x)) ->
    Znth i (vertex_pos_pairs g x) = inr (x, i).
Proof.
  intros. unfold vertex_pos_pairs.
  assert (0 <= i < Zlength (nat_inc_list (length (raw_fields (vlabel g x))))) by
      (rewrite Zlength_correct, nat_inc_list_length, <- Zlength_correct; assumption).
  rewrite Znth_map by assumption. do 2 f_equal. rewrite <- nth_Znth by assumption.
  rewrite nat_inc_list_nth. 1: rewrite Z2Nat.id; omega.
  rewrite <- ZtoNat_Zlength, <- Z2Nat.inj_lt; omega.
Qed.

Lemma forward_loop_add_tail_vpp: forall from to depth x g g1 g2 g3 roots i,
    0 <= i < Zlength (raw_fields (vlabel g x)) ->
    forward_loop from to depth (sublist 0 i (vertex_pos_pairs g x)) g1 g2 ->
    forward_relation from to depth (forward_p2forward_t (inr (x, i)) roots g2) g2 g3 ->
    forward_loop from to depth (sublist 0 (i + 1) (vertex_pos_pairs g x)) g1 g3.
Proof.
  intros. rewrite <- vpp_Zlength in H. rewrite sublist_last_1; [|omega..].
  rewrite vpp_Zlength in H. rewrite vpp_Znth by assumption.
  apply forward_loop_add_tail with (g2 := g2) (roots := roots); assumption.
Qed.

Lemma lcv_vlabel_new: forall g v to,
    vgeneration v <> to ->
    vlabel (lgraph_copy_v g v to) (new_copied_v g to) = vlabel g v.
Proof.
  intros. unfold lgraph_copy_v.
  rewrite lmc_vlabel_not_eq, lacv_vlabel_new;
    [| unfold new_copied_v; intro; apply H; inversion H0; simpl]; reflexivity.
Qed.

Inductive scan_vertex_for_loop (from to: nat) (v: VType):
  list nat -> LGraph -> LGraph -> Prop :=
| svfl_nil: forall g, scan_vertex_for_loop from to v nil g g
| svfl_cons: forall g1 g2 g3 i il,
  forward_relation
    from to O (forward_p2forward_t (inr (v, (Z.of_nat i))) nil g1) g1 g2 ->
  scan_vertex_for_loop from to v il g2 g3 ->
  scan_vertex_for_loop from to v (i :: il) g1 g3.

Definition no_scan (g: LGraph) (v: VType): Prop :=
  NO_SCAN_TAG <= (vlabel g v).(raw_tag).

Inductive scan_vertex_while_loop (from to: nat):
  list nat -> LGraph -> LGraph -> Prop :=
| svwl_nil: forall g, scan_vertex_while_loop from to nil g g
| svwl_no_scan: forall g1 g2 i il,
    gen_has_index g1 to i -> no_scan g1 (to, i) ->
    scan_vertex_while_loop from to il g1 g2 ->
    scan_vertex_while_loop from to (i :: il) g1 g2
| svwl_scan: forall g1 g2 g3 i il,
    gen_has_index g1 to i -> ~ no_scan g1 (to, i) ->
    scan_vertex_for_loop
      from to (to, i)
      (nat_inc_list (length (vlabel g1 (to, i)).(raw_fields))) g1 g2 ->
    scan_vertex_while_loop from to il g2 g3 ->
    scan_vertex_while_loop from to (i :: il) g1 g3.

Definition do_scan_relation (from to to_index: nat) (g1 g2: LGraph) : Prop :=
  exists n, scan_vertex_while_loop from to (nat_seq to_index n) g1 g2 /\
            ~ gen_has_index g2 to (to_index + n).

Definition gen_unmarked (g: LGraph) (gen: nat): Prop :=
  graph_has_gen g gen ->
  forall idx, gen_has_index g gen idx -> (vlabel g (gen, idx)).(raw_mark) = false.

Lemma lcv_graph_has_v_inv: forall (g : LGraph) (v : VType) (to : nat) (x : VType),
    graph_has_gen g to -> graph_has_v (lgraph_copy_v g v to) x ->
    graph_has_v g x \/ x = new_copied_v g to.
Proof.
  intros. unfold lgraph_copy_v in H0. rewrite <- lmc_graph_has_v in H0.
  apply (lacv_graph_has_v_inv g v); assumption.
Qed.

Lemma lcv_gen_unmarked: forall (to : nat) (g : LGraph) (v : VType),
    graph_has_gen g to -> raw_mark (vlabel g v) = false ->
    forall gen, vgeneration v <> gen ->
                gen_unmarked g gen -> gen_unmarked (lgraph_copy_v g v to) gen.
Proof.
  intros. unfold gen_unmarked in *. intros.
  assert (graph_has_v (lgraph_copy_v g v to) (gen, idx)) by (split; assumption).
  apply lcv_graph_has_v_inv in H5. 2: assumption. destruct H5.
  - pose proof H5. destruct H6. simpl in * |- . specialize (H2 H6 _ H7).
    rewrite <- lcv_raw_mark; try assumption. destruct v. simpl in *. intro. apply H1.
    inversion H8. reflexivity.
  - rewrite H5. rewrite lcv_vlabel_new; try assumption. unfold new_copied_v in H5.
    inversion H5. subst. assumption.
Qed.

Lemma fr_gen_unmarked: forall from to depth p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall gen, from  <> gen -> gen_unmarked g gen -> gen_unmarked g' gen.
Proof.
  intros. remember (fun (g: LGraph) (gen: nat) (x: nat) => x <> gen) as Q.
  remember (fun (g1 g2: LGraph) gen =>
              gen_unmarked g1 gen -> gen_unmarked g2 gen) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H3; clear H3; intros; try assumption; try reflexivity.
  - apply H4, H3. assumption.
  - rewrite <- H7 in H4. apply lcv_gen_unmarked; assumption.
Qed.

Lemma svfl_graph_has_gen: forall from to v l g g',
    graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, graph_has_gen g x <-> graph_has_gen g' x.
Proof.
  intros from to v l. revert from to v. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (graph_has_gen g2 x).
  - eapply fr_graph_has_gen; eauto.
  - apply (IHl from to v). 2: assumption. rewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma svfl_gen_unmarked: forall from to v l g g',
    graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall gen, from <> gen -> gen_unmarked g gen -> gen_unmarked g' gen.
Proof.
  intros from to v l. revert from to v.
  induction l; intros; inversion H0; subst; try assumption.
  eapply (IHl from to _ g2); eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_gen_unmarked; eauto.
Qed.

Lemma svwl_gen_unmarked: forall from to l g g',
    graph_has_gen g to -> scan_vertex_while_loop from to l g g' ->
    forall gen, from <> gen -> gen_unmarked g gen -> gen_unmarked g' gen.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst;
                [| apply (IHl g) | apply (IHl g2)]; try assumption.
  - rewrite <- svfl_graph_has_gen; eauto.
  - eapply svfl_gen_unmarked; eauto.
Qed.

Lemma make_header_tag: forall g v,
    raw_mark (vlabel g v) = false ->
    Int.and (Int.repr (make_header g v)) (Int.repr 255) =
    Int.repr (raw_tag (vlabel g v)).
Proof.
  intros. replace (Int.repr 255) with (Int.sub (Int.repr 256) Int.one) by
      (vm_compute; reflexivity).
  assert (Int.is_power2 (Int.repr 256) = Some (Int.repr 8)) by
      (vm_compute; reflexivity).
  rewrite <- (Int.modu_and _ _ (Int.repr 8)) by assumption.
  rewrite Int.modu_divu by (vm_compute; intro S; inversion S).
  rewrite (Int.divu_pow2 _ _ (Int.repr 8)) by assumption.
  rewrite (Int.mul_pow2 _ _ (Int.repr 8)) by assumption.
  assert (0 <= make_header g v <= Int.max_unsigned). {
    pose proof (make_header_range g v). unfold Int.max_unsigned, Int.modulus.
    rep_omega. }
  rewrite Int.shru_div_two_p, !Int.unsigned_repr; [| rep_omega | assumption].
  rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_omega.
  unfold make_header in *. remember (vlabel g v). clear Heqr.
  rewrite H, !Int.Zshiftl_mul_two_p in * by omega. rewrite <- Z.add_assoc.
  replace (raw_color r * two_p 8 + Zlength (raw_fields r) * two_p 10)
    with ((raw_color r + Zlength (raw_fields r) * two_p 2) * two_p 8) by
      (rewrite Z.mul_add_distr_r, <- Z.mul_assoc, <- two_p_is_exp by omega;
       reflexivity). rewrite Z.div_add by (vm_compute; intros S; inversion S).
  assert (raw_tag r / two_p 8 = 0) by (apply Z.div_small, raw_tag_range).
  rewrite H2, Z.add_0_l, mul_repr, sub_repr,
  <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r. reflexivity.
Qed.

Lemma svfl_vertex_address: forall from to v l g g',
    graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, closure_has_v g x -> vertex_address g x = vertex_address g' x.
Proof.
  do 4 intro. revert from to v. induction l; intros; simpl; inversion H0; subst.
  1: reflexivity. assert (graph_has_gen g2 to) by
      (eapply fr_graph_has_gen in H4; [rewrite <- H4 |]; assumption).
  assert (closure_has_v g2 x) by (eapply fr_closure_has_v in H4; eauto).
  eapply (IHl from to _ g2) in H7; eauto. rewrite <- H7.
  eapply fr_vertex_address; eauto.
Qed.

Lemma svfl_graph_has_v: forall from to v l g g',
    graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, graph_has_v g x -> graph_has_v g' x.
Proof.
  do 4 intro. revert from to v. induction l; intros; simpl; inversion H0; subst.
  1: assumption. assert (graph_has_gen g2 to) by
      (eapply fr_graph_has_gen in H4; [rewrite <- H4 |]; assumption).
  assert (graph_has_v g2 x) by (eapply fr_graph_has_v in H4; eauto).
  eapply (IHl from to _ g2) in H7; eauto.
Qed.

Lemma svfl_raw_fields: forall from to v l g g',
    graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, graph_has_v g x -> raw_fields (vlabel g x) = raw_fields (vlabel g' x).
Proof.
  do 4 intro. revert from to v. induction l; intros; simpl; inversion H0; subst.
  1: reflexivity. assert (graph_has_gen g2 to) by
      (eapply fr_graph_has_gen in H4; [rewrite <- H4 |]; assumption).
  assert (graph_has_v g2 x) by (eapply fr_graph_has_v in H4; eauto).
  eapply (IHl from to _ g2) in H7; eauto. rewrite <- H7.
  eapply fr_raw_fields; eauto.
Qed.

Lemma svfl_raw_mark: forall from to v l g g',
    graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, graph_has_v g x -> vgeneration x <> from ->
              raw_mark (vlabel g x) = raw_mark (vlabel g' x).
Proof.
  do 4 intro. revert from to v. induction l; intros; simpl; inversion H0; subst.
  1: reflexivity. assert (graph_has_gen g2 to) by
      (eapply fr_graph_has_gen in H5; [rewrite <- H5 |]; assumption).
  assert (graph_has_v g2 x) by (eapply fr_graph_has_v in H5; eauto).
  eapply (IHl from to _ g2) in H8; eauto. rewrite <- H8.
  eapply fr_raw_mark; eauto.
Qed.

Lemma forward_p2t_inr_roots: forall v n roots g,
    forward_p2forward_t (inr (v, n)) roots g = forward_p2forward_t (inr (v, n)) nil g.
Proof. intros. simpl. reflexivity. Qed.

Lemma svfl_add_tail: forall from to v l roots i g1 g2 g3,
    scan_vertex_for_loop from to v l g1 g2 ->
    forward_relation from to 0
                     (forward_p2forward_t (inr (v, Z.of_nat i)) roots g2) g2 g3 ->
    scan_vertex_for_loop from to v (l +:: i) g1 g3.
Proof.
  do 4 intro. revert from to v. induction l; intros; inversion H; subst.
  - simpl. rewrite forward_p2t_inr_roots in H0.
    apply svfl_cons with g3. 1: assumption. constructor.
  - simpl app. apply svfl_cons with g4. 1: assumption.
    apply IHl with roots g2; assumption.
Qed.

Lemma svwl_add_tail_no_scan: forall from to l g1 g2 i,
    scan_vertex_while_loop from to l g1 g2 -> gen_has_index g2 to i ->
    no_scan g2 (to, i) -> scan_vertex_while_loop from to (l +:: i) g1 g2.
Proof.
  do 3 intro. revert from to. induction l; intros; inversion H; subst.
  - simpl. apply svwl_no_scan; assumption.
  - simpl app. apply svwl_no_scan; try assumption. apply IHl; assumption.
  - simpl app. apply svwl_scan with g3; try assumption. apply IHl; assumption.
Qed.

Lemma svwl_add_tail_scan: forall from to l g1 g2 g3 i,
    scan_vertex_while_loop from to l g1 g2 -> gen_has_index g2 to i ->
    ~ no_scan g2 (to, i) ->
    scan_vertex_for_loop
      from to (to, i)
      (nat_inc_list (length (raw_fields (vlabel g2 (to, i)))))
      g2 g3 ->
    scan_vertex_while_loop from to (l +:: i) g1 g3.
Proof.
  do 3 intro. revert from to. induction l; intros; inversion H; subst.
  - simpl. apply svwl_scan with g3; try assumption. constructor.
  - simpl app. apply svwl_no_scan; try assumption. apply IHl with g2; assumption.
  - simpl app. apply svwl_scan with g4; try assumption. apply IHl with g2; assumption.
Qed.

Lemma root_in_outlier: forall (roots: roots_t) outlier p,
    In (inl (inr p)) roots ->
    incl (filter_sum_right (filter_sum_left roots)) outlier -> In p outlier.
Proof.
  intros. apply H0. rewrite <- filter_sum_right_In_iff, <- filter_sum_left_In_iff.
  assumption.
Qed.

Definition do_generation_relation (from to: nat) (f_info: fun_info)
           (roots roots': roots_t) (g g': LGraph): Prop := exists g1 g2,
    forward_roots_relation from to f_info roots g roots' g1 /\
    do_scan_relation from to (number_of_vertices (nth_gen g to)) g1 g2 /\
    g' = reset_graph from g2.

Definition space_address (t_info: thread_info) (gen: nat) :=
  offset_val (SPACE_STRUCT_SIZE * Z.of_nat gen) (ti_heap_p t_info).

Definition enough_space_to_have_g g t_info from to: Prop :=
  graph_gen_size g from <= rest_gen_size t_info to.

Definition roots_fi_compatible (roots: roots_t) f_info: Prop :=
  Zlength roots = Zlength (live_roots_indices f_info) /\
  forall i j,
    0 <= i < Zlength roots -> 0 <= j < Zlength roots ->
    Znth i (live_roots_indices f_info) = Znth j (live_roots_indices f_info) ->
    Znth i roots = Znth j roots.

Definition do_generation_condition g t_info roots f_info from to: Prop :=
  enough_space_to_have_g g t_info from to /\ graph_has_gen g from /\
  graph_has_gen g to /\ copy_compatible g /\ no_dangling_dst g /\
  0 < gen_size t_info to /\ gen_unmarked g to /\ roots_fi_compatible roots f_info.

Lemma dgc_imply_fc: forall g t_info roots f_info from to,
    do_generation_condition g t_info roots f_info from to ->
    forward_condition g t_info from to /\ 0 < gen_size t_info to /\
    gen_unmarked g to /\ roots_fi_compatible roots f_info.
Proof.
  intros. destruct H. do 2 (split; [|intuition]). clear H0. red in H |-* .
  transitivity (graph_gen_size g from); [apply unmarked_gen_size_le | assumption].
Qed.

Lemma upd_roots_Zlength: forall from to p g roots f_info,
    Zlength roots = Zlength (live_roots_indices f_info) ->
    Zlength (upd_roots from to p g roots f_info) = Zlength roots.
Proof.
  intros. unfold upd_roots. destruct p. 2: reflexivity.
  destruct (Znth z roots). 1: destruct s; reflexivity. if_tac. 2: reflexivity.
  destruct (raw_mark (vlabel g v)); rewrite upd_bunch_Zlength; auto.
Qed.

Lemma frl_roots_Zlength: forall from to f_info l roots g roots' g',
    Zlength roots = Zlength (live_roots_indices f_info) ->
    forward_roots_loop from to f_info l roots g roots' g' ->
    Zlength roots' = Zlength roots.
Proof.
  intros. induction H0. 1: reflexivity. rewrite IHforward_roots_loop.
  - apply upd_roots_Zlength; assumption.
  - rewrite upd_roots_Zlength; assumption.
Qed.

Opaque upd_roots.

Lemma frl_add_tail: forall from to f_info l i g1 g2 g3 roots1 roots2,
    forward_roots_loop from to f_info l roots1 g1 roots2 g2 ->
    forward_relation from to O (root2forward (Znth (Z.of_nat i) roots2)) g2 g3 ->
    forward_roots_loop
      from to f_info (l +:: i) roots1 g1
      (upd_roots from to (inl (Z.of_nat i)) g2 roots2 f_info) g3.
Proof.
  intros ? ? ? ?. induction l; intros.
  - simpl. inversion H. subst. apply frl_cons with g3. 2: constructor. apply H0.
  - inversion H. subst. clear H. simpl app. apply frl_cons with g4. 1: assumption.
    apply IHl; assumption.
Qed.

Transparent upd_roots.

Lemma frr_vertex_address: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, closure_has_v g1 v -> vertex_address g1 v = vertex_address g2 v.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_vertex_address; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_closure_has_v; eauto.
Qed.

Lemma frr_closure_has_v: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, closure_has_v g1 v -> closure_has_v g2 v.
Proof.
  intros. induction H0. 1: assumption. apply IHforward_roots_loop.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_closure_has_v; eauto.
Qed.

Lemma frr_gen_unmarked: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen, gen <> from -> gen_unmarked g1 gen -> gen_unmarked g2 gen.
Proof.
  intros. induction H0. 1: assumption. apply IHforward_roots_loop.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_gen_unmarked; eauto.
Qed.

Definition graph_gen_clear (g: LGraph) (gen: nat) :=
  number_of_vertices (nth_gen g gen) = O.

Lemma pvs_reset_unchanged: forall g gen n l,
    previous_vertices_size (reset_graph gen g) n l =
    previous_vertices_size g n l.
Proof.
  intros. unfold previous_vertices_size. apply fold_left_ext. intros.
  unfold vertex_size_accum. f_equal. unfold vertex_size. simpl.
  rewrite remove_ve_vlabel_unchanged. reflexivity.
Qed.

Lemma graph_thread_info_compatible_reset: forall g t_info gen,
    graph_thread_info_compatible g t_info ->
    graph_thread_info_compatible (reset_graph gen g)
                                 (reset_nth_heap_thread_info gen t_info).
Proof.
  intros. destruct H as [? [? ?]].
  split; [|split]; [|simpl; rewrite reset_nth_gen_info_length..].
  - rewrite gsc_iff by
        (simpl; rewrite remove_ve_glabel_unchanged, reset_nth_space_length,
                reset_nth_gen_info_length; assumption).
    intros n ?. rewrite gsc_iff in H by assumption. rewrite graph_has_gen_reset in H2.
    specialize (H _ H2). red in H. simpl. unfold nth_gen, nth_space in *. simpl.
    rewrite remove_ve_glabel_unchanged. destruct (Nat.eq_dec n gen).
    + subst gen. red in H2. rewrite reset_nth_gen_info_same.
      rewrite reset_nth_space_same by omega. intuition.
    + rewrite reset_nth_gen_info_diff, reset_nth_space_diff by assumption.
      destruct H as [? [? ?]]. split. 1: assumption. split. 1: assumption.
      rewrite pvs_reset_unchanged. assumption.
  - rewrite remove_ve_glabel_unchanged.
    destruct (le_lt_dec (length (spaces (ti_heap t_info))) gen).
    + rewrite reset_nth_space_overflow; assumption.
    + rewrite reset_nth_space_Znth by assumption. rewrite <- upd_Znth_map. simpl.
      remember (spaces (ti_heap t_info)).
      assert (0 <= Z.of_nat gen < Zlength l0) by (rewrite Zlength_correct; omega).
      replace (space_start (Znth (Z.of_nat gen) l0))
        with (Znth (Z.of_nat gen) (map space_start l0)) by (rewrite Znth_map; auto).
      rewrite upd_Znth_unchanged; [|rewrite Zlength_map]; assumption.
  - rewrite remove_ve_glabel_unchanged, reset_nth_space_length. assumption.
Qed.

Lemma upd_bunch_rf_compatible: forall f_info roots z r,
    roots_fi_compatible roots f_info ->
    roots_fi_compatible (upd_bunch z f_info roots r) f_info.
Proof.
  intros. unfold roots_fi_compatible in *. destruct H.
  assert (Zlength (upd_bunch z f_info roots r) = Zlength (live_roots_indices f_info))
    by (rewrite upd_bunch_Zlength; assumption). split; intros. 1: assumption.
  rewrite H1 in *. rewrite <- H in *.
  destruct (Z.eq_dec (Znth i (live_roots_indices f_info))
                     (Znth z (live_roots_indices f_info))).
  - rewrite !upd_bunch_same; try assumption; try reflexivity.
    rewrite H4 in e; assumption.
  - rewrite !upd_bunch_diff; try assumption; [apply H0 | rewrite <- H4]; assumption.
Qed.

Lemma upd_roots_rf_compatible: forall from to f_info roots p g,
    roots_fi_compatible roots f_info ->
    roots_fi_compatible (upd_roots from to p g roots f_info) f_info.
Proof.
  intros. unfold upd_roots. destruct p; [|assumption]. destruct (Znth z roots).
  1: destruct s; assumption. if_tac. 2: assumption.
  destruct (raw_mark (vlabel g v)); apply upd_bunch_rf_compatible; assumption.
Qed.

Definition np_roots_rel from f_info (roots roots': roots_t) (l: list Z) : Prop :=
  let lri := live_roots_indices f_info in
  let maped_lri := (map (flip Znth lri) l) in
  forall v j, Znth j roots' = inr v ->
              (In (Znth j lri) maped_lri -> vgeneration v <> from) /\
              (~ In (Znth j lri) maped_lri -> Znth j roots = inr v).

Lemma upd_roots_not_pointing: forall from to i g roots f_info roots',
    copy_compatible g -> roots_graph_compatible roots g -> from <> to ->
    0 <= i < Zlength roots -> roots_fi_compatible roots f_info ->
    roots' = upd_roots from to (inl i) g roots f_info ->
    np_roots_rel from f_info roots roots' [i].
Proof.
  intros. unfold np_roots_rel. intros. simpl. unfold flip.
  assert (Zlength roots' = Zlength roots) by
      (rewrite H4; apply upd_roots_Zlength, (proj1 H3)).
  assert (0 <= j < Zlength roots). {
    rewrite <- H6. destruct (Z_lt_le_dec j (Zlength roots')).
    2: rewrite Znth_outofbounds in H5 by omega; inversion H5. split; auto.
    destruct (Z_lt_le_dec j 0); auto. rewrite Znth_outofbounds in H5 by omega.
    inversion H5. } simpl in H4. destruct H3. destruct (Znth i roots) eqn:? .
  - assert (roots' = roots) by (destruct s; assumption). clear H4. subst roots'.
    split; intros; auto. destruct H4; auto.
    destruct H3. apply H8 in H4; try assumption. rewrite Heqr, H5 in H4. inversion H4.
  - if_tac in H4.
    + destruct (raw_mark (vlabel g v0)) eqn: ?; subst; split; intros.
      * destruct H4; auto. symmetry in H4. rewrite upd_bunch_same in H5 by assumption.
        inversion H5. red in H0. rewrite Forall_forall in H0.
        assert (graph_has_v g v0). {
          apply H0. rewrite <- filter_sum_right_In_iff, <- Heqr.
          apply Znth_In; assumption. } destruct (H _ H9 Heqb) as [_ ?]. auto.
      * assert (Znth j (live_roots_indices f_info) <>
                Znth i (live_roots_indices f_info)) by intuition. clear H4.
        rewrite upd_bunch_diff in H5; assumption.
      * destruct H4; auto. symmetry in H4. rewrite upd_bunch_same in H5 by assumption.
        inversion H5. unfold new_copied_v. simpl. auto.
      * assert (Znth j (live_roots_indices f_info) <>
                Znth i (live_roots_indices f_info)) by intuition. clear H4.
        rewrite upd_bunch_diff in H5; assumption.
    + split; intros; subst roots'; auto. destruct H10; auto.
      apply H8 in H4; try assumption. rewrite Heqr, H5 in H4. inversion H4.
      subst v0. assumption.
Qed.

Lemma np_roots_rel_cons: forall roots1 roots2 roots3 from f_info i l,
    np_roots_rel from f_info roots1 roots2 [i] ->
    np_roots_rel from f_info roots2 roots3 l ->
    np_roots_rel from f_info roots1 roots3 (i :: l).
Proof.
  intros. unfold np_roots_rel in *. intros. simpl. specialize (H0 _ _ H1).
  destruct H0. split; intros; unfold flip in H2 at 1.
  - destruct (in_dec Z.eq_dec (Znth j (live_roots_indices f_info))
                     (map (flip Znth (live_roots_indices f_info)) l)).
    1: apply H0; assumption. destruct H3. 2: contradiction. unfold flip in H3.
    specialize (H2 n). specialize (H _ _ H2). destruct H. apply H. simpl. unfold flip.
    left; assumption.
  - unfold flip in H3 at 1. apply Decidable.not_or in H3. destruct H3.
    specialize (H2 H4). specialize (H _ _ H2). destruct H. apply H5. simpl. tauto.
Qed.

Lemma fr_copy_compatible: forall depth from to p g g',
    from <> to -> graph_has_gen g to -> forward_relation from to depth p g g' ->
    copy_compatible g -> copy_compatible g'.
Proof.
  intros. remember (fun (g: LGraph) (v: VType) (x: nat) => True) as Q.
  remember (fun g1 g2 (v: VType) => copy_compatible g1 -> copy_compatible g2) as P.
  remember (fun (x y: nat) => x <> y) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H3; clear H3; intros; try assumption; try reflexivity.
  - apply H4, H3. assumption.
  - subst from0. apply lcv_copy_compatible; auto.
  - exact (O, O).
Qed.

Lemma fr_right_roots_graph_compatible: forall depth from to e g g' roots,
    graph_has_gen g to -> forward_p_compatible (inr e) roots g from ->
    forward_relation from to depth (forward_p2forward_t (inr e) [] g) g g' ->
    roots_graph_compatible roots g -> roots_graph_compatible roots g'.
Proof.
  intros. simpl in H1, H0. destruct e. destruct H0 as [_ [_ [? _]]]. rewrite H0 in H1.
  simpl in H1. remember (fun (g: LGraph) (v: nat) (x: nat) => True) as Q.
  remember (fun g1 g2 (x: nat) => roots_graph_compatible roots g1->
                                  roots_graph_compatible roots g2) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop
                depth from to (field2forward (Znth z (make_fields g v))) g g' _ Q P R).
  subst Q P R. apply H3; clear H3; intros; try assumption; try reflexivity.
  - apply H4, H3. assumption.
  - apply lcv_rgc_unchanged; assumption.
Qed.

Lemma fl_edge_roots_graph_compatible: forall depth from to l g g' v roots,
    vgeneration v <> from ->
    graph_has_gen g to -> graph_has_v g v -> raw_mark (vlabel g v) = false ->
    forward_loop from to depth (map (fun x : nat => inr (v, Z.of_nat x)) l) g g' ->
    (forall i, In i l -> i < length (raw_fields (vlabel g v)))%nat ->
    roots_graph_compatible roots g -> roots_graph_compatible roots g'.
Proof.
  do 4 intro. induction l; intros; simpl in H3; inversion H3; subst. 1: assumption.
  cut (roots_graph_compatible roots g2).
  - intros. apply (IHl g2 _ v); try assumption.
    + rewrite <- fr_graph_has_gen; eauto.
    + eapply fr_graph_has_v; eauto.
    + rewrite <- H2. symmetry. eapply fr_raw_mark; eauto.
    + assert (raw_fields (vlabel g v) = raw_fields (vlabel g2 v)) by
          (eapply fr_raw_fields; eauto). rewrite <- H7.
      intros; apply H4; right; assumption.
  - specialize (H4 _ (in_eq a l)). eapply fr_right_roots_graph_compatible; eauto.
    simpl. intuition. rewrite Zlength_correct. apply inj_lt; assumption.
Qed.

Lemma fr_roots_outlier_compatible: forall from to p g roots f_info outlier,
    roots_outlier_compatible roots outlier ->
    roots_outlier_compatible (upd_roots from to p g roots f_info) outlier.
Proof.
  intros. destruct p; simpl in *. 2: assumption. destruct (Znth z roots) eqn: ?.
  + destruct s; assumption.
  + if_tac. 2: assumption.
    destruct (raw_mark (vlabel g v)); apply upd_roots_outlier_compatible; assumption.
Qed.

Lemma fr_roots_graph_compatible: forall depth from to p g g' roots f_info,
    graph_has_gen g to -> forward_p_compatible p roots g from -> copy_compatible g ->
    forward_relation from to depth (forward_p2forward_t p roots g) g g' ->
    from <> to -> roots_graph_compatible roots g ->
    roots_graph_compatible (upd_roots from to p g roots f_info) g'.
Proof.
  intros. destruct p.
  - simpl in *. destruct (Znth z roots) eqn: ?; simpl in H2.
    + destruct s; inversion H2; subst; assumption.
    + assert (graph_has_v g v). {
        red in H4. rewrite Forall_forall in H4. apply H4.
        rewrite <- filter_sum_right_In_iff. rewrite <- Heqr. apply Znth_In.
        assumption. }
      inversion H2; destruct (Nat.eq_dec (vgeneration v) from);
        try contradiction; subst; try assumption.
      * destruct (raw_mark (vlabel g' v)) eqn:? . 2: inversion H9.
        apply upd_bunch_graph_compatible. 1: assumption. specialize (H1 _ H5 Heqb).
        destruct H1; assumption.
      * destruct (raw_mark (vlabel g v)) eqn:? . 1: inversion H9.
        apply lcv_roots_graph_compatible; assumption.
      * destruct (raw_mark (vlabel g v)) eqn:? . 1: inversion H8.
        remember (upd_bunch z f_info roots (inr (new_copied_v g to))) as roots'.
        assert (roots_graph_compatible roots' new_g) by
            (subst; subst new_g; apply lcv_roots_graph_compatible; assumption).
        assert (raw_mark (vlabel new_g (new_copied_v g to)) = false). {
          subst new_g. unfold lgraph_copy_v. rewrite <- lmc_raw_mark.
          - rewrite lacv_vlabel_new. assumption.
          - unfold new_copied_v. destruct v. destruct H5. simpl in H7.
            red in H7. intro HS. inversion HS. omega. }
        assert (graph_has_v new_g (new_copied_v g to)) by
            (subst new_g; apply lcv_graph_has_v_new; assumption).
        unfold vertex_pos_pairs in H10.
        remember (nat_inc_list
                    (length (raw_fields (vlabel new_g (new_copied_v g to))))).
        eapply (fl_edge_roots_graph_compatible
                  depth0 (vgeneration v) to l new_g); eauto.
        -- unfold new_copied_v. simpl; auto.
        -- subst new_g. rewrite <- lcv_graph_has_gen; assumption.
        -- intros. subst l. rewrite nat_inc_list_In_iff in H11. assumption.
  - simpl. eapply fr_right_roots_graph_compatible; eauto.
Qed.

Lemma fr_roots_compatible: forall depth from to p g g' roots f_info outlier,
    graph_has_gen g to -> forward_p_compatible p roots g from -> copy_compatible g ->
    forward_relation from to depth (forward_p2forward_t p roots g) g g' ->
    roots_compatible g outlier roots -> from <> to ->
    roots_compatible g' outlier (upd_roots from to p g roots f_info).
Proof.
  intros. destruct H3. split.
  - apply fr_roots_outlier_compatible; assumption.
  - eapply fr_roots_graph_compatible; eauto.
Qed.

Lemma frl_not_pointing: forall from to f_info l roots1 g1 roots2 g2,
    copy_compatible g1 -> roots_graph_compatible roots1 g1 -> from <> to ->
    (forall i, In i l -> i < length roots1)%nat -> roots_fi_compatible roots1 f_info ->
    forward_roots_loop from to f_info l roots1 g1 roots2 g2 -> graph_has_gen g1 to ->
    np_roots_rel from f_info roots1 roots2 (map Z.of_nat l).
Proof.
  do 4 intro. induction l; intros; inversion H4; subst.
  1: red; simpl; intros; intuition.
  remember (upd_roots from to (inl (Z.of_nat a)) g1 roots1 f_info) as roots3.
  simpl. apply np_roots_rel_cons with roots3.
  - apply (upd_roots_not_pointing from to _ g1); try assumption.
    split. 1: omega. rewrite Zlength_correct. apply inj_lt. apply H2. left; auto.
  - assert (Zlength roots3 = Zlength roots1) by
        (subst roots3; apply upd_roots_Zlength; apply (proj1 H3)).
    apply (IHl _ g3 _ g2); auto.
    + apply fr_copy_compatible in H8; assumption.
    + subst roots3. eapply fr_roots_graph_compatible; eauto. simpl. split. 1: omega.
      specialize (H2 _ (in_eq a l)). rewrite Zlength_correct. apply inj_lt; assumption.
    + intros. subst roots3. rewrite <- ZtoNat_Zlength, H6, ZtoNat_Zlength.
      apply H2; right; assumption.
    + subst roots3; apply upd_roots_rf_compatible; assumption.
    + rewrite <- (fr_graph_has_gen _ _ _ _ _ _ H5 H8); assumption.
Qed.

Definition roots_have_no_gen (roots: roots_t) (gen: nat): Prop :=
  forall v, In (inr v) roots -> vgeneration v <> gen.

Lemma frr_not_pointing: forall from to f_info roots1 g1 roots2 g2,
    copy_compatible g1 -> roots_graph_compatible roots1 g1 -> from <> to ->
    graph_has_gen g1 to -> roots_fi_compatible roots1 f_info ->
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    roots_have_no_gen roots2 from.
Proof.
  intros. unfold forward_roots_relation in H0. eapply frl_not_pointing in H0; eauto.
  red; intros. 2: intros; rewrite nat_inc_list_In_iff in H5; assumption. red in H0.
  apply In_Znth in H5. destruct H5 as [i [? ?]]. specialize (H0 _ _ H6). destruct H0.
  apply H0. destruct H3 as [? _].
  replace (length roots1) with (length (live_roots_indices f_info)) by
      (rewrite <- !ZtoNat_Zlength, H3; reflexivity).
  remember (live_roots_indices f_info). rewrite map_map. unfold flip.
  assert (map (fun x : nat => Znth (Z.of_nat x) l) (nat_inc_list (length l)) = l). {
    clear. rewrite Znth_list_eq. split.
    - rewrite Zlength_map, !Zlength_correct, nat_inc_list_length. reflexivity.
    - intros. rewrite Zlength_map in H. rewrite Znth_map by assumption. f_equal.
      rewrite <- nth_Znth by assumption. rewrite nat_inc_list_nth.
      1: apply Z2Nat.id; omega. rewrite Zlength_correct, nat_inc_list_length in H.
      rep_omega. } rewrite H8. clear H8. apply Znth_In. apply frl_roots_Zlength in H4.
  2: subst; assumption. rewrite <- H3, <- H4. assumption.
Qed.

Lemma fta_compatible_reset: forall g t_info fi r gen,
    fun_thread_arg_compatible g t_info fi r ->
    fun_thread_arg_compatible (reset_graph gen g)
                              (reset_nth_heap_thread_info gen t_info) fi r.
Proof.
  intros. unfold fun_thread_arg_compatible in *. rewrite Znth_list_eq in *.
  destruct H. rewrite !Zlength_map in *. split. 1: assumption. intros.
  specialize (H0 _ H1). rewrite Znth_map in * by assumption. simpl. rewrite <- H0.
  destruct (Znth j r) eqn: ?; simpl. 1: reflexivity.
  apply vertex_address_reset.
Qed.

Lemma gen_has_index_reset: forall (g: LGraph) gen1 gen2 idx,
    gen_has_index (reset_graph gen1 g) gen2 idx <->
    gen_has_index g gen2 idx /\ gen1 <> gen2.
Proof.
  intros. unfold gen_has_index. unfold nth_gen. simpl.
  rewrite remove_ve_glabel_unchanged. destruct (Nat.eq_dec gen1 gen2).
  - subst. rewrite reset_nth_gen_info_same. simpl. intuition.
  - rewrite reset_nth_gen_info_diff by auto. intuition.
Qed.

Lemma graph_has_v_reset: forall (g: LGraph) gen v,
    graph_has_v (reset_graph gen g) v <->
    graph_has_v g v /\ gen <> vgeneration v.
Proof.
  intros. split; intros; destruct v; unfold graph_has_v in *; simpl in *.
  - rewrite graph_has_gen_reset, gen_has_index_reset in H. intuition.
  - rewrite graph_has_gen_reset, gen_has_index_reset. intuition.
Qed.

Lemma rgc_reset: forall g gen roots,
    roots_graph_compatible roots g ->
    roots_have_no_gen roots gen ->
    roots_graph_compatible roots (reset_graph gen g).
Proof.
  intros. red in H |-*. rewrite Forall_forall in *. intros.
  specialize (H _ H1). destruct H. split.
  - rewrite graph_has_gen_reset. assumption.
  - rewrite gen_has_index_reset. split. 1: assumption.
    rewrite <- filter_sum_right_In_iff in H1. apply H0 in H1. auto.
Qed.

Lemma roots_compatible_reset: forall g gen outlier roots,
    roots_compatible g outlier roots ->
    roots_have_no_gen roots gen ->
    roots_compatible (reset_graph gen g) outlier roots.
Proof. intros. destruct H. split; [|apply rgc_reset]; assumption. Qed.

Lemma outlier_compatible_reset: forall g outlier gen,
    outlier_compatible g outlier ->
    outlier_compatible (reset_graph gen g) outlier.
Proof.
  intros. unfold outlier_compatible in *. intros. simpl.
  rewrite remove_ve_vlabel_unchanged. apply H.
  rewrite graph_has_v_reset in H0. destruct H0. assumption.
Qed.

Lemma super_compatible_reset: forall g t_info roots f_info outlier gen,
    roots_have_no_gen roots gen ->
    super_compatible (g, t_info, roots) f_info outlier ->
    super_compatible (reset_graph gen g,
                      reset_nth_heap_thread_info gen t_info, roots) f_info outlier.
Proof.
  intros. destruct H0 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply graph_thread_info_compatible_reset; assumption.
  - apply fta_compatible_reset; assumption.
  - apply roots_compatible_reset; assumption.
  - apply outlier_compatible_reset; assumption.
Qed.

Lemma tir_reset: forall t_info gen,
    thread_info_relation t_info (reset_nth_heap_thread_info gen t_info).
Proof.
  intros. split; simpl. 1: reflexivity.
  unfold gen_size, nth_space. simpl.
  destruct (le_lt_dec (length (spaces (ti_heap t_info))) gen).
  - rewrite reset_nth_space_overflow by assumption. split; intros; reflexivity.
  - split; intros; destruct (Nat.eq_dec n gen).
    + subst. rewrite reset_nth_space_same; simpl; [reflexivity | assumption].
    + rewrite reset_nth_space_diff; [reflexivity | assumption].
    + subst. rewrite reset_nth_space_same; simpl; [reflexivity | assumption].
    + rewrite reset_nth_space_diff; [reflexivity | assumption].
Qed.

Lemma frr_graph_has_gen: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to ->
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen, graph_has_gen g1 gen <-> graph_has_gen g2 gen.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_graph_has_gen; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma svwl_graph_has_gen: forall from to l g1 g2,
    graph_has_gen g1 to ->
    scan_vertex_while_loop from to l g1 g2 ->
    forall gen, graph_has_gen g1 gen <-> graph_has_gen g2 gen.
Proof.
  intros ? ? ?. induction l; intros; inversion H0; subst. 1: reflexivity.
  - apply IHl; assumption.
  - transitivity (graph_has_gen g3 gen).
    + eapply svfl_graph_has_gen; eauto.
    + apply IHl. 2: assumption. rewrite <- svfl_graph_has_gen; eauto.
Qed.

Lemma do_gen_graph_has_gen: forall from to f_info roots roots' g g',
    graph_has_gen g to ->
    do_generation_relation from to f_info roots roots' g g' ->
    forall gen, graph_has_gen g gen <-> graph_has_gen g' gen.
Proof.
  intros. destruct H0 as [g1 [g2 [? [? ?]]]]. transitivity (graph_has_gen g1 gen).
  - eapply frr_graph_has_gen; eauto.
  - transitivity (graph_has_gen g2 gen).
    + destruct H1 as [n [? ?]]. eapply svwl_graph_has_gen; eauto.
      rewrite <- frr_graph_has_gen; eauto.
    + subst g'. rewrite graph_has_gen_reset. reflexivity.
Qed.

Definition graph_unmarked (g: LGraph): Prop := forall v,
    graph_has_v g v -> raw_mark (vlabel g v) = false.

Lemma graph_gen_unmarked_iff: forall g,
    graph_unmarked g <-> forall gen, gen_unmarked g gen.
Proof.
  intros. unfold graph_unmarked, gen_unmarked. split; intros.
  - apply H. unfold graph_has_v. simpl. split; assumption.
  - destruct v as [gen idx]. destruct H0. simpl in *. apply H; assumption.
Qed.

Lemma graph_unmarked_copy_compatible: forall g,
    graph_unmarked g -> copy_compatible g.
Proof.
  intros. red in H |-* . intros. apply H in H0. rewrite H0 in H1. inversion H1.
Qed.

Lemma gen_unmarked_reset_same: forall g gen,
    gen_unmarked (reset_graph gen g) gen.
Proof.
  intros. red. intros. rewrite graph_has_gen_reset in H.
  rewrite gen_has_index_reset in H0. destruct H0. contradiction.
Qed.

Lemma gen_unmarked_reset_diff: forall g gen1 gen2,
    gen_unmarked g gen2 -> gen_unmarked (reset_graph gen1 g) gen2.
Proof.
  intros. unfold gen_unmarked in *. intros. rewrite graph_has_gen_reset in H0.
  rewrite gen_has_index_reset in H1. destruct H1. specialize (H H0 _ H1). simpl.
  rewrite remove_ve_vlabel_unchanged. assumption.
Qed.

Lemma do_gen_graph_unmarked: forall from to f_info roots roots' g g',
    graph_has_gen g to ->
    do_generation_relation from to f_info roots roots' g g' ->
    graph_unmarked g -> graph_unmarked g'.
Proof.
  intros. destruct H0 as [g1 [g2 [? [? ?]]]]. rewrite graph_gen_unmarked_iff in H1.
  assert (forall gen, from <> gen -> gen_unmarked g1 gen) by
      (intros; eapply frr_gen_unmarked; eauto).
  assert (forall gen, from <> gen -> gen_unmarked g2 gen). {
    intros. destruct H2 as [n [? ?]]. eapply (svwl_gen_unmarked _ _ _ g1 g2); eauto.
    rewrite <- frr_graph_has_gen; eauto. } subst g'.
  rewrite graph_gen_unmarked_iff. intros. destruct (Nat.eq_dec from gen).
  - subst. apply gen_unmarked_reset_same.
  - apply gen_unmarked_reset_diff. apply H5. assumption.
Qed.

Definition graph_has_e (g: LGraph) (e: EType): Prop :=
  let v := fst e in graph_has_v g v /\ In e (get_edges g v).

Definition gen2gen_no_edge (g: LGraph) (gen1 gen2: nat): Prop :=
  forall vidx eidx, let e := (gen1, vidx, eidx) in
                    graph_has_e g e -> vgeneration (dst g e) <> gen2.

Definition no_edge2gen (g: LGraph) (gen: nat): Prop :=
  forall another, another <> gen -> gen2gen_no_edge g another gen.

Definition egeneration (e: EType): nat := vgeneration (fst e).

Lemma get_edges_reset: forall g gen v,
    get_edges (reset_graph gen g) v = get_edges g v.
Proof.
  intros. unfold get_edges, make_fields. simpl. rewrite remove_ve_vlabel_unchanged.
  reflexivity.
Qed.

Lemma graph_has_e_reset: forall g gen e,
    graph_has_e (reset_graph gen g) e <->
    graph_has_e g e /\ gen <> egeneration e.
Proof.
  intros. unfold graph_has_e, egeneration. destruct e as [v idx]. simpl.
  rewrite graph_has_v_reset, get_edges_reset. intuition.
Qed.

Lemma gen2gen_no_edge_reset_inv: forall g gen1 gen2 gen3,
    gen1 <> gen2 -> gen2gen_no_edge (reset_graph gen1 g) gen2 gen3 ->
    gen2gen_no_edge g gen2 gen3.
Proof.
  intros. unfold gen2gen_no_edge. intros. red in H0. simpl in H0.
  specialize (H0 vidx eidx). rewrite remove_ve_dst_unchanged in H0. apply H0.
  rewrite graph_has_e_reset. unfold egeneration. simpl. split; assumption.
Qed.

Lemma gen2gen_no_edge_reset: forall g gen1 gen2 gen3,
    gen2gen_no_edge g gen2 gen3 ->
    gen2gen_no_edge (reset_graph gen1 g) gen2 gen3.
Proof.
  intros. unfold gen2gen_no_edge. intros. simpl. rewrite remove_ve_dst_unchanged.
  apply H. rewrite graph_has_e_reset in H0. destruct H0. assumption.
Qed.

Lemma fr_O_dst_unchanged_root: forall from to r g g',
    forward_relation from to O (root2forward r) g g' ->
    forall e, graph_has_v g (fst e) -> dst g e = dst g' e.
Proof.
  intros. destruct r; [destruct s|]; simpl in H; inversion H; subst; try reflexivity.
  simpl. rewrite pcv_dst_old. 1: reflexivity. destruct e as [[gen vidx] eidx].
  unfold graph_has_v in H0. unfold new_copied_v. simpl in *. destruct H0. intro.
  inversion H2. subst. red in H1. omega.
Qed.

Lemma frr_dst_unchanged: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall e, graph_has_v g1 (fst e) -> dst g1 e = dst g2 e.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_O_dst_unchanged_root; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_graph_has_v; eauto.
Qed.

Lemma fr_O_graph_has_v_inv: forall from to p g g',
    graph_has_gen g to -> forward_relation from to O p g g' ->
    forall v, graph_has_v g' v -> graph_has_v g v \/ v = new_copied_v g to.
Proof.
  intros. inversion H0; subst; try (left; assumption);
            [|subst new_g; rewrite <- lgd_graph_has_v in H1];
            apply lcv_graph_has_v_inv in H1; assumption.
Qed.

Definition gen_v_num (g: LGraph) (gen: nat): nat := number_of_vertices (nth_gen g gen).

Definition nth_gen_size (n: nat) := NURSERY_SIZE * two_p (Z.of_nat n).

Definition nth_gen_size_spec (tinfo: thread_info) (n: nat): Prop :=
  if Val.eq (nth_space tinfo n).(space_start) nullval
  then True
  else gen_size tinfo n = nth_gen_size n.

Definition ti_size_spec (tinfo: thread_info): Prop :=
  Forall (nth_gen_size_spec tinfo) (nat_inc_list (Z.to_nat MAX_SPACES)).

Definition safe_to_copy_gen g from to: Prop :=
  nth_gen_size from <= nth_gen_size to - graph_gen_size g to.

Lemma ngs_range: forall i,
    0 <= i < MAX_SPACES -> 0 <= nth_gen_size (Z.to_nat i) < MAX_SPACE_SIZE.
Proof.
  intros. unfold nth_gen_size. rewrite MAX_SPACES_eq in H.
  rewrite Z2Nat.id, NURSERY_SIZE_eq, Int.Zshiftl_mul_two_p,
  Z.mul_1_l, <- two_p_is_exp by omega. split.
  - cut (two_p (16 + i) > 0). 1: intros; omega. apply two_p_gt_ZERO. omega.
  - transitivity (two_p 28). 1: apply two_p_monotone_strict; omega.
    vm_compute. reflexivity.
Qed.

Lemma ngs_int_singed_range: forall i,
    0 <= i < MAX_SPACES ->
    Int.min_signed <= nth_gen_size (Z.to_nat i) <= Int.max_signed.
Proof.
  intros. apply ngs_range in H. destruct H. split.
  - transitivity 0. 2: assumption. vm_compute. intro HS; inversion HS.
  - apply Z.lt_le_incl. transitivity MAX_SPACE_SIZE. 1: assumption.
    vm_compute. reflexivity.
Qed.

Lemma ngs_S: forall i,
    0 <= i -> 2 * nth_gen_size (Z.to_nat i) = nth_gen_size (Z.to_nat (i + 1)).
Proof.
  intros. unfold nth_gen_size. rewrite !Z2Nat.id by omega.
  rewrite Z.mul_comm, <- Z.mul_assoc, (Z.mul_comm (two_p i)), <- two_p_S by assumption.
  reflexivity.
Qed.

Lemma space_start_isptr: forall (g: LGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (spaces (ti_heap t_info)) ->
    graph_has_gen g (Z.to_nat i) ->
    isptr (space_start (Znth i (spaces (ti_heap t_info)))).
Proof.
  intros. destruct (gt_gs_compatible _ _ H _ H1) as [? _].
  rewrite nth_space_Znth in H2. rewrite Z2Nat.id in H2 by omega. rewrite <- H2.
  apply start_isptr.
Qed.

Lemma space_start_isnull: forall (g: LGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (spaces (ti_heap t_info)) ->
    ~ graph_has_gen g (Z.to_nat i) ->
    space_start (Znth i (spaces (ti_heap t_info))) = nullval.
Proof.
  intros. unfold graph_has_gen in H1. destruct H as [_ [? ?]].
  rewrite Forall_forall in H. symmetry. apply H. rewrite <- map_skipn.
  apply List.in_map. remember (g_gen (glabel g)).
  replace i with (i - Zlength l + Zlength l) by omega.
  assert (length l <= Z.to_nat i)%nat by omega. clear H1.
  assert (0 <= i - Zlength l) by
      (rewrite <- ZtoNat_Zlength, <- Z2Nat.inj_le in H3; rep_omega).
  rewrite <- Znth_skipn by rep_omega. unfold nat_of_Z. rewrite ZtoNat_Zlength.
  apply Znth_In. split. 1: assumption. rewrite <- ZtoNat_Zlength, Zlength_skipn.
  rewrite (Z.max_r 0 (Zlength l)) by rep_omega. rewrite Z.max_r; rep_omega.
Qed.

Lemma space_start_is_pointer_or_null: forall (g: LGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (spaces (ti_heap t_info)) ->
    is_pointer_or_null (space_start (Znth i (spaces (ti_heap t_info)))).
Proof.
  intros. destruct (graph_has_gen_dec g (Z.to_nat i)).
  - apply val_lemmas.isptr_is_pointer_or_null. eapply space_start_isptr; eauto.
  - cut (space_start (Znth i (spaces (ti_heap t_info))) = nullval).
    + intros. rewrite H1. apply mapsto_memory_block.is_pointer_or_null_nullval.
    + eapply space_start_isnull; eauto.
Qed.

Lemma space_start_isptr_iff: forall (g: LGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (spaces (ti_heap t_info)) ->
    graph_has_gen g (Z.to_nat i) <->
    isptr (space_start (Znth i (spaces (ti_heap t_info)))).
Proof.
  intros. split; intros.
  - eapply space_start_isptr; eauto.
  - destruct (graph_has_gen_dec g (Z.to_nat i)). 1: assumption. exfalso.
    eapply space_start_isnull in n; eauto. rewrite n in H1. inversion H1.
Qed.

Lemma space_start_isnull_iff: forall (g: LGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (spaces (ti_heap t_info)) ->
    ~ graph_has_gen g (Z.to_nat i) <->
    space_start (Znth i (spaces (ti_heap t_info))) = nullval.
Proof.
  intros. split; intros. 1: eapply space_start_isnull; eauto.
  destruct (graph_has_gen_dec g (Z.to_nat i)). 2: assumption. exfalso.
  eapply space_start_isptr in g0; eauto. rewrite H1 in g0. inversion g0.
Qed.

Lemma ti_size_gen: forall (g : LGraph) (t_info : thread_info) (gen : nat),
    graph_thread_info_compatible g t_info ->
    graph_has_gen g gen -> ti_size_spec t_info ->
    gen_size t_info gen = nth_gen_size gen.
Proof.
  intros. red in H1. rewrite Forall_forall in H1.
  assert (0 <= (Z.of_nat gen) < Zlength (spaces (ti_heap t_info))). {
    split. 1: rep_omega. rewrite Zlength_correct. apply inj_lt.
    destruct H as [_ [_ ?]]. red in H0. omega. }
  assert (nth_gen_size_spec t_info gen). {
    apply H1. rewrite nat_inc_list_In_iff. destruct H as [_ [_ ?]]. red in H0.
    rewrite <- (spaces_size (ti_heap t_info)), ZtoNat_Zlength. omega. } red in H3.
  destruct (Val.eq (space_start (nth_space t_info gen)) nullval). 2: assumption.
  rewrite nth_space_Znth in e. erewrite <- space_start_isnull_iff in e; eauto.
  unfold graph_has_gen in e. exfalso; apply e. rewrite Nat2Z.id. assumption.
Qed.

Lemma ti_size_gt_0: forall (g : LGraph) (t_info : thread_info) (gen : nat),
    graph_thread_info_compatible g t_info ->
    graph_has_gen g gen -> ti_size_spec t_info -> 0 < gen_size t_info gen.
Proof.
  intros. erewrite ti_size_gen; eauto. unfold nth_gen_size. apply Z.mul_pos_pos.
  - rewrite NURSERY_SIZE_eq. vm_compute. reflexivity.
  - cut (two_p (Z.of_nat gen) > 0). 1: omega. apply two_p_gt_ZERO. omega.
Qed.

Local Close Scope Z_scope.

Lemma lcv_gen_v_num_to: forall g v to,
    graph_has_gen g to -> gen_v_num g to <= gen_v_num (lgraph_copy_v g v to) to.
Proof.
  intros. unfold gen_v_num, nth_gen; simpl. rewrite cvmgil_eq by assumption.
  simpl. omega.
Qed.

Lemma lgd_gen_v_num_to: forall g e v to,
    gen_v_num (labeledgraph_gen_dst g e v) to = gen_v_num g to.
Proof. intros. reflexivity. Qed.

Lemma fr_O_gen_v_num_to: forall from to p g g',
    graph_has_gen g to -> forward_relation from to O p g g' ->
    gen_v_num g to <= gen_v_num g' to.
Proof.
  intros. inversion H0; subst; try omega; [|subst new_g..].
  - apply lcv_gen_v_num_to; auto.
  - rewrite lgd_gen_v_num_to. omega.
  - rewrite lgd_gen_v_num_to. apply lcv_gen_v_num_to. assumption.
Qed.

Lemma frr_gen_v_num_to: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    gen_v_num g1 to <= gen_v_num g2 to.
Proof.
  intros. induction H0. 1: omega. transitivity (gen_v_num g2 to).
  - eapply fr_O_gen_v_num_to; eauto.
  - apply IHforward_roots_loop; rewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma frr_graph_has_v_inv: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, graph_has_v g2 v -> graph_has_v g1 v \/
                                  (vgeneration v = to /\
                                   gen_v_num g1 to <= vindex v < gen_v_num g2 to).
Proof.
  intros. induction H0. 1: left; assumption.
  assert (graph_has_gen g2 to) by (rewrite <- fr_graph_has_gen; eauto).
  specialize (IHforward_roots_loop H3 H1). destruct IHforward_roots_loop.
  - eapply (fr_O_graph_has_v_inv from to _ g1 g2) in H0; eauto. destruct H0.
    1: left; assumption. right. unfold new_copied_v in H0. subst v.
    clear H2. destruct H1. red in H1. simpl in *. unfold gen_v_num. omega.
  - right. destruct H4. split. 1: assumption. destruct H5. split. 2: assumption.
    apply fr_O_gen_v_num_to in H0; [omega | assumption].
Qed.

Lemma frr_raw_fields: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, graph_has_v g1 v -> raw_fields (vlabel g1 v) = raw_fields (vlabel g2 v).
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_raw_fields; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_graph_has_v; eauto.
Qed.

Lemma frr_gen2gen_no_edge: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen1 gen2, gen1 <> to -> gen2gen_no_edge g1 gen1 gen2 ->
                      gen2gen_no_edge g2 gen1 gen2.
Proof.
  intros. unfold gen2gen_no_edge in *. intros.
  cut (graph_has_e g1 (gen1, vidx, eidx)).
  - intros. erewrite <- frr_dst_unchanged; eauto. destruct H4. assumption.
  - destruct H3. eapply frr_graph_has_v_inv in H3; eauto. destruct H3 as [? | [? ?]].
    2: simpl in H3; contradiction. split. 1: simpl; assumption. simpl in *.
    cut (get_edges g1 (gen1, vidx) = get_edges g2 (gen1, vidx)).
    + intros; rewrite H5; assumption.
    + unfold get_edges. unfold make_fields. erewrite frr_raw_fields; eauto.
Qed.

Lemma fr_O_dst_unchanged_field: forall from to v n g g',
    forward_p_compatible (inr (v, Z.of_nat n)) [] g from ->
    forward_relation from to O (forward_p2forward_t (inr (v, Z.of_nat n)) [] g) g g' ->
    forall e, graph_has_v g (fst e) -> e <> (v, n) -> dst g e = dst g' e.
Proof.
  intros. simpl in *. destruct H as [? [? [? ?]]]. rewrite H4 in H0. simpl in H0.
  remember (Znth (Z.of_nat n) (make_fields g v)).
  assert (forall e0, inr e0 = Znth (Z.of_nat n) (make_fields g v) -> e0 <> e). {
    intros. symmetry in H6. apply make_fields_Znth_edge in H6. 2: assumption.
    rewrite Nat2Z.id in H6. rewrite <- H6 in H2. auto. }
  destruct f; [destruct s |]; simpl in H0; inversion H0; subst; try reflexivity.
  - subst new_g. rewrite lgd_dst_old. 1: reflexivity. apply H6; assumption.
  - subst new_g. rewrite lgd_dst_old. 2: apply H6; assumption. simpl.
    rewrite pcv_dst_old. 1: reflexivity. intro. rewrite H7 in H1. destruct H1.
    unfold new_copied_v in H8. simpl in H8. red in H8. omega.
Qed.

Lemma svfl_dst_unchanged: forall from to v l g1 g2,
    graph_has_v g1 v -> raw_mark (vlabel g1 v) = false -> vgeneration v <> from ->
    (forall i,  In i l -> i < length (raw_fields (vlabel g1 v))) ->
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall e, graph_has_v g1 (fst e) -> (forall i, In i l -> e <> (v, i)) ->
              dst g1 e = dst g2 e.
Proof.
  intros ? ? ? ?. induction l; intros; inversion H4; subst. 1: reflexivity.
  transitivity (dst g3 e).
  - eapply fr_O_dst_unchanged_field; eauto.
    + simpl. intuition. rewrite Zlength_correct. apply inj_lt. apply H2.
      left; reflexivity.
    + apply H6. left; reflexivity.
  - apply IHl; auto.
    + eapply fr_graph_has_v; eauto.
    + erewrite <- fr_raw_mark; eauto.
    + intros. erewrite <- fr_raw_fields; eauto. apply H2. right; assumption.
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_graph_has_v; eauto.
    + intros. apply H6. right; assumption.
Qed.

Lemma svwl_dst_unchanged: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    from <> to -> gen_unmarked g1 to ->
    forall e, graph_has_v g1 (fst e) ->
              (vgeneration (fst e) = to -> ~ In (vindex (fst e)) l) ->
              dst g1 e = dst g2 e.
Proof.
  intros. induction H0. 1: reflexivity.
  - apply IHscan_vertex_while_loop; try assumption. intros. specialize (H4 H7).
    intro. apply H4. right. assumption.
  - transitivity (dst g2 e).
    + eapply (svfl_dst_unchanged from to (to, i)); eauto.
      * split; assumption.
      * intros. rewrite nat_inc_list_In_iff in H8. assumption.
      * intros. destruct (Nat.eq_dec (vgeneration (fst e)) to).
        -- specialize (H4 e0). intro. subst e. simpl in H4. apply H4. left; auto.
        -- intro. subst e. simpl in n. apply n; reflexivity.
    + apply IHscan_vertex_while_loop.
      * erewrite <- svfl_graph_has_gen; eauto.
      * eapply svfl_gen_unmarked; eauto.
      * eapply svfl_graph_has_v; eauto.
      * intros. specialize (H4 H8). intro. apply H4. right; assumption.
Qed.

Lemma svfl_gen_v_num_to: forall from to v l g1 g2,
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    gen_v_num g1 to <= gen_v_num g2 to.
Proof.
  intros ? ? ? ?. induction l; intros; inversion H0; subst. 1: omega.
  assert (graph_has_gen g3 to) by (rewrite <- fr_graph_has_gen; eauto).
  specialize (IHl _ _ H1 H6). transitivity (gen_v_num g3 to); auto.
  eapply fr_O_gen_v_num_to; eauto.
Qed.

Lemma svfl_graph_has_v_inv: forall from to v l g1 g2,
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall v2,
      graph_has_v g2 v2 ->
      graph_has_v g1 v2 \/
      (vgeneration v2 = to /\ gen_v_num g1 to <= vindex v2 < gen_v_num g2 to).
Proof.
  intros ? ? ? ?. induction l; intros; inversion H0; subst. 1: left; assumption.
  assert (graph_has_gen g3 to) by (rewrite <- fr_graph_has_gen; eauto).
  specialize (IHl _ _ H2 H7 _ H1). destruct IHl.
  - eapply (fr_O_graph_has_v_inv from to _ g1 g3) in H4; eauto. destruct H4.
    1: left; assumption. right. clear -H1 H4. unfold new_copied_v in H4. subst.
    destruct H1. unfold gen_v_num. simpl in *. red in H0. omega.
  - right. destruct H3. split. 1: assumption. destruct H5. split; auto.
    eapply fr_O_gen_v_num_to in H4; [omega | assumption].
Qed.

Lemma svwl_graph_has_v: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall v, graph_has_v g1 v -> graph_has_v g2 v.
Proof.
  intros ? ? ?. induction l; intros; inversion H0; subst. 1: assumption.
  1: eapply IHl; eauto. assert (graph_has_gen g3 to) by
      (rewrite <- svfl_graph_has_gen; eauto). eapply IHl; eauto.
  eapply (svfl_graph_has_v _ _ _ _ g1 g3); eauto.
Qed.

Lemma svwl_gen_v_num_to: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    gen_v_num g1 to <= gen_v_num g2 to.
Proof.
  intros ? ? ?. induction l; intros; inversion H0; subst. 1: omega.
  1: apply IHl; auto. transitivity (gen_v_num g3 to).
  - eapply svfl_gen_v_num_to; eauto.
  - apply IHl; auto. rewrite <- svfl_graph_has_gen; eauto.
Qed.

Lemma svwl_graph_has_v_inv: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall v,
      graph_has_v g2 v ->
      graph_has_v g1 v \/
      (vgeneration v = to /\ gen_v_num g1 to <= vindex v < gen_v_num g2 to).
Proof.
  intros ? ? ?. induction l; intros; inversion H0; subst. 1: left; assumption.
  1: eapply IHl; eauto. assert (graph_has_gen g3 to) by
      (rewrite <- svfl_graph_has_gen; eauto).
  specialize (IHl _ _ H2 H9 _ H1). destruct IHl.
  - eapply svfl_graph_has_v_inv in H6; eauto. destruct H6; [left|right]. 1: assumption.
    destruct H6 as [? [? ?]]. split; [|split]; [assumption..|].
    apply svwl_gen_v_num_to in H9; [omega | assumption].
  - right. destruct H3 as [? [? ?]]. split; [|split]; try assumption.
    apply svfl_gen_v_num_to in H6; [omega | assumption].
Qed.

Lemma svwl_raw_fields: forall from to l g g',
    graph_has_gen g to -> scan_vertex_while_loop from to l g g' ->
    forall v, graph_has_v g v -> raw_fields (vlabel g v) = raw_fields (vlabel g' v).
Proof.
  do 3 intro. induction l; intros; inversion H0; subst. 1: reflexivity.
  1: eapply IHl; eauto. erewrite <- (IHl g2 g'); eauto.
  - eapply svfl_raw_fields; eauto.
  - rewrite <- svfl_graph_has_gen; eauto.
  - eapply svfl_graph_has_v; eauto.
Qed.

Lemma svwl_gen2gen_no_edge: forall from to l g1 g2,
    graph_has_gen g1 to -> from <> to -> gen_unmarked g1 to ->
    scan_vertex_while_loop from to l g1 g2 ->
    forall gen1 gen2, gen1 <> to -> gen2gen_no_edge g1 gen1 gen2 ->
                      gen2gen_no_edge g2 gen1 gen2.
Proof.
  intros. unfold gen2gen_no_edge in *. intros. destruct H5. simpl in H5.
  eapply svwl_graph_has_v_inv in H5; eauto. simpl in H5. destruct H5 as [? | [? ?]].
  2: contradiction. erewrite <- svwl_dst_unchanged; eauto.
  apply H4. split; simpl in *. 1: assumption.
  cut (get_edges g1 (gen1, vidx) = get_edges g2 (gen1, vidx)).
  + intros; rewrite H7; assumption.
  + unfold get_edges. unfold make_fields. erewrite svwl_raw_fields; eauto.
Qed.

Lemma frr_graph_has_v: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, graph_has_v g1 v -> graph_has_v g2 v.
Proof.
  intros. induction H0; subst. 1: assumption. cut (graph_has_v g2 v).
  - intros. apply IHforward_roots_loop; auto. erewrite <- fr_graph_has_gen; eauto.
  - eapply fr_graph_has_v; eauto.
Qed.

Lemma fr_O_dst_changed_field: forall from to v n g g',
    copy_compatible g -> no_dangling_dst g -> from <> to -> graph_has_gen g to ->
    forward_p_compatible (inr (v, Z.of_nat n)) [] g from ->
    forward_relation from to O (forward_p2forward_t (inr (v, Z.of_nat n)) [] g) g g' ->
    forall e, Znth (Z.of_nat n) (make_fields g' v) = inr e ->
              vgeneration (dst g' e) <> from.
Proof.
  intros. simpl in *. destruct H3 as [? [? [? ?]]]. rewrite H7 in H4. simpl in H4.
  assert (make_fields g v = make_fields g' v) by
      (unfold make_fields; erewrite fr_raw_fields; eauto). rewrite <- H9 in *.
  clear H9. remember (Znth (Z.of_nat n) (make_fields g v)). destruct f; inversion H5.
  subst. clear H5. symmetry in Heqf. pose proof Heqf.
  apply make_fields_Znth_edge in Heqf. 2: assumption. simpl in H4. subst.
  rewrite Nat2Z.id in *.
  inversion H4; subst; try assumption; subst new_g; rewrite lgd_dst_new.
  - apply H in H12. 1: destruct H12; auto. specialize (H0 _ H3). apply H0.
    unfold get_edges. rewrite <- filter_sum_right_In_iff, <- H5. apply Znth_In.
    rewrite make_fields_eq_length. assumption.
  - unfold new_copied_v. simpl. auto.
Qed.

Lemma fr_O_no_dangling_dst: forall from to p g g' roots,
    forward_p_compatible p roots g from -> graph_has_gen g to ->
    roots_graph_compatible roots g -> copy_compatible g ->
    forward_relation from to O (forward_p2forward_t p roots g) g g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  intros. inversion H3; subst; try assumption.
  - destruct p; simpl in H5.
    + destruct (Znth z roots) eqn:? ; [destruct s|]; simpl in H5; inversion H5.
      subst v0. clear H5. apply lcv_no_dangling_dst; auto. red in H1.
      rewrite Forall_forall in H1. apply H1. rewrite <- filter_sum_right_In_iff.
      rewrite <- Heqr. apply Znth_In. assumption.
    + destruct p. simpl in H. destruct H as [? [? [? ?]]]. rewrite H8 in H5.
      simpl in H5. destruct (Znth z (make_fields g v0)); [destruct s|];
                     simpl in H5; inversion H5.
  - subst new_g. apply lgd_no_dangling_dst_copied_vert; auto.
    destruct p; simpl in H5.
    + destruct (Znth z roots); [destruct s|]; simpl in H5; inversion H5.
    + destruct p. simpl in H. destruct H as [? [? [? ?]]]. rewrite H7 in H5.
      simpl in H5. destruct (Znth z (make_fields g v)) eqn:? ; [destruct s|];
                     simpl in H5; inversion H5. subst e0. clear H5.
      specialize (H4 _ H). apply H4. unfold get_edges.
      rewrite <- filter_sum_right_In_iff, <- Heqf. apply Znth_In.
      rewrite make_fields_eq_length. assumption.
  - subst new_g. apply lgd_no_dangling_dst. 1: apply lcv_graph_has_v_new; auto.
    apply lcv_no_dangling_dst; auto. destruct p; simpl in H5.
    + destruct (Znth z roots); [destruct s|]; simpl in H5; inversion H5.
    + destruct p. simpl in H. destruct H as [? [? [? ?]]]. rewrite H8 in H5.
      simpl in H5. destruct (Znth z (make_fields g v)) eqn:? ; [destruct s|];
                     simpl in H5; inversion H5. subst e0. clear H5.
      specialize (H4 _ H). apply H4. unfold get_edges.
      rewrite <- filter_sum_right_In_iff, <- Heqf. apply Znth_In.
      rewrite make_fields_eq_length. assumption.
Qed.

Lemma svfl_dst_changed: forall from to v l g1 g2,
    graph_has_v g1 v -> raw_mark (vlabel g1 v) = false -> vgeneration v <> from ->
    copy_compatible g1 -> no_dangling_dst g1 -> from <> to ->
    (forall i,  In i l -> i < length (raw_fields (vlabel g1 v))) -> NoDup l ->
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall e i, In i l -> Znth (Z.of_nat i) (make_fields g2 v) = inr e ->
                vgeneration (dst g2 e) <> from.
Proof.
  intros ? ? ? ?. induction l; intros; inversion H8; subst. 1: inversion H9.
  assert (e = (v, i)). {
    apply make_fields_Znth_edge in H10. 1: rewrite Nat2Z.id in H10; assumption.
    split. 1: omega. rewrite Zlength_correct. apply inj_lt.
    erewrite <- svfl_raw_fields; eauto. }
  assert (graph_has_v g3 v) by (eapply fr_graph_has_v; eauto).
  assert (raw_mark (vlabel g3 v) = false) by (erewrite <- fr_raw_mark; eauto).
  assert (graph_has_gen g3 to) by (erewrite <- fr_graph_has_gen; eauto).
  assert (forall j : nat, In j l -> j < Datatypes.length (raw_fields (vlabel g3 v))). {
    intros. erewrite <- (fr_raw_fields _ _ _ _ g1); eauto. apply H5.
    right; assumption. } simpl in H9. destruct H9.
  - subst a. cut (vgeneration (dst g3 e) <> from).
    + intros. cut (dst g2 e = dst g3 e). 1: intro HS; rewrite HS; assumption.
      symmetry. apply (svfl_dst_unchanged from to v l); auto.
      * subst e; simpl; assumption.
      * intros. subst e. intro. inversion H11. subst. apply NoDup_cons_2 in H6.
        contradiction.
    + eapply (fr_O_dst_changed_field from to); eauto.
      * simpl. intuition. rewrite Zlength_correct. apply inj_lt. apply H5.
        left; reflexivity.
      * unfold make_fields in H8 |-*. erewrite svfl_raw_fields; eauto.
  - eapply (IHl g3); eauto.
    + eapply (fr_copy_compatible _ _ _ _ g1); eauto.
    + eapply (fr_O_no_dangling_dst _ _ _ g1); eauto.
      * simpl. intuition. rewrite Zlength_correct. apply inj_lt. apply H5.
        left; reflexivity.
      * simpl. constructor.
    + apply NoDup_cons_1 in H6; assumption.
Qed.

Lemma svfl_no_edge2from: forall from to v g1 g2,
    graph_has_v g1 v -> raw_mark (vlabel g1 v) = false -> vgeneration v <> from ->
    copy_compatible g1 -> no_dangling_dst g1 -> from <> to -> graph_has_gen g1 to ->
    scan_vertex_for_loop
      from to v (nat_inc_list (length (raw_fields (vlabel g1 v)))) g1 g2 ->
    forall e, In e (get_edges g2 v) -> vgeneration (dst g2 e) <> from.
Proof.
  intros. unfold get_edges in H7. rewrite <- filter_sum_right_In_iff in H7.
  apply In_Znth in H7. destruct H7 as [i [? ?]].
  rewrite <- (Z2Nat.id i) in H8 by omega. eapply svfl_dst_changed; eauto.
  - intros. rewrite nat_inc_list_In_iff in H9. assumption.
  - apply nat_inc_list_NoDup.
  - rewrite nat_inc_list_In_iff. rewrite make_fields_eq_length in H7.
    erewrite svfl_raw_fields; eauto. rewrite <- ZtoNat_Zlength.
    apply Z2Nat.inj_lt; omega.
Qed.

Lemma no_scan_no_edge: forall g v, no_scan g v -> get_edges g v = nil.
Proof.
  intros. unfold no_scan in H. apply tag_no_scan in H. unfold get_edges.
  destruct (filter_sum_right (make_fields g v)) eqn:? . 1: reflexivity. exfalso.
  assert (In e (filter_sum_right (make_fields g v))) by (rewrite Heql; left; auto).
  rewrite <- filter_sum_right_In_iff in H0. clear l Heql. apply H. clear H.
  unfold make_fields in H0. remember (raw_fields (vlabel g v)). clear Heql.
  remember O. clear Heqn. revert n H0. induction l; simpl; intros; auto.
  destruct a; [destruct s|]; simpl in H0;
    [right; destruct H0; [inversion H | eapply IHl; eauto]..|left]; auto.
Qed.

Lemma svfl_copy_compatible: forall from to v l g1 g2,
    from <> to -> graph_has_gen g1 to ->
    scan_vertex_for_loop from to v l g1 g2 ->
    copy_compatible g1 -> copy_compatible g2.
Proof.
  do 4 intro. induction l; intros; inversion H1; subst. 1: assumption.
  cut (copy_compatible g3).
  - intros. apply (IHl g3); auto. erewrite <- fr_graph_has_gen; eauto.
  - eapply fr_copy_compatible; eauto.
Qed.

Lemma svfl_no_dangling_dst: forall from to v l g1 g2,
    graph_has_v g1 v -> raw_mark (vlabel g1 v) = false -> vgeneration v <> from ->
    copy_compatible g1 -> graph_has_gen g1 to -> from <> to ->
    scan_vertex_for_loop from to v l g1 g2 ->
    (forall i,  In i l -> i < length (raw_fields (vlabel g1 v))) ->
    no_dangling_dst g1 -> no_dangling_dst g2.
Proof.
  do 4 intro. induction l; intros; inversion H5; subst. 1: assumption.
  cut (no_dangling_dst g3).
  - intros. apply (IHl g3); auto.
    + eapply fr_graph_has_v; eauto.
    + erewrite <- fr_raw_mark; eauto.
    + eapply (fr_copy_compatible O from to); eauto.
    + erewrite <- fr_graph_has_gen; eauto.
    + intros. erewrite <- fr_raw_fields; eauto. apply H6. right; assumption.
  - eapply fr_O_no_dangling_dst; eauto.
    + simpl. intuition. rewrite Zlength_correct. apply inj_lt.
      apply H6. left; reflexivity.
    + simpl. constructor.
Qed.

Lemma svwl_no_edge2from: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    gen_unmarked g1 to -> copy_compatible g1 -> no_dangling_dst g1 ->
    from <> to -> NoDup l ->
    forall e i, In i l -> In e (get_edges g2 (to, i)) ->
                vgeneration (dst g2 e) <> from.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst. 1: inversion H6.
  - simpl in H6. destruct H6. 2: apply NoDup_cons_1 in H5; eapply IHl; eauto. subst a.
    assert (In e (get_edges g1 (to, i))). {
      unfold get_edges, make_fields in H7 |-*.
      erewrite svwl_raw_fields; eauto. split; simpl; assumption. }
    rewrite no_scan_no_edge in H6. 2: assumption. inversion H6.
  - simpl in H6.
    assert (graph_has_gen g3 to) by (erewrite <- svfl_graph_has_gen; eauto).
    assert (gen_unmarked g3 to) by (eapply (svfl_gen_unmarked _ _ _ _ g1); eauto).
    destruct H6.
    + subst a. cut (vgeneration (dst g3 e) <> from).
      * intros. cut (dst g3 e = dst g2 e). 1: intros HS; rewrite <- HS; assumption.
        eapply svwl_dst_unchanged; eauto.
        -- erewrite get_edges_fst; eauto. eapply (svfl_graph_has_v _ _ _ _ g1); eauto.
           split; simpl; assumption.
        -- intros. erewrite get_edges_fst; eauto. simpl.
           apply NoDup_cons_2 in H5. assumption.
      * assert (graph_has_v g1 (to, i)) by (split; simpl; assumption).
        eapply svfl_no_edge2from; eauto. unfold get_edges, make_fields in H7 |-*.
        erewrite svwl_raw_fields; eauto. eapply (svfl_graph_has_v _ _ _ _ g1); eauto.
    + eapply (IHl g3); eauto.
      * eapply (svfl_copy_compatible _ _ _ _ g1); eauto.
      * eapply (svfl_no_dangling_dst from to); eauto.
        -- split; simpl; assumption.
        -- intros. rewrite nat_inc_list_In_iff in H13. assumption.
      * apply NoDup_cons_1 in H5. assumption.
Qed.

Lemma no_dangling_dst_reset: forall g gen,
    no_dangling_dst g -> no_edge2gen g gen ->
    no_dangling_dst (reset_graph gen g).
Proof.
  intros. unfold no_dangling_dst in *. red in H0. simpl. intros.
  rewrite graph_has_v_reset in *. destruct H1. rewrite get_edges_reset in H2.
  rewrite remove_ve_dst_unchanged. split.
  - apply (H v); assumption.
  - cut (vgeneration (dst g e) <> gen). 1: intuition. unfold gen2gen_no_edge in H0.
    destruct e as [[vgen vidx] eidx]. pose proof H2. apply get_edges_fst in H2.
    simpl in H2. subst v. simpl in *. apply H0; intuition. split; simpl; assumption.
Qed.

Lemma frr_copy_compatible: forall from to f_info roots g roots' g',
    from <> to -> graph_has_gen g to ->
    forward_roots_relation from to f_info roots g roots' g' ->
    copy_compatible g -> copy_compatible g'.
Proof.
  intros. induction H1. 1: assumption. apply IHforward_roots_loop.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_copy_compatible; eauto.
Qed.

Lemma frl_no_dangling_dst: forall from to f_info l roots g roots' g',
    graph_has_gen g to -> copy_compatible g -> from <> to ->
    (forall i, In i l -> i < length roots) ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    roots_graph_compatible roots g ->
    forward_roots_loop from to f_info l roots g roots' g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  do 4 intro. induction l; intros; inversion H5; subst. 1: assumption.
  assert (forward_p_compatible (inl (Z.of_nat a)) roots g from). {
    simpl. split. 1: omega. rewrite Zlength_correct. apply inj_lt.
    apply H2; left; reflexivity. } cut (no_dangling_dst g2).
  - intros. eapply (IHl (upd_roots from to (inl (Z.of_nat a)) g roots f_info)
                        g2 roots'); eauto.
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply (fr_copy_compatible O from to _ g); eauto.
    + intros. rewrite <- ZtoNat_Zlength, upd_roots_Zlength, ZtoNat_Zlength; auto.
      apply H2. right; assumption.
    + rewrite upd_roots_Zlength; assumption.
    + eapply fr_roots_graph_compatible; eauto.
  - fold (forward_p2forward_t (inl (Z.of_nat a)) roots g) in H9.
    eapply fr_O_no_dangling_dst; eauto.
Qed.

Lemma frr_no_dangling_dst: forall from to f_info roots g roots' g',
    graph_has_gen g to -> copy_compatible g -> from <> to ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    roots_graph_compatible roots g ->
    forward_roots_relation from to f_info roots g roots' g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  intros. eapply frl_no_dangling_dst; eauto. intros.
  rewrite nat_inc_list_In_iff in H6. assumption.
Qed.

Lemma frr_dsr_no_edge2gen: forall from to f_info roots roots' g g1 g2,
    graph_has_gen g to -> from <> to -> gen_unmarked g to ->
    copy_compatible g -> no_dangling_dst g ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    roots_graph_compatible roots g ->
    forward_roots_relation from to f_info roots g roots' g1 ->
    do_scan_relation from to (number_of_vertices (nth_gen g to)) g1 g2 ->
    no_edge2gen g from -> no_edge2gen g2 from.
Proof.
  intros. unfold no_edge2gen in *. intros. specialize (H8 _ H9).
  destruct (Nat.eq_dec another to).
  - subst. unfold gen2gen_no_edge in *. intros.
    destruct H10. simpl fst in *. destruct H7 as [m [? ?]].
    assert (graph_has_gen g1 to) by (erewrite <- frr_graph_has_gen; eauto).
    assert (graph_has_v g (to, vidx) \/ gen_v_num g to <= vidx < gen_v_num g2 to). {
      eapply (svwl_graph_has_v_inv from to _ g1 g2) in H10; eauto. simpl in H10.
      destruct H10.
      - eapply (frr_graph_has_v_inv from _ _ _ g) in H10; eauto.
        simpl in H10. destruct H10. 1: left; assumption.
        right. destruct H10 as [_ [? ?]]. split; auto.
        apply svwl_gen_v_num_to in H7; [omega | assumption].
      - right. destruct H10 as [_ [? ?]]. split; auto.
        apply frr_gen_v_num_to in H6; [omega | assumption]. } destruct H14.
    + assert (graph_has_v g1 (to, vidx)) by
          (eapply (frr_graph_has_v from to _ _ g); eauto).
      assert (get_edges g (to, vidx) = get_edges g2 (to, vidx)). {
        transitivity (get_edges g1 (to, vidx)); unfold get_edges, make_fields.
        - erewrite frr_raw_fields; eauto.
        - erewrite svwl_raw_fields; eauto. } rewrite <- H16 in H11.
      assert (graph_has_e g (to, vidx, eidx)) by (split; simpl; assumption).
      specialize (H8 _ _ H17).
      erewrite (frr_dst_unchanged _ _ _ _ _ _ g1) in H8; eauto.
      erewrite (svwl_dst_unchanged) in H8; eauto; simpl.
      * eapply (frr_gen_unmarked _ _ _ _ g); eauto.
      * repeat intro. rewrite nat_seq_In_iff in H19. destruct H19 as [? _].
        destruct H14. simpl in H20. red in H20. omega.
    + eapply svwl_no_edge2from; eauto.
      * eapply (frr_gen_unmarked _ _ _ _ g); eauto.
      * eapply (frr_copy_compatible from to _ _ g); eauto.
      * eapply (frr_no_dangling_dst _ _ _ _ g); eauto.
      * apply nat_seq_NoDup.
      * rewrite nat_seq_In_iff. unfold gen_has_index in H12.
        unfold gen_v_num in H14. omega.
  - eapply (frr_gen2gen_no_edge _ _ _ _ g _ g1) in H8; eauto.
    destruct H7 as [m [? ?]]. eapply (svwl_gen2gen_no_edge from to _ g1 g2); eauto.
    + erewrite <- frr_graph_has_gen; eauto.
    + eapply frr_gen_unmarked; eauto.
Qed.

Lemma svwl_no_dangling_dst: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    gen_unmarked g1 to -> copy_compatible g1 -> from <> to ->
    no_dangling_dst g1 -> no_dangling_dst g2.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst;
                [assumption | eapply IHl; eauto|]. cut (no_dangling_dst g3).
  - intros. apply (IHl g3); auto.
    + erewrite <- svfl_graph_has_gen; eauto.
    + eapply svfl_gen_unmarked; eauto.
    + eapply svfl_copy_compatible; eauto.
  - eapply (svfl_no_dangling_dst from to _ _ g1); eauto.
    + split; simpl; assumption.
    + intros. rewrite nat_inc_list_In_iff in H5. assumption.
Qed.

Lemma frr_roots_fi_compatible: forall from to f_info roots1 g1 roots2 g2,
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    roots_fi_compatible roots1 f_info -> roots_fi_compatible roots2 f_info.
Proof.
  intros. induction H; subst. 1: assumption. apply IHforward_roots_loop.
  apply upd_roots_rf_compatible; assumption.
Qed.

Definition no_backward_edge (g: LGraph): Prop :=
  forall gen1 gen2, gen1 > gen2 -> gen2gen_no_edge g gen1 gen2.

Definition firstn_gen_clear (g: LGraph) (n: nat): Prop :=
  forall i, i < n -> graph_gen_clear g i.

Definition safe_to_copy_to_except (g: LGraph) (gen: nat): Prop :=
  forall n, n <> O -> n <> gen -> graph_has_gen g n -> safe_to_copy_gen g (pred n) n .

Definition safe_to_copy (g: LGraph): Prop :=
  forall n, graph_has_gen g (S n) -> safe_to_copy_gen g n (S n).

Lemma stc_stcte_O_iff: forall g, safe_to_copy g <-> safe_to_copy_to_except g O.
Proof.
  intros. unfold safe_to_copy, safe_to_copy_to_except. split; intros.
  - destruct n. 1: contradiction. simpl. apply H; assumption.
  - specialize (H (S n)). simpl in H. apply H; auto.
Qed.

Lemma fgc_nbe_no_edge2gen: forall g n,
    firstn_gen_clear g n -> no_backward_edge g -> no_edge2gen g n.
Proof.
  intros. red in H, H0 |-* . intros. red. intros. destruct H2. simpl in *.
  destruct (lt_eq_lt_dec another n) as [[?|?]|?]. 2: contradiction.
  - specialize (H _ l). red in H. destruct H2. simpl in *.
    red in H4. rewrite H in H4. omega.
  - assert (another > n) by omega. specialize (H0 _ _ H4). apply H0.
    split; simpl; assumption.
Qed.

Definition add_new_gen (gi: graph_info) (gen_i: generation_info): graph_info :=
  Build_graph_info (g_gen gi +:: gen_i) (app_not_nil (g_gen gi) gen_i).

Definition lgraph_add_new_gen (g: LGraph) (gen_i: generation_info): LGraph :=
  Build_LabeledGraph _ _ _
                     (pg_lg g) (vlabel g) (elabel g) (add_new_gen (glabel g) gen_i).

Definition new_gen_relation (gen: nat) (g1 g2: LGraph): Prop :=
  if graph_has_gen_dec g1 gen then g1 = g2
  else exists gen_i: generation_info, number_of_vertices gen_i = O /\
                                      g2 = lgraph_add_new_gen g1 gen_i.

Inductive garbage_collect_loop (f_info : fun_info)
  : list nat -> roots_t -> LGraph -> roots_t -> LGraph -> Prop :=
  gcl_nil: forall g roots, garbage_collect_loop f_info nil roots g roots g
| gcl_cons: forall (g1 g2 g3 g4: LGraph) (i: nat) (il: list nat)
                   (roots1 roots2 roots3: roots_t),
    new_gen_relation (S i) g1 g2 ->
    do_generation_relation i (S i) f_info roots1 roots2 g2 g3 ->
    garbage_collect_loop f_info il roots2 g3 roots3 g4 ->
    garbage_collect_loop f_info (i :: il) roots1 g1 roots3 g4.

Definition garbage_collect_relation (f_info: fun_info)
           (roots1 roots2: roots_t) (g1 g2: LGraph): Prop :=
  exists n, garbage_collect_loop f_info (nat_inc_list (S n)) roots1 g1 roots2 g2 /\
            safe_to_copy_gen g2 n (S n).

Definition garbage_collect_condition (g: LGraph) (t_info : thread_info)
           (roots : roots_t) (f_info : fun_info) : Prop :=
  graph_unmarked g /\ no_backward_edge g /\ no_dangling_dst g /\
  roots_fi_compatible roots f_info /\ ti_size_spec t_info.

Local Open Scope Z_scope.

Lemma upd_heap_Zlength: forall (hp : heap) (sp : space) (i : Z),
    0 <= i < MAX_SPACES -> Zlength (upd_Znth i (spaces hp) sp) = MAX_SPACES.
Proof.
  intros. rewrite upd_Znth_Zlength; rewrite spaces_size; [reflexivity | assumption].
Qed.

Definition add_new_space (hp: heap) (sp: space) i (Hs: 0 <= i < MAX_SPACES): heap :=
  Build_heap (upd_Znth i (spaces hp) sp) (upd_heap_Zlength hp sp i Hs).

Definition ti_add_new_space (ti: thread_info) (sp: space) i
           (Hs: 0 <= i < MAX_SPACES): thread_info :=
  Build_thread_info (ti_heap_p ti) (add_new_space (ti_heap ti) sp i Hs)
                    (ti_args ti) (arg_size ti).

Lemma ang_nth_old: forall g gi gen,
    graph_has_gen g gen -> nth_gen (lgraph_add_new_gen g gi) gen = nth_gen g gen.
Proof. intros. unfold nth_gen. simpl. rewrite app_nth1; [reflexivity|assumption]. Qed.

Lemma ang_nth_new: forall g gi,
    nth_gen (lgraph_add_new_gen g gi) (length (g_gen (glabel g))) = gi.
Proof.
  intros. unfold nth_gen. simpl. rewrite app_nth2 by omega. rewrite Nat.sub_diag.
  simpl. reflexivity.
Qed.

Lemma ans_nth_old: forall ti sp i (Hs: 0 <= i < MAX_SPACES) gen,
    gen <> Z.to_nat i -> nth_space (ti_add_new_space ti sp i Hs) gen =
                         nth_space ti gen.
Proof.
  intros. rewrite !nth_space_Znth. simpl. rewrite upd_Znth_diff_strong.
  - reflexivity.
  - rewrite spaces_size. assumption.
  - intro. apply H. subst. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma ans_nth_new: forall ti sp i (Hs: 0 <= i < MAX_SPACES),
    nth_space (ti_add_new_space ti sp i Hs) (Z.to_nat i) = sp.
Proof.
  intros. rewrite nth_space_Znth. simpl. rewrite Z2Nat.id by omega.
  rewrite upd_Znth_same; [reflexivity | rewrite spaces_size; assumption].
Qed.

Lemma ang_graph_has_gen: forall g gi gen,
    graph_has_gen (lgraph_add_new_gen g gi) gen <->
    graph_has_gen g gen \/ gen = length (g_gen (glabel g)).
Proof.
  intros. unfold graph_has_gen. simpl. rewrite app_length. simpl. omega.
Qed.

Lemma gti_compatible_add: forall g ti gi sp i (Hs: 0 <= i < MAX_SPACES),
    graph_thread_info_compatible g ti ->
    ~ graph_has_gen g (Z.to_nat i) -> graph_has_gen g (Z.to_nat (i - 1)) ->
    (forall (gr: LGraph), generation_space_compatible gr (Z.to_nat i, gi, sp)) ->
    graph_thread_info_compatible (lgraph_add_new_gen g gi)
                                 (ti_add_new_space ti sp i Hs).
Proof.
  intros. unfold graph_thread_info_compatible in *. destruct H as [? [? ?]].
  assert (length (g_gen (glabel g)) = Z.to_nat i). {
    clear -H0 H1. unfold graph_has_gen in *.
    rewrite Z2Nat.inj_sub in H1 by omega. simpl in H1. omega. }
  pose proof (spaces_size (ti_heap ti)).
  assert (length (g_gen (glabel (lgraph_add_new_gen g gi))) <=
          length (spaces (ti_heap (ti_add_new_space ti sp i Hs))))%nat. {
    simpl. rewrite <- !ZtoNat_Zlength, upd_Znth_Zlength by omega.
    rewrite H6, ZtoNat_Zlength, app_length, H5. simpl. change (S O) with (Z.to_nat 1).
    rewrite <- Z2Nat.inj_add, <- Z2Nat.inj_le by omega. omega. }
  split; [|split]; auto.
  - rewrite gsc_iff in H |- * by assumption. intros.
    apply ang_graph_has_gen in H8. destruct H8.
    + rewrite ang_nth_old by assumption. rewrite ans_nth_old.
      1: apply H; assumption. red in H8. rewrite H5 in H8. omega.
    + subst gen. rewrite ang_nth_new, H5, ans_nth_new. apply H2.
  - simpl. rewrite <- upd_Znth_map. rewrite app_length. rewrite H5 in *. simpl.
    change (S O) with (Z.to_nat 1).
    rewrite <- Z2Nat.inj_add, <- sublist_skip in * by omega.
    rewrite upd_Znth_Zlength; rewrite Zlength_map, spaces_size in *. 2: assumption.
    rewrite sublist_upd_Znth_r. 2: omega. 2: rewrite Zlength_map, spaces_size; omega.
    apply Forall_incl with
        (sublist i MAX_SPACES (map space_start (spaces (ti_heap ti)))). 2: assumption.
    rewrite Z.add_comm. replace MAX_SPACES with (MAX_SPACES - i + i) at 1 by omega.
    rewrite <- sublist_sublist with (j := MAX_SPACES) by omega.
    unfold incl. intro a. apply sublist_In.
Qed.

Lemma ang_graph_has_v: forall g gi v,
    graph_has_v g v -> graph_has_v (lgraph_add_new_gen g gi) v.
Proof.
  intros. destruct v as [gen idx]. destruct H; split; simpl in *.
  - unfold graph_has_gen in *. simpl. rewrite app_length. simpl. omega.
  - unfold gen_has_index in *. rewrite ang_nth_old; assumption.
Qed.

Lemma ang_roots_graph_compatible: forall roots g gi,
    roots_graph_compatible roots g ->
    roots_graph_compatible roots (lgraph_add_new_gen g gi).
Proof.
  intros. unfold roots_graph_compatible in *. rewrite Forall_forall in *. intros.
  apply ang_graph_has_v. apply H. assumption.
Qed.

Lemma ang_roots_compatible: forall roots out g gi,
    roots_compatible g out roots ->
    roots_compatible (lgraph_add_new_gen g gi) out roots.
Proof. intros. destruct H. split; auto. apply ang_roots_graph_compatible. auto. Qed.

Lemma ang_graph_has_v_inv: forall g gi v,
    number_of_vertices gi = O -> graph_has_v (lgraph_add_new_gen g gi) v ->
    graph_has_v g v.
Proof.
  intros. destruct v as [gen idx]. destruct H0; split; simpl in *.
  - apply ang_graph_has_gen in H0. destruct H0; auto. red in H1. exfalso. subst.
    rewrite ang_nth_new, H in H1. omega.
  - apply ang_graph_has_gen in H0. red in H1. destruct H0.
    + rewrite ang_nth_old in H1; assumption.
    + exfalso. subst. rewrite ang_nth_new, H in H1. omega.
Qed.

Lemma ang_outlier_compatible: forall g gi out,
    number_of_vertices gi = O -> outlier_compatible g out ->
    outlier_compatible (lgraph_add_new_gen g gi) out.
Proof.
  intros. unfold outlier_compatible in *. intros.
  apply ang_graph_has_v_inv in H1; auto. simpl. apply H0. assumption.
Qed.

Lemma ang_vertex_address_old: forall (g : LGraph) (gi : generation_info) (v : VType),
    graph_has_v g v ->
    vertex_address (lgraph_add_new_gen g gi) v = vertex_address g v.
Proof.
  intros. unfold vertex_address. f_equal. unfold gen_start. destruct H.
  rewrite if_true by (rewrite ang_graph_has_gen; left; assumption).
  rewrite if_true by assumption. rewrite ang_nth_old by assumption. reflexivity.
Qed.

Lemma fta_compatible_add: forall g ti gi sp i (Hs: 0 <= i < MAX_SPACES) fi roots,
    fun_thread_arg_compatible g ti fi roots -> roots_graph_compatible roots g ->
    fun_thread_arg_compatible (lgraph_add_new_gen g gi)
                              (ti_add_new_space ti sp i Hs) fi roots.
Proof.
  intros. unfold fun_thread_arg_compatible in *. simpl. rewrite <- H.
  apply map_ext_in. intros. destruct a; [destruct s|]; simpl; try reflexivity.
  apply ang_vertex_address_old. red in H0. rewrite Forall_forall in H0. apply H0.
  rewrite <- filter_sum_right_In_iff. assumption.
Qed.

Lemma super_compatible_add: forall g ti gi sp i (Hs: 0 <= i < MAX_SPACES) fi roots out,
    ~ graph_has_gen g (Z.to_nat i) -> graph_has_gen g (Z.to_nat (i - 1)) ->
    (forall (gr: LGraph), generation_space_compatible gr (Z.to_nat i, gi, sp)) ->
    number_of_vertices gi = O -> super_compatible (g, ti, roots) fi out ->
    super_compatible (lgraph_add_new_gen g gi, ti_add_new_space ti sp i Hs, roots)
                     fi out.
Proof.
  intros. destruct H3 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply gti_compatible_add; assumption.
  - apply fta_compatible_add; [|destruct H5]; assumption.
  - apply ang_roots_compatible; assumption.
  - apply ang_outlier_compatible; assumption.
Qed.

Lemma ti_size_spec_add: forall ti sp i (Hs: 0 <= i < MAX_SPACES),
    total_space sp = nth_gen_size (Z.to_nat i) -> ti_size_spec ti ->
    ti_size_spec (ti_add_new_space ti sp i Hs).
Proof.
  intros. unfold ti_size_spec in *. rewrite Forall_forall in *. intros.
  specialize (H0 _ H1). unfold nth_gen_size_spec in *.
  destruct (Nat.eq_dec x (Z.to_nat i)); unfold gen_size.
  - subst x. rewrite !ans_nth_new. if_tac; auto.
  - rewrite !ans_nth_old; assumption.
Qed.

Lemma firstn_gen_clear_add: forall g gi i,
    graph_has_gen g (Z.to_nat i) -> firstn_gen_clear g (Z.to_nat i) ->
    firstn_gen_clear (lgraph_add_new_gen g gi) (Z.to_nat i).
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros. specialize (H0 _ H1).
  rewrite ang_nth_old; auto. unfold graph_has_gen in *. omega.
Qed.

Lemma ans_space_address: forall ti sp i (Hs: 0 <= i < MAX_SPACES) j,
    space_address (ti_add_new_space ti sp i Hs) (Z.to_nat j) =
    space_address ti (Z.to_nat j).
Proof. intros. unfold space_address. simpl. reflexivity. Qed.

Lemma ang_make_header: forall g gi v,
    make_header g v = make_header (lgraph_add_new_gen g gi) v.
Proof. intros. unfold make_header. reflexivity. Qed.

Lemma ang_make_fields_vals_old: forall g gi v,
    graph_has_v g v -> copy_compatible g -> no_dangling_dst g ->
    make_fields_vals g v = make_fields_vals (lgraph_add_new_gen g gi) v.
Proof.
  intros. unfold make_fields_vals. simpl.
  assert (map (field2val g) (make_fields g v) =
          map (field2val (lgraph_add_new_gen g gi))
              (make_fields (lgraph_add_new_gen g gi) v)). {
    unfold make_fields. simpl. apply map_ext_in. intros.
    destruct a; [destruct s|]; simpl; auto. rewrite ang_vertex_address_old; auto.
    red in H1. apply (H1 v); auto. unfold get_edges.
    rewrite <- filter_sum_right_In_iff. assumption. } rewrite <- H2.
  destruct (raw_mark (vlabel g v)) eqn:?; auto. f_equal.
  rewrite ang_vertex_address_old; auto. destruct (H0 _ H Heqb). assumption.
Qed.

Lemma ang_graph_gen_size_old: forall g gi gen,
    graph_has_gen g gen -> graph_gen_size g gen =
                           graph_gen_size (lgraph_add_new_gen g gi) gen.
Proof.
  intros. unfold graph_gen_size. rewrite ang_nth_old by assumption.
  apply fold_left_ext. intros. unfold vertex_size_accum. reflexivity.
Qed.

Lemma nth_gen_size_le_S: forall n : nat, nth_gen_size n <= nth_gen_size (S n).
Proof.
  intros n. unfold nth_gen_size. rewrite Nat2Z.inj_succ, two_p_S by omega.
  assert (two_p (Z.of_nat n) > 0) by (apply two_p_gt_ZERO; omega).
  assert (0 < NURSERY_SIZE) by (vm_compute; reflexivity).
  rewrite Z.mul_assoc, (Z.mul_comm NURSERY_SIZE 2).
  assert (0 < NURSERY_SIZE * two_p (Z.of_nat n)). apply Z.mul_pos_pos; omega.
  rewrite <- Z.add_diag, Z.mul_add_distr_r. omega.
Qed.

Lemma stcte_add: forall g gi i,
    number_of_vertices gi = O -> safe_to_copy_to_except g i ->
    safe_to_copy_to_except (lgraph_add_new_gen g gi) i.
Proof.
  intros. unfold safe_to_copy_to_except in *. intros. rewrite ang_graph_has_gen in H3.
  destruct H3.
  - specialize (H0 _ H1 H2 H3). unfold safe_to_copy_gen in *.
    rewrite <- ang_graph_gen_size_old; assumption.
  - unfold safe_to_copy_gen. simpl. unfold graph_gen_size.
    rewrite H3 at 4. rewrite ang_nth_new, H. unfold previous_vertices_size.
    simpl. destruct n. 1: contradiction. simpl. rewrite Z.sub_0_r.
    apply nth_gen_size_le_S.
Qed.

Lemma graph_unmarked_add: forall g gi,
    number_of_vertices gi = O -> graph_unmarked g ->
    graph_unmarked (lgraph_add_new_gen g gi).
Proof.
  intros. unfold graph_unmarked in *. intros. apply ang_graph_has_v_inv in H1; auto.
  simpl. apply H0. assumption.
Qed.

Lemma ang_get_edges: forall g gi v,
    get_edges g v = get_edges (lgraph_add_new_gen g gi) v.
Proof. intros. unfold get_edges, make_fields. simpl. reflexivity. Qed.

Lemma no_backward_edge_add: forall g gi,
    number_of_vertices gi = O -> no_backward_edge g ->
    no_backward_edge (lgraph_add_new_gen g gi).
Proof.
  intros. unfold no_backward_edge, gen2gen_no_edge in *. intros. simpl.
  destruct H2. simpl in *. rewrite <- ang_get_edges in H3.
  apply ang_graph_has_v_inv in H2; auto. apply H0; auto. split; simpl; auto.
Qed.

Lemma no_dangling_dst_add: forall g gi,
    number_of_vertices gi = O -> no_dangling_dst g ->
    no_dangling_dst (lgraph_add_new_gen g gi).
Proof.
  intros. unfold no_dangling_dst in *. intros. simpl.
  apply ang_graph_has_v_inv in H1; auto. rewrite <- ang_get_edges in H2.
  apply ang_graph_has_v, (H0 v); auto.
Qed.

Lemma gcc_add: forall g ti gi sp i (Hs: 0 <= i < MAX_SPACES) roots fi,
    number_of_vertices gi = O -> total_space sp = nth_gen_size (Z.to_nat i) ->
    garbage_collect_condition g ti roots fi ->
    garbage_collect_condition (lgraph_add_new_gen g gi)
                              (ti_add_new_space ti sp i Hs) roots fi.
Proof.
  intros. destruct H1 as [? [? [? [? ?]]]]. split; [|split; [|split; [|split]]].
  - apply graph_unmarked_add; assumption.
  - apply no_backward_edge_add; assumption.
  - apply no_dangling_dst_add; assumption.
  - assumption.
  - apply ti_size_spec_add; assumption.
Qed.

Lemma ngs_0_lt: forall i, 0 < nth_gen_size i.
Proof.
  intros. unfold nth_gen_size.
  rewrite NURSERY_SIZE_eq, Int.Zshiftl_mul_two_p, Z.mul_1_l, <- two_p_is_exp by omega.
  cut (two_p (16 + Z.of_nat i) > 0); [|apply two_p_gt_ZERO]; omega.
Qed.

Lemma gc_cond_implies_do_gen_cons: forall g t_info roots f_info i,
    safe_to_copy_to_except g i ->
    graph_has_gen g (S i) ->
    graph_thread_info_compatible g t_info ->
    garbage_collect_condition g t_info roots f_info ->
    do_generation_condition g t_info roots f_info i (S i).
Proof.
  intros. destruct H2 as [? [? [? [? ?]]]].
  assert (graph_has_gen g i) by (unfold graph_has_gen in H0 |-*; omega).
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; auto.
  - unfold safe_to_copy_to_except, safe_to_copy_gen in H. red.
    unfold rest_gen_size. specialize (H (S i)). simpl in H.
    destruct (gt_gs_compatible _ _ H1 _ H0) as [_ [_ ?]].
    destruct (gt_gs_compatible _ _ H1 _ H7) as [_ [_ ?]].
    fold (graph_gen_size g (S i)) in H8. fold (graph_gen_size g i) in H9.
    rewrite <- H8. fold (gen_size t_info (S i)).
    destruct (space_order (nth_space t_info i)) as [_ ?].
    fold (gen_size t_info i) in H10. rewrite <- H9 in H10.
    transitivity (gen_size t_info i). 1: assumption.
    rewrite (ti_size_gen _ _ _ H1 H7 H6), (ti_size_gen _ _ _ H1 H0 H6).
    apply H; [omega.. | assumption].
  - apply graph_unmarked_copy_compatible; assumption.
  - rewrite (ti_size_gen _ _ _ H1 H0 H6). apply ngs_0_lt.
  - rewrite graph_gen_unmarked_iff in H2. apply H2.
Qed.

Lemma do_gen_no_dangling_dst: forall g1 g2 roots1 roots2 f_info from to,
  graph_has_gen g1 to -> copy_compatible g1 -> gen_unmarked g1 to ->
  Zlength roots1 = Zlength (live_roots_indices f_info) -> from <> to ->
  roots_graph_compatible roots1 g1 -> firstn_gen_clear g1 from ->
  no_backward_edge g1 ->
  do_generation_relation from to f_info roots1 roots2 g1 g2 ->
  no_dangling_dst g1 -> no_dangling_dst g2.
Proof.
  intros. destruct H7 as [g3 [g4 [? [? ?]]]].
  assert (no_dangling_dst g3) by (eapply (frr_no_dangling_dst from); eauto).
  assert (no_dangling_dst g4). {
    destruct H9 as [n [? ?]]. eapply (svwl_no_dangling_dst _ _ _ g3); eauto.
    - rewrite <- frr_graph_has_gen; eauto.
    - eapply frr_gen_unmarked; eauto.
    - eapply frr_copy_compatible; eauto. }
  subst g2. apply no_dangling_dst_reset; auto.
  eapply frr_dsr_no_edge2gen; eauto. apply fgc_nbe_no_edge2gen; auto.
Qed.

Lemma fr_O_nth_gen_unchanged: forall from to p g1 g2,
    graph_has_gen g1 to -> forward_relation from to O p g1 g2 ->
    forall gen, gen <> to -> nth_gen g1 gen = nth_gen g2 gen.
Proof.
  intros. inversion H0; subst; try reflexivity.
  - rewrite lcv_nth_gen; auto.
  - subst new_g. transitivity (nth_gen (lgraph_copy_v g1 (dst g1 e) to) gen).
    2: reflexivity. rewrite lcv_nth_gen; [reflexivity | assumption..].
Qed.

Lemma frr_nth_gen_unchanged: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen, gen <> to -> nth_gen g1 gen = nth_gen g2 gen.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_O_nth_gen_unchanged; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma svfl_nth_gen_unchanged: forall from to v l g1 g2,
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall gen, gen <> to -> nth_gen g1 gen = nth_gen g2 gen.
Proof.
  intros. induction H0; subst; try reflexivity. transitivity (nth_gen g2 gen).
  - eapply fr_O_nth_gen_unchanged; eauto.
  - apply IHscan_vertex_for_loop. rewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma svwl_nth_gen_unchanged: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall gen, gen <> to -> nth_gen g1 gen = nth_gen g2 gen.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst; try reflexivity.
  1: apply IHl; auto. transitivity (nth_gen g3 gen).
  - eapply svfl_nth_gen_unchanged; eauto.
  - apply IHl; auto. rewrite <- svfl_graph_has_gen; eauto.
Qed.

Lemma frr_firstn_gen_clear: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen, (gen <= to)%nat ->
                firstn_gen_clear g1 gen -> firstn_gen_clear g2 gen.
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros.
  erewrite <- frr_nth_gen_unchanged; eauto. omega.
Qed.

Lemma svwl_firstn_gen_clear: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall gen, (gen <= to)%nat ->
                firstn_gen_clear g1 gen -> firstn_gen_clear g2 gen.
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros.
  erewrite <- (svwl_nth_gen_unchanged from); eauto. omega.
Qed.

Lemma firstn_gen_clear_reset: forall g i,
    firstn_gen_clear g i -> firstn_gen_clear (reset_graph i g) (S i).
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros.
  assert (i0 < i \/ i0 = i)%nat by omega. destruct H1.
  - rewrite reset_nth_gen_diff by omega. apply H; assumption.
  - subst i0. unfold nth_gen. simpl. rewrite reset_nth_gen_info_same.
    simpl. reflexivity.
Qed.

Lemma do_gen_firstn_gen_clear: forall g1 g2 roots1 roots2 f_info i,
    do_generation_relation i (S i) f_info roots1 roots2 g1 g2 ->
    graph_has_gen g1 (S i) -> firstn_gen_clear g1 i -> firstn_gen_clear g2 (S i).
Proof.
  intros. destruct H as [g3 [g4 [? [? ?]]]].
  eapply frr_firstn_gen_clear in H1; eauto. destruct H2 as [n [? ?]].
  eapply svwl_firstn_gen_clear in H1; eauto. 2: erewrite <- frr_graph_has_gen; eauto.
  subst g2. apply firstn_gen_clear_reset. assumption.
Qed.

Lemma do_gen_no_backward_edge: forall g1 g2 roots1 roots2 f_info i,
    do_generation_relation i (S i) f_info roots1 roots2 g1 g2 ->
    no_dangling_dst g2 -> graph_has_gen g1 (S i) -> gen_unmarked g1 (S i) ->
    firstn_gen_clear g1 i -> no_backward_edge g1 -> no_backward_edge g2.
Proof.
  intros. unfold no_backward_edge in *. intros. destruct (Nat.eq_dec gen1 (S i)).
  - red. intros. destruct H6. simpl in *. eapply do_gen_firstn_gen_clear in H3; eauto.
    subst. specialize (H0 _ H6 _ H7). destruct H0. red in H8. intro. rewrite H9 in H8.
    red in H3. assert (gen2 < S i)%nat by omega. specialize (H3 _ H10). red in H3.
    rewrite H3 in H8. omega.
  - destruct H as [g3 [g4 [? [? ?]]]]. subst g2. apply gen2gen_no_edge_reset.
    assert (gen2gen_no_edge g3 gen1 gen2) by (eapply frr_gen2gen_no_edge; eauto).
    destruct H6 as [m [? ?]]. eapply (svwl_gen2gen_no_edge i _ _ g3); eauto.
    + rewrite <- frr_graph_has_gen; eauto.
    + eapply frr_gen_unmarked; eauto.
Qed.

Lemma ti_relation_size_spec: forall t_info1 t_info2 : thread_info,
    thread_info_relation t_info1 t_info2 ->
    ti_size_spec t_info1 -> ti_size_spec t_info2.
Proof.
  intros. unfold ti_size_spec in *. rewrite Forall_forall in *. intros.
  specialize (H0 _ H1). unfold nth_gen_size_spec in *. destruct H as [? [? ?]].
  rewrite <- H2, <- H3. assumption.
Qed.

Lemma do_gen_gcc: forall g1 t_info1 roots1 g2 t_info2 roots2 f_info i out,
    super_compatible (g1, t_info1, roots1) f_info out ->
    firstn_gen_clear g1 i -> graph_has_gen g1 (S i) ->
    thread_info_relation t_info1 t_info2 ->
    garbage_collect_condition g1 t_info1 roots1 f_info ->
    do_generation_relation i (S i) f_info roots1 roots2 g1 g2 ->
    garbage_collect_condition g2 t_info2 roots2 f_info.
Proof.
  intros. destruct H3 as [? [? [? [? ?]]]].
  assert (gen_unmarked g1 (S i)) by (rewrite graph_gen_unmarked_iff in H3; apply H3).
  assert (no_dangling_dst g2). {
    eapply do_gen_no_dangling_dst; eauto.
    - apply graph_unmarked_copy_compatible; assumption.
    - apply (proj1 H7).
    - destruct H as [_ [_ [[_ ?] _]]]. assumption. }
  split; [|split; [|split; [|split]]]; auto.
  - eapply do_gen_graph_unmarked; eauto.
  - eapply do_gen_no_backward_edge; eauto.
  - destruct H4 as [g3 [g4 [? _]]]. eapply frr_roots_fi_compatible; eauto.
  - eapply ti_relation_size_spec; eauto.
Qed.

Lemma fr_vertex_size: forall depth from to p g1 g2,
    graph_has_gen g1 to -> forward_relation from to depth p g1 g2 ->
    forall v, graph_has_v g1 v -> vertex_size g1 v = vertex_size g2 v.
Proof.
  intros. remember (fun g v (x: nat) => graph_has_v g v) as Q.
  remember (fun g1 g2 v => vertex_size g1 v = vertex_size g2 v) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g1 g2 _ Q P R). subst Q P R.
  apply H2; clear H2; intros; try assumption; try reflexivity.
  - rewrite H2. assumption.
  - rewrite lcv_vertex_size_old; [reflexivity | assumption..].
  - apply (fr_graph_has_v _ _ _ _ _ _ H2 H3 _ H4).
  - apply lcv_graph_has_v_old; assumption.
Qed.

Lemma fr_O_graph_gen_size_unchanged: forall from to p g1 g2,
    graph_has_gen g1 to -> forward_relation from to O p g1 g2 ->
    forall gen, graph_has_gen g1 gen -> gen <> to ->
                graph_gen_size g1 gen = graph_gen_size g2 gen.
Proof.
  intros. unfold graph_gen_size.
  erewrite <- (fr_O_nth_gen_unchanged from to _ g1 g2); eauto.
  unfold previous_vertices_size. apply fold_left_ext. intros.
  unfold vertex_size_accum. f_equal. rewrite nat_inc_list_In_iff in H3.
  eapply (fr_vertex_size O from to); eauto. split; simpl; assumption.
Qed.

Lemma fr_O_stcg: forall from to p g1 g2,
    graph_has_gen g1 to -> forward_relation from to O p g1 g2 ->
    forall gen1 gen2, graph_has_gen g1 gen2 -> gen2 <> to ->
                      safe_to_copy_gen g1 gen1 gen2 -> safe_to_copy_gen g2 gen1 gen2.
Proof.
  intros. unfold safe_to_copy_gen in *.
  erewrite <- (fr_O_graph_gen_size_unchanged from to); eauto.
Qed.

Lemma frr_stcg: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen1 gen2, graph_has_gen g1 gen2 -> gen2 <> to ->
                      safe_to_copy_gen g1 gen1 gen2 -> safe_to_copy_gen g2 gen1 gen2.
Proof.
  intros. induction H0. 1: assumption. apply IHforward_roots_loop.
  - erewrite <- (fr_graph_has_gen O from to); eauto.
  - erewrite <- (fr_graph_has_gen O from to); eauto.
  - eapply (fr_O_stcg from to); eauto.
Qed.

Lemma svfl_stcg: forall from to v l g1 g2,
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall gen1 gen2, graph_has_gen g1 gen2 -> gen2 <> to ->
                      safe_to_copy_gen g1 gen1 gen2 -> safe_to_copy_gen g2 gen1 gen2.
Proof.
  intros. induction H0; subst; try assumption. apply IHscan_vertex_for_loop.
  - erewrite <- (fr_graph_has_gen O from to); eauto.
  - erewrite <- (fr_graph_has_gen O from to); eauto.
  - eapply (fr_O_stcg from to); eauto.
Qed.

Lemma svwl_stcg: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall gen1 gen2, graph_has_gen g1 gen2 -> gen2 <> to ->
                      safe_to_copy_gen g1 gen1 gen2 -> safe_to_copy_gen g2 gen1 gen2.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst; try assumption.
  1: apply (IHl g1); auto. apply (IHl g3); auto.
  - erewrite <- (svfl_graph_has_gen from to); eauto.
  - erewrite <- (svfl_graph_has_gen from to); eauto.
  - eapply (svfl_stcg from to); eauto.
Qed.

Lemma reset_graph_gen_size_eq: forall g i j,
    i <> j -> graph_gen_size (reset_graph i g) j = graph_gen_size g j.
Proof.
  intros. unfold graph_gen_size.
  rewrite pvs_reset_unchanged, reset_nth_gen_diff; auto.
Qed.

Lemma reset_stct: forall g i gen1 gen2,
    i <> gen2 -> safe_to_copy_gen g gen1 gen2 ->
    safe_to_copy_gen (reset_graph i g) gen1 gen2.
Proof.
  intros. unfold safe_to_copy_gen in *. rewrite reset_graph_gen_size_eq; auto.
Qed.

Lemma do_gen_stcte: forall g1 roots1 g2 roots2 f_info i,
    safe_to_copy_to_except g1 i -> graph_has_gen g1 (S i) ->
    do_generation_relation i (S i) f_info roots1 roots2 g1 g2 ->
    safe_to_copy_to_except g2 (S i).
Proof.
  intros. unfold safe_to_copy_to_except in *. intros.
  destruct H1 as [g3 [g4 [? [? ?]]]]. destruct (Nat.eq_dec n i).
  - subst. red. unfold graph_gen_size, nth_gen. simpl.
    rewrite reset_nth_gen_info_same. simpl. unfold previous_vertices_size.
    simpl. destruct i. 1: contradiction. simpl. rewrite Z.sub_0_r.
    apply nth_gen_size_le_S.
  - subst g2. apply reset_stct; auto. destruct H5 as [m [? ?]].
    rewrite graph_has_gen_reset in H4.
    assert (graph_has_gen g3 (S i)) by (erewrite <- frr_graph_has_gen; eauto).
    assert (graph_has_gen g3 n) by (erewrite svwl_graph_has_gen; eauto).
    eapply (svwl_stcg i (S i) _ g3); eauto.
    assert (graph_has_gen g1 n) by (erewrite frr_graph_has_gen; eauto).
    eapply (frr_stcg i (S i) _ _ g1); eauto.
Qed.

Lemma gcl_add_tail: forall l g1 roots1 g2 roots2 g3 roots3 g4 f_info i,
    garbage_collect_loop f_info l roots1 g1 roots2 g2 ->
    new_gen_relation (S i) g2 g3 ->
    do_generation_relation i (S i) f_info roots2 roots3 g3 g4 ->
    garbage_collect_loop f_info (l +:: i) roots1 g1 roots3 g4.
Proof.
  induction l; intros.
  - simpl. inversion H. subst. eapply gcl_cons; eauto. constructor.
  - inversion H. subst. clear H. simpl app. eapply gcl_cons; eauto.
Qed.

Lemma safe_to_copy_complete: forall g i,
    safe_to_copy_to_except g (S i) -> safe_to_copy_gen g i (S i) -> safe_to_copy g.
Proof.
  intros. unfold safe_to_copy_to_except in H. unfold safe_to_copy. intros.
  destruct (Nat.eq_dec n i).
  - subst. assumption.
  - specialize (H (S n)). simpl in H. apply H; auto.
Qed.
