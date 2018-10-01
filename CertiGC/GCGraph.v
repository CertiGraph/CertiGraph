Require Import Coq.ZArith.ZArith.
Require Export Coq.Program.Basics.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
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
Require Import RamifyCoq.msl_ext.iter_sepcon.
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
    Ptrofs.min_signed <= WORD_SIZE * (total_space sp) <= Ptrofs.max_signed.
Proof. intros. apply MSS_max_4_signed_range, total_space_tight_range. Qed.

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

Definition roots_compatible (g: LGraph) (outlier: outlier_t) (roots: roots_t): Prop :=
  incl (filter_sum_right (filter_sum_left roots)) outlier /\
  Forall (graph_has_v g) (filter_sum_right roots).

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

Definition reset_generation_info (gi: generation_info) : generation_info :=
  Build_generation_info (start_address gi) O (generation_sh gi) (start_isptr gi)
                        (generation_share_writable gi).

Fixpoint reset_nth_gen_info
         (n: nat) (gi: list generation_info) : list generation_info :=
  match n with
  | O => match gi with
         | nil => nil
         | g :: l => reset_generation_info g :: l
         end
  | S m => match gi with
           | nil => nil
           | g :: l => g :: reset_nth_gen_info m l
           end
  end.

Lemma reset_nth_gen_info_preserve_length: forall n gl,
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

Definition reset_nth_graph_info (n: nat) (g: graph_info) : graph_info :=
  Build_graph_info (reset_nth_gen_info n g.(g_gen)) (reset_nth_gen_info_not_nil n g).

Definition reset_nth_gen_graph (n: nat) (g: LGraph) : LGraph :=
  Build_LabeledGraph _ _ _ (pg_lg g) (vlabel g) (elabel g)
                     (reset_nth_graph_info n (glabel g)).

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

Lemma reset_nth_space_Zlength: forall n s, Zlength s = Zlength (reset_nth_space n s).
Proof.
  induction n; intros; simpl.
  - destruct s; simpl; [|rewrite !Zlength_cons]; reflexivity.
  - destruct s; [|rewrite !Zlength_cons, (IHn s0)]; reflexivity.
Qed.

Lemma reset_nth_heap_Zlength: forall n h,
    Zlength (reset_nth_space n (spaces h)) = MAX_SPACES.
Proof. intros. rewrite <- reset_nth_space_Zlength. apply spaces_size. Qed.

Definition reset_nth_heap (n: nat) (h: heap) : heap :=
  Build_heap (reset_nth_space n (spaces h)) (reset_nth_heap_Zlength n h).

Definition reset_nth_heap_thread_info (n: nat) (ti: thread_info) :=
  Build_thread_info (ti_heap_p ti) (reset_nth_heap n (ti_heap ti))
                    (ti_args ti) (arg_size ti).

Definition resume_graph_relation (g1 g2: LGraph): Prop :=
  g1.(pg_lg) = g2.(pg_lg) /\
  g1.(vlabel) = g2.(vlabel) /\
  g1.(elabel) = g2.(elabel) /\
  tl (glabel g1).(g_gen) = tl (glabel g2).(g_gen) /\
  let h1 := graph_info_head g1.(glabel) in
  let h2 := graph_info_head g2.(glabel) in
  start_address h1 = start_address h2 /\
  generation_sh h1 = generation_sh h2 /\ number_of_vertices h2 = O.

Definition resume_thread_info_relation (t1 t2: thread_info): Prop :=
  t1.(ti_heap_p) = t2.(ti_heap_p) /\
  t1.(ti_args) = t2.(ti_args) /\
  tl t1.(ti_heap).(spaces) = tl t2.(ti_heap).(spaces) /\
  let h1 := heap_head t1.(ti_heap) in
  let h2 := heap_head t2.(ti_heap) in
  h1.(space_start) = h2.(space_start) /\ h1.(total_space) = h2.(total_space) /\
  h1.(space_sh) = h2.(space_sh) /\ h2.(used_space) = 0%Z.

Lemma reset_resume_g_relation: forall g,
    resume_graph_relation g (reset_nth_gen_graph O g).
Proof.
  intros. hnf. unfold reset_nth_gen_graph. simpl.
  destruct (graph_info_head_cons (glabel g)) as [s [l [? ?]]]. rewrite H, H0. simpl.
  destruct (graph_info_head_cons (reset_nth_graph_info 0 (glabel g))) as
      [s' [l' [? ?]]]. rewrite H2. unfold reset_nth_graph_info in H1. simpl in H1.
  rewrite H in H1. inversion H1. subst l' s'.
  unfold reset_generation_info. simpl. tauto.
Qed.

Lemma reset_resume_t_relation: forall t,
    resume_thread_info_relation t (reset_nth_heap_thread_info O t).
Proof.
  intros. hnf. unfold reset_nth_heap_thread_info. simpl.
  destruct (heap_head_cons (ti_heap t)) as [s [l [? ?]]]. rewrite H0, H. simpl.
  destruct (heap_head_cons (reset_nth_heap 0 (ti_heap t))) as [s' [l' [? ?]]].
  rewrite H2. unfold reset_nth_heap in H1. simpl in H1. rewrite H in H1.
  inversion H1. subst l' s'. unfold reset_space. simpl. tauto.
Qed.

(*
Class SoundGCGraph (g: LGraph) :=
  {
    field_decided_edges: forall v e,
      vvalid g v -> (src g e = v /\ evalid g e <-> In e (get_edges g v));
    generation_limit: (Zlength g.(glabel) <= MAX_SPACES)%Z;
    vertex_valid: forall v,
        vvalid g v <->
        vgeneration v < length g.(glabel) /\
        vindex v < (nth (vgeneration v) g.(glabel) null_info).(number_of_vertices);
    (* Other constraints would be added later *)
  }.

Definition Graph :=
  GeneralGraph VType EType raw_vertex_block unit graph_info (fun g => SoundGCGraph g).

Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.

Definition Graph_LGraph (g: Graph): LGraph := lg_gg g.

 *)

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

Definition make_fields (g: LGraph) (v: VType): list field_t :=
  make_fields' (vlabel g v).(raw_fields) v O.

Definition get_edges (g: LGraph) (v: VType): list EType :=
  filter_sum_right (make_fields g v).

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
        rewrite <- Heqn0; rewrite Z2Nat.id; try assumption.
      }
      destruct a; [destruct s|]; simpl in H0; apply IHl;
        try assumption; apply make_fields'_n_doesnt_matter with (n:=1%nat);
        rewrite Nat2Z.id; try assumption.
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
    map start_address l = map start_address (reset_nth_gen_info n l).
Proof.
  intros. revert n.
  induction l; intros; simpl; destruct n; simpl; [| | | rewrite <- IHl]; reflexivity.
Qed.

Lemma vertex_address_reset: forall (g: LGraph) v n,
    vertex_address g v = vertex_address (reset_nth_gen_graph n g) v.
Proof.
  intros. apply vertex_address_the_same; unfold reset_nth_gen_graph;
            simpl; [intro | rewrite <- start_address_reset]; reflexivity.
Qed.

Lemma make_fields_reset: forall (g: LGraph) v n,
    make_fields_vals g v = make_fields_vals (reset_nth_gen_graph n g) v.
Proof.
  intros. apply make_fields_the_same; unfold reset_nth_gen_graph; simpl;
            [intros; reflexivity..| apply start_address_reset].
Qed.

Lemma resume_preverse_graph_thread_info_compatible: forall (g g': LGraph) t t',
    graph_thread_info_compatible g t ->
    resume_graph_relation g g' ->
    resume_thread_info_relation t t' ->
    graph_thread_info_compatible g' t'.
Proof.
  intros. hnf in *. destruct H. destruct H0 as [? [? [? [? [? ?]]]]]. cbn in H7.
  destruct H7. destruct H1 as [? [? [? ?]]]. cbn in H11.
  destruct H11 as [? [? [? ?]]].
  destruct (graph_info_head_cons (glabel g')) as [gi' [gl' [? ?]]].
  rewrite H15, H16 in *.
  destruct (graph_info_head_cons (glabel g)) as [gi [gl [? ?]]]. rewrite H17, H18 in *.
  destruct (heap_head_cons (ti_heap t')) as [h' [l' [? ?]]]. rewrite H19, H20 in *.
  destruct (heap_head_cons (ti_heap t)) as [h [l [? ?]]]. rewrite H21, H22 in *.
  simpl in *. subst gl'. subst l'. split. 2: apply H2. constructor.
  - apply Forall_inv in H. hnf in *. destruct H as [? [? ?]]. split; [|split].
    + rewrite <- H6, <- H11. assumption.
    + rewrite <- H7, <- H13. assumption.
    + rewrite H8, H14. simpl. reflexivity.
  - apply Forall_tl in H.
    remember (combine (combine (nat_seq 1 (length gl)) gl) l) as hl.
    rewrite Forall_forall in H |- *. intros. destruct x as [[gen gin] sp].
    specialize (H _ H5). hnf in H |- *. destruct H as [? [? ?]].
    split; [|split]; [assumption..|].
    rewrite <- H23. remember (number_of_vertices gin) as n. clear -H3.
    assert (forall v, vlabel g v = vlabel g' v) by
        (intro; rewrite H3; reflexivity). induction n; simpl; auto.
    rewrite !pvs_S, IHn. f_equal. unfold vertex_size. rewrite H. reflexivity.
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
    true new_v (raw_fields rvb) (raw_color rvb) (raw_tag rvb)
    (raw_tag_range rvb) (raw_color_range rvb) (raw_fields_range rvb).

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

(* ugly, plus we need additional proofs that we won't actully hit the 0 branches. I would have made it with Option but even that's unnecessary in the end. *)
Definition val2nat (g: LGraph) (gen: nat) (v: val) : nat :=
  let start := gen_start g gen in
  match start, v with
  | Vptr b1 o1, Vptr b2 o2 =>
      if (eq_dec b1 b2) then Z.to_nat (Ptrofs.unsigned o2 - Ptrofs.unsigned o1) else 0
  | _,_ => 0
  end.

Definition forward_p_compatible
           (p: forward_p_type) (roots: roots_t) (g: LGraph): Prop :=
  match p with
  | inl root_index => 0 <= root_index < Zlength roots
  | inr (v, n) => graph_has_v g v /\ 0 <= n < Zlength (vlabel g v).(raw_fields) /\
                  (vlabel g v).(raw_mark) = false
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

Definition get_roots_indices (index: Z) (live_indices: list Z) :=
  collect_Z_indices Z.eq_dec (Znth index live_indices) live_indices 0.

Definition upd_bunch (index: Z) (f_info: fun_info)
           (roots: roots_t) (v: root_t): roots_t :=
  fold_right (fun i rs => upd_Znth i rs v) roots
             (get_roots_indices index (live_roots_indices f_info)).

Lemma fold_right_upd_Znth_Zlength {A}: forall (l: list Z) (roots: list A) (v: A),
    (forall j, In j l -> 0 <= j < Zlength roots) ->
    Zlength (fold_right (fun (i : Z) (rs : list A) => upd_Znth i rs v) roots l) =
    Zlength roots.
Proof.
  induction l; intros; simpl. 1: reflexivity. rewrite upd_Znth_Zlength.
  - apply IHl. intros. apply H. right. assumption.
  - rewrite IHl; intros; apply H; [left; reflexivity | right; assumption].
Qed.

Lemma get_roots_indices_spec: forall (l: list Z) (z j : Z),
    In j (get_roots_indices z l) <-> 0 <= j < Zlength l /\ Znth j l = Znth z l.
Proof.
  intros. unfold get_roots_indices. remember (Znth z l) as p. clear Heqp z.
  apply collect_Z_indices_spec. 2: omega. rewrite skipn_0. reflexivity.
Qed.

Lemma upd_bunch_Zlength: forall (f_info : fun_info) (roots : roots_t) (z : Z),
    Zlength roots = Zlength (live_roots_indices f_info) ->
    forall r : root_t, Zlength (upd_bunch z f_info roots r) = Zlength roots.
Proof.
  intros. unfold upd_bunch. apply fold_right_upd_Znth_Zlength.
  intros. rewrite H. rewrite get_roots_indices_spec in H0. destruct H0; assumption.
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
  - intros. rewrite get_roots_indices_spec in H2. destruct H2. rewrite H0; assumption.
  - rewrite get_roots_indices_spec. split; [rewrite <- H0|]; assumption.
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
  - intros. rewrite get_roots_indices_spec in H2. destruct H2. rewrite H0; assumption.
  - rewrite get_roots_indices_spec. intro. destruct H2. apply H1. assumption.
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

Lemma upd_roots_compatible: forall g f_info roots outlier z,
    roots_compatible g outlier roots ->
    forall v : VType, graph_has_v g v ->
                      roots_compatible g outlier (upd_bunch z f_info roots (inr v)).
Proof.
  intros. destruct H. split.
  - red in H |-* . clear H1. intros.
    rewrite <- filter_sum_right_In_iff, <- filter_sum_left_In_iff in H1.
    unfold upd_bunch in H1. apply fold_right_upd_Znth_In in H1. destruct H1.
    2: inversion H1. apply H.
    rewrite <- filter_sum_right_In_iff, <- filter_sum_left_In_iff. assumption.
  - clear H. rewrite Forall_forall in H1 |-* . intros.
    rewrite <- filter_sum_right_In_iff in H. unfold upd_bunch in H.
    apply fold_right_upd_Znth_In in H. destruct H. 2: inversion H; assumption.
    apply H1. rewrite <- filter_sum_right_In_iff. assumption.
Qed.

Local Close Scope Z_scope.

Definition forwarded_roots (from to: nat) (forward_p: forward_p_type)
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

(* Goes over all the roots, and forwards those that point to the from *)
(* space. The graph relation proposed is that between g_alpha and *)
(* g_omega. Borrows heavily from forward_relation. Perhaps *)
(* forward_relation itself can be changed to accept both root_t and *)
(* field_t in the forward loop? *)

Inductive forward_roots_loop (from to: nat): roots_t -> LGraph -> LGraph -> Prop :=
| frl_nil: forall g, forward_roots_loop from to nil g g
| frl_cons: forall g1 g2 g3 f rl,
    forward_relation from to O (root2forward f) g1 g2 ->
    forward_roots_loop from to rl g2 g3 ->
    forward_roots_loop from to (f :: rl) g1 g3.

(* Forwards all roots that are pointing at the from space. Borrows *)
(* heavily from forwarded_roots above. *)

Definition forward_all_roots (from to: nat) (roots: roots_t)
           (g: LGraph) (f_info: fun_info) : roots_t :=
  fold_left (fun rts i => forwarded_roots from to (inl (Z.of_nat i)) g rts f_info)
            (nat_inc_list (length roots)) roots.

Definition nth_space (t_info: thread_info) (n: nat): space :=
  nth n t_info.(ti_heap).(spaces) null_space.

Lemma nth_space_Znth: forall t n,
    nth_space t n = Znth (Z.of_nat n) (spaces (ti_heap t)).
Proof.
  intros. unfold nth_space, Znth. rewrite if_false. 2: omega.
  rewrite Nat2Z.id. reflexivity.
Qed.

Definition gen_size t_info n := total_space (nth_space t_info n).

Lemma gsc_iff: forall g t_info,
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
    graph_has_v g v -> raw_mark (vlabel g v) = false -> graph_has_gen g to ->
    copy_compatible g -> copy_compatible (lgraph_add_copied_v g v to).
Proof.
  repeat intro. destruct (V_EqDec v0 (new_copied_v g to)).
  - unfold equiv in e. subst v0. rewrite lacv_vlabel_new in *.
    rewrite H4 in H0. inversion H0.
  - assert (v0 <> (new_copied_v g to)) by intuition. clear c.
    rewrite lacv_vlabel_old in * by assumption.
    assert (graph_has_v g v0). {
      apply lacv_graph_has_v_inv in H3. 2: assumption. destruct H3. 1: assumption.
      contradiction. } split.
    + apply lacv_graph_has_v_old; [|apply H2]; assumption.
    + apply H2; assumption.
Qed.

Lemma lcv_copy_compatible: forall g v to,
    graph_has_v g v -> raw_mark (vlabel g v) = false -> graph_has_gen g to ->
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
  intros. apply utia_estc. clear index uv Hm. unfold lgraph_copy_v.
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

Lemma lcv_roots_compatible: forall g roots outlier v to f_info z,
    graph_has_gen g to ->
    roots_compatible g outlier roots ->
    roots_compatible (lgraph_copy_v g v to) outlier
                     (upd_bunch z f_info roots (inr (new_copied_v g to))).
Proof.
  intros. unfold lgraph_copy_v. apply upd_roots_compatible.
  - unfold roots_compatible in *. destruct H0. split. 1: assumption.
    rewrite Forall_forall in H1 |-* . intros. specialize (H1 _ H2).
    rewrite <- lmc_graph_has_v. apply lacv_graph_has_v_old; assumption.
  - rewrite <- lmc_graph_has_v. apply lacv_graph_has_v_new; assumption.
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

Lemma lcv_fun_thread_arg_compatible: forall
    g t_info f_info roots z v to i s
    (Hi : 0 <= i < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (spaces (ti_heap t_info))) s)
    (Hm : 0 <= Znth z (live_roots_indices f_info) < MAX_ARGS),
    graph_has_gen g to -> Forall (graph_has_v g) (filter_sum_right roots) ->
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
  unfold fun_thread_arg_compatible in *. simpl. rewrite <- H1. apply map_ext_in.
  intros. destruct a; [destruct s0|]; [reflexivity..| simpl].
  apply lcv_vertex_address_old. 1: assumption. rewrite Forall_forall in H0.
  apply H0. rewrite <- filter_sum_right_In_iff. assumption.
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
    g t_info v to index adr
    (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info))) (vertex_size g v))
    (Hm : 0 <= index < MAX_ARGS),
    graph_has_gen g to ->
    graph_thread_info_compatible g t_info ->
    graph_thread_info_compatible
      (lgraph_copy_v g v to)
      (update_thread_info_arg (cut_thread_info t_info (Z.of_nat to) (vertex_size g v)
                                               Hi Hh) index adr Hm).
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

Lemma utiacti_gen_size: forall t_info i1 i2 s ad n
    (Hi : 0 <= i1 < Zlength (spaces (ti_heap t_info)))
    (Hh : has_space (Znth i1 (spaces (ti_heap t_info))) s)
    (Hm : 0 <= i2 < MAX_ARGS),
    gen_size (update_thread_info_arg (cut_thread_info t_info i1 s Hi Hh) i2 ad Hm) n =
    gen_size t_info n.
Proof.
  intros. unfold gen_size. rewrite !nth_space_Znth. simpl.
  pose proof (Nat2Z.is_nonneg n). remember (Z.of_nat n). clear Heqz.
  remember (spaces (ti_heap t_info)). destruct (Z_lt_le_dec z (Zlength l)).
  - assert (0 <= z < Zlength l) by omega. destruct (Z.eq_dec z i1).
    + rewrite e. rewrite upd_Znth_same by assumption. simpl. reflexivity.
    + rewrite upd_Znth_diff; [|assumption..]. reflexivity.
  - rewrite !Znth_overflow;
      [reflexivity | | rewrite upd_Znth_Zlength by assumption]; omega.
Qed.

Definition thread_info_relation t t':=
  ti_heap_p t = ti_heap_p t' /\ forall n, gen_size t n = gen_size t' n.

Lemma tir_id: forall t, thread_info_relation t t.
Proof. intros. red. split; reflexivity. Qed.

Lemma lgd_graph_has_gen: forall g e v x,
    graph_has_gen (labeledgraph_gen_dst g e v) x <-> graph_has_gen g x.
Proof. intros. unfold graph_has_gen. simpl. intuition. Qed.

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

Lemma fr_general_prop: forall depth from to p g g' A (Q: LGraph -> A -> nat -> Prop)
                               (P: LGraph -> LGraph -> A -> Prop),
    graph_has_gen g to -> (forall g v, P g g v) ->
    (forall g1 g2 g3 v, P g1 g2 v -> P g2 g3 v -> P g1 g3 v) ->
    (forall g e v x, P g (labeledgraph_gen_dst g e v) x) ->
    (forall from g v to x,
        graph_has_gen g to -> Q g x from -> vgeneration v = from ->
        P g (lgraph_copy_v g v to) x) ->
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
  - inversion H7; subst; try (specialize (H0 g' v); assumption).
    + apply (H3 (vgeneration v0)); [assumption.. | reflexivity].
    + subst new_g. apply H2.
    + subst new_g. remember (lgraph_copy_v g (dst g e) to) as g1.
      remember (labeledgraph_gen_dst g1 e (new_copied_v g to)) as g2.
      cut (P g1 g2 v). 2: subst; apply H2. intros. apply (H1 g g1 g2).
      2: assumption. subst g1.
      apply (H3 (vgeneration (dst g e))); [assumption.. | reflexivity].
  - assert (forall l from to g1 g2,
               graph_has_gen g1 to -> forward_loop from to depth l g1 g2 ->
               forall v, Q g1 v from -> P g1 g2 v). {
      induction l; intros; inversion H10. 1: apply H0. subst.
      specialize (IHdepth _ _ _ _ _ _ _ _ H9 H0 H1 H2 H3 H4 H5 H6 H15 _ H11).
      apply (H4 _ _ _ _ _ _ H9 H15) in H11.
      rewrite (fr_graph_has_gen _ _ _ _ _ _ H9 H15) in H9.
      specialize (IHl _ _ _ _ H9 H18 _ H11). apply (H1 _ _ _ _ IHdepth IHl). }
    clear IHdepth. inversion H7; subst; try (specialize (H0 g' v); assumption).
    + cut (P g new_g v).
      * intros. apply (H1 g new_g g'). 1: assumption.
        assert (graph_has_gen new_g to) by
            (subst new_g; rewrite <- lcv_graph_has_gen; assumption).
        apply (H9 _ _ _ _ _ H11 H13). subst new_g. apply H5; assumption.
      * subst new_g. apply (H3 (vgeneration v0)); [assumption.. | reflexivity].
    + subst new_g. apply H2.
    + cut (P g new_g v).
      * intros. apply (H1 g new_g g'). 1: assumption.
        assert (graph_has_gen new_g to) by
            (subst new_g; rewrite lgd_graph_has_gen, <- lcv_graph_has_gen; assumption).
        apply (H9 _ _ _ _ _ H11 H13). subst new_g. apply H6, H5; assumption.
      * subst new_g. remember (lgraph_copy_v g (dst g e) to) as g1.
        remember (labeledgraph_gen_dst g1 e (new_copied_v g to)) as g2.
        cut (P g1 g2 v). 2: subst; apply H2. intros. apply (H1 g g1 g2).
        2: assumption. subst g1.
        apply (H3 (vgeneration (dst g e))); [assumption.. | reflexivity].
Qed.

Lemma fr_gen_start: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall x, gen_start g x = gen_start g' x.
Proof.
  intros. remember (fun (g: LGraph) (v: nat) (x: nat) => True) as Q.
  remember (fun g1 g2 x => gen_start g1 x = gen_start g2 x) as P.
  pose proof (fr_general_prop depth from to p g g' _ Q P). subst Q P.
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
  pose proof (fr_general_prop depth from to p g g' _ Q P). subst Q P.
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
  pose proof (fr_general_prop depth from to p g g' _ Q P). subst Q P.
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
  pose proof (fr_general_prop depth from to p g g' _ Q P). subst Q P.
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

Lemma fr_raw_fields: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, graph_has_v g v -> raw_fields (vlabel g v) = raw_fields (vlabel g' v).
Proof.
  intros. remember (fun (g: LGraph) (v: VType) (x: nat) => graph_has_v g v) as Q.
  remember (fun (g1 g2: LGraph) v =>
              raw_fields (vlabel g1 v) = raw_fields (vlabel g2 v)) as P.
  pose proof (fr_general_prop depth from to p g g' _ Q P). subst Q P.
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
  pose proof (fr_general_prop depth from to p g g' _ Q P). subst Q P.
  apply H3; clear H3; intros; try assumption; try reflexivity.
  - rewrite H3. apply H4.
  - destruct H4. rewrite <- lcv_raw_mark; [reflexivity | try assumption..].
    destruct x, v0. simpl in *. intro. inversion H7. subst. contradiction.
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
Proof. intros. destruct H, H0.
       split; [rewrite H; assumption | intros; rewrite H1; apply H2].
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

Lemma lgd_gen_has_index: forall (g: LGraph) (e : EType) (v : VType) (gen idx : nat),
    gen_has_index (labeledgraph_gen_dst g e v) gen idx <-> gen_has_index g gen idx.
Proof.
  intros. unfold labeledgraph_gen_dst, gen_has_index, nth_gen. simpl. reflexivity.
Qed.

Lemma lgd_vlabel: forall (g: LGraph) (e : EType) (v x : VType),
    vlabel (labeledgraph_gen_dst g e v) x = vlabel g x.
Proof. intros. simpl. reflexivity. Qed.

Lemma lcv_gen_unmarked: forall (to : nat) (g : LGraph) (v : VType),
    vgeneration v <> to -> graph_has_gen g to -> gen_unmarked g to ->
    raw_mark (vlabel g v) = false -> gen_unmarked (lgraph_copy_v g v to) to.
Proof.
  intros. assert (forward_relation
                    (vgeneration v) to 0 (inl (inr v)) g (lgraph_copy_v g v to)) by
      (constructor; [reflexivity | assumption]).
  unfold gen_unmarked in *. intros. specialize (H1 H0 idx).
  assert (graph_has_v (lgraph_copy_v g v to) (to, idx)) by (split; assumption).
  apply lcv_graph_has_v_inv in H6. 2: assumption. destruct H6.
  * pose proof H6. destruct H6. simpl in * |-. specialize (H1 H8). rewrite <- H1.
    symmetry. apply (fr_raw_mark _ _ _ _ _ _ H0 H3); [assumption | simpl; omega].
  * rewrite H6. rewrite lcv_vlabel_new; assumption.
Qed.

Lemma lgd_gen_unmarked: forall (g: LGraph) (e : EType) (v : VType) (gen : nat),
    gen_unmarked (labeledgraph_gen_dst g e v) gen <-> gen_unmarked g gen.
Proof.
  intros. unfold gen_unmarked. rewrite lgd_graph_has_gen. split; intros.
  - specialize (H H0 idx). rewrite lgd_gen_has_index in H. specialize (H H1).
    rewrite lgd_vlabel in H. assumption.
  - rewrite lgd_gen_has_index in H1. rewrite lgd_vlabel. apply H; assumption.
Qed.

Lemma fr_gen_unmarked: forall from to depth t g g',
    from <> to -> graph_has_gen g to -> forward_relation from to depth t g g' ->
    gen_unmarked g to -> gen_unmarked g' to.
Proof.
  intros ? ? ?. revert from to. induction depth; intros.
  - inversion H1; subst; try assumption.
    + eapply lcv_gen_unmarked; eauto.
    + subst new_g. rewrite lgd_gen_unmarked. eapply lcv_gen_unmarked; eauto.
  - assert (forall l from to g1 g2,
               from <> to -> graph_has_gen g1 to -> gen_unmarked g1 to ->
               forward_loop from to depth l g1 g2 -> gen_unmarked g2 to). {
    induction l; intros; inversion H6; subst; try assumption.
    specialize (IHdepth _ _ _ _ _ H3 H4 H10 H5).
    rewrite (fr_graph_has_gen _ _ _ _ _ _ H4 H10) in H4.
    specialize (IHl _ _ _ _ H3 H4 IHdepth H13). assumption. }
    clear IHdepth. inversion H1; subst; try assumption.
    + assert (graph_has_gen new_g to) by
          (subst new_g; rewrite <- lcv_graph_has_gen; assumption).
      assert (gen_unmarked new_g to) by
          (subst new_g; apply lcv_gen_unmarked; assumption).
      eapply (H3 _ _ _ new_g); eauto.
    + assert (graph_has_gen new_g to) by
          (subst new_g; rewrite lgd_graph_has_gen, <- lcv_graph_has_gen; assumption).
      assert (gen_unmarked new_g to) by
          (subst new_g; rewrite lgd_gen_unmarked; apply lcv_gen_unmarked; assumption).
      eapply (H3 _ _ _ new_g); eauto.
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

Lemma svfl_graph_unmarked: forall from to v l g g',
    from <> to -> graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    gen_unmarked g to -> gen_unmarked g' to.
Proof.
  intros from to v l. revert from to v.
  induction l; intros; inversion H1; subst; try assumption.
  eapply (IHl from to _ g2); eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_gen_unmarked; eauto.
Qed.

Lemma svwl_gen_unmarked: forall from to l g g',
    from <> to -> graph_has_gen g to ->
    gen_unmarked g to -> scan_vertex_while_loop from to l g g' -> gen_unmarked g' to.
Proof.
  intros. revert g H H0 H1 H2. induction l; intros; inversion H2; subst;
                                 [| apply (IHl g) | apply (IHl g2)]; try assumption.
  - rewrite <- svfl_graph_has_gen; eauto.
  - eapply svfl_graph_unmarked; eauto.
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

Definition do_generation_relation (from to: nat) (roots: roots_t)
           (g g': LGraph): Prop := exists g1 g2,
    forward_roots_loop from to roots g g1 /\
    do_scan_relation from to (S (number_of_vertices (nth_gen g to))) g1 g2 /\
    g' = reset_nth_gen_graph from g2.
