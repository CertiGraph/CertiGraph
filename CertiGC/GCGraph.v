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
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
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

Definition single_vertex_size (g: LGraph) (v: VType): Z :=
  Zlength (vlabel g v).(raw_fields) + 1.

Lemma svs_gt_one: forall g v, 1 < single_vertex_size g v.
Proof.
  intros. unfold single_vertex_size. pose proof (raw_fields_range (vlabel g v)). omega.
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

Local Open Scope Z_scope.

Definition vertex_size_accum g gen (s: Z) (n: nat) :=
  s + single_vertex_size g (gen, n).

Definition previous_vertices_size (g: LGraph) (gen i: nat): Z :=
  fold_left (vertex_size_accum g gen) (nat_inc_list i) 0.

Lemma vs_accum_list_ge: forall g gen s l, s <= fold_left (vertex_size_accum g gen) l s.
Proof.
  intros. revert s. rev_induction l. 1: simpl; intuition.
  rewrite fold_left_app. simpl. unfold vertex_size_accum at 1.
  pose proof (svs_gt_one g (gen, x)). specialize (H s). omega.
Qed.

Lemma pvs_S: forall g gen i,
    previous_vertices_size g gen (S i) =
    previous_vertices_size g gen i + single_vertex_size g (gen, i).
Proof.
  intros. unfold previous_vertices_size at 1. rewrite nat_inc_list_S, fold_left_app.
  fold (previous_vertices_size g gen i). simpl. reflexivity.
Qed.

Lemma pvs_ge_zero: forall g gen i, 0 <= previous_vertices_size g gen i.
Proof. intros. unfold previous_vertices_size. apply vs_accum_list_ge. Qed.

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
    word_size_range: (0 <= fun_word_size <= Int.max_unsigned)%Z;
  }.

Definition vertex_offset (g: LGraph) (v: VType): Z :=
  previous_vertices_size g (vgeneration v) (vindex v) + 1.

Definition nth_gen (g: LGraph) (gen: nat): generation_info :=
  nth gen g.(glabel).(g_gen) null_info.

Definition generation_size g gen :=
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
            graph_has_v g (vlabel g v).(copied_vertex).

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

Fixpoint get_edges' (lf: list raw_field) (v: VType) (n: nat) : list EType :=
  match lf with
  | nil => nil
  | Some _ :: lf' => get_edges' lf' v (n + 1)
  | None :: lf' => (v, n) :: get_edges' lf' v (n + 1)
  end.

Definition get_edges (g: LGraph) (v: VType): list EType :=
  get_edges' (raw_fields (vlabel g v)) v O.

Lemma get_edges'_range: forall v n l m,
    In (v, n) (get_edges' l v m) -> m <= n < m + length l.
Proof.
  intros v n l. revert v n. induction l; simpl; intros. 1: exfalso; auto.
  specialize (IHl v n (m + 1)). destruct a. 1: apply IHl in H; omega.
  simpl in H. destruct H. 1: inversion H; omega. apply IHl in H. omega.
Qed.

Lemma get_edges'_nth: forall n l a m v,
    n < length l -> nth n l a = None <-> In (v, n + m) (get_edges' l v m).
Proof.
  induction n.
  - induction l; simpl; intros. 1: inversion H. destruct a.
    + split; intros. inversion H0. apply get_edges'_range in H0. exfalso; omega.
    + simpl. intuition.
  - destruct l; simpl; intros. 1: inversion H. assert (n < length l) by omega.
    specialize (IHn l a (m + 1) v H0).
    replace (n + (m + 1)) with (S (n + m)) in IHn by omega. rewrite IHn.
    destruct o; intuition. simpl in H3. destruct H3; auto. inversion H3. omega.
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
                                      
Definition field_t: Type := Z + GC_Pointer + EType.

Instance field_t_inhabitant: Inhabitant field_t := inl (inl Z.zero).

Definition field2val (g: LGraph) (fd: field_t) : val :=
  match fd with
  | inl (inl z) => odd_Z2val z
  | inl (inr p) => GC_Pointer2val p
  | inr e => vertex_address g (dst g e)
  end.

Fixpoint make_fields' (g: LGraph) (l_raw: list raw_field)
         (v: VType) (n: nat): list field_t :=
  match l_raw with
  | nil => nil
  | Some (inl z) :: l => inl (inl z) :: make_fields' g l v (n + 1)
  | Some (inr ptr) :: l => inl (inr ptr) :: make_fields' g l v (n + 1)
  | None :: l => inr (v, n) :: make_fields' g l v (n + 1)
  end.

Lemma make_fields'_eq_length: forall g l v n, length (make_fields' g l v n) = length l.
Proof.
  intros. revert n. induction l; intros; simpl. 1: reflexivity.
  destruct a; [destruct s|]; simpl; rewrite IHl; reflexivity.
Qed.

Definition make_fields (g: LGraph) (v: VType): list field_t :=
  make_fields' g (vlabel g v).(raw_fields) v O.

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

Lemma vertex_address_the_same: forall (g1 g2: LGraph) v,
    (forall v, g1.(vlabel) v = g2.(vlabel) v) ->
    map start_address g1.(glabel).(g_gen) = map start_address g2.(glabel).(g_gen) ->
    vertex_address g1 v = vertex_address g2 v.
Proof.
  intros. unfold vertex_address. f_equal.
  - f_equal. unfold vertex_offset. f_equal. remember (vindex v). clear Heqn.
    induction n; simpl; auto. rewrite !pvs_S, IHn. f_equal. unfold single_vertex_size.
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
  assert (forall n, make_fields' g1 l v n = make_fields' g2 l v n). {
    induction l; intros; simpl; auto.
    destruct a; [destruct s|]; rewrite IHl; reflexivity.
  } rewrite H2. cut (forall fl, map (field2val g1) fl = map (field2val g2) fl).
  - intros. rewrite H3. rewrite (vertex_address_the_same g1 g2) by assumption.
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
    rewrite !pvs_S, IHn. f_equal. unfold single_vertex_size. rewrite H. reflexivity.
Qed.

Definition copy1v_add_edge
           (s: VType) (g: PreGraph VType EType) (p: EType * VType):
  PreGraph VType EType := pregraph_add_edge g (fst p) s (snd p).

Definition pregraph_copy1v (g: LGraph) (old_v new_v: VType) : PreGraph VType EType :=
  let old_edges := get_edges g old_v in
  let new_edges := combine (repeat new_v (length old_edges)) (map snd old_edges) in
  let new_edge_dst_l := combine new_edges (map (dst g) old_edges) in
  fold_left (copy1v_add_edge new_v) new_edge_dst_l (pregraph_add_vertex g new_v).

Definition copy1v_mod_rvb (rvb: raw_vertex_block) (new_v: VType) : raw_vertex_block :=
  Build_raw_vertex_block
    true new_v (raw_fields rvb) (raw_color rvb) (raw_tag rvb)
    (raw_tag_range rvb) (raw_color_range rvb) (raw_fields_range rvb).

Definition copy1v_update_vlabel (g: LGraph) (old_v new_v: VType) :=
  let old_rvb := vlabel g old_v in
  update_vlabel (update_vlabel (vlabel g) old_v (copy1v_mod_rvb old_rvb new_v))
                new_v old_rvb.

Definition copy1v_mod_gen_info (gi: generation_info) : generation_info :=
  Build_generation_info (start_address gi) (number_of_vertices gi + 1)
                        (generation_sh gi) (start_isptr gi)
                        (generation_share_writable gi).

Definition copy1v_mod_gen_info_list
           (l: list generation_info) (to: nat) : list generation_info :=
  firstn to l ++ copy1v_mod_gen_info (nth to l null_info) :: skipn (to + 1) l.

Lemma copy1v_mod_gen_no_nil: forall l to, copy1v_mod_gen_info_list l to <> nil.
Proof.
  repeat intro. unfold copy1v_mod_gen_info_list in H. apply app_eq_nil in H.
  destruct H. inversion H0.
Qed.

Definition copy1v_update_glabel (gi: graph_info) (to: nat): graph_info :=
  Build_graph_info (copy1v_mod_gen_info_list (g_gen gi) to)
                   (copy1v_mod_gen_no_nil (g_gen gi) to).

Definition copy1v_new_v (g: LGraph) (to: nat): VType :=
  (to, number_of_vertices (nth_gen g to)).

Definition lgraph_copy1v (g: LGraph) (v: VType) (to: nat): LGraph :=
  let new_v := copy1v_new_v g to in
  Build_LabeledGraph _ _ _ (pregraph_copy1v g v new_v)
                     (copy1v_update_vlabel g v new_v)
                     (elabel g) (copy1v_update_glabel (glabel g) to).

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
    forward_relation from to O (inl (inr v)) g (lgraph_copy1v g v to)
| fr_v_in_not_forwarded_Sn: forall depth v g g',
    vgeneration v = from -> (vlabel g v).(raw_mark) = false ->
    let new_g := lgraph_copy1v g v to in
    forward_loop from to depth (make_fields new_g (copy1v_new_v g to)) new_g g' ->
    forward_relation from to (S depth) (inl (inr v)) g g'
| fr_e_not_to: forall depth e (g: LGraph),
    vgeneration (dst g e) <> from -> forward_relation from to depth (inr e) g g
| fr_e_to_forwarded: forall depth e (g: LGraph),
    vgeneration (dst g e) = from -> (vlabel g (dst g e)).(raw_mark) = true ->
    let new_g := labeledgraph_gen_dst g e (vlabel g (dst g e)).(copied_vertex) in
    forward_relation from to depth (inr e) g new_g
| fr_e_to_not_forwarded_O: forall e (g: LGraph),
    vgeneration (dst g e) = from -> (vlabel g (dst g e)).(raw_mark) = false ->
    let new_g := labeledgraph_gen_dst (lgraph_copy1v g (dst g e) to) e
                                      (copy1v_new_v g to) in
    forward_relation from to O (inr e) g new_g
| fr_e_to_not_forwarded_Sn: forall depth e (g g': LGraph),
    vgeneration (dst g e) = from -> (vlabel g (dst g e)).(raw_mark) = false ->
    let new_g := labeledgraph_gen_dst (lgraph_copy1v g (dst g e) to) e
                                      (copy1v_new_v g to) in
    forward_loop from to depth (make_fields new_g (copy1v_new_v g to)) new_g g' ->
    forward_relation from to (S depth) (inr e) g g'
with
forward_loop (from to: nat): nat -> list field_t -> LGraph -> LGraph -> Prop :=
| fl_nil: forall depth g, forward_loop from to depth nil g g
| fl_cons: forall depth g1 g2 g3 f fl,
    forward_relation from to depth (field2forward f) g1 g2 ->
    forward_loop from to depth fl g2 g3 -> forward_loop from to depth (f :: fl) g1 g3.

Definition forward_p_type: Type := Z + (VType * Z).

Definition forward_p2forward_t
           (p: forward_p_type) (roots: roots_t) (g: LGraph): forward_t :=
  match p with
  | inl root_index => root2forward (Znth root_index roots)
  | inr (v, n) => field2forward (Znth n (make_fields g v))
  end.

Definition forward_p_compatible
           (p: forward_p_type) (roots: roots_t) (g: LGraph): Prop :=
  match p with
  | inl root_index => 0 <= root_index < Zlength roots
  | inr (v, n) => graph_has_v g v /\ 0 <= n < Zlength (vlabel g v).(raw_fields)
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
    0 <= i < 1024 -> Zlength (upd_Znth i (ti_args t) v) = MAX_ARGS.
Proof.
  intros. rewrite upd_Znth_Zlength; [apply arg_size | rewrite arg_size; rep_omega].
Qed.

Definition upd_thread_info_arg
           (t: thread_info) (i: Z) (v: val) (H: 0 <= i < 1024) : thread_info :=
  Build_thread_info (ti_heap_p t) (ti_heap t) (upd_Znth i (ti_args t) v)
                    (upd_thread_info_Zlength t i v H).

Lemma upd_fun_thread_arg_compatible: forall g t_info f_info roots z,
    fun_thread_arg_compatible g t_info f_info roots ->
    forall (v : VType) (HB : 0 <= Znth z (live_roots_indices f_info) < 1024),
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
                                                (inr (copy1v_new_v g to))
                            else roots
                 end
  end.

(* 
Goes over all the roots, and forwards those that point to the from space. The graph relation proposed is that between g_alpha and g_omega. Borrows heavily from forward_relation. Perhaps forward_relation itself can be changed to accept both root_t and field_t in the forward loop?
*)
Inductive forward_roots_loop (from to: nat):
  nat -> roots_t -> LGraph -> LGraph -> Prop :=
| frl_nil: forall depth g, forward_roots_loop from to depth nil g g
| frl_cons: forall depth g1 g2 g3 f rl,
    forward_relation from to depth (root2forward f) g1 g2 ->
    forward_roots_loop from to depth rl g2 g3 ->
    forward_roots_loop from to depth (f :: rl) g1 g3.

(* 
Forwards all roots that are pointing at the from space. Borrows heavily from forwarded_roots above. 
*)
Fixpoint forward_all_roots (from to: nat) (roots: roots_t) (g: LGraph) : roots_t :=
  match roots with
  | [] => []
  | r :: roots' =>
    let tail := forward_all_roots from to roots' g in
    match r with
    | inl (inl z) => r :: tail 
    | inl (inr p) => r :: tail
    | inr v =>
        if Nat.eq_dec (vgeneration v) from
        then if (vlabel g v).(raw_mark)
             then (inr (vlabel g v).(copied_vertex)) :: tail
             else (inr (copy1v_new_v g to)) :: tail
        else r :: tail
    end
  end.

Definition nth_space (t_info: thread_info) (n: nat): space :=
  nth n t_info.(ti_heap).(spaces) null_space.

Definition gen_size (t_info: thread_info) (n: nat): Z :=
  total_space (nth_space t_info n).

Lemma graph_thread_generation_space_compatible:
  forall (g: LGraph) (t_info: thread_info),
    graph_thread_info_compatible g t_info ->
    forall gen,
      graph_has_gen g gen -> 
      generation_space_compatible g (gen, nth_gen g gen, nth_space t_info gen).
Proof.
  intros. destruct H as [? [? ?]]. red in H0. rewrite Forall_forall in H.
  remember (g_gen (glabel g)). remember (nat_inc_list (length l)).
  remember (spaces (ti_heap t_info)).
  assert (length (combine l0 l) = length l) by
      (subst; rewrite combine_length, nat_inc_list_length, Nat.min_id; reflexivity).
  assert (length (combine (combine l0 l) l1) = length l) by
      (rewrite combine_length, H3, min_l by assumption; reflexivity).
  assert (generation_space_compatible
            g (nth gen (combine (combine l0 l) l1) (O, null_info, null_space))) by
      (apply H, nth_In; rewrite H4; assumption).
  rewrite combine_nth_lt in H5; [|rewrite H3; omega | omega].
  rewrite combine_nth in H5 by (subst l0; rewrite nat_inc_list_length; reflexivity).
  rewrite Heql0 in H5. rewrite nat_inc_list_nth in H5 by assumption.
   rewrite Heql in H5. unfold nth_gen. unfold nth_space. rewrite Heql1 in H5. apply H5.
Qed.

Lemma pvs_mono: forall g gen i j,
    i <= j -> (previous_vertices_size g gen i <= previous_vertices_size g gen j)%Z.
Proof.
  intros. assert (j = i + (j - i)) by omega. rewrite H0. remember (j - i). subst j.
  unfold previous_vertices_size. rewrite nat_inc_list_app, fold_left_app.
  apply vs_accum_list_ge.
Qed.

Local Open Scope Z_scope.

Lemma vo_lt_gs: forall g v,
    gen_has_index g (vgeneration v) (vindex v) ->
    vertex_offset g v < generation_size g (vgeneration v).
Proof.
  intros. unfold vertex_offset, generation_size. red in H.
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
    destruct (graph_thread_generation_space_compatible _ _ H _ H0) as [? [? ?]].
    rewrite <- H4, Heqn. apply vo_lt_gs. subst n. assumption.
Qed.

Definition nth_sh g gen := generation_sh (nth_gen g gen).
