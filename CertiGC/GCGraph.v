Require Import Coq.ZArith.ZArith.
Require Export Coq.Program.Basics.
Require Import Coq.micromega.Lia.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import VST.veric.base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.val_lemmas.
Require Import VST.veric.shares.
Require Import VST.msl.seplog.
Require Import VST.msl.shares.
Require Import VST.zlist.sublist.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.functional_base.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.zlist.list_solver.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Export CertiGraph.graph.graph_gen.
Import ListNotations.

Local Open Scope Z_scope.
Require CertiGraph.CertiGC.gc_stack.
Import Ctypes compspecs Cop2 Clight.

Fixpoint find_struct (i: ident) (cs: list composite_definition) : option members :=
  match cs with
  | nil => None
  | Composite name Struct m _ :: rest =>
     if eqb_ident i name then Some m else find_struct i rest
  |  _ :: rest => find_struct i rest
  end.

Definition MAX_SPACES: Z := Eval compute in
    (match find_struct gc_stack._heap gc_stack.composites with
     | Some  (Member_plain _ (Tarray _ n _) :: nil) => n | _ => 0
     end).

Lemma MAX_SPACES_eq: MAX_SPACES = ltac:(let n := eval compute in MAX_SPACES in exact n). Proof. reflexivity. Qed.
#[export] Hint Rewrite MAX_SPACES_eq: rep_lia.

Definition LOG_NURSERY_SIZE : Z.
let f := constr:(fn_body gc_stack.f_create_heap) in
let f := eval hnf in f in
match f with context [Scall _ (Evar gc_stack._create_space _) [_; Ebinop _ _ (Econst_int (Int.repr ?e) _) _]] =>
  exact e
end.
Defined.

Definition NURSERY_SIZE: Z := Z.shiftl 1 LOG_NURSERY_SIZE.
Lemma NURSERY_SIZE_eq: NURSERY_SIZE = Z.shiftl 1 ltac:(let n := eval hnf in LOG_NURSERY_SIZE in exact n). Proof. reflexivity. Qed.
#[export] Hint Rewrite NURSERY_SIZE_eq: rep_lia.
Global Opaque NURSERY_SIZE.

Definition MAX_ARGS: Z := 1024.
Lemma MAX_ARGS_eq: MAX_ARGS = 1024. Proof. reflexivity. Qed.
#[export] Hint Rewrite MAX_ARGS_eq: rep_lia.
Global Opaque MAX_ARGS.

Definition WORD_SIZE: Z := Eval cbv [Archi.ptr64] in if Archi.ptr64 then 8 else 4.

Definition MAX_UINT: Z := Eval cbv [Archi.ptr64] in
      if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned.

Definition MAX_SPACE_SIZE: Z :=
    Z.shiftl 1 ltac:(let a := constr:(LOG_NURSERY_SIZE+MAX_SPACES-1) in
                     let a := eval compute in a in exact a).

Global Opaque MAX_SPACES.

Definition NO_SCAN_TAG: Z := 251.
Lemma NO_SCAN_TAG_eq: NO_SCAN_TAG = 251. Proof. reflexivity. Qed.
#[export] Hint Rewrite NO_SCAN_TAG_eq: rep_lia.
Global Opaque NO_SCAN_TAG.

Definition SPACE_STRUCT_SIZE: Z :=
  Eval cbv [Archi.ptr64] in if Archi.ptr64 then 32 else 16.

Lemma four_div_WORD_SIZE: (4 | WORD_SIZE).
Proof. first [now exists 1 | now exists 2]. Qed.

Lemma MSS_max_unsigned_range: forall n,
    0 <= n <= MAX_SPACE_SIZE ->
    0 <= n <= if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned.
Proof.
  intros. cbv [Archi.ptr64]. destruct H.
  split; auto.
  assert (n <= MAX_SPACE_SIZE); try lia.
  transitivity MAX_SPACE_SIZE. 1: assumption.
  intro Hx; inv Hx.
Qed.

Lemma MSS_max_wordsize_unsigned_range: forall n,
    0 <= n <= MAX_SPACE_SIZE ->
    0 <= WORD_SIZE * n <= if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned.
Proof.
  intros. cbv [Archi.ptr64]. destruct H. split. 1: unfold WORD_SIZE; lia.
  transitivity (WORD_SIZE * MAX_SPACE_SIZE); unfold WORD_SIZE. 1: lia.
  intro; discriminate.
Qed.

Lemma MSS_max_wordsize_signed_range: forall n,
    0 <= n <= MAX_SPACE_SIZE -> Ptrofs.min_signed <= WORD_SIZE * n <= Ptrofs.max_signed.
Proof.
  intros. destruct H. split.
  - unfold WORD_SIZE. transitivity 0. 2: lia. rewrite Z.le_lteq. left.
    apply Ptrofs.min_signed_neg.
  - apply Z.le_trans with (WORD_SIZE * MAX_SPACE_SIZE).
    apply Z.mul_le_mono_nonneg_l. compute; congruence.  auto.
    unfold WORD_SIZE.
    unfold MAX_SPACE_SIZE.
    unfold Ptrofs.max_signed, Ptrofs.half_modulus, Ptrofs.modulus, Ptrofs.wordsize,
      Wordsize_Ptrofs.wordsize.
    destruct Archi.ptr64 eqn:?; first [now inversion Heqb | simpl; lia].
Qed.

Definition VType: Type := nat * nat.  (* generation number, block-number within generation *)
Definition EType: Type := VType * nat.  (* vertex, out-edge-index *)
Definition vgeneration: VType -> nat := fst.
Definition vindex: VType -> nat := snd.

#[export] Instance V_EqDec: EqDec VType eq.
Proof.
  hnf. intros [x] [y]. destruct (Nat.eq_dec x y).
  - destruct (Nat.eq_dec n n0); subst.
    + left. reflexivity.
    + right. intro. apply n1. inversion H. reflexivity.
  - right. intro. apply n1. inversion H. reflexivity.
Defined.

#[export] Instance E_EqDec: EqDec EType eq.
Proof.
  hnf. intros [x] [y]. destruct (equiv_dec x y).
  - hnf in e. destruct (Nat.eq_dec n n0); subst.
    + left; reflexivity.
    + right; intro; apply n1; inversion H; reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

Inductive GC_Pointer := | GCPtr: block -> ptrofs -> GC_Pointer.

Inductive raw_field: Type :=
| RawInternal (* internal-heap-pointer *)
| RawUnboxed: Z -> raw_field (* unboxed value *)
| RawOutlier: GC_Pointer -> raw_field. (* outlier *)

#[export] Instance raw_field_inhabitant: Inhabitant raw_field := RawInternal.

Definition odd_Z2val (x: Z) : val :=
  Eval cbv delta [Archi.ptr64] match
         in (if Archi.ptr64 then Vlong (Int64.repr (2 * x + 1)%Z)
              else Vint (Int.repr (2 * x + 1)%Z)).

Definition Z2val (x: Z) : val :=
  Eval cbv delta [Archi.ptr64] match
         in if Archi.ptr64 then Vlong (Int64.repr x) else Vint (Int.repr x).

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
    raw_fields_range: 0 < Zlength raw_fields < two_p (WORD_SIZE * 8 - 10);
    tag_no_scan: NO_SCAN_TAG <= raw_tag -> ~ In RawInternal raw_fields;
    (* what's up with this? why can raw_f be None at all? *)
  }.

Local Close Scope Z_scope.

Lemma raw_fields_not_nil: forall rvb, raw_fields rvb <> nil.
Proof.
  intros. pose proof raw_fields_range rvb. destruct (raw_fields rvb).
  - simpl in H. rewrite Zlength_nil in H. exfalso; lia.
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
  - exfalso. clear Heqr. rewrite Zlength_nil in raw_fields_range0. lia.
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

#[export] Instance gen_info_inhabitant: Inhabitant generation_info := null_info.

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

Definition LGraph := LabeledGraph VType EType raw_vertex_block nat graph_info.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Record space: Type :=
  {
    space_start: val;
    used_space: Z;
    available_space: Z;
    total_space: Z;
    space_sh: share;
    used_leq_available: 0 <= used_space <= available_space;
    available_leq_total: available_space <= total_space;
    space_upper_bound: total_space <= MAX_SPACE_SIZE;
  }.

Definition null_space: space.
Proof.
  refine (Build_space nullval 0 0 0 emptyshare _ _ _).
  - split; apply Z.le_refl.
  - apply Z.le_refl.
  - apply Z.shiftl_nonneg, Z.le_0_1.
Defined.

#[export] Instance space_inhabitant: Inhabitant space := null_space.

Lemma available_space_tight_range: forall sp, 0 <= available_space sp <= MAX_SPACE_SIZE.
Proof.
  intros. split.
  - destruct (used_leq_available sp). transitivity (used_space sp); assumption.
  - transitivity (total_space sp); [apply available_leq_total | apply space_upper_bound].
Qed.

Lemma available_space_range: forall sp, 0 <= available_space sp <= (if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned).
Proof.
  intros. apply MSS_max_unsigned_range. pose proof available_space_tight_range sp. lia.
Qed.

Lemma available_space_signed_range: forall sp,
    Ptrofs.min_signed <= WORD_SIZE * available_space sp <= Ptrofs.max_signed.
Proof. intros. apply MSS_max_wordsize_signed_range, available_space_tight_range. Qed.

Lemma used_space_signed_range: forall sp,
    Ptrofs.min_signed <= WORD_SIZE * used_space sp <= Ptrofs.max_signed.
Proof.
  intros. apply MSS_max_wordsize_signed_range. destruct (used_leq_available sp). split.
  1: assumption. apply Z.le_trans with (available_space sp). 1: assumption.
  apply (proj2 (available_space_tight_range sp)).
Qed.

Lemma total_space_tight_range: forall sp, 0 <= total_space sp <= MAX_SPACE_SIZE.
Proof.
  intros. pose proof used_leq_available sp. pose proof available_leq_total sp.
  pose proof space_upper_bound sp. lia.
Qed.

Lemma total_space_signed_range: forall sp,
    Ptrofs.min_signed <= WORD_SIZE * total_space sp <= Ptrofs.max_signed.
Proof. intros. apply MSS_max_wordsize_signed_range, total_space_tight_range. Qed.

Lemma rest_space_signed_range: forall sp,
    Ptrofs.min_signed <=
      WORD_SIZE * available_space sp - WORD_SIZE * used_space sp <= Ptrofs.max_signed.
Proof.
  intros. rewrite <- Z.mul_sub_distr_l. apply MSS_max_wordsize_signed_range.
  destruct (used_leq_available sp). pose proof available_space_tight_range sp. lia.
Qed.

Lemma remset_space_signed_range: forall sp,
    Ptrofs.min_signed <=
      WORD_SIZE * total_space sp - WORD_SIZE * available_space sp <= Ptrofs.max_signed.
Proof.
  intros. rewrite <- Z.mul_sub_distr_l. apply MSS_max_wordsize_signed_range.
  pose proof used_leq_available sp. pose proof available_leq_total sp.
  pose proof space_upper_bound sp. lia.
Qed.

Definition range_signed (z: Z) :=
  (if Archi.ptr64 then Int64.min_signed else Int.min_signed) <= z <=
  (if Archi.ptr64 then Int64.max_signed else Int.max_signed).

Lemma signed_range_repable_signed: forall z,
    Ptrofs.min_signed <= z <= Ptrofs.max_signed <-> range_signed z.
Proof.
  intros. unfold range_signed.
  replace Ptrofs.max_signed with
      (if Archi.ptr64 then Int64.max_signed else Int.max_signed) by
      (vm_compute; reflexivity).
  replace Ptrofs.min_signed with
      (if Archi.ptr64 then Int64.min_signed else Int.min_signed) by
      (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma used_space_repable_signed: forall sp, range_signed (used_space sp).
Proof.
  intros. rewrite <- signed_range_repable_signed.
  pose proof used_space_signed_range sp. unfold WORD_SIZE in H. rep_lia.
Qed.

Lemma available_space_repable_signed: forall sp, range_signed (available_space sp).
Proof.
  intros. rewrite <- signed_range_repable_signed.
  pose proof available_space_signed_range sp. unfold WORD_SIZE in H. rep_lia.
Qed.

Lemma total_space_repable_signed: forall sp, range_signed (total_space sp).
Proof.
  intros. rewrite <- signed_range_repable_signed.
  pose proof total_space_signed_range sp. unfold WORD_SIZE in H. rep_lia.
Qed.

Lemma rest_space_repable_signed: forall sp, range_signed (available_space sp - used_space sp).
Proof.
  intros. rewrite <- signed_range_repable_signed.
  pose proof rest_space_signed_range sp. unfold WORD_SIZE in H. rep_lia.
Qed.

Lemma remset_space_repable_signed: forall sp, range_signed (total_space sp - available_space sp).
Proof.
  intros. rewrite <- signed_range_repable_signed.
  pose proof remset_space_signed_range sp. unfold WORD_SIZE in H. rep_lia.
Qed.

Definition repable64_signed (z: Z) :=
  Int64.min_signed <= z <= Int64.max_signed.

Lemma lt64_repr: forall i j,
    repable64_signed i -> repable64_signed j ->
    Int64.lt (Int64.repr i) (Int64.repr j) = true -> i < j.
Proof.
  intros. unfold Int64.lt in H1. if_tac in H1. 2: inversion H1.
  rewrite !Int64.signed_repr in H2; auto.
Qed.

Lemma lt64_repr_false: forall i j,
    repable64_signed i -> repable64_signed j ->
    Int64.lt (Int64.repr i) (Int64.repr j) = false -> i >= j.
Proof.
  intros. unfold Int64.lt in H1. if_tac in H1. 1: inversion H1.
  rewrite !Int64.signed_repr in H2; auto.
Qed.

Record heap: Type :=
  {
    spaces: list space;
    spaces_size: Zlength spaces = MAX_SPACES;
  }.

Lemma heap_spaces_nil: forall h: heap, nil = spaces h -> False.
Proof.
  intros. pose proof spaces_size h. rewrite <- H, Zlength_nil in H0. discriminate.
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

Record frame : Type :=
  { fr_adr: val;
    fr_root: val;
    fr_roots: list val
  }.

#[export] Instance Inh_frame: Inhabitant frame := Build_frame nullval nullval nil.

Record rootpair : Type := { rp_adr: val; rp_val: val }.

Fixpoint frame2rootpairs' (base: val) (z: Z) (al: list val) : list rootpair :=
  match al with
  | nil => nil
  | a :: al' => {| rp_adr := offset_val (z * WORD_SIZE) base; rp_val := a |}
                  :: frame2rootpairs' base (Z.succ z) al'
  end.

Definition frame2rootpairs (f: frame) : list rootpair :=
  frame2rootpairs' f.(fr_root) 0 f.(fr_roots).

Record thread_info: Type :=
  {
    ti_heap_p: val;
    ti_heap: heap;
    ti_args: list val;
    arg_size: Zlength ti_args = MAX_ARGS;
    ti_frames: list frame;
    ti_nalloc: Ptrofs.int
  }.

Definition vertex_size (g: LGraph) (v: VType): Z :=
  Zlength (vlabel g v).(raw_fields) + 1.

Lemma svs_gt_one: forall g v, 1 < vertex_size g v.
Proof.
  intros. unfold vertex_size. pose proof raw_fields_range (vlabel g v). lia.
Qed.

Local Close Scope Z_scope.

Lemma seq_Permutation_cons: forall s i n,
    i < n -> exists l, Permutation (seq s n) (s + i :: l).
Proof.
  intros. induction n. 1: lia. replace (S n) with (n + 1) by lia.
  rewrite seq_app. simpl. destruct (Nat.eq_dec i n).
  - subst i. exists (seq s n). symmetry. apply Permutation_cons_append.
  - assert (i < n) by lia. apply IHn in H0. destruct H0 as [l ?].
    exists (l +:: (s + n)). rewrite app_comm_cons. apply Permutation_app_tail.
    assumption.
Qed.

Definition nat_inc_list (n: nat) : list nat := seq O n.

Lemma nat_inc_list_length: forall num, length (nat_inc_list num) = num.
Proof. intros. unfold nat_inc_list. rewrite seq_length. reflexivity. Qed.

Lemma nat_inc_list_S: forall num, nat_inc_list (S num) = nat_inc_list num ++ [num].
Proof. intros. unfold nat_inc_list. rewrite seq_S. repeat f_equal. Qed.

Lemma nat_inc_list_In_iff: forall i n, In i (nat_inc_list n) <-> i < n.
Proof. intros. unfold nat_inc_list. rewrite in_seq. lia. Qed.

Lemma nat_inc_list_nth: forall i n a, i < n -> nth i (nat_inc_list n) a = i.
Proof. intros. unfold nat_inc_list. rewrite seq_nth; [lia | assumption]. Qed.

Lemma nat_inc_list_app: forall n m,
    nat_inc_list (n + m) = nat_inc_list n ++ seq n m.
Proof. intros. unfold nat_inc_list. rewrite seq_app. reflexivity. Qed.

Lemma nat_inc_list_NoDup: forall n, NoDup (nat_inc_list n).
Proof. intros. unfold nat_inc_list. apply seq_NoDup. Qed.

Lemma nat_inc_list_Permutation_cons: forall i n,
    i < n -> exists l, Permutation (nat_inc_list n) (i :: l).
Proof.
  intros. unfold nat_inc_list. replace i with (O + i) by lia.
  apply seq_Permutation_cons. assumption.
Qed.

Local Open Scope Z_scope.

Definition vertex_size_accum g gen (s: Z) (n: nat) := s + vertex_size g (gen, n).

Definition previous_vertices_size (g: LGraph) (gen i: nat): Z :=
  fold_left (vertex_size_accum g gen) (nat_inc_list i) 0.

Lemma vsa_mono: forall g gen s n, s < vertex_size_accum g gen s n.
Proof.
  intros. unfold vertex_size_accum. pose proof svs_gt_one g (gen, n). lia.
Qed.

Lemma vsa_comm: forall g gen s n1 n2,
    vertex_size_accum g gen (vertex_size_accum g gen s n1) n2 =
    vertex_size_accum g gen (vertex_size_accum g gen s n2) n1.
Proof. intros. unfold vertex_size_accum. lia. Qed.

Lemma vs_accum_list_lt: forall g gen s l,
    l <> nil -> s < fold_left (vertex_size_accum g gen) l s.
Proof.
  intros; apply (fold_left_Z_mono_strict (vertex_size_accum g gen) nil l l);
    [apply vsa_mono | apply vsa_comm | assumption | apply Permutation_refl].
Qed.

Lemma vs_accum_list_le: forall g gen s l, s <= fold_left (vertex_size_accum g gen) l s.
Proof.
  intros. destruct l. 1: simpl; lia. rename l into l1. remember (n :: l1).
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

Definition graph_heap_compatible (g: LGraph) (h: heap): Prop :=
  Forall (generation_space_compatible g)
         (combine (combine (nat_inc_list (length g.(glabel).(g_gen)))
                           g.(glabel).(g_gen)) h.(spaces)) /\
  Forall (eq nullval)
         (skipn (length g.(glabel).(g_gen)) (map space_start h.(spaces))) /\
  length g.(glabel).(g_gen) <= length h.(spaces).

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
  intros. hnf. destruct (g_gen (glabel g)) eqn:? ; simpl; try lia.
  pose proof g_gen_not_nil (glabel g). contradiction.
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

Lemma graph_has_v_addr_isptr: forall g v, graph_has_v g v -> isptr (vertex_address g v).
Proof.
  intros. unfold vertex_address. apply isptr_offset_val', graph_has_gen_start_isptr.
  destruct v, H. simpl in H |- *. assumption.
Qed.

Inductive exterior_t: Type :=
| ExteriorUnboxed: Z -> exterior_t
| ExteriorOutlier: GC_Pointer -> exterior_t
| ExteriorVertex: VType -> exterior_t.

#[export] Instance exterior_t_inhabitant: Inhabitant exterior_t := ExteriorUnboxed Z.zero.

Definition exterior2val (g: LGraph) (fd: exterior_t) : val :=
  match fd with
  | ExteriorUnboxed z => odd_Z2val z
  | ExteriorOutlier p => GC_Pointer2val p
  | ExteriorVertex v => vertex_address g v
  end.

Definition roots_t: Type := list exterior_t.

Definition outlier_t: Type := list GC_Pointer.

Definition frames2rootpairs (frames: list frame) : list rootpair :=
    List.concat (map frame2rootpairs frames).

Lemma frames2rootpairs_app: forall al bl, frames2rootpairs (al++bl) = frames2rootpairs al ++ frames2rootpairs bl.
    Proof.
     unfold frames2rootpairs.
     induction al; simpl; intros; auto.
     rewrite <- app_assoc. f_equal. auto.
    Qed.

Lemma frames2rootpairs_cons: forall a bl, frames2rootpairs (a::bl) = frame2rootpairs a ++ frames2rootpairs bl.
    Proof.
     intros.
     reflexivity.
    Qed.

Lemma frames2rootpairs_nil: frames2rootpairs nil = nil.
Proof. reflexivity. Qed.

#[export] Hint Rewrite frames2rootpairs_app frames2rootpairs_cons frames2rootpairs_nil : sublist list_solve_rewrite.

Lemma Zlength_frames2rootpairs_sublist:
  forall k frs,
    (0 <= k <= Zlength frs ->
     Zlength (frames2rootpairs (sublist 0 k frs)) <= Zlength(frames2rootpairs frs))%Z.
  Proof.
   intros ? ? H2.
   rewrite <- (sublist_same 0 (Zlength frs) frs) at 2 by auto.
   rewrite (sublist_split 0 k (Zlength frs)) by lia.
   rewrite frames2rootpairs_app. Zlength_solve.
  Qed.

Fixpoint update_rootpairs (rootpairs: list rootpair) (roots: list val) : list rootpair :=
  match rootpairs, roots with
  | {| rp_adr := a; rp_val := _ |} :: rp' , r::roots' =>
      {|rp_adr := a; rp_val := r |} :: update_rootpairs rp' roots'
      | _, _ => nil
  end.

Fixpoint update_frames (frames: list frame) (roots: list val) : list frame :=
 match frames with
 | {| fr_adr := a; fr_root := r; fr_roots := s |} :: rest =>
 {| fr_adr := a; fr_root := r; fr_roots := sublist 0 (Zlength s) roots |}
    :: update_frames rest (sublist (Zlength s) (Zlength roots) roots)
  | nil => nil
 end.

Lemma update_rootpairs_same: forall rootpairs,
    update_rootpairs rootpairs (map rp_val rootpairs) = rootpairs.
Proof.
  induction rootpairs as [ | [a r] rest ]; simpl; f_equal; auto.
Qed.

#[export] Instance rootpair_inhabitant: Inhabitant rootpair := Build_rootpair Vundef Vundef.

Lemma update_rootpairs_upd_Znth: forall rootpairs i v,
    update_rootpairs rootpairs (upd_Znth i (map rp_val rootpairs) v) =
      upd_Znth i rootpairs {|rp_adr := rp_adr (Znth i rootpairs); rp_val := v |}.
Proof.
  intros.
  destruct (Sumbool.sumbool_and (0 <= i)%Z (0 > i)%Z (i < Zlength rootpairs)%Z
              (~ (i < Zlength rootpairs)%Z)
              (Z_le_gt_dec 0 i) (Z_lt_dec i (Zlength rootpairs))).
  - revert i a. induction rootpairs; simpl; intros. 1: list_solve. destruct (Z.eq_dec i 0).
    + subst i. destruct a. rewrite Znth_0_cons, !upd_Znth0. simpl. f_equal.
      apply update_rootpairs_same.
    + destruct a. rewrite !upd_Znth_cons, Znth_pos_cons by lia. simpl. f_equal.
      apply IHrootpairs. list_solve.
  - rewrite !upd_Znth_out_of_range by list_solve. apply update_rootpairs_same.
Qed.

 Lemma Zlength_frame2rootpairs': forall r i s, Zlength (frame2rootpairs' r i s) = Zlength s.
 Proof.
   intros.
   revert i; induction s; simpl; intros; auto.
   list_solve.
 Qed.

 Lemma Zlength_frame2rootpairs: forall f, Zlength (frame2rootpairs f) = Zlength (fr_roots f).
 Proof.
   intros.
   apply Zlength_frame2rootpairs'.
 Qed.

 #[export] Hint Rewrite Zlength_frame2rootpairs Zlength_frame2rootpairs': sublist Zlength.


Lemma rp_val_frame2rootpairs': forall r k s, map rp_val (frame2rootpairs' r k s) = s.
Proof.
 intros.
  revert r k; induction s; simpl in *; intros; auto.
  f_equal; auto.
Qed.

Lemma rp_val_frame2rootpairs: forall f, map rp_val (frame2rootpairs f) = fr_roots f.
Proof.
 intros.
  destruct f as [a r s].
  unfold frame2rootpairs.
  forget 0%Z as k.
  revert r k; induction s; simpl in *; intros; auto.
  f_equal; auto.
Qed.


#[export] Hint Rewrite rp_val_frame2rootpairs rp_val_frame2rootpairs': sublist list_solve_rewrite.

Lemma update_frames_same: forall frames, update_frames frames (map rp_val (frames2rootpairs frames)) = frames.
Proof.
  induction frames as [ | [a r s] rest ]; simpl; auto.
  rewrite !frames2rootpairs_cons.
  rewrite !map_app.
  rewrite !rp_val_frame2rootpairs.
  simpl.
  f_equal. f_equal. list_solve.
  etransitivity ; [ | eassumption].
  f_equal.
  list_solve.
Qed.

Lemma update_update_rootpairs: forall rp v1 v2,
  (Zlength v1 >= Zlength rp)%Z ->
  (Zlength v2 >= Zlength rp)%Z ->
  update_rootpairs (update_rootpairs rp v1) v2 = update_rootpairs rp v2.
  Proof.
        induction rp as [ | [? ? ]]; destruct v1; destruct v2; simpl; intros; try list_solve.
        f_equal.
        apply IHrp; list_solve.
  Qed.

Lemma Zlength_update_rootpairs':
  forall (rootpairs : list rootpair) (roots : list val),
  (Zlength rootpairs <= Zlength roots)%Z <->
  Zlength (update_rootpairs rootpairs roots) = Zlength rootpairs.
  Proof. induction rootpairs as [|[??]]; destruct roots; simpl; intros; try list_solve.

  rewrite !Zlength_cons. specialize (IHrootpairs roots).
      split; intros. f_equal; apply IHrootpairs. lia. lia.
  Qed.

Definition rootpairs_compatible (g: LGraph) (rootpairs: list rootpair) (roots: roots_t) : Prop :=
  map (exterior2val g) roots = map rp_val rootpairs.

Definition frames_compatible (g: LGraph) (frames: list frame) (roots: roots_t) : Prop :=
  map (exterior2val g) roots = map rp_val (frames2rootpairs frames).

Definition exterior_proj_outlier (r : exterior_t): option GC_Pointer :=
  match r with
  | ExteriorOutlier p => Some p
  | _ => None
  end.

Lemma exterior_proj_outlier_spec: forall r p, exterior_proj_outlier r = Some p <-> r = ExteriorOutlier p.
Proof. intros. destruct r; simpl; split; intro S; inversion S; subst; reflexivity. Qed.

Definition roots_outlier_compatible (roots: roots_t) (outlier: outlier_t): Prop :=
  incl (filter_proj exterior_proj_outlier roots) outlier.

Definition exterior_proj_vertex (r : exterior_t): option VType :=
  match r with
  | ExteriorVertex v => Some v
  | _ => None
  end.

Lemma exterior_proj_vertex_spec: forall r p, exterior_proj_vertex r = Some p <-> r = ExteriorVertex p.
Proof. intros. destruct r; simpl; split; intro S; inversion S; subst; reflexivity. Qed.

Definition roots_graph_compatible (roots: roots_t) (g: LGraph): Prop :=
  Forall (graph_has_v g) (filter_proj exterior_proj_vertex roots).

Definition roots_compatible (g: LGraph) (outlier: outlier_t) (roots: roots_t): Prop :=
  roots_outlier_compatible roots outlier /\ roots_graph_compatible roots g.

Definition exterior_compatible (g: LGraph) (outlier: outlier_t) (extr: exterior_t) : Prop :=
  match extr with
  | ExteriorOutlier p => In p outlier
  | ExteriorVertex v => graph_has_v g v
  | _ => True
  end.

(* A weaker version which does not require outlier *)
Definition exterior_compatible' (g: LGraph) (extr: exterior_t) : Prop :=
  match extr with
  | ExteriorVertex v => graph_has_v g v
  | _ => True
  end.

Lemma roots_iff_exterior_compatible: forall g outlier roots,
    roots_compatible g outlier roots <-> Forall (exterior_compatible g outlier) roots.
Proof.
  intros g outlier. induction roots.
  - split; intros; [constructor| split; [repeat intro; contradiction |constructor]].
  - rewrite Forall_cons_iff, <- IHroots. clear IHroots. split; intros; destruct H.
    + hnf in H, H0. rewrite filter_proj_cons in H. rewrite filter_proj_cons in H0.
      destruct a; simpl in *.
      * do 2 (split; auto).
      * split. 1: apply H; now left. split; auto. hnf. intros. apply H. right; assumption.
      * rewrite Forall_cons_iff in H0. destruct H0. do 2 (split; auto).
    + hnf. unfold roots_outlier_compatible, roots_graph_compatible.
      rewrite !filter_proj_cons. destruct a; simpl in *.
      * destruct H0; split; assumption.
      * rewrite incl_cons_iff. destruct H0. do 2 (split; auto).
      * rewrite Forall_cons_iff. destruct H0. do 2 (split; auto).
Qed.

Definition raw_proj_outlier (r : raw_field) : option GC_Pointer :=
  match r with
  | RawOutlier p => Some p
  | _ => None
  end.

Lemma raw_proj_outlier_spec: forall r p, raw_proj_outlier r = Some p <-> r = RawOutlier p.
Proof. intros. destruct r; simpl; split; intro S; inversion S; subst; reflexivity. Qed.

Definition outlier_compatible (g: LGraph) (outlier: outlier_t): Prop :=
  forall v,
    graph_has_v g v ->
    incl (filter_proj raw_proj_outlier (vlabel g v).(raw_fields)) outlier.

Definition copy_compatible (g: LGraph): Prop :=
  forall v, graph_has_v g v -> (vlabel g v).(raw_mark) = true ->
            graph_has_v g (vlabel g v).(copied_vertex) /\
            vgeneration v <> vgeneration (vlabel g v).(copied_vertex).

Definition super_compatible (g: LGraph) (h: heap) (rootpairs: list rootpair) (r: roots_t) (out: outlier_t) : Prop :=
  graph_heap_compatible g h /\
  rootpairs_compatible g rootpairs r /\
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
  intros. pose proof g_gen_not_nil g. destruct (g_gen g).
  - contradiction.
  - destruct n; simpl; discriminate.
Qed.

Lemma reset_nth_gen_info_diff: forall gl i j a,
    i <> j -> nth i (reset_nth_gen_info j gl) a = nth i gl a.
Proof.
  intros ? ? ?. revert gl i. induction j; intros; simpl; destruct gl; try reflexivity.
  - destruct i. 1: contradiction. simpl. reflexivity.
  - destruct i. 1: reflexivity. simpl. apply IHj. lia.
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
  1: lia. rewrite IHi; [reflexivity | lia].
Qed.

Lemma sublist_pos_cons: forall {A: Type} (lo hi: Z) (al: list A) v,
    (0 < lo)%Z -> sublist lo hi (v :: al) = sublist (lo - 1) (hi - 1) al.
Proof.
  intros. unfold_sublist_old. f_equal. 1: f_equal; lia.
  replace (Z.to_nat lo) with (S (Z.to_nat (lo - 1))) by lia.
  simpl. reflexivity.
Qed.

Lemma upd_Znth_pos_cons: forall {A: Type} (i: Z) (l: list A) v x,
    (0 < i <= Zlength l)%Z -> upd_Znth i (v :: l) x = v :: upd_Znth (i - 1) l x.
Proof.
  intros. unfold_upd_Znth_old.
  rewrite (sublist_split 0 1 i); [| |rewrite Zlength_cons]; [| lia..].
  unfold sublist at 1. simpl. rewrite !sublist_pos_cons by lia. do 4 f_equal.
  1: lia. rewrite Zlength_cons; lia.
Qed.

Definition reset_nth_graph_info (n: nat) (g: graph_info) : graph_info :=
  Build_graph_info (reset_nth_gen_info n g.(g_gen)) (reset_nth_gen_info_not_nil n g).

Lemma reset_used_leq_available: forall sp, (0 <= 0 <= total_space sp)%Z.
Proof.
  intros. pose proof used_leq_available sp. pose proof available_leq_total sp. lia.
Qed.

Definition reset_space (sp: space) : space :=
  Build_space (space_start sp) 0 (total_space sp) (total_space sp) (space_sh sp)
    (reset_used_leq_available sp) (Z.le_refl (total_space sp)) (space_upper_bound sp).

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
  induction n; intros; destruct s; simpl in *; try lia.
  - exists s0. split; constructor; reflexivity.
  - assert (n < length s0) by lia. destruct (IHn _ H0) as [ll [? ?]].
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
  intros ? ?. revert s. induction i; intros; destruct s; simpl in H; try lia.
  - simpl.
    rewrite upd_Znth0_old, Znth_0_cons, sublist_1_cons, sublist_same;
      try reflexivity; rewrite Zlength_cons. lia.
    pose proof (Zlength_nonneg s0). lia.
  - replace (Z.of_nat (S i)) with (Z.of_nat i + 1)%Z by (zify; lia).
    rewrite Znth_pos_cons by lia.
    replace (Z.of_nat i + 1 - 1)%Z with (Z.of_nat i) by lia. simpl.
    rewrite upd_Znth_pos_cons.
    + replace (Z.of_nat i + 1 - 1)%Z with (Z.of_nat i) by lia.
      rewrite <- IHi; [reflexivity | lia].
    + rewrite Zlength_correct. lia.
Qed.

Lemma reset_nth_space_overflow: forall s i, length s <= i -> reset_nth_space i s = s.
Proof.
  intros ? ?. revert s.
  induction i; intros; destruct s; simpl in *; try lia; try reflexivity.
  rewrite IHi; [reflexivity | lia].
Qed.

Lemma reset_nth_space_diff: forall gl i j a,
    i <> j -> nth i (reset_nth_space j gl) a = nth i gl a.
Proof.
  intros ? ? ?. revert gl i. induction j; intros; simpl; destruct gl; try reflexivity.
  - destruct i. 1: contradiction. simpl. reflexivity.
  - destruct i. 1: reflexivity. simpl. apply IHj. lia.
Qed.

Lemma reset_nth_space_same: forall gl i a,
    i < length gl -> nth i (reset_nth_space i gl) a = reset_space (nth i gl a).
Proof.
  intros. revert gl H. induction i; intros; destruct gl; simpl in *; try lia.
  - reflexivity.
  - apply IHi. lia.
Qed.

Definition reset_nth_heap (n: nat) (h: heap) : heap :=
  Build_heap (reset_nth_space n (spaces h)) (reset_nth_heap_Zlength n h).

Definition reset_nth_heap_thread_info (n: nat) (ti: thread_info) : thread_info :=
  Build_thread_info (ti_heap_p ti) (reset_nth_heap n (ti_heap ti))
                    (ti_args ti) (arg_size ti) (ti_frames ti) (ti_nalloc ti).


Lemma reset_heap_overflow: forall n h,
    length (spaces h) <= n -> reset_nth_heap n h = h.
Proof.
  intros. unfold reset_nth_heap.  destruct h. simpl in *.
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
  intros. unfold make_header. destruct (raw_mark (vlabel g v)). tauto.
  split; intros. 2: inversion H. exfalso.
  destruct (raw_tag_range (vlabel g v)) as [? _].
  assert (0 <= Z.shiftl (raw_color (vlabel g v)) 8). {
    rewrite Z.shiftl_nonneg. apply (proj1 (raw_color_range (vlabel g v))).
  } assert (Z.shiftl (Zlength (raw_fields (vlabel g v))) 10 <= 0) by lia.
  clear -H2. assert (0 <= Z.shiftl (Zlength (raw_fields (vlabel g v))) 10) by
      (rewrite Z.shiftl_nonneg; apply Zlength_nonneg).
  assert (Z.shiftl (Zlength (raw_fields (vlabel g v))) 10 = 0) by lia. clear -H0.
  rewrite Z.shiftl_eq_0_iff in H0 by lia.
  pose proof (proj1 (raw_fields_range (vlabel g v))). lia.
Qed.

Lemma make_header_range: forall g v, 0 <= make_header g v < two_p (WORD_SIZE * 8).
Proof.
  intros. unfold make_header. destruct (raw_mark (vlabel g v)).
  - pose proof (two_p_gt_ZERO (WORD_SIZE * 8)). unfold WORD_SIZE in *; lia.
  - pose proof (raw_tag_range (vlabel g v)). pose proof (raw_color_range (vlabel g v)).
    pose proof (raw_fields_range (vlabel g v)). remember (raw_tag (vlabel g v)) as z1.
    clear Heqz1. remember (raw_color (vlabel g v)) as z2. clear Heqz2.
    remember (Zlength (raw_fields (vlabel g v))) as z3. clear Heqz3.
    assert (0 <= 8) by lia. apply (Zbits.Zshiftl_mul_two_p z2) in H2. rewrite H2.
    clear H2. assert (0 <= 10) by lia. apply (Zbits.Zshiftl_mul_two_p z3) in H2.
    rewrite H2. clear H2. assert (two_p 10 > 0) by (apply two_p_gt_ZERO; lia).
    assert (two_p 8 > 0) by (apply two_p_gt_ZERO; lia). split.
    + assert (0 <= z2 * two_p 8) by (apply Z.mul_nonneg_nonneg; lia).
      assert (0 <= z3 * two_p 10) by (apply Z.mul_nonneg_nonneg; lia). lia.
    + destruct H as [_ ?]. destruct H0 as [_ ?]. destruct H1 as [_ ?].
      change 256 with (two_p 8) in H. change 4 with (two_p 2) in H0.
      assert (z1 <= two_p 8 - 1) by lia. clear H.
      assert (z2 <= two_p 2 - 1) by lia. clear H0.
      assert (z3 <= two_p (WORD_SIZE * 8 - 10) - 1) by lia. clear H1.
      apply Z.mul_le_mono_nonneg_r with (p := two_p 8) in H. 2: lia.
      apply Z.mul_le_mono_nonneg_r with (p := two_p 10) in H0. 2: lia.
      rewrite Z.mul_sub_distr_r in H, H0. rewrite Z.mul_1_l in H, H0.
      assert (0 <= WORD_SIZE * 8 - 10) by (unfold WORD_SIZE; lia).
      rewrite <- two_p_is_exp in H, H0 by lia. simpl Z.add in H, H0. clear H1.
      Opaque two_p. simpl. Transparent two_p. lia.
Qed.

Lemma make_header_int_rep_mark_iff: forall g v,
    (if Archi.ptr64 then Int64.repr (make_header g v) = Int64.repr 0
     else Int.repr (make_header g v) = Int.repr 0) <->
    raw_mark (vlabel g v) = true.
Proof.
  intros. rewrite <- make_header_mark_iff. split; intros; [|rewrite H; reflexivity].
  cbv delta [Archi.ptr64] in H. simpl in H. Transparent Int.repr Int64.repr.
  inversion H. Opaque Int64.repr Int.repr. clear H. rewrite H1.
  match goal with
  | H : Int64.Z_mod_modulus _ = _ |- _ => rewrite Int64.Z_mod_modulus_eq in H
  | H : Int.Z_mod_modulus _ = _ |- _ => rewrite Int.Z_mod_modulus_eq in H
  end.
  rewrite Z.mod_small in H1; auto. apply make_header_range.
Qed.

Lemma make_header_Wosize: forall g v,
    raw_mark (vlabel g v) = false ->
    if Archi.ptr64 then
      Int64.shru (Int64.repr (make_header g v)) (Int64.repr 10) =
      Int64.repr (Zlength (raw_fields (vlabel g v)))
    else
      Int.shru (Int.repr (make_header g v)) (Int.repr 10) =
      Int.repr (Zlength (raw_fields (vlabel g v))).
Proof.
  intros. cbv delta [Archi.ptr64]. simpl.
  match goal with
  | |- Int64.shru _ _ = Int64.repr _ =>
    rewrite Int64.shru_div_two_p, !Int64.unsigned_repr
  | |- Int.shru _ _ = Int.repr _ => rewrite Int.shru_div_two_p, !Int.unsigned_repr
  end.
  - f_equal. unfold make_header.
    remember (vlabel g v). clear Heqr.
    rewrite H, !Zbits.Zshiftl_mul_two_p by lia. rewrite Z.div_add. 2: compute; lia.
    pose proof (raw_tag_range r). pose proof (raw_color_range r).
    cut ((raw_tag r + raw_color r * two_p 8) / two_p 10 = 0). 1: intros; lia.
    apply Z.div_small. change 256 with (two_p 8) in H0. change 4 with (two_p 2) in H1.
    assert (0 <= raw_tag r <= two_p 8 - 1) by lia. clear H0. destruct H2.
    assert (0 <= raw_color r <= two_p 2 - 1) by lia. clear H1. destruct H3.
    assert (two_p 8 > 0) by (apply two_p_gt_ZERO; lia). split.
    + assert (0 <= raw_color r * two_p 8) by (apply Z.mul_nonneg_nonneg; lia). lia.
    + apply Z.mul_le_mono_nonneg_r with (p := two_p 8) in H3. 2: lia.
      rewrite Z.mul_sub_distr_r, <- two_p_is_exp in H3 by lia. simpl Z.add in H3. lia.
  - rep_lia.
  - pose proof (make_header_range g v). unfold WORD_SIZE in *.
    match goal with
    | |- context [Int64.max_unsigned] =>
      unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize
    | |- context [Int.max_unsigned] =>
      unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize
    end. simpl Z.mul in H0. rewrite two_power_nat_two_p. simpl Z.of_nat. lia.
Qed.

Inductive field_t: Type :=
| FieldUnboxed: Z -> field_t
| FieldOutlier: GC_Pointer -> field_t
| FieldEdge: EType -> field_t.

#[export] Instance field_t_inhabitant: Inhabitant field_t := FieldUnboxed Z.zero.

Definition field2val (tag: Z) (g: LGraph) (fd: field_t) : val :=
  match fd with
  | FieldUnboxed z => if zlt tag NO_SCAN_TAG then odd_Z2val z else Vlong (Int64.repr z)
  | FieldOutlier p => GC_Pointer2val p
  | FieldEdge e => vertex_address g (dst g e)
  end.

Fixpoint make_fields' (l_raw: list raw_field) (v: VType) (n: nat): list field_t :=
  match l_raw with
  | nil => nil
  | RawUnboxed z :: l => FieldUnboxed z :: make_fields' l v (n + 1)
  | RawOutlier ptr :: l => FieldOutlier ptr :: make_fields' l v (n + 1)
  | RawInternal :: l => FieldEdge (v, n) :: make_fields' l v (n + 1)
  end.

Lemma make_fields'_eq_length: forall l v n, length (make_fields' l v n) = length l.
Proof.
  intros. revert n. induction l; intros; simpl. 1: reflexivity.
  destruct a; simpl; rewrite IHl; reflexivity.
Qed.

Lemma make_fields'_eq_Zlength: forall l v n, Zlength (make_fields' l v n) = Zlength l.
Proof.
  intros. rewrite !Zlength_correct. rewrite make_fields'_eq_length. reflexivity.
Qed.

Lemma make_fields'_edge_depends_on_index:
  forall n l_raw i v e,
    0 <= Z.of_nat n < Zlength l_raw ->
    nth n (make_fields' l_raw v i) field_t_inhabitant = FieldEdge e ->
    e = (v, n+i)%nat.
Proof.
  induction n as [|n' IHn'].
  - intros. destruct l_raw; try inversion H0.
    destruct r; simpl in H0; inversion H0; reflexivity.
  - intro. destruct l_raw; try inversion 2.
    replace (S n' + i)%nat with (n' + S i)%nat by lia.
    specialize (IHn' l_raw (S i) v e).
    assert (0 <= Z.of_nat n' < Zlength l_raw) by
          (rewrite Zlength_cons, Nat2Z.inj_succ in H; lia).
      assert (nth n' (make_fields' l_raw v (S i)) field_t_inhabitant = FieldEdge e) by
        (destruct r; simpl in H2; replace (i + 1)%nat with (S i) in H2 by lia; assumption).
      destruct r; simpl; apply IHn'; assumption.
Qed.

Definition make_fields (g: LGraph) (v: VType): list field_t :=
  make_fields' (vlabel g v).(raw_fields) v O.

Definition field_proj_edge (f: field_t) : option EType :=
  match f with
  | FieldEdge e => Some e
  | _ => None
  end.

Lemma field_proj_edge_spec: forall r p, field_proj_edge r = Some p <-> r = FieldEdge p.
Proof. intros. destruct r; simpl; split; intro S; inversion S; subst; reflexivity. Qed.

Definition get_edges (g: LGraph) (v: VType): list EType :=
  filter_proj field_proj_edge (make_fields g v).

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

Lemma remove_ve_elabel_unchanged: forall g gen e,
    elabel (remove_nth_gen_ve g gen) e = elabel g e.
Proof.
  intros. unfold remove_nth_gen_ve.
  remember (map (fun idx : nat => (gen, idx))
                (nat_inc_list (number_of_vertices (nth_gen g gen)))). clear Heql.
  revert g e. induction l; intros; simpl. 1: reflexivity. rewrite IHl. reflexivity.
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
  let original_fields_val := map (field2val (raw_tag vb) g) (make_fields g v) in
  if vb.(raw_mark)
  then vertex_address g vb.(copied_vertex) :: tl original_fields_val
  else original_fields_val.

Lemma fields_eq_length: forall g v,
    Zlength (make_fields_vals g v) = Zlength (raw_fields (vlabel g v)).
Proof.
  intros. rewrite !Zlength_correct. f_equal. unfold make_fields_vals, make_fields.
  destruct (raw_mark (vlabel g v)).
  - destruct (raw_fields_head_cons (vlabel g v)) as [r [l [? ?]]].
    rewrite H; simpl; destruct r; simpl;
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
    Znth n (make_fields g v) = FieldEdge e -> e = (v, Z.to_nat n).
Proof.
  intros. rewrite <- nth_Znth in H0. 2: rewrite make_fields_eq_length; assumption.
  apply make_fields'_edge_depends_on_index in H0.
  - rewrite Nat.add_0_r in H0; assumption.
  - rewrite Z2Nat.id; [assumption | lia].
Qed.

Lemma Znth_skip_hd_same: forall A (d: Inhabitant A) (l: list A) a n,
    n > 0 ->
    Zlength l > 0 ->
    Znth n (a :: tl l) = Znth n l.
Proof.
  intros. destruct l.
  - rewrite Zlength_nil in H0; inversion H0.
  - repeat rewrite Znth_pos_cons by lia. reflexivity.
Qed.

Lemma make_fields'_n_doesnt_matter: forall i l v n m gcptr,
    nth i (make_fields' l v n) field_t_inhabitant = FieldOutlier gcptr ->
    nth i (make_fields' l v m) field_t_inhabitant = FieldOutlier gcptr.
Proof.
  intros.
  unfold make_fields' in *.
  generalize dependent i.
  generalize dependent n.
  generalize dependent m.
  induction l.
  + intros; assumption.
  + induction i.
    - destruct a; simpl; intros; try assumption; try inversion H.
    - destruct a; simpl; intro; apply IHl with (m:=(m+1)%nat) in H; assumption.
Qed.

Lemma make_fields'_item_was_in_list: forall l v n gcptr,
    0 <= n < Zlength l ->
    Znth n (make_fields' l v 0) = FieldOutlier gcptr ->
    Znth n l = RawOutlier gcptr.
Proof.
  intros.
  rewrite <- nth_Znth; rewrite <- nth_Znth in H0; [| rewrite Zlength_correct in *..];
    try rewrite make_fields'_eq_length; [|assumption..].
  generalize dependent n.
  induction l.
  - intros. rewrite nth_Znth in H0; try assumption.
    unfold make_fields' in H0; rewrite Znth_nil in H0; inversion H0.
  - intro n. induction (Z.to_nat n) eqn:?.
    + intros. destruct a; simpl in *; try inversion H0; try reflexivity.
    + intros. simpl in *. clear IHn0.
      replace n0 with (Z.to_nat (Z.of_nat n0)) by apply Nat2Z.id.
      assert (0 <= Z.of_nat n0 < Zlength l). {
        split; try lia.
        destruct H; rewrite Zlength_cons in H1.
        apply Zsucc_lt_reg; rewrite <- Nat2Z.inj_succ.
        rewrite <- Heqn0; rewrite Z2Nat.id; assumption.
      }
      destruct a; simpl in H0; apply IHl;
        try assumption; apply make_fields'_n_doesnt_matter with (n:=1%nat);
        rewrite Nat2Z.id; assumption.
Qed.

Lemma make_fields_edge_unique: forall g e v1 v2 n m,
    0 <= n < Zlength (make_fields g v1) ->
    0 <= m < Zlength (make_fields g v2) ->
    Znth n (make_fields g v1) = FieldEdge e ->
    Znth m (make_fields g v2) = FieldEdge e ->
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
  rewrite Nat.add_cancel_r, Z2Nat.inj_iff in H9 by lia.
  split; [assumption | reflexivity].
Qed.

Lemma in_gcptr_outlier: forall g gcptr outlier n v,
    graph_has_v g v ->
    outlier_compatible g outlier ->
    0 <= n < Zlength (raw_fields (vlabel g v)) ->
    Znth n (make_fields g v) = FieldOutlier gcptr ->
    In gcptr outlier.
Proof.
  intros.
  apply H0 in H; apply H; clear H; clear H0.
  unfold make_fields in H2.
  apply make_fields'_item_was_in_list in H2; try assumption.
  rewrite <- (filter_proj_In_iff raw_proj_outlier_spec).
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
  cut (forall fl, map (field2val (raw_tag (vlabel g2 v)) g1) fl =
                  map (field2val (raw_tag (vlabel g2 v)) g2) fl).
  - intros. rewrite H2. rewrite (vertex_address_the_same g1 g2) by assumption.
    reflexivity.
  - apply map_ext. intros. unfold field2val. destruct a; [reflexivity..|].
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

Inductive forward_t: Type :=
| ForwardUnboxed: Z -> forward_t
| ForwardOutlier: GC_Pointer -> forward_t
| ForwardVertex: VType -> forward_t
| ForwardEdge: EType -> forward_t.

Definition exterior2forward (r: exterior_t): forward_t :=
  match r with
  | ExteriorUnboxed z => ForwardUnboxed z
  | ExteriorOutlier p => ForwardOutlier p
  | ExteriorVertex v => ForwardVertex v
  end.

Definition field2forward (f: field_t): forward_t :=
  match f with
  | FieldUnboxed z => ForwardUnboxed z
  | FieldOutlier p => ForwardOutlier p
  | FieldEdge e => ForwardEdge e
  end.

Inductive interior_t : Type := InteriorVertexPos (vertex: VType) (field_pos: Z).

Definition interior2forward (intr: interior_t) (g: LGraph) :=
  match intr with
  | InteriorVertexPos v n => field2forward (Znth n (make_fields g v))
  end.

Inductive forward_p_type: Type :=
  | FwdPntExtr (extr: exterior_t) : forward_p_type
  | FwdPntIntr (intr: interior_t) : forward_p_type.

Definition forward_p2forward_t (p: forward_p_type) (g: LGraph): forward_t :=
  match p with
  | FwdPntExtr extr => exterior2forward extr
  | FwdPntIntr intr => interior2forward intr g
  end.

Definition vertex_pos_pairs (g: LGraph) (v: VType) : list interior_t :=
  map (fun x => InteriorVertexPos v (Z.of_nat x))
    (nat_inc_list (length (raw_fields (vlabel g v)))).

Definition has_space (sp: space) (s: Z): Prop :=
  0 <= s <= available_space sp - used_space sp.

Lemma has_space_dec: forall sp s, {has_space sp s} + {~ has_space sp s}.
Proof.
  intros. unfold has_space. destruct (Z_le_dec 0 s).
  - destruct (Z_le_dec s (available_space sp - used_space sp)).
    + left. split; assumption.
    + right. lia.
  - right. lia.
Qed.

Lemma cut_used_leq_available: forall (sp : space) (s : Z),
    has_space sp s -> 0 <= used_space sp + s <= available_space sp.
Proof. intros. pose proof (used_leq_available sp). red in H. lia. Qed.

Definition cut_space (sp: space) (s: Z): space :=
  match has_space_dec sp s with
  | left H => Build_space (space_start sp) (used_space sp + s) (available_space sp)
               (total_space sp) (space_sh sp) (cut_used_leq_available sp s H)
               (available_leq_total sp) (space_upper_bound sp)
  | right _ => sp
  end.

Ltac unfold_cut_space := unfold cut_space; destruct (has_space_dec _ _); [| contradiction].

Lemma cut_heap_size: forall (h : heap) (i s : Z) ,
    0 <= i < Zlength (spaces h) ->
    Zlength (upd_Znth i (spaces h) (cut_space (Znth i (spaces h)) s)) = MAX_SPACES.
Proof. intros. rewrite upd_Znth_Zlength; [apply spaces_size | assumption]. Qed.

Lemma spaces_index_dec: forall i h,
    { 0 <= i < Zlength (spaces h) } + { ~ 0 <= i < Zlength (spaces h) }.
Proof.
  intros. destruct (Z_le_dec 0 i).
  - destruct (Z_lt_dec i (Zlength (spaces h))).
    + left; split; assumption.
    + right. lia.
  - right. lia.
Qed.

Definition cut_heap (h: heap) (i s: Z): heap :=
  match spaces_index_dec i h with
  | left H => Build_heap (upd_Znth i (spaces h) (cut_space (Znth i (spaces h)) s))
               (cut_heap_size h i s H)
  | right _ => h
  end.

Ltac unfold_cut_heap := unfold cut_heap; destruct (spaces_index_dec _ _); [|contradiction].

Inductive forward_relation (from to: nat):
  nat -> forward_t -> LGraph -> LGraph -> Prop :=
| fr_z: forall depth z g, forward_relation from to depth (ForwardUnboxed z) g g
| fr_p: forall depth p g, forward_relation from to depth (ForwardOutlier p) g g
| fr_v_not_in: forall depth v g,
    vgeneration v <> from -> forward_relation from to depth (ForwardVertex v) g g
| fr_v_in_forwarded: forall depth v g,
    vgeneration v = from -> (vlabel g v).(raw_mark) = true ->
    forward_relation from to depth (ForwardVertex v) g g
| fr_v_in_not_forwarded_O: forall v g,
    vgeneration v = from -> (vlabel g v).(raw_mark) = false ->
    forward_relation from to O (ForwardVertex v) g (lgraph_copy_v g v to)
| fr_v_in_not_forwarded_Sn: forall depth v g g',
    vgeneration v = from -> (vlabel g v).(raw_mark) = false ->
    (vlabel g v).(raw_tag) < NO_SCAN_TAG ->
    let new_g := lgraph_copy_v g v to in
    forward_loop from to depth (vertex_pos_pairs new_g (new_copied_v g to)) new_g g' ->
    forward_relation from to (S depth) (ForwardVertex v) g g'
| fr_v_in_not_forwarded_noscan: forall depth v g,
    vgeneration v = from -> (vlabel g v).(raw_mark) = false ->
    (vlabel g v).(raw_tag) >= NO_SCAN_TAG ->
    forward_relation from to (S depth) (ForwardVertex v) g (lgraph_copy_v g v to)
| fr_e_not_to: forall depth e (g: LGraph),
    vgeneration (dst g e) <> from -> forward_relation from to depth (ForwardEdge e) g g
| fr_e_to_forwarded: forall depth e (g: LGraph),
    vgeneration (dst g e) = from -> (vlabel g (dst g e)).(raw_mark) = true ->
    let new_g := labeledgraph_gen_dst g e (vlabel g (dst g e)).(copied_vertex) in
    forward_relation from to depth (ForwardEdge e) g new_g
| fr_e_to_not_forwarded_O: forall e (g: LGraph),
    vgeneration (dst g e) = from -> (vlabel g (dst g e)).(raw_mark) = false ->
    let new_g := labeledgraph_gen_dst (lgraph_copy_v g (dst g e) to) e
                                      (new_copied_v g to) in
    forward_relation from to O (ForwardEdge e) g new_g
| fr_e_to_not_forwarded_Sn: forall depth e (g g': LGraph),
    vgeneration (dst g e) = from -> (vlabel g (dst g e)).(raw_mark) = false ->
    (vlabel g (dst g e)).(raw_tag) < NO_SCAN_TAG ->
    let new_g := labeledgraph_gen_dst (lgraph_copy_v g (dst g e) to) e
                                      (new_copied_v g to) in
    forward_loop from to depth (vertex_pos_pairs new_g (new_copied_v g to)) new_g g' ->
    forward_relation from to (S depth) (ForwardEdge e) g g'
| fr_e_to_not_forwarded_noscan: forall depth e (g: LGraph),
    vgeneration (dst g e) = from -> (vlabel g (dst g e)).(raw_mark) = false ->
    (vlabel g (dst g e)).(raw_tag) >= NO_SCAN_TAG ->
    let new_g := labeledgraph_gen_dst (lgraph_copy_v g (dst g e) to) e
                                      (new_copied_v g to) in
    forward_relation from to (S depth) (ForwardEdge e) g new_g
with
forward_loop (from to: nat): nat -> list interior_t -> LGraph -> LGraph -> Prop :=
| fl_nil: forall depth g, forward_loop from to depth nil g g
| fl_cons: forall depth g1 g2 g3 f fl,
    forward_relation from to depth (interior2forward f g1) g1 g2 ->
    forward_loop from to depth fl g2 g3 -> forward_loop from to depth (f :: fl) g1 g3.

Definition forward_gh_loop (f: nat -> nat -> nat -> forward_t -> LGraph -> heap -> LGraph * heap)
  (from to dep: nat) (l: list interior_t) (gh: LGraph * heap) :=
  fold_left (fun (gnh: LGraph * heap) fp =>
               let (gg, hh) := gnh in
               f from to dep (interior2forward fp gg) gg hh) l gh.

Fixpoint forward_graph_and_heap (from to depth: nat) (f: forward_t)
  (g: LGraph) (h: heap) : (LGraph * heap) :=
  match f with
  | ForwardUnboxed _
  | ForwardOutlier _  => (g, h)
  | ForwardVertex v =>
      if Nat.eq_dec (vgeneration v) from
      then if (vlabel g v).(raw_mark)
           then (g, h)
           else let new_g := lgraph_copy_v g v to in
                let new_h := cut_heap h (Z.of_nat to) (vertex_size g v) in
                match depth with
                | O => (new_g, new_h)
                | S n => if Z_lt_ge_dec (vlabel g v).(raw_tag) NO_SCAN_TAG
                        then  forward_gh_loop forward_graph_and_heap from to n
                               (vertex_pos_pairs new_g (new_copied_v g to)) (new_g, new_h)
                        else (new_g, new_h)
                end
      else (g, h)
  | ForwardEdge e =>
      if Nat.eq_dec (vgeneration (dst g e)) from
      then if (vlabel g (dst g e)).(raw_mark)
           then (labeledgraph_gen_dst g e (vlabel g (dst g e)).(copied_vertex), h)
           else let new_g := labeledgraph_gen_dst (lgraph_copy_v g (dst g e) to) e
                               (new_copied_v g to) in
                let new_h := cut_heap h (Z.of_nat to) (vertex_size g (dst g e)) in
                match depth with
                | O => (new_g, new_h)
                | S n => if Z_lt_ge_dec (vlabel g (dst g e)).(raw_tag) NO_SCAN_TAG
                        then forward_gh_loop forward_graph_and_heap from to n
                               (vertex_pos_pairs new_g (new_copied_v g to)) (new_g, new_h)
                        else (new_g, new_h)
                end
      else (g, h)
  end.

Lemma fwd_graph_heap_unfold: forall from to depth f g h,
    forward_graph_and_heap from to depth f g h =
      match f with
      | ForwardUnboxed _
      | ForwardOutlier _  => (g, h)
      | ForwardVertex v =>
          if Nat.eq_dec (vgeneration v) from
          then if (vlabel g v).(raw_mark)
               then (g, h)
               else let new_g := lgraph_copy_v g v to in
                    let new_h := cut_heap h (Z.of_nat to) (vertex_size g v) in
                    match depth with
                    | O => (new_g, new_h)
                    | S n => if Z_lt_ge_dec (vlabel g v).(raw_tag) NO_SCAN_TAG
                            then  forward_gh_loop forward_graph_and_heap from to n
                                    (vertex_pos_pairs new_g (new_copied_v g to))
                                    (new_g, new_h)
                            else (new_g, new_h)
                    end
          else (g, h)
      | ForwardEdge e =>
          if Nat.eq_dec (vgeneration (dst g e)) from
          then if (vlabel g (dst g e)).(raw_mark)
               then (labeledgraph_gen_dst g e (vlabel g (dst g e)).(copied_vertex), h)
               else let new_g := labeledgraph_gen_dst (lgraph_copy_v g (dst g e) to) e
                                   (new_copied_v g to) in
                    let new_h := cut_heap h (Z.of_nat to) (vertex_size g (dst g e)) in
                    match depth with
                    | O => (new_g, new_h)
                    | S n => if Z_lt_ge_dec (vlabel g (dst g e)).(raw_tag) NO_SCAN_TAG
                            then forward_gh_loop forward_graph_and_heap from to n
                                   (vertex_pos_pairs new_g (new_copied_v g to))
                                   (new_g, new_h)
                            else (new_g, new_h)
                    end
          else (g, h)
      end.
Proof. intros from to. induction depth; simpl; reflexivity. Qed.

Ltac raw_mark_contra :=
  lazymatch goal with
  | H1: ?A = true, H2: ?A = false |- _ => rewrite H1 in H2; discriminate
  end.

Lemma forward_relation_unique: forall from to depth p g g1 g2,
    forward_relation from to depth p g g1 ->
    forward_relation from to depth p g g2 -> g1 = g2.
Proof.
  intros from to depth. induction depth; intros.
  - inversion H; subst; inversion H0; subst; try reflexivity;
      try contradiction; raw_mark_contra.
  - assert (forall l lg lg1 lg2,
               forward_loop from to depth l lg lg1 ->
               forward_loop from to depth l lg lg2 -> lg1 = lg2). {
      clear -IHdepth. induction l; intros.
      - inversion H; subst. inversion H0; subst. reflexivity.
      - inversion H; subst. inversion H0; subst.
        assert (g0 = g2) by (eapply IHdepth; eassumption). subst g0.
        eapply IHl; eassumption. }
    clear IHdepth. inversion H; subst; inversion H0; subst;
      try reflexivity; try contradiction; try raw_mark_contra.
    + assert (new_g = new_g0) by (subst; reflexivity). rewrite <- H2 in H10.
        eapply H1; eassumption.
    + assert (new_g = new_g0) by (subst; reflexivity). rewrite <- H2 in H10.
        eapply H1; eassumption.
Qed.

Lemma fr_forward_graph_and_heap: forall from to depth p g h,
    forward_relation from to depth p g (fst (forward_graph_and_heap from to depth p g h)).
Proof.
  intros from to depth. induction depth; intros.
  - destruct p; simpl; [constructor..| |].
    + destruct (Nat.eq_dec _ _); simpl; [|econstructor; eassumption].
      destruct (raw_mark _) eqn:? ; simpl; econstructor; eassumption.
    + destruct (Nat.eq_dec _ _); simpl; [|econstructor; eassumption].
      destruct (raw_mark _) eqn:? ; simpl; econstructor; eassumption.
  - assert (forall l gh, forward_loop from to depth l (fst gh)
                      (fst (forward_gh_loop forward_graph_and_heap from to depth l gh))). {
      induction l; intros; simpl. constructor. destruct gh as [gg hh]. simpl fst.
      econstructor; [apply IHdepth | apply IHl]. } clear IHdepth.
    destruct p; simpl; [constructor..| |].
    + destruct (Nat.eq_dec _ _); simpl; [|econstructor; eassumption];
      destruct (raw_mark _) eqn:? ; simpl; [econstructor; eassumption |];
      destruct (Z_lt_ge_dec _ _); [|econstructor; eassumption].
      apply fr_v_in_not_forwarded_Sn; [assumption..|].
      remember (lgraph_copy_v _ _ _) as gg. remember (cut_heap _ _ _) as hh.
      apply (H _ (gg, hh)).
    + destruct (Nat.eq_dec _ _); simpl; [|econstructor; eassumption];
      destruct (raw_mark _) eqn:? ; simpl; [econstructor; eassumption |];
        destruct (Z_lt_ge_dec _ _); [|econstructor; eassumption].
      remember (labeledgraph_gen_dst _ _ _) as gg. remember (cut_heap _ _ _) as hh.
      apply fr_e_to_not_forwarded_Sn; [assumption..|]. rewrite <- Heqgg.
      apply (H _ (gg ,hh)).
Qed.

Lemma fl_fwd_gh_loop: forall from to depth l gh,
    forward_loop from to depth l (fst gh)
      (fst (forward_gh_loop forward_graph_and_heap from to depth l gh)).
Proof.
  intros from to depth. induction l; intros; simpl; [constructor|]. destruct gh as [gg hh].
  simpl fst. econstructor; [apply fr_forward_graph_and_heap | apply IHl].
Qed.

Definition interior_compatible (g: LGraph) (from: nat) (intr: interior_t) : Prop :=
  match intr with
  | InteriorVertexPos v n => graph_has_v g v /\ 0 <= n < Zlength (vlabel g v).(raw_fields) /\
                             (vlabel g v).(raw_mark) = false /\
                             (vlabel g v).(raw_tag) < NO_SCAN_TAG /\
                              vgeneration v <> from
  end.

Definition forward_p_compatible
  (p: forward_p_type) (outlier: outlier_t) (g: LGraph) (from: nat): Prop :=
  match p with
  | FwdPntExtr extr => exterior_compatible g outlier extr
  | FwdPntIntr intr => interior_compatible g from intr
  end.

(* A weaker version which does not require outlier *)
Definition forward_p_compatible' (p: forward_p_type) (g: LGraph) (from: nat): Prop :=
  match p with
  | FwdPntExtr extr => exterior_compatible' g extr
  | FwdPntIntr intr => interior_compatible g from intr
  end.

(*
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
    rewrite Z.max_l_iff in H2. lia.
  - assert (l = skipn (Z.to_nat (ind + 1)) c). {
      clear -H H0. rewrite Z2Nat.inj_add by lia. simpl Z.to_nat at 2.
      remember (Z.to_nat ind). clear ind Heqn H0.
      replace (n + 1)%nat with (S n) by lia. revert a l c H.
      induction n; intros; simpl in H; destruct c; [inversion H | | inversion H|].
      - simpl. inversion H; reflexivity.
      - apply IHn in H. rewrite H. simpl. destruct c; reflexivity. }
    assert (0 <= ind + 1) by lia. specialize (IHl _ H1 H2). simpl.
    assert (Znth ind c = a). {
      clear -H H0. apply Z2Nat.id in H0. remember (Z.to_nat ind). rewrite <- H0.
      clear ind Heqn H0. revert a l c H.
      induction n; intros; simpl in H; destruct c; [inversion H | | inversion H|].
      - simpl. inversion H. rewrite Znth_0_cons. reflexivity.
      - rewrite Nat2Z.inj_succ, Znth_pos_cons by lia. apply IHn in H.
        replace (Z.succ (Z.of_nat n) - 1) with (Z.of_nat n) by lia.
        assumption. }
    destruct (eqdec target a).
    + simpl. rewrite IHl. clear IHl. split; intros; destruct H4; [|intuition auto with *| ].
      * subst j. split; [split|]; [lia | | rewrite <- e in H3; assumption].
        pose proof (Zlength_skipn ind c). rewrite <- H in H4.
        rewrite Zlength_cons in H4. pose proof (Zlength_nonneg l).
        destruct (Z.max_spec 0 (Zlength c - Z.max 0 ind)). 2: exfalso; lia.
        destruct H6 as [? _]. rewrite Z.max_r in H6; lia.
      * assert (ind = j \/ ind + 1 <= j < Zlength c) by lia.
        destruct H6; [left | right; split]; assumption.
    + rewrite IHl; split; intros; destruct H4; split;
        [lia | assumption | | assumption].
      assert (ind = j \/ ind + 1 <= j < Zlength c) by lia. clear H4. destruct H6.
      2: assumption. exfalso; subst j. rewrite H5 in H3. rewrite H3 in n.
      apply n; reflexivity.
Qed.

Definition get_indices (index: Z) (live_indices: list Z) :=
  collect_Z_indices Z.eq_dec (Znth index live_indices) live_indices 0.
*)

Lemma upd_roots_outlier_compatible: forall roots outlier z v,
    roots_outlier_compatible roots outlier ->
    roots_outlier_compatible (upd_Znth z roots (ExteriorVertex v)) outlier.
Proof.
  intros. do 2 red in H |-* . intros.
  rewrite <- (filter_proj_In_iff exterior_proj_outlier_spec) in H0.
  apply In_upd_Znth in H0. destruct H0.
  inversion H0. apply H.
  rewrite <- (filter_proj_In_iff exterior_proj_outlier_spec). assumption.
Qed.

Lemma upd_Znth_graph_compatible: forall g roots z,
    roots_graph_compatible roots g ->
    forall v : VType,
      graph_has_v g v ->
      roots_graph_compatible (upd_Znth z roots (ExteriorVertex v)) g.
Proof.
  intros. red in H |-* . rewrite Forall_forall in H |-* . intros.
  rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec) in H1.
  apply In_upd_Znth in H1. destruct H1. inversion H1; assumption.
  apply H. rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec). assumption.
Qed.

Lemma upd_roots_compatible: forall g roots outlier z,
    roots_compatible g outlier roots ->
    forall v : VType, graph_has_v g v ->
                      roots_compatible g outlier (upd_Znth z roots (ExteriorVertex v)).
Proof.
  intros. destruct H. split.
  - apply upd_roots_outlier_compatible; assumption.
  - apply upd_Znth_graph_compatible; assumption.
Qed.

Local Close Scope Z_scope.

Definition update_vertex (from to: nat) (g: LGraph) (v: VType) : VType :=
  if Nat.eq_dec (vgeneration v) from
  then if (vlabel g v).(raw_mark)
       then (vlabel g v).(copied_vertex)
       else new_copied_v g to
  else v.

Definition upd_exterior (from to: nat)
           (g: LGraph) (extr: exterior_t) : exterior_t :=
  match extr with
  | ExteriorVertex v => ExteriorVertex (update_vertex from to g v)
  | _ => extr
  end.

Definition upd_fwd (from to: nat) (g: LGraph) (fwd_p: forward_p_type): forward_p_type :=
  match fwd_p with
  | FwdPntExtr extr => FwdPntExtr (upd_exterior from to g extr)
  | FwdPntIntr _ => fwd_p
  end.

Definition upd_roots (from to: nat) (index: Z) (g: LGraph) (roots: roots_t) : roots_t :=
  upd_Znth index roots (upd_exterior from to g (Znth index roots)).

Inductive forward_roots_relation (from to: nat): forall (roots1: roots_t) (g1: LGraph) (roots2: roots_t) (g2: LGraph), Prop :=
  | fwd_roots_nil: forall g, forward_roots_relation from to nil g nil g
  | fwd_roots_cons: forall r roots1 g1 roots2 g2 g3,
       forward_relation from to 0 (exterior2forward r) g1 g2 ->
       forward_roots_relation from to roots1 g2 roots2 g3 ->
       forward_roots_relation from to (r::roots1) g1 (upd_exterior from to g1 r :: roots2) g3.

Definition nth_space (h: heap) (n: nat): space :=
  nth n h.(spaces) null_space.

Lemma nth_space_Znth: forall h n,
    nth_space h n = Znth (Z.of_nat n) (spaces h).
Proof.
  intros. unfold nth_space, Znth. rewrite if_false. 2: lia.
  rewrite Nat2Z.id. reflexivity.
Qed.

Definition available_size h n := available_space (nth_space h n).

Lemma gsc_iff': forall (g: LGraph) (sp: list space),
    length (g_gen (glabel g)) <= length sp ->
    Forall (generation_space_compatible g)
           (combine (combine (nat_inc_list (length (g_gen (glabel g))))
                             (g_gen (glabel g))) sp) <->
    forall gen,
      graph_has_gen g gen ->
      generation_space_compatible g (gen, nth_gen g gen, nth gen sp null_space).
Proof.
  intros. rewrite Forall_forall. remember (g_gen (glabel g)).
  remember (nat_inc_list (length l)).
  assert (length (combine l0 l) = length l) by
      (subst; rewrite combine_length, nat_inc_list_length, Nat.min_id; reflexivity).
  assert (length (combine (combine l0 l) sp) = length l) by
      (rewrite combine_length, H0, min_l by assumption; reflexivity).
  cut (forall x, In x (combine (combine l0 l) sp) <->
                    exists gen, graph_has_gen g gen /\
                                x = (gen, nth_gen g gen, nth gen sp null_space)).
  - intros. split; intros.
    + apply H3. rewrite H2. exists gen. intuition auto.
    + rewrite H2 in H4. destruct H4 as [gen [? ?]]. subst x. apply H3. assumption.
  - intros.
    assert (forall gen,
               graph_has_gen g gen ->
               nth gen (combine (combine l0 l) sp) (0, null_info, null_space) =
               (gen, nth_gen g gen, nth gen sp null_space)). {
      intros. red in H2. rewrite <- Heql in H2.
      rewrite combine_nth_lt; [|rewrite H0; lia | lia].
      rewrite combine_nth by (subst l0; rewrite nat_inc_list_length; reflexivity).
      rewrite Heql0. rewrite nat_inc_list_nth by assumption.
      rewrite Heql. unfold nth_gen. reflexivity. }
    split; intros.
    + apply (In_nth (combine (combine l0 l) sp) x (O, null_info, null_space)) in H3.
      destruct H3 as [gen [? ?]]. exists gen. rewrite H1 in H3.
      assert (graph_has_gen g gen) by (subst l; assumption). split. 1: assumption.
      rewrite H2 in H4 by assumption. subst x. reflexivity.
    + destruct H3 as [gen [? ?]]. rewrite <- H2 in H4 by assumption. subst x.
      apply nth_In. rewrite H1. subst l. assumption.
Qed.

Lemma gsc_iff: forall (g: LGraph) h,
    length (g_gen (glabel g)) <= length (spaces h) ->
    Forall (generation_space_compatible g)
           (combine (combine (nat_inc_list (length (g_gen (glabel g))))
                             (g_gen (glabel g))) (spaces h)) <->
    forall gen,
      graph_has_gen g gen ->
      generation_space_compatible g (gen, nth_gen g gen, nth_space h gen).
Proof. intros. apply gsc_iff'. assumption. Qed.

Lemma gt_gs_compatible:
  forall (g: LGraph) (h: heap),
    graph_heap_compatible g h ->
    forall gen,
      graph_has_gen g gen ->
      generation_space_compatible g (gen, nth_gen g gen, nth_space h gen).
Proof.
  intros. destruct H as [? [_ ?]]. rewrite gsc_iff in H by assumption.
  apply H. assumption.
Qed.

Lemma pvs_mono_strict: forall g gen i j,
    i < j -> (previous_vertices_size g gen i < previous_vertices_size g gen j)%Z.
Proof.
  intros. assert (j = i + (j - i)) by lia. rewrite H0. remember (j - i). subst j.
  unfold previous_vertices_size. rewrite nat_inc_list_app, fold_left_app.
  apply vs_accum_list_lt. pose proof (seq_length n i). destruct (seq i n).
  - simpl in H0. lia.
  - intro S; inversion S.
Qed.

Lemma pvs_mono: forall g gen i j,
    i <= j -> (previous_vertices_size g gen i <= previous_vertices_size g gen j)%Z.
Proof.
  intros. rewrite Nat.le_lteq in H. destruct H. 2: subst; lia.
  rewrite Z.le_lteq. left. apply pvs_mono_strict. assumption.
Qed.

Lemma pvs_lt_rev: forall g gen i j,
    (previous_vertices_size g gen i < previous_vertices_size g gen j)%Z -> i < j.
Proof.
  intros. destruct (le_lt_dec j i).
  - apply (pvs_mono g gen) in l. exfalso. lia.
  - assumption.
Qed.

Local Open Scope Z_scope.

Lemma vo_lt_gs: forall g v,
    gen_has_index g (vgeneration v) (vindex v) ->
    vertex_offset g v < graph_gen_size g (vgeneration v).
Proof.
  intros. unfold vertex_offset, graph_gen_size. red in H.
  remember (number_of_vertices (nth_gen g (vgeneration v))). remember (vgeneration v).
  assert (S (vindex v) <= n)%nat by lia.
  apply Z.lt_le_trans with (previous_vertices_size g n0 (S (vindex v))).
  - rewrite pvs_S. apply Zplus_lt_compat_l, svs_gt_one.
  - apply pvs_mono; assumption.
Qed.

Definition v_in_range (v: val) (start: val) (n: Z): Prop :=
  exists i, 0 <= i < n /\ v = offset_val i start.

Lemma graph_thread_v_in_range: forall g h v,
    graph_heap_compatible g h -> graph_has_v g v ->
    v_in_range (vertex_address g v) (gen_start g (vgeneration v))
               (WORD_SIZE * available_size h (vgeneration v)).
Proof.
  intros. red. unfold vertex_address. exists (WORD_SIZE * vertex_offset g v).
  split. 2: reflexivity. unfold available_size. destruct H0. remember (vgeneration v). split.
  - unfold vertex_offset. unfold WORD_SIZE.
    pose proof (pvs_ge_zero g (vgeneration v) (vindex v)). rep_lia.
  - unfold WORD_SIZE. apply Zmult_lt_compat_l. 1: rep_lia.
    apply Z.lt_le_trans with (used_space (nth_space h n)).
    2: pose proof used_leq_available (nth_space h n);
    pose proof available_leq_total (nth_space h n); lia.
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
  - unfold Znth; if_tac; if_tac; try lia; destruct (Z.to_nat (i + 1));
      destruct (Z.to_nat i); simpl; reflexivity.
  - rewrite Znth_pos_cons by lia. replace (i + 1 - 1) with i by lia. reflexivity.
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

Definition rest_gen_size (h: heap) (gen: nat): Z :=
  available_space (nth_space h gen) - used_space (nth_space h gen).

Definition general_enough_space_to_copy g h from to size: Prop :=
  unmarked_gen_size g from + size <= rest_gen_size h to.

Definition enough_space_to_copy g h from to: Prop :=
  general_enough_space_to_copy g h from to 0.

Definition no_dangling_dst (g: LGraph): Prop :=
  forall v, graph_has_v g v ->
            forall e, In e (get_edges g v) -> graph_has_v g (dst g e).

Definition forward_condition g h from to: Prop :=
  enough_space_to_copy g h from to /\
  graph_has_gen g from /\ graph_has_gen g to /\
  copy_compatible g /\ no_dangling_dst g.

Lemma upd_Znth_tl {A}: forall (i: Z) (l: list A) (x: A),
    0 <= i -> l <> nil -> tl (upd_Znth (i + 1) l x) = upd_Znth i (tl l) x.
Proof.
  intros. destruct l; simpl. 1: contradiction.
  destruct (Z_lt_le_dec i (Zlength l)).
  2: rewrite !upd_Znth_out_of_range; auto; [|rewrite Zlength_cons]; lia.
  rewrite !upd_Znth_unfold; auto. 2: rewrite Zlength_cons; lia.
  unfold_sublist_old. replace (i - 0) with i by lia.
  replace (i + 1 - 0) with (i + 1) by lia. simpl.
  assert (forall j, 0 <= j -> Z.to_nat (j + 1) = S (Z.to_nat j)) by
      (intros; rewrite <- Z2Nat.inj_succ; rep_lia).
  rewrite (H1 _ H). simpl tl. do 3 f_equal.
  - f_equal. rewrite Zlength_cons. lia.
  - remember (S (Z.to_nat i)). replace (Z.to_nat (i + 1 + 1)) with (S n).
    + simpl. reflexivity.
    + do 2 rewrite H1 by lia. subst n. reflexivity.
Qed.

Lemma isptr_is_pointer_or_integer: forall p, isptr p -> is_pointer_or_integer p.
Proof. intros. destruct p; try contradiction. exact I. Qed.

Lemma mfv_unmarked_all_is_ptr_or_int: forall (tag: Z) (g : LGraph) (v : VType),
    no_dangling_dst g -> graph_has_v g v ->
    Forall is_pointer_or_integer (map (field2val tag g) (make_fields g v)).
Proof.
  intros. rewrite Forall_forall. intros f ?. apply list_in_map_inv in H1.
  destruct H1 as [x [? ?]]. destruct x; simpl in H1; subst.
  - if_tac; apply I.
  - destruct g0. exact I.
  - apply isptr_is_pointer_or_integer. unfold vertex_address.
    rewrite isptr_offset_val. apply graph_has_gen_start_isptr.
    apply (filter_proj_In_iff field_proj_edge_spec), H in H2; [destruct H2|]; assumption.
Qed.

Lemma mfv_all_is_ptr_or_int: forall g v,
    copy_compatible g -> no_dangling_dst g -> graph_has_v g v ->
    Forall is_pointer_or_integer (make_fields_vals g v).
Proof.
  intros. rewrite Forall_forall. intros f ?. unfold make_fields_vals in H2.
  pose proof (mfv_unmarked_all_is_ptr_or_int (raw_tag (vlabel g v)) _ _ H0 H1). rewrite Forall_forall in H3.
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
                    (upd_tf_arg_Zlength t index v H) (ti_frames t) (ti_nalloc t).

Definition update_thread_info_frames (t: thread_info) (fr: list frame) :=
  Build_thread_info (ti_heap_p t) (ti_heap t) (ti_args t) (arg_size t) fr (ti_nalloc t).

Local Close Scope Z_scope.

Lemma cvmgil_length: forall l to,
    to < length l -> length (copy_v_mod_gen_info_list l to) = length l.
Proof.
  intros. unfold copy_v_mod_gen_info_list. rewrite app_length. simpl.
  rewrite firstn_length_le by lia. rewrite skipn_length. lia.
Qed.

Lemma cvmgil_not_eq: forall to n l,
    n <> to -> to < length l ->
    nth n (copy_v_mod_gen_info_list l to) null_info = nth n l null_info.
Proof.
  intros. unfold copy_v_mod_gen_info_list.
  assert (length (firstn to l) = to) by (rewrite firstn_length_le; lia).
  destruct (Nat.lt_ge_cases n to).
  - rewrite app_nth1 by lia. apply sublist.nth_firstn. assumption.
  - rewrite Nat.lt_eq_cases in H2. destruct H2. 2: exfalso; intuition auto.
    rewrite <- (firstn_skipn (to + 1) l) at 4. rewrite app_cons_assoc, !app_nth2.
    + do 2 f_equal. rewrite app_length, H1, firstn_length_le by lia. reflexivity.
    + rewrite firstn_length_le; lia.
    + rewrite app_length, H1. simpl. lia.
Qed.

Lemma cvmgil_eq: forall to l,
    to < length l -> nth to (copy_v_mod_gen_info_list l to) null_info =
                     copy_v_mod_gen_info (nth to l null_info).
Proof.
  intros. unfold copy_v_mod_gen_info_list.
  assert (length (firstn to l) = to) by (rewrite firstn_length_le; lia).
  rewrite app_nth2 by lia. rewrite H0. replace (to - to) with O by lia.
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
    rewrite nat_inc_list_In_iff in H2. subst n. red in H1. lia.
  - simpl. apply lacv_gen_start. assumption.
Qed.

Lemma graph_has_v_in_closure: forall g v, graph_has_v g v -> closure_has_v g v.
Proof.
  intros g v. destruct v as [gen index].
  unfold graph_has_v, closure_has_v, closure_has_index, gen_has_index.
  simpl. intros. intuition auto with *.
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
    In (FieldEdge e) (make_fields' l v n) -> exists s, e = (v, s).
Proof.
  induction l; intros; simpl in *. 1: exfalso; assumption. destruct a.
  - simpl in H. destruct H. 1: inversion H; now exists n. apply IHl with (n + 1). assumption.
  - simpl in H. destruct H. 1: inversion H. apply IHl with (n + 1). assumption.
  - simpl in H. destruct H.
    + inversion H.
    + apply IHl with (n + 1). assumption.
Qed.

Lemma e_in_make_fields: forall g v e,
    In (FieldEdge e) (make_fields g v) -> exists s, e = (v, s).
Proof. unfold make_fields. intros. apply e_in_make_fields' in H. assumption. Qed.

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

Lemma get_edges_In_iff: forall g v e, In e (get_edges g v) <-> In (FieldEdge e) (make_fields g v).
Proof.
  intros. unfold get_edges. rewrite <- (filter_proj_In_iff field_proj_edge_spec). tauto.
Qed.

Lemma e_in_get_edges: forall g v e, In e (get_edges g v) -> exists s, e = (v, s).
Proof. intros. rewrite get_edges_In_iff in H. apply e_in_make_fields in H. assumption. Qed.

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
      simpl. destruct a; simpl; try apply IHl. constructor.
      2: apply IHl. clear.
      cut (forall a b,
              In a (map snd (filter_proj field_proj_edge (make_fields' l old b))) -> b <= a).
      * repeat intro. apply H in H0. lia.
      * induction l; intros; simpl in H. 1: exfalso; assumption.
        destruct a; simpl in H; try (apply IHl in H; lia).
        destruct H; [|apply IHl in H]; lia.
    + unfold EType. rewrite combine_length, repeat_length, !map_length, Nat.min_id.
      reflexivity.
  - apply list_in_map_inv in H. destruct H as [[x ?] [? ?]]. simpl in H. subst n0.
    assert (x = old). {
      apply e_in_get_edges in H0. destruct H0 as [s ?]. inversion H. reflexivity. }
    subst x. remember (get_edges g old). clear Heql.
    induction l; simpl in *. 1: assumption. destruct H0.
    + subst a. simpl. left; reflexivity.
    + right. apply IHl. assumption.
Qed.

Lemma graph_has_v_not_eq: forall g to x,
    graph_has_v g x -> x <> new_copied_v g to.
Proof.
  intros. destruct H. unfold new_copied_v. destruct x as [gen idx]. simpl in *.
  destruct (Nat.eq_dec gen to).
  - subst gen. intro S; inversion S. red in H0. lia.
  - intro S; inversion S. apply n; assumption.
Qed.

Lemma lacv_make_fields_not_eq: forall (g : LGraph) (v : VType) (to : nat) x,
    x <> new_copied_v g to ->
    make_fields (lgraph_add_copied_v g v to) x = make_fields g x.
Proof.
  intros. unfold make_fields. simpl. unfold update_copied_new_vlabel, update_vlabel.
  rewrite if_false. 1: reflexivity. intuition auto.
Qed.

Lemma lacv_field2val_make_fields_old:  forall (tag: Z) (g : LGraph) (v : VType) (to : nat) x,
    graph_has_v g x -> graph_has_gen g to -> no_dangling_dst g ->
    map (field2val tag (lgraph_add_copied_v g v to))
        (make_fields (lgraph_add_copied_v g v to) x) =
    map (field2val tag g) (make_fields g x).
Proof.
  intros. unfold make_fields. pose proof (graph_has_v_not_eq _ to _ H).
  rewrite lacv_vlabel_old by assumption. apply map_ext_in.
  intros [? | ? | ?] ?; simpl; try reflexivity. unfold new_copied_v.
  rewrite pcv_dst_old.
  - apply lacv_vertex_address_old. 2: assumption. specialize (H1 _ H). apply H1.
    rewrite get_edges_In_iff. assumption.
  - apply e_in_make_fields' in H3. destruct H3 as [s ?]. subst e. simpl. intro.
    unfold new_copied_v in H2. contradiction.
Qed.

Lemma lacv_make_fields_vals_old: forall (g : LGraph) (v : VType) (to: nat) x,
    graph_has_v g x -> graph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    make_fields_vals (lgraph_add_copied_v g v to) x = make_fields_vals g x.
Proof.
  intros. pose proof (lacv_field2val_make_fields_old (raw_tag (vlabel g x))  _ v _ _ H H0 H1).
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

Lemma lacv_field2val_make_fields_new: forall (tag: Z) g v to,
    graph_has_v g v -> graph_has_gen g to -> no_dangling_dst g ->
    map (field2val tag (lgraph_add_copied_v g v to))
        (make_fields (lgraph_add_copied_v g v to) (new_copied_v g to)) =
    map (field2val tag g) (make_fields g v).
Proof.
  intros. unfold make_fields. rewrite lacv_vlabel_new.
  remember (raw_fields (vlabel g v)). remember 0 as n.
  assert (forall m, In m (map snd (filter_proj field_proj_edge (make_fields' l v n))) ->
                    In m (map snd (get_edges g v))). {
    unfold get_edges, make_fields. subst. intuition auto. }
  clear Heql Heqn. revert n H2. induction l; intros; simpl. 1: reflexivity. destruct a.
  - simpl in *. rewrite IHl.
    + assert (In n (map snd (get_edges g v))) by (apply H2; left; reflexivity).
      f_equal. rewrite pcv_dst_new by assumption. apply lacv_vertex_address_old.
      2: assumption. red in H1. apply (H1 v). 1: assumption. apply in_map_iff in H3.
      destruct H3 as [[x ?] [? ?]]. simpl in H3. subst n0. clear -H4. pose proof H4.
      apply e_in_get_edges in H4. destruct H4 as [s ?]. inversion H0. subst. assumption.
    + intros. apply H2. right; assumption.
  - simpl in *. rewrite IHl; [reflexivity | assumption].
  - simpl in *. rewrite IHl; [reflexivity | assumption].
Qed.

Lemma lacv_make_fields_vals_new: forall g v to,
    graph_has_v g v -> graph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    make_fields_vals (lgraph_add_copied_v g v to) (new_copied_v g to) =
    make_fields_vals g v.
Proof.
  intros. unfold make_fields_vals. rewrite lacv_vlabel_new.
  rewrite (lacv_field2val_make_fields_new _ _ _ _ H H0 H1).
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
      simpl. red in H1. unfold nth_gen in H1. lia.
    + rewrite lacv_nth_gen; assumption.
Qed.

Lemma lacv_graph_has_v_new: forall g v to,
    graph_has_gen g to -> graph_has_v (lgraph_add_copied_v g v to) (new_copied_v g to).
Proof.
  intros. split; simpl.
  - red. simpl. rewrite cvmgil_length; assumption.
  - red. unfold nth_gen. simpl. rewrite cvmgil_eq by assumption. simpl. lia.
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

Lemma lmc_field2val_make_fields: forall (tag: Z) (g : LGraph) (v new_v x: VType),
    map (field2val tag (lgraph_mark_copied g v new_v))
        (make_fields (lgraph_mark_copied g v new_v) x) =
    map (field2val tag g) (make_fields g x).
Proof.
  intros. rewrite lmc_make_fields. apply map_ext; intros.
  destruct a; simpl; [| |rewrite lmc_vertex_address]; reflexivity.
Qed.

Lemma lmc_vlabel_not_eq: forall g v new_v x,
    x <> v -> vlabel (lgraph_mark_copied g v new_v) x = vlabel g x.
Proof.
  intros. unfold lgraph_mark_copied, update_copied_old_vlabel, update_vlabel. simpl.
  rewrite if_false. 1: reflexivity. unfold equiv. intuition auto.
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
  assert (tl (make_fields_vals g v) = tl (map (field2val (raw_tag (vlabel g v)) g) (make_fields g v))) by
      (unfold make_fields_vals; destruct (raw_mark (vlabel g v)); simpl; reflexivity).
  rewrite H. clear H. do 2 f_equal. apply lmc_field2val_make_fields.
Qed.

Lemma lmc_nth_sh: forall (g: LGraph) (v new_v: VType) n,
    nth_sh (lgraph_mark_copied g v new_v) n = nth_sh g n.
Proof. intros. unfold lgraph_mark_copied, nth_sh, nth_gen. simpl. reflexivity. Qed.

Lemma lcv_graph_has_gen: forall g v to x,
    graph_has_gen g to -> graph_has_gen g x <-> graph_has_gen (lgraph_copy_v g v to) x.
Proof. unfold graph_has_gen. intros. simpl. rewrite cvmgil_length; intuition auto. Qed.

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
  - assert (v <> old) by intuition auto with *. clear c.
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
    + assert (x <> (new_copied_v g to)) by intuition auto. clear c H0.
      unfold gen_has_index in *. unfold nth_gen, lgraph_add_copied_v in H1.
      simpl in H1. destruct x as [gen index]. simpl in *. unfold new_copied_v in H2.
      destruct (Nat.eq_dec gen to).
      * subst gen. rewrite cvmgil_eq in H1 by assumption. simpl in H1.
        change (nth to (g_gen (glabel g)) null_info) with (nth_gen g to) in H1.
        remember (number_of_vertices (nth_gen g to)).
        assert (index <> n) by (intro; apply H2; f_equal; assumption). lia.
      * rewrite cvmgil_not_eq in H1; assumption.
Qed.

Lemma lacv_copy_compatible: forall (g : LGraph) (v : VType) (to : nat),
    raw_mark (vlabel g v) = false -> graph_has_gen g to ->
    copy_compatible g -> copy_compatible (lgraph_add_copied_v g v to).
Proof.
  repeat intro. destruct (V_EqDec v0 (new_copied_v g to)).
  - unfold equiv in e. subst v0. rewrite lacv_vlabel_new in *.
    rewrite H3 in H. inversion H.
  - assert (v0 <> (new_copied_v g to)) by intuition auto. clear c.
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
  1: reflexivity. destruct a; rewrite filter_proj_cons; simpl; rewrite IHl; try reflexivity.
  intuition auto. inversion H0. left; reflexivity.
Qed.

Lemma get_edges_fst: forall g v e, In e (get_edges g v) -> fst e = v.
Proof.
  intros g v e. unfold get_edges, make_fields. remember (raw_fields (vlabel g v)).
  remember 0 as n. clear Heqn Heql. revert n. induction l; intros; simpl in *.
  - exfalso; assumption.
  - destruct a; rewrite filter_proj_cons in H; simpl in *;
      [destruct H; [subst e; simpl; reflexivity|] | |]; apply IHl in H; assumption.
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
  destruct a; rewrite filter_proj_cons; simpl; rewrite IHl; reflexivity.
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
  - assert (x <> new_copied_v g to) by intuition auto. clear c. rewrite pcv_dst_old.
    + apply lacv_graph_has_v_old. 1: assumption. apply lacv_graph_has_v_inv in H2.
      2: assumption. destruct H2. 2: contradiction. apply (H x). 1: assumption.
      unfold get_edges in *. rewrite lacv_make_fields_not_eq in H3; assumption.
    + apply e_in_get_edges in H3. destruct H3 as [s ?]. subst e. simpl. assumption.
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

Lemma utia_estc: forall g t_info from to frames,
    enough_space_to_copy g t_info.(ti_heap) from to ->
    enough_space_to_copy g (update_thread_info_frames t_info frames).(ti_heap) from to.
Proof. intros. apply H.
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

Lemma lacv_gestc: forall g t_info from to size v,
    from <> to -> graph_has_gen g to ->
    general_enough_space_to_copy g t_info from to size ->
    general_enough_space_to_copy (lgraph_add_copied_v g v to) t_info from to size.
Proof.
  unfold general_enough_space_to_copy. intros. rewrite <- lacv_unmarked_gen_size; assumption.
Qed.

Lemma lacv_estc: forall g t_info from to v,
    from <> to -> graph_has_gen g to ->
    enough_space_to_copy g t_info from to ->
    enough_space_to_copy (lgraph_add_copied_v g v to) t_info from to.
Proof. unfold enough_space_to_copy. intros; apply lacv_gestc; assumption. Qed.

Lemma vsa_fold_left:
  forall (g : LGraph) (gen : nat) (l : list nat) (z1 z2 : Z),
    fold_left (vertex_size_accum g gen) l (z2 + z1) =
    fold_left (vertex_size_accum g gen) l z2 + z1.
Proof.
  intros. revert z1 z2. induction l; intros; simpl. 1: reflexivity.
  rewrite <- IHl. f_equal. unfold vertex_size_accum. lia.
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

Lemma gestc_has_space: forall to g h v size,
    graph_has_v g v -> raw_mark (vlabel g v) = false ->
    general_enough_space_to_copy g h (vgeneration v) to size -> 0 <= size ->
    has_space (Znth (Z.of_nat to) (spaces h)) (vertex_size g v).
Proof.
  intros; split. 1: pose proof (svs_gt_one g v); lia.
  transitivity (unmarked_gen_size g (vgeneration v)).
  - apply single_unmarked_le; assumption.
  - red in H1. unfold rest_gen_size in H1. rewrite nth_space_Znth in H1. lia.
Qed.

Lemma estc_has_space: forall to g h v,
    graph_has_v g v -> raw_mark (vlabel g v) = false ->
    enough_space_to_copy g h (vgeneration v) to ->
    has_space (Znth (Z.of_nat to) (spaces h)) (vertex_size g v).
Proof. intros. eapply gestc_has_space; eauto. apply Z.le_refl. Qed.

Lemma lmc_general_enough_space_to_copy:
  forall (g : LGraph) (h : heap) (v v': VType) (to : nat) size,
    general_enough_space_to_copy g h (vgeneration v) to size ->
    graph_has_v g v -> raw_mark (vlabel g v) = false -> 0 <= size ->
    general_enough_space_to_copy (lgraph_mark_copied g v v')
      (cut_heap h (Z.of_nat to) (vertex_size g v)) (vgeneration v) to size.
Proof.
  intros. pose proof gestc_has_space _ _ _ _ _ H0 H1 H H2.
  unfold general_enough_space_to_copy in *.
  rewrite (lmc_unmarked_gen_size g v v') in H by assumption. pose proof svs_gt_one g v.
  unfold cut_heap. destruct (spaces_index_dec _ _); [|lia].
  unfold rest_gen_size in *. rewrite !nth_space_Znth in *. simpl.
  rewrite upd_Znth_same by assumption. unfold_cut_space. simpl. lia.
Qed.

Lemma lmc_enough_space_to_copy:
  forall (g : LGraph) (h : heap) (v v': VType) (to : nat),
    enough_space_to_copy g h (vgeneration v) to ->
    graph_has_v g v -> raw_mark (vlabel g v) = false ->
    enough_space_to_copy (lgraph_mark_copied g v v')
      (cut_heap h (Z.of_nat to) (vertex_size g v)) (vgeneration v) to.
Proof. intros; eapply lmc_general_enough_space_to_copy; eauto. apply Z.le_refl. Qed.

Lemma lcv_general_enough_space_to_copy: forall g h v to size,
    vgeneration v <> to -> graph_has_gen g to ->
    graph_has_v g v -> raw_mark (vlabel g v) = false ->
    general_enough_space_to_copy g h (vgeneration v) to size -> 0 <= size ->
    general_enough_space_to_copy (lgraph_copy_v g v to)
         (cut_heap h (Z.of_nat to) (vertex_size g v)) (vgeneration v) to size.
Proof.
  intros g h v to size H1 H2 H3 H4 H5 Hs. unfold lgraph_copy_v.
  pose proof gestc_has_space _ _ _ _ _ H3 H4 H5 Hs as H0.
  apply (lacv_gestc _ _ _ _ _ v) in H5; [| assumption..].
  assert (H6: vertex_size g v = vertex_size (lgraph_add_copied_v g v to) v). {
    unfold vertex_size. rewrite lacv_vlabel_old. 1: reflexivity.
    intro H6. destruct v as [gen index]. simpl in H0.
    unfold new_copied_v in H6. inversion H6. apply H1. assumption. }
  remember (lgraph_add_copied_v g v to) as g'. rewrite H6 in H0.
  replace (cut_heap h (Z.of_nat to) (vertex_size g v)) with
    (cut_heap h (Z.of_nat to) (vertex_size g' v)) by (now rewrite H6).
  apply lmc_general_enough_space_to_copy; try assumption.
  - subst g'. apply lacv_graph_has_v_old; assumption.
  - subst g'. rewrite lacv_vlabel_old; [| apply graph_has_v_not_eq]; assumption.
Qed.

Lemma lcv_enough_space_to_copy: forall g h v to,
    vgeneration v <> to -> graph_has_gen g to ->
    graph_has_v g v -> raw_mark (vlabel g v) = false ->
    enough_space_to_copy g h (vgeneration v) to ->
    enough_space_to_copy (lgraph_copy_v g v to)
         (cut_heap h (Z.of_nat to) (vertex_size g v)) (vgeneration v) to.
Proof. intros. eapply lcv_general_enough_space_to_copy; eauto. apply Z.le_refl. Qed.

Lemma lcv_forward_condition: forall g h v to,
    vgeneration v <> to -> graph_has_v g v -> raw_mark (vlabel g v) = false ->
    forward_condition g h (vgeneration v) to ->
    forward_condition (lgraph_copy_v g v to)
        (cut_heap h (Z.of_nat to) (vertex_size g v)) (vgeneration v) to.
Proof.
  intros. destruct H2 as [? [? [? [? ?]]]]. split; [|split; [|split; [|split]]].
  - apply lcv_enough_space_to_copy;  assumption.
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

Lemma lcv_roots_graph_compatible: forall g roots v to z,
    graph_has_gen g to ->
    roots_graph_compatible roots g ->
    roots_graph_compatible (upd_Znth z roots (ExteriorVertex (new_copied_v g to)))
                           (lgraph_copy_v g v to).
Proof.
  intros. apply upd_Znth_graph_compatible.
  - apply lcv_rgc_unchanged; assumption.
  - unfold lgraph_copy_v; rewrite <- lmc_graph_has_v;
      apply lacv_graph_has_v_new; assumption.
Qed.

Lemma lcv_roots_compatible: forall g roots outlier v to z,
    graph_has_gen g to ->
    roots_compatible g outlier roots ->
    roots_compatible (lgraph_copy_v g v to) outlier
                     (upd_Znth z roots (ExteriorVertex (new_copied_v g to))).
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

Lemma lcv_rootpairs_compatible_unchanged: forall
    g rootpairs roots v to,
    graph_has_gen g to ->
    roots_graph_compatible roots g ->
    rootpairs_compatible g rootpairs roots ->
    rootpairs_compatible (lgraph_copy_v g v to) rootpairs roots.
Proof.
 intros. unfold rootpairs_compatible in *; simpl in *.
 rewrite <- H1; clear H1.
 pose proof lcv_vertex_address_old g.
 induction roots; simpl; auto.
 f_equal.
 - destruct a; auto. destruct v0; auto.
    hnf in H0; simpl in H0. inv H0.
    unfold exterior2val. apply H1; auto.
 - apply IHroots; auto.
   red in H0 |- *.
   destruct a; auto. destruct v0; auto. simpl in H0. inv H0; auto.
Qed.

Lemma upd_Znth_unchanged: forall {A : Type} {d : Inhabitant A} (i : Z) (l : list A),
    0 <= i < Zlength l -> upd_Znth i l (Znth i l) = l.
Proof. intros. list_solve. Qed.

Lemma upd_rootpairs_compatible': forall g rootpairs roots i extr,
    rootpairs_compatible g rootpairs roots ->
    rootpairs_compatible g
      (update_rootpairs rootpairs (map (exterior2val g) (upd_Znth i roots extr)))
      (upd_Znth i roots extr).
Proof.
  intros. unfold rootpairs_compatible in *.
  rewrite <- upd_Znth_map, H, update_rootpairs_upd_Znth, <- upd_Znth_map.
  simpl. reflexivity.
Qed.

Lemma upd_rootpairs_compatible: forall g rootpairs roots z,
    rootpairs_compatible g rootpairs roots ->
    forall (v : VType) (HB : 0 <= z < Zlength roots),
      rootpairs_compatible g
      (update_rootpairs rootpairs
            (upd_Znth z (map rp_val rootpairs) (vertex_address g v)))
       (upd_Znth z roots (ExteriorVertex v)).
Proof.
  intros. hnf in H. rewrite <- H.
  change (vertex_address g v) with (exterior2val g (ExteriorVertex v)).
  rewrite upd_Znth_map. apply upd_rootpairs_compatible'. apply H.
Qed.

Lemma lcv_rootpairs_compatible: forall
    g rootpairs roots z v to
    (Hm : 0 <= z < Zlength roots),
    graph_has_gen g to -> roots_graph_compatible roots g ->
    rootpairs_compatible g rootpairs roots ->
    rootpairs_compatible
      (lgraph_copy_v g v to)
      (update_rootpairs rootpairs
        (upd_Znth z (map rp_val rootpairs)
          (vertex_address g (new_copied_v g to))))
      (upd_Znth z roots (ExteriorVertex (new_copied_v g to))).
Proof.
  intros. rewrite <- (lcv_vertex_address_new g v to H).
  apply upd_rootpairs_compatible; auto.
  apply lcv_rootpairs_compatible_unchanged; assumption.
Qed.

#[export] Instance share_inhabitant: Inhabitant share := emptyshare.

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
  replace (n + 1)%nat with (S n) by lia. rewrite pvs_S. f_equal.
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

Lemma lcv_graph_heap_compatible: forall
    g h v to
    (Hh : has_space (Znth (Z.of_nat to) (spaces h)) (vertex_size g v)),
    graph_has_gen g to ->
    graph_heap_compatible g h ->
    graph_heap_compatible (lgraph_copy_v g v to)
      (cut_heap h (Z.of_nat to) (vertex_size g v)).
Proof.
  unfold graph_heap_compatible. intros. destruct H0 as [? [? ?]].
  assert (Hi : 0 <= Z.of_nat to < Zlength (spaces h)). {
    unfold graph_has_gen in H. rewrite Zlength_correct. list_solve. }
  assert (map space_start (spaces h) =
          map space_start (upd_Znth (Z.of_nat to) (spaces h)
                             (cut_space (Znth (Z.of_nat to) (spaces h))
                                (vertex_size g v)))). {
    rewrite <- upd_Znth_map. unfold_cut_space. simpl. rewrite <- Znth_map by assumption.
    rewrite upd_Znth_unchanged; [reflexivity | rewrite Zlength_map; assumption]. }
  unfold_cut_heap. split; [|split]; [|simpl; rewrite cvmgil_length by assumption..].
  - rewrite gsc_iff in *; simpl. 2: assumption.
    + intros. unfold nth_space. simpl.
      rewrite <- lcv_graph_has_gen in H4 by assumption. specialize (H0 _ H4).
      simpl in H0. destruct H0 as [? [? ?]]. split; [|split].
      * clear -H0 H3 H. rewrite <- map_nth, <- H3, map_nth. clear H3.
        unfold nth_gen, nth_space in *. simpl. destruct (Nat.eq_dec gen to).
        -- subst gen. rewrite cvmgil_eq; simpl; assumption.
        -- rewrite cvmgil_not_eq; assumption.
      * assert (map space_sh
                    (upd_Znth (Z.of_nat to) (spaces h)
                              (cut_space (Znth (Z.of_nat to) (spaces h))
                                 (vertex_size g v))) =
                map space_sh (spaces h)). {
          rewrite <- upd_Znth_map. unfold_cut_space. simpl.
          rewrite <- Znth_map by assumption.
          rewrite upd_Znth_unchanged; [reflexivity|rewrite Zlength_map; assumption]. }
        rewrite <- map_nth, H7, map_nth. clear -H5 H. unfold nth_gen, nth_space in *.
        simpl. destruct (Nat.eq_dec gen to).
        -- subst gen. rewrite cvmgil_eq; simpl; assumption.
        -- rewrite cvmgil_not_eq; assumption.
      * assert (0 <= Z.of_nat gen < Zlength (spaces h)). {
          split. 1: apply Nat2Z.is_nonneg. rewrite Zlength_correct.
          apply inj_lt. red in H4. lia. }
        rewrite <- (Nat2Z.id gen) at 3. rewrite nth_Znth.
        2: rewrite upd_Znth_Zlength; assumption. destruct (Nat.eq_dec gen to).
        -- subst gen. rewrite upd_Znth_same by assumption.
           rewrite lcv_pvs_same by assumption. unfold_cut_space. simpl.
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
    g h rootpairs roots outlier to v
    (Hh : has_space (Znth (Z.of_nat to) (spaces h)) (vertex_size g v)),
    graph_has_gen g to -> graph_has_v g v ->
    super_compatible g h rootpairs roots outlier ->
    super_compatible (lgraph_copy_v g v to)
      (cut_heap h (Z.of_nat to) (vertex_size g v))
      rootpairs roots outlier.
Proof.
  intros. destruct H1 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply lcv_graph_heap_compatible; assumption.
  - destruct H3. apply lcv_rootpairs_compatible_unchanged; assumption.
  - apply lcv_roots_compatible_unchanged; assumption.
  - apply lcv_outlier_compatible; assumption.
Qed.

Lemma lcv_super_compatible: forall
    g h rootpairs roots outlier to v z
    (Hh : has_space (Znth (Z.of_nat to) (spaces h)) (vertex_size g v))
    (Hm : 0 <= z < Zlength roots),
    graph_has_gen g to -> graph_has_v g v ->
    super_compatible g h rootpairs roots outlier ->
    super_compatible (lgraph_copy_v g v to)
      (cut_heap h (Z.of_nat to) (vertex_size g v))
      (update_rootpairs rootpairs
         (upd_Znth z (map rp_val rootpairs)
            (vertex_address g (new_copied_v g to))))
      (upd_Znth z roots (ExteriorVertex (new_copied_v g to))) outlier.
Proof.
  intros. destruct H1 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply lcv_graph_heap_compatible; assumption.
  - destruct H3. eapply lcv_rootpairs_compatible; eassumption.
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

Lemma cti_available_size: forall h i s n,
    available_size (cut_heap h i s) n = available_size h n.
Proof.
  intros. unfold available_size, cut_heap. destruct (spaces_index_dec _ _); simpl; auto.
  rewrite !nth_space_Znth. simpl. destruct (Z.eq_dec (Z.of_nat n) i).
  - subst i. rewrite upd_Znth_same; auto. unfold cut_space.
    destruct (has_space_dec _ _); auto.
  - rewrite Znth_upd_Znth_diff; [reflexivity | assumption].
Qed.

Lemma cti_space_start: forall h i s n,
    space_start (nth_space (cut_heap h i s) n) = space_start (nth_space h n).
Proof.
  intros. unfold cut_heap. destruct (spaces_index_dec _ _); simpl; auto.
  rewrite !nth_space_Znth. simpl. destruct (Z.eq_dec (Z.of_nat n) i).
  - subst i. rewrite upd_Znth_same; auto. unfold cut_space.
    destruct (has_space_dec _ _); auto.
  - rewrite Znth_upd_Znth_diff; [reflexivity | assumption].
Qed.

Lemma cti_total_space: forall h i s n,
    total_space (nth_space (cut_heap h i s) n) = total_space (nth_space h n).
Proof.
  intros. unfold cut_heap. destruct (spaces_index_dec _ _); simpl; auto.
  rewrite !nth_space_Znth. simpl. destruct (Z.eq_dec (Z.of_nat n) i).
  - subst i. rewrite upd_Znth_same; auto. unfold cut_space.
    destruct (has_space_dec _ _); auto.
  - rewrite Znth_upd_Znth_diff; [reflexivity | assumption].
Qed.

Definition heap_relation (h h': heap) :=
  (forall n, available_size h n = available_size h' n) /\
  (forall n, space_start (nth_space h n) = space_start (nth_space h' n)).

Definition thread_info_relation t t':=
  ti_heap_p t = ti_heap_p t' /\ heap_relation (ti_heap t) (ti_heap t').

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
  apply upd_Znth_diff; auto; lia.
  { rewrite !Znth_overflow; auto.
    rewrite upd_Znth_Zlength; auto. }
Qed.

Lemma lgd_graph_has_v: forall g e v v',
    graph_has_v g v <-> graph_has_v (labeledgraph_gen_dst g e v') v.
Proof. reflexivity. Qed.

Lemma lgd_graph_has_gen: forall g e v x,
    graph_has_gen (labeledgraph_gen_dst g e v) x <-> graph_has_gen g x.
Proof. intros; unfold graph_has_gen; intuition auto. Qed.

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

Lemma lgd_f2v_eq_except_one: forall tag g fd e v',
    fd <> (FieldEdge e) ->
    field2val tag g fd = field2val tag (labeledgraph_gen_dst g e v') fd.
Proof.
  intros; unfold field2val; simpl.
  destruct fd; try reflexivity.
  unfold updateEdgeFunc; if_tac; [exfalso; apply H; rewrite H0|]; reflexivity.
Qed.

Lemma Znth_list_eq {X: Type} {d: Inhabitant X}: forall (l1 l2: list X),
    l1 = l2 <-> (Zlength l1 = Zlength l2 /\
                 forall j, 0 <= j < Zlength l1 -> Znth j l1 = Znth j l2).
Proof.
  induction l1; destruct l2; split; intros.
  - split; intros; reflexivity.
  - reflexivity.
  - inversion H.
  - destruct H. rewrite Zlength_nil, Zlength_cons in H. exfalso; rep_lia.
  - inversion H.
  - destruct H. rewrite Zlength_nil, Zlength_cons in H. exfalso; rep_lia.
  - inversion H. subst a. subst l1. split; intros; reflexivity.
  - destruct H. assert (0 <= 0 < Zlength (a :: l1)) by
        (rewrite Zlength_cons; rep_lia). apply H0 in H1. rewrite !Znth_0_cons in H1.
    subst a. rewrite !Zlength_cons in H. f_equal. rewrite IHl1. split. 1: rep_lia.
    intros. assert (0 < j + 1) by lia.
    assert (0 <= j + 1 < Zlength (x :: l1)) by (rewrite Zlength_cons; rep_lia).
    specialize (H0 _ H3). rewrite !Znth_pos_cons in H0 by assumption.
    replace (j + 1 - 1) with j in H0 by lia. assumption.
Qed.

Lemma lgd_map_f2v_diff_vert_eq: forall tag g v v' v1 e n,
    0 <= n < Zlength (make_fields g v) ->
    Znth n (make_fields g v) = FieldEdge e ->
    v1 <> v ->
    map (field2val tag g) (make_fields g v1) =
    map (field2val tag (labeledgraph_gen_dst g e v'))
        (make_fields (labeledgraph_gen_dst g e v') v1).
Proof.
    intros.
    rewrite lgd_make_fields_eq.
    apply Znth_list_eq. split.
    1: repeat rewrite Zlength_map; reflexivity.
    intros. rewrite Zlength_map in H2.
    repeat rewrite Znth_map by assumption.
    apply lgd_f2v_eq_except_one. intro.
    pose proof (make_fields_edge_unique g e v v1 n j H H2 H0 H3).
    destruct H4. unfold not in H1. symmetry in H5.
    apply (H1 H5).
Qed.

Lemma lgd_f2v_eq_after_update: forall tag g v v' e n j,
  0 <= n < Zlength (make_fields g v) ->
  0 <= j < Zlength (make_fields g v) ->
  Znth n (make_fields g v) = FieldEdge e ->
  Znth j (upd_Znth n (map (field2val tag g)
                          (make_fields g v)) (vertex_address g v')) =
  Znth j
    (map (field2val tag (labeledgraph_gen_dst g e v'))
         (make_fields (labeledgraph_gen_dst g e v') v)).
Proof.
  intros.
  rewrite Znth_map.
  2: rewrite lgd_make_fields_eq; assumption.
  assert (j = n \/ j <> n) by lia; destruct H2.
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
    apply (lgd_f2v_eq_except_one _ g (Znth j (make_fields g v))).
    intro. pose proof (make_fields_edge_unique g e v v n j H H0 H1 H3).
    lia.
Qed.

Lemma lgd_mfv_change_in_one_spot: forall g v e v' n,
    0 <= n < Zlength (make_fields g v) ->
    raw_mark (vlabel g v) = false ->
    Znth n (make_fields g v) = FieldEdge e ->
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
    no_dangling_dst g -> no_dangling_dst (labeledgraph_gen_dst g e v').
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

Lemma lgd_general_enough_space_to_copy: forall g e v' t_info gen sp size,
    general_enough_space_to_copy g t_info gen sp size ->
    general_enough_space_to_copy (labeledgraph_gen_dst g e v') t_info gen sp size.
Proof. intros. unfold enough_space_to_copy in *. intuition auto. Qed.

Lemma lgd_enough_space_to_copy: forall g e v' t_info gen sp,
    enough_space_to_copy g t_info gen sp ->
    enough_space_to_copy (labeledgraph_gen_dst g e v') t_info gen sp.
Proof. intros. apply lgd_general_enough_space_to_copy; assumption. Qed.

Lemma lgd_copy_compatible: forall g v' e,
    copy_compatible g ->
    copy_compatible (labeledgraph_gen_dst g e v').
Proof. intros. unfold copy_compatible in *. intuition auto. Qed.

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

Lemma lgd_graph_heap_compatible:
  forall (g : LGraph) (h : heap) e (v' : VType),
  graph_heap_compatible g h ->
  graph_heap_compatible (labeledgraph_gen_dst g e v') h.
Proof. intros; destruct H; split; assumption. Qed.

Lemma lgd_fun_thread_arg_compatible:
  forall (g : LGraph) rootpairs e (v' : VType) roots,
    rootpairs_compatible g rootpairs roots ->
    rootpairs_compatible (labeledgraph_gen_dst g e v') rootpairs roots.
Proof.
  intros. unfold rootpairs_compatible in *.
  rewrite <- H. apply map_ext_in. intros. destruct a; reflexivity.
Qed.

Lemma lgd_outlier_compatible:
  forall (g : LGraph) e (v' : VType) outlier,
    outlier_compatible g outlier ->
    outlier_compatible (labeledgraph_gen_dst g e v') outlier.
Proof.
  intros. intro v. intros.
  rewrite <- lgd_graph_has_v in H0.
  unfold labeledgraph_gen_dst, pregraph_gen_dst, updateEdgeFunc; simpl.
  apply (H v H0).
Qed.

Lemma lgd_super_compatible: forall g (h: heap) (rootpairs: list rootpair) roots outlier v' e,
    super_compatible g h rootpairs roots outlier ->
    super_compatible (labeledgraph_gen_dst g e v') h rootpairs roots outlier.
Proof.
  intros. destruct H as [? [? [? ?]]]. split; [|split; [|split]].
  - apply lgd_graph_heap_compatible; assumption.
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
  - inversion H3; subst; try (specialize (H to g'); assumption); try solve [auto].
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
      * intros. apply (H0 to g new_g g'). 1: assumption. apply (H4 _ _ _ _ _ H9).
      * subst new_g. apply H2.
    + inv H3; eauto.
    + subst new_g. apply H1.
    + cut (P to g new_g).
      * intros. apply (H0 to g new_g g'). 1: assumption. apply (H4 _ _ _ _ _ H9).
      * subst new_g. remember (lgraph_copy_v g (dst g e) to) as g1.
        remember (labeledgraph_gen_dst g1 e (new_copied_v g to)) as g2.
        cut (P to g1 g2). 2: subst; apply H1. intros. apply (H0 to g g1 g2).
        2: assumption. subst g1. apply H2.
    + subst new_g. inv H3; eauto.
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
  - inversion H8; subst; try (specialize (H1 g' v); assumption); try solve [eauto].
  - assert (forall l from to g1 g2,
               graph_has_gen g1 to -> forward_loop from to depth l g1 g2 ->
               R from to -> forall v, Q g1 v from -> P g1 g2 v). {
      induction l; intros; inversion H11. 1: apply H1. subst.
      specialize (IHdepth _ _ _ _ _ _ _ _ _ H12 H10 H1 H2 H3 H4 H5 H6 H7 H17 _ H13).
      apply (H5 _ _ _ _ _ _ H10 H17) in H13.
      rewrite (fr_graph_has_gen _ _ _ _ _ _ H10 H17) in H10.
      specialize (IHl _ _ _ _ H10 H20 H12 _ H13). apply (H2 _ _ _ _ IHdepth IHl). }
    clear IHdepth. inversion H8; subst; try (specialize (H1 g' v); assumption); try solve [eauto].
    + cut (P g new_g v).
      * intros. apply (H2 g new_g g'). 1: assumption.
        assert (graph_has_gen new_g to) by
            (subst new_g; rewrite <- lcv_graph_has_gen; assumption).
        apply (H10 _ _ _ _ _ H12 H15 H). subst new_g. apply H6; assumption.
      * subst new_g. apply (H4 (vgeneration v0)); [assumption.. | reflexivity].
    + cut (P g new_g v).
      * intros. apply (H2 g new_g g'). 1: assumption.
        assert (graph_has_gen new_g to) by
            (subst new_g; rewrite lgd_graph_has_gen, <- lcv_graph_has_gen; assumption).
        apply (H10 _ _ _ _ _ H12 H15 H). subst new_g. apply H7, H6; assumption.
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
    simpl. red in H1. unfold nth_gen in H1. lia.
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
  - assert (x <> old) by intuition auto with *.
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


Lemma lmc_raw_tag: forall g old new x,
    x <> old -> raw_tag (vlabel g x) =
                raw_tag (vlabel (lgraph_mark_copied g old new) x).
Proof.
  intros. destruct (V_EqDec x old).
  - unfold equiv in e. contradiction.
  - rewrite lmc_vlabel_not_eq; [reflexivity | assumption].
Qed.

Lemma lcv_raw_tag: forall g v to x,
    x <> v -> graph_has_gen g to -> graph_has_v g x ->
    raw_tag (vlabel g x) = raw_tag (vlabel (lgraph_copy_v g v to) x).
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_raw_tag by assumption.
  rewrite lacv_vlabel_old. 1: reflexivity. apply graph_has_v_not_eq; assumption.
Qed.


Lemma fr_raw_tag: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, graph_has_v g v -> vgeneration v <> from ->
              raw_tag (vlabel g v) = raw_tag (vlabel g' v).
Proof.
  intros. remember (fun (g: LGraph) (v: VType) (x: nat) =>
                      graph_has_v g v /\ vgeneration v <> x) as Q.
  remember (fun (g1 g2: LGraph) v =>
              raw_tag (vlabel g1 v) = raw_tag (vlabel g2 v)) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H3; clear H3; intros; try assumption; try reflexivity.
  - rewrite H3. apply H4.
  - destruct H4. rewrite <- lcv_raw_tag; [reflexivity | try assumption..].
    destruct x, v0. simpl in *. intro. inversion H9. subst. contradiction.
  - destruct H5. split. 2: assumption.
    apply (fr_graph_has_v _ _ _ _ _ _ H3 H4 _ H5).
  - destruct H4. split. 2: assumption. apply lcv_graph_has_v_old; assumption.
  - split; assumption.
Qed.

Lemma fl_raw_mark: forall depth from to l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, graph_has_v g v -> from <> vgeneration v ->
              raw_mark (vlabel g v) = raw_mark (vlabel g' v).
Proof.
  intros. revert g g' H H0 v H1 H2. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (raw_mark (vlabel g2 v)).
  - apply not_eq_sym in H2. apply (fr_raw_mark _ _ _ _ _ _ H H6 _ H1 H2).
  - apply IHl; [|assumption| |assumption].
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_graph_has_v; eauto.
Qed.

Lemma fl_raw_tag: forall depth from to l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, graph_has_v g v -> from <> vgeneration v ->
              raw_tag (vlabel g v) = raw_tag (vlabel g' v).
Proof.
  intros. revert g g' H H0 v H1 H2. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (raw_tag (vlabel g2 v)).
  - apply not_eq_sym in H2. apply (fr_raw_tag _ _ _ _ _ _ H H6 _ H1 H2).
  - apply IHl; [|assumption| |assumption].
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_graph_has_v; eauto.
Qed.

Lemma hr_refl: forall h, heap_relation h h.
Proof.
  intros; split; auto.
Qed.

Lemma hr_trans: forall h1 h2 h3,
  heap_relation h1 h2 -> heap_relation h2 h3 -> heap_relation h1 h3.
Proof.
  intros ? ? ? [? ?] [? ?]; split; intros; congruence.
Qed.

Lemma tir_trans: forall t1 t2 t3,
    thread_info_relation t1 t2 -> thread_info_relation t2 t3 ->
    thread_info_relation t1 t3.
Proof.
  intros. destruct H as [? [? ?]], H0 as [? [? ?]].
  split; [|split]; [rewrite H; assumption | intros; rewrite H1; apply H3|
                   intros; rewrite H2; apply H4].
Qed.

Lemma forward_loop_add_tail: forall from to depth l intr g1 g2 g3,
    forward_loop from to depth l g1 g2 ->
    forward_relation from to depth (interior2forward intr g2) g2 g3 ->
    forward_loop from to depth (l +:: intr) g1 g3.
Proof.
  intros. revert intr g1 g2 g3 H H0. induction l; intros.
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

#[export] Instance interior_Inhabitant: Inhabitant interior_t := InteriorVertexPos (O, O) 0.

Lemma vpp_Znth: forall (x : VType) (g : LGraph) (i : Z),
    0 <= i < Zlength (raw_fields (vlabel g x)) ->
    Znth i (vertex_pos_pairs g x) = InteriorVertexPos x i.
Proof.
  intros. unfold vertex_pos_pairs.
  assert (0 <= i < Zlength (nat_inc_list (length (raw_fields (vlabel g x))))) by
      (rewrite Zlength_correct, nat_inc_list_length, <- Zlength_correct; assumption).
  rewrite Znth_map by assumption. do 2 f_equal. rewrite <- nth_Znth by assumption.
  rewrite nat_inc_list_nth. 1: rewrite Z2Nat.id; lia.
  rewrite <- ZtoNat_Zlength, <- Z2Nat.inj_lt; lia.
Qed.

Lemma forward_loop_add_tail_vpp: forall from to depth x g g1 g2 g3 i,
    0 <= i < Zlength (raw_fields (vlabel g x)) ->
    forward_loop from to depth (sublist 0 i (vertex_pos_pairs g x)) g1 g2 ->
    forward_relation from to depth
      (interior2forward (InteriorVertexPos x i) g2) g2 g3 ->
    forward_loop from to depth (sublist 0 (i + 1) (vertex_pos_pairs g x)) g1 g3.
Proof.
  intros. rewrite <- vpp_Zlength in H. rewrite sublist_last_1; [|lia..].
  rewrite vpp_Zlength in H. rewrite vpp_Znth by assumption.
  apply forward_loop_add_tail with (g2 := g2); assumption.
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
      from to O (interior2forward (InteriorVertexPos v (Z.of_nat i)) g1) g1 g2 ->
    scan_vertex_for_loop from to v il g2 g3 ->
    scan_vertex_for_loop from to v (i :: il) g1 g3.

Definition no_scan (g: LGraph) (v: VType): Prop := NO_SCAN_TAG <= (vlabel g v).(raw_tag).

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
  exists n, scan_vertex_while_loop from to (seq to_index n) g1 g2 /\
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

Lemma make_header_tag_prep64: forall z,
    0 <= z < two_p (8 * 8) ->
    Int64.and (Int64.repr z) (Int64.repr 255) =
    Int64.sub (Int64.repr z)
              (Int64.mul (Int64.repr (z / two_p 8)) (Int64.repr (two_p 8))).
Proof.
  intros. replace (Int64.repr 255) with (Int64.sub (Int64.repr 256) Int64.one) by
      now vm_compute.
  rewrite <- (Int64.modu_and _ _ (Int64.repr 8)) by now vm_compute.
  rewrite Int64.modu_divu by (vm_compute; intro S; inversion S).
  rewrite (Int64.divu_pow2 _ _ (Int64.repr 8)) by now vm_compute.
  rewrite (Int64.mul_pow2 _ _ (Int64.repr 8)) by now vm_compute.
  rewrite Int64.shru_div_two_p, !Int64.unsigned_repr; [| rep_lia | ].
  - rewrite Int64.shl_mul_two_p, Int64.unsigned_repr by rep_lia. easy.
  - simpl Z.mul in H. unfold Int64.max_unsigned, Int64.modulus.
    unfold Int64.wordsize, Wordsize_64.wordsize. rewrite two_power_nat_two_p.
    simpl Z.of_nat. lia.
Qed.

Lemma make_header_tag_prep32: forall z,
    0 <= z < two_p (4 * 8) ->
    Int.and (Int.repr z) (Int.repr 255) =
    Int.sub (Int.repr z)
              (Int.mul (Int.repr (z / two_p 8)) (Int.repr (two_p 8))).
Proof.
  intros. replace (Int.repr 255) with (Int.sub (Int.repr 256) Int.one) by
      now vm_compute.
  rewrite <- (Int.modu_and _ _ (Int.repr 8)) by now vm_compute.
  rewrite Int.modu_divu by (vm_compute; intro S; inversion S).
  rewrite (Int.divu_pow2 _ _ (Int.repr 8)) by now vm_compute.
  rewrite (Int.mul_pow2 _ _ (Int.repr 8)) by now vm_compute.
  rewrite Int.shru_div_two_p, !Int.unsigned_repr; [| rep_lia | ].
  - rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia. easy.
  - simpl Z.mul in H. unfold Int.max_unsigned, Int.modulus.
    unfold Int.wordsize, Wordsize_32.wordsize. rewrite two_power_nat_two_p.
    simpl Z.of_nat. lia.
Qed.

Lemma make_header_tag: forall g v,
    raw_mark (vlabel g v) = false ->
    if Archi.ptr64 then
        Int64.and (Int64.repr (make_header g v)) (Int64.repr 255) =
        Int64.repr (raw_tag (vlabel g v))
    else Int.and (Int.repr (make_header g v)) (Int.repr 255) =
         Int.repr (raw_tag (vlabel g v)).
Proof.
  intros. cbv delta [Archi.ptr64]. simpl.
  first [rewrite make_header_tag_prep32 | rewrite make_header_tag_prep64].
  2: apply make_header_range.
  unfold make_header in *. remember (vlabel g v). clear Heqr.
  rewrite H, !Zbits.Zshiftl_mul_two_p in * by lia. rewrite <- Z.add_assoc.
  replace (raw_color r * two_p 8 + Zlength (raw_fields r) * two_p 10)
    with ((raw_color r + Zlength (raw_fields r) * two_p 2) * two_p 8) by
      (rewrite Z.mul_add_distr_r, <- Z.mul_assoc, <- two_p_is_exp by lia;
       reflexivity). rewrite Z.div_add by (vm_compute; intros S; inversion S).
  assert (raw_tag r / two_p 8 = 0) by (apply Z.div_small, raw_tag_range).
  rewrite H0, Z.add_0_l.
  first [rewrite mul_repr, sub_repr | rewrite mul64_repr, sub64_repr].
  now rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
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

Lemma svfl_raw_tag: forall from to v l g g',
    graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, graph_has_v g x -> vgeneration x <> from ->
              raw_tag (vlabel g x) = raw_tag (vlabel g' x).
Proof.
  do 4 intro. revert from to v. induction l; intros; simpl; inversion H0; subst.
  1: reflexivity. assert (graph_has_gen g2 to) by
      (eapply fr_graph_has_gen in H5; [rewrite <- H5 |]; assumption).
  assert (graph_has_v g2 x) by (eapply fr_graph_has_v in H5; eauto).
  eapply (IHl from to _ g2) in H8; eauto. rewrite <- H8.
  eapply fr_raw_tag; eauto.
Qed.

Lemma svfl_add_tail: forall from to v l i g1 g2 g3,
    scan_vertex_for_loop from to v l g1 g2 ->
    forward_relation from to 0
      (interior2forward (InteriorVertexPos v (Z.of_nat i)) g2) g2 g3 ->
    scan_vertex_for_loop from to v (l +:: i) g1 g3.
Proof.
  do 4 intro. revert from to v. induction l; intros; inversion H; subst.
  - simpl. apply svfl_cons with g3. 1: assumption. constructor.
  - simpl app. apply svfl_cons with g4. 1: assumption. apply IHl with g2; assumption.
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
    In (ExteriorOutlier p) roots ->
    incl (filter_proj exterior_proj_outlier roots) outlier -> In p outlier.
Proof.
  intros. apply H0. rewrite <- (filter_proj_In_iff exterior_proj_outlier_spec).
  assumption.
Qed.

Definition do_generation_relation (from to: nat)
           (roots roots': roots_t) (g g': LGraph): Prop := exists g1 g2,
    forward_roots_relation from to roots g roots' g1 /\
    do_scan_relation from to (number_of_vertices (nth_gen g to)) g1 g2 /\
    g' = reset_graph from g2.

Definition space_address (heap_p: val) (gen: nat) :=
  offset_val (SPACE_STRUCT_SIZE * Z.of_nat gen) heap_p.

Definition enough_space_to_have_g g t_info from to: Prop :=
  graph_gen_size g from <= rest_gen_size t_info to.

Definition roots_frames_compatible (roots: roots_t) t_info: Prop :=
  Zlength roots = Zlength (frames2rootpairs (ti_frames t_info)).

Definition do_generation_condition g t_info (*roots*) from to: Prop :=
  enough_space_to_have_g g t_info from to /\ graph_has_gen g from /\
  graph_has_gen g to /\ copy_compatible g /\ no_dangling_dst g /\
  0 < available_size t_info to /\ gen_unmarked g to.

Lemma dgc_imply_fc: forall g t_info (*roots*) from to,
    do_generation_condition g t_info (*roots*) from to ->
    forward_condition g t_info from to /\ 0 < available_size t_info to /\
    gen_unmarked g to.
Proof.
  intros. destruct H. do 2 (split; [|intuition auto]). clear H0. red in H |-* .
  unfold general_enough_space_to_copy. transitivity (graph_gen_size g from); try assumption.
  rewrite Z.add_0_r. apply unmarked_gen_size_le.
Qed.

(*
Lemma upd_roots_Zlength: forall from to p g roots,
    Zlength (upd_roots from to p g roots) = Zlength roots.
Proof.
  intros. unfold upd_roots. destruct p. 2: reflexivity. list_solve.
Qed.
 *)

(*
Lemma frl_roots_Zlength: forall from to l roots g roots' g',
    forward_roots_loop from to l roots g roots' g' ->
    Zlength roots' = Zlength roots.
Proof.
  intros. induction H. 1: reflexivity. rewrite IHforward_roots_loop.
  apply upd_roots_Zlength; assumption.
Qed.

Opaque upd_roots.

Lemma frl_add_tail: forall from to l i g1 g2 g3 roots1 roots2,
    forward_roots_loop from to l roots1 g1 roots2 g2 ->
    forward_relation from to O (exterior2forward (Znth (Z.of_nat i) roots2)) g2 g3 ->
    forward_roots_loop
      from to (l +:: i) roots1 g1
      (upd_roots from to (inl (Z.of_nat i)) g2 roots2) g3.
Proof.
  intros ? ? ? ?. induction l; intros.
  - simpl. inversion H. subst. apply frl_cons with g3. 2: constructor. apply H0.
  - inversion H. subst. clear H. simpl app. apply frl_cons with g4. 1: assumption.
    apply IHl; assumption.
Qed.

Transparent upd_roots.
*)

Lemma frr_vertex_address: forall from to roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall v, closure_has_v g1 v -> vertex_address g1 v = vertex_address g2 v.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_relation.
  - eapply fr_vertex_address; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_closure_has_v; eauto.
Qed.

Lemma frr_closure_has_v: forall from to roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall v, closure_has_v g1 v -> closure_has_v g2 v.
Proof.
  intros. induction H0. 1: assumption. apply IHforward_roots_relation.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_closure_has_v; eauto.
Qed.

Lemma frr_gen_unmarked: forall from to roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall gen, gen <> from -> gen_unmarked g1 gen -> gen_unmarked g2 gen.
Proof.
  intros. induction H0. 1: assumption. apply IHforward_roots_relation.
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

Lemma graph_thread_info_compatible_reset: forall g h gen,
    graph_heap_compatible g h ->
    graph_heap_compatible (reset_graph gen g)
                                 (reset_nth_heap gen h).
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
      rewrite reset_nth_space_same by lia. intuition auto.
    + rewrite reset_nth_gen_info_diff, reset_nth_space_diff by assumption.
      destruct H as [? [? ?]]. split. 1: assumption. split. 1: assumption.
      rewrite pvs_reset_unchanged. assumption.
  - rewrite remove_ve_glabel_unchanged.
    destruct (le_lt_dec (length (spaces h)) gen).
    + rewrite reset_nth_space_overflow; assumption.
    + rewrite reset_nth_space_Znth by assumption. rewrite <- upd_Znth_map. simpl.
      remember (spaces h).
      assert (0 <= Z.of_nat gen < Zlength l0) by (rewrite Zlength_correct; lia).
      replace (space_start (Znth (Z.of_nat gen) l0))
        with (Znth (Z.of_nat gen) (map space_start l0)) by (rewrite Znth_map; auto).
      rewrite upd_Znth_unchanged; [|rewrite Zlength_map]; assumption.
  - rewrite remove_ve_glabel_unchanged, reset_nth_space_length. assumption.
Qed.

(*
Definition np_roots_rel from (roots roots': roots_t) (l: list Z) : Prop :=
  forall v j, Znth j roots' = ExteriorVertex v ->
         (In j l -> vgeneration v <> from) /\ (~ In j l -> Znth j roots = ExteriorVertex v).

Lemma upd_roots_not_pointing: forall from to i g roots roots',
    copy_compatible g -> roots_graph_compatible roots g -> from <> to ->
    0 <= i < Zlength roots ->
    roots' = upd_roots from to (ForwardPntRoot i) g roots ->
    np_roots_rel from roots roots' [i].
Proof.
  intros * ? ? ? ?. pose proof I. intros. unfold np_roots_rel. intros. simpl. unfold flip.
  assert (Zlength roots' = Zlength roots) by (rewrite H4; apply upd_roots_Zlength).
  assert (0 <= j < Zlength roots). {
    rewrite <- H6. destruct (Z_lt_le_dec j (Zlength roots')).
    2: rewrite Znth_outofbounds in H5 by lia; inversion H5. split; auto.
    destruct (Z_lt_le_dec j 0); auto. rewrite Znth_outofbounds in H5 by lia.
    inversion H5. }
  unfold upd_roots, upd_exterior in *.
  simpl in H4. destruct (Znth i roots) eqn:Heqr .
  - assert (roots' = roots) by (rewrite <- Heqr, upd_Znth_unchanged in H4; auto). clear H4.
    subst roots'. split; intros; auto. destruct H4; auto. congruence.
  - assert (roots' = roots) by (rewrite <- Heqr, upd_Znth_unchanged in H4; auto). clear H4.
    subst roots'. split; intros; auto. destruct H4; auto. congruence.
  - if_tac in H4.
    + destruct (raw_mark (vlabel g v0)) eqn: ?; subst; split; intros.
      * destruct H4; auto. subst.
        rewrite upd_Znth_same in H5 by auto.
        inversion H5. red in H0. rewrite Forall_forall in H0.
        assert (graph_has_v g v0). {
          apply H0. rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec), <- Heqr.
          apply Znth_In; assumption. }
        hnf in H. destruct (H _ H4 Heqb) as [_ ?]. auto.
      * assert (i<>j) by tauto. rewrite upd_Znth_diff in H5 by auto. auto.
      * destruct H4; auto. subst j. rewrite upd_Znth_same in H5 by assumption.
        inversion H5. unfold new_copied_v. simpl. auto.
      * assert (i<>j) by tauto. rewrite upd_Znth_diff in H5 by auto; auto.
    + rewrite <- Heqr in H4. rewrite upd_Znth_unchanged in H4 by auto. subst roots'.
      split; intros; auto. destruct H4; auto. congruence.
Qed.

Lemma np_roots_rel_cons: forall roots1 roots2 roots3 from i l,
    np_roots_rel from roots1 roots2 [i] ->
    np_roots_rel from roots2 roots3 l ->
    np_roots_rel from roots1 roots3 (i :: l).
Proof.
  intros. unfold np_roots_rel in *. intros. simpl. specialize (H0 _ _ H1).
  destruct H0. split; intros.
  - destruct H3; auto. subst.
    destruct (in_dec Z.eq_dec j l); auto.
    destruct (H v j (H2 n)). apply H3. hnf; auto.
  - apply Decidable.not_or in H3. destruct H3.
    specialize (H2 H4). specialize (H _ _ H2). destruct H. apply H5. simpl. tauto.
Qed.
 *)

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

Lemma fr_roots_graph_compatible: forall depth from to f g g' roots,
    graph_has_gen g to ->
    forward_relation from to depth f g g' ->
    roots_graph_compatible roots g -> roots_graph_compatible roots g'.
Proof.
  intros. unfold roots_graph_compatible in H1 |- *. rewrite Forall_forall in H1 |- *.
  intros. specialize (H1 _ H2). eapply fr_graph_has_v; eassumption.
Qed.

Lemma fl_edge_roots_graph_compatible: forall depth from to l g g' v roots,
    graph_has_gen g to ->
    forward_loop from to depth (map (fun x : nat => InteriorVertexPos v (Z.of_nat x)) l) g g' ->
    roots_graph_compatible roots g -> roots_graph_compatible roots g'.
Proof.
  do 4 intro. induction l; intros; simpl in H0; inversion H0; subst. 1: assumption.
  cut (roots_graph_compatible roots g2).
  - intros. apply (IHl g2 _ v); try assumption. rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_roots_graph_compatible; eassumption.
Qed.

Lemma upd_Znth_unchanged': forall {A} `{d: Inhabitant A} (i: Z) (al: list A),
   upd_Znth i al (Znth i al) = al.
Proof.
  intros.
  unfold upd_Znth. unfold Sumbool.sumbool_and.
  if_tac; auto.
  list_solve.
Qed.

Lemma fr_roots_outlier_compatible: forall from to i g roots outlier,
    roots_outlier_compatible roots outlier ->
    roots_outlier_compatible (upd_roots from to i g roots) outlier.
Proof.
  intros. unfold upd_roots.
  assert (roots_outlier_compatible (upd_Znth i roots (Znth i roots)) outlier)
    by (rewrite upd_Znth_unchanged'; assumption). unfold upd_exterior, update_vertex.
  destruct (Znth i roots) eqn: ?; auto. if_tac; auto.
  destruct (raw_mark (vlabel g v)); apply upd_roots_outlier_compatible; assumption.
Qed.

Lemma fr_upd_roots_graph_compatible: forall depth from to i g g' roots,
    graph_has_gen g to -> copy_compatible g ->
    0 <= i < Zlength roots ->
    forward_relation from to depth (exterior2forward (Znth i roots)) g g' ->
    from <> to -> roots_graph_compatible roots g ->
    roots_graph_compatible (upd_roots from to i g roots) g'.
Proof.
  intros depth from to i g g' roots Hghg Hcc Hir Hfr Hft Hrgc.
  unfold upd_roots, upd_exterior, update_vertex.
  destruct (Znth i roots) eqn:Heqr; simpl in Hfr;
    [rewrite <- Heqr; rewrite upd_Znth_unchanged'; inversion Hfr; subst; assumption..|].
  assert (graph_has_v g v). {
    red in Hrgc. rewrite Forall_forall in Hrgc. apply Hrgc.
    rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec), <- Heqr. now apply Znth_In. }
  inversion Hfr; destruct (Nat.eq_dec (vgeneration v) from);
    try contradiction; subst; try assumption.
  - rewrite <- Heqr, upd_Znth_unchanged'; assumption.
  - rewrite H3. apply upd_Znth_graph_compatible. 1: assumption. specialize (Hcc _ H H3).
    destruct Hcc; assumption.
  - destruct (raw_mark (vlabel g v)) eqn:? . 1: discriminate.
    apply lcv_roots_graph_compatible; assumption.
  - destruct (raw_mark (vlabel g v)) eqn:?; [discriminate|].
    remember (upd_Znth i roots (ExteriorVertex (new_copied_v g to))) as roots'.
    assert (roots_graph_compatible roots' new_g) by
      (subst; subst new_g; apply lcv_roots_graph_compatible; assumption).
    assert (raw_mark (vlabel new_g (new_copied_v g to)) = false). {
      subst new_g. unfold lgraph_copy_v. rewrite <- lmc_raw_mark.
      - rewrite lacv_vlabel_new. assumption.
      - unfold new_copied_v. destruct v. simpl in Hft. intro HS. inversion HS. lia. }
    assert (graph_has_v new_g (new_copied_v g to)) by
      (subst new_g; apply lcv_graph_has_v_new; assumption).
    unfold vertex_pos_pairs in H5.
    remember (nat_inc_list (length (raw_fields (vlabel new_g (new_copied_v g to))))).
    eapply (fl_edge_roots_graph_compatible
              depth0 (vgeneration v) to l new_g); try eassumption.
    subst new_g. rewrite <- lcv_graph_has_gen; assumption.
  - rewrite H2. apply lcv_roots_graph_compatible; assumption.
Qed.

Lemma fr_roots_compatible: forall depth from to i g g' roots outlier,
    0 <= i < Zlength roots ->
    graph_has_gen g to -> copy_compatible g ->
    forward_relation from to depth (exterior2forward (Znth i roots)) g g' ->
    roots_compatible g outlier roots -> from <> to ->
    roots_compatible g' outlier (upd_roots from to i g roots).
Proof.
  intros. destruct H3. split.
  - apply fr_roots_outlier_compatible; assumption.
  - eapply fr_upd_roots_graph_compatible; eassumption.
Qed.

(*
Lemma frl_not_pointing: forall from to (*t_info*) l roots1 g1 roots2 g2,
    copy_compatible g1 -> roots_graph_compatible roots1 g1 -> from <> to ->
    (forall i, In i l -> i < length roots1)%nat ->
    forward_roots_loop from to l roots1 g1 roots2 g2 -> graph_has_gen g1 to ->
    np_roots_rel from roots1 roots2 (map Z.of_nat l).
Proof.
  do 3 intro. induction l; intros; inversion H3; subst.
  1: red; simpl; intros; intuition.
  remember (upd_roots from to (inl (Z.of_nat a)) g1 roots1) as roots3.
  simpl. apply np_roots_rel_cons with roots3.
  - apply (upd_roots_not_pointing from to _ g1); try assumption.
    split. 1: lia. rewrite Zlength_correct. apply inj_lt. apply H2. left; auto.
  - assert (Zlength roots3 = Zlength roots1) by
        (subst roots3; apply upd_roots_Zlength; apply (proj1 H3)).
    apply (IHl _ g3 _ g2); auto.
    + apply fr_copy_compatible in H7; assumption.
    + subst roots3. eapply fr_roots_graph_compatible; eauto. simpl. split. 1: lia.
      specialize (H2 _ (in_eq a l)). rewrite Zlength_correct. apply inj_lt; assumption.
    + intros. subst roots3. rewrite <- ZtoNat_Zlength, H5, ZtoNat_Zlength.
      apply H2; right; assumption.
    + rewrite <- (fr_graph_has_gen _ _ _ _ _ _ H4 H7); assumption.
Qed.
*)

Definition roots_have_no_gen (roots: roots_t) (gen: nat): Prop :=
  forall v, In (ExteriorVertex v) roots -> vgeneration v <> gen.

Lemma roots_graph_compatible_inv: forall r roots g,
    roots_graph_compatible (r :: roots) g -> roots_graph_compatible roots g.
Proof.
  intros r roots g. unfold roots_graph_compatible. rewrite filter_proj_cons.
  destruct r; simpl; try tauto. rewrite Forall_cons_iff. tauto.
Qed.

Lemma rgc_cons_vertex: forall v roots g,
    roots_graph_compatible (ExteriorVertex v :: roots) g -> graph_has_v g v.
Proof.
  intros v roots g. unfold roots_graph_compatible. rewrite filter_proj_cons. simpl.
  rewrite Forall_cons_iff. tauto.
Qed.

Lemma frr_not_pointing: forall from to roots1 g1 roots2 g2,
    copy_compatible g1 -> roots_graph_compatible roots1 g1 -> from <> to ->
    graph_has_gen g1 to ->
    forward_roots_relation from to roots1 g1 roots2 g2 ->
    roots_have_no_gen roots2 from.
Proof.
  intros.
  revert H H0 H2; induction H3; intros. 1: intros ? Hx; inv Hx.
  intros ? ?. destruct H5.
  - clear IHforward_roots_relation. destruct r; simpl in H5; try discriminate.
    unfold update_vertex in H5. destruct (Nat.eq_dec _ _).
    + destruct (raw_mark _) eqn:?H; inversion H5; subst.
      * hnf in H2. rewrite filter_proj_cons in H2. simpl in H2.
        rewrite Forall_cons_iff in H2. destruct H2. destruct (H0 _ H2 H6).
        symmetry. assumption.
      * unfold new_copied_v. simpl. symmetry. assumption.
    + inversion H5. subst. assumption.
  - apply IHforward_roots_relation; auto.
    + eapply fr_copy_compatible; eassumption.
    + cut (roots_graph_compatible roots1 g1).
      * intros. eapply fr_roots_graph_compatible; eassumption.
      * eapply roots_graph_compatible_inv; eassumption.
    + erewrite <- fr_graph_has_gen; eassumption.
Qed.

Lemma fta_compatible_reset: forall g rootpairs r gen,
    rootpairs_compatible g rootpairs r ->
    rootpairs_compatible (reset_graph gen g) rootpairs r.
Proof.
  intros. unfold rootpairs_compatible in *.
  rewrite <- H.
  clear H.
  induction r; simpl; f_equal; auto.
  clear.
  destruct a; simpl; auto.
  apply vertex_address_reset.
Qed.

Lemma gen_has_index_reset: forall (g: LGraph) gen1 gen2 idx,
    gen_has_index (reset_graph gen1 g) gen2 idx <->
    gen_has_index g gen2 idx /\ gen1 <> gen2.
Proof.
  intros. unfold gen_has_index. unfold nth_gen. simpl.
  rewrite remove_ve_glabel_unchanged. destruct (Nat.eq_dec gen1 gen2).
  - subst. rewrite reset_nth_gen_info_same. simpl. intuition auto with *.
  - rewrite reset_nth_gen_info_diff by auto. intuition auto.
Qed.

Lemma graph_has_v_reset: forall (g: LGraph) gen v,
    graph_has_v (reset_graph gen g) v <->
    graph_has_v g v /\ gen <> vgeneration v.
Proof.
  intros. split; intros; destruct v; unfold graph_has_v in *; simpl in *.
  - rewrite graph_has_gen_reset, gen_has_index_reset in H. intuition auto.
  - rewrite graph_has_gen_reset, gen_has_index_reset. intuition auto.
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
    rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec) in H1. apply H0 in H1. auto.
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

Lemma super_compatible_reset: forall g h rootpairs roots outlier gen,
    roots_have_no_gen roots gen ->
    super_compatible g h rootpairs roots outlier ->
    super_compatible (reset_graph gen g) (reset_nth_heap gen h) rootpairs roots outlier.
Proof.
  intros. destruct H0 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply graph_thread_info_compatible_reset; assumption.
  - apply fta_compatible_reset; assumption.
  - apply roots_compatible_reset; assumption.
  - apply outlier_compatible_reset; assumption.
Qed.

(*
Lemma heaprel_reset: forall h gen,
  heap_relation h (reset_nth_heap gen h).
Proof.
    intros. red. unfold gen_size, nth_space. simpl.
    destruct (le_lt_dec (length (spaces h)) gen).
    - rewrite reset_nth_space_overflow by assumption. split; intros; reflexivity.
    - split; intros; destruct (Nat.eq_dec n gen).
      + subst. rewrite reset_nth_space_same; simpl; [reflexivity | assumption].
      + rewrite reset_nth_space_diff; [reflexivity | assumption].
      + subst. rewrite reset_nth_space_same; simpl; [reflexivity | assumption].
      + rewrite reset_nth_space_diff; [reflexivity | assumption].
Qed.
 *)

Lemma frr_graph_has_gen: forall from to roots1 g1 roots2 g2,
    graph_has_gen g1 to ->
    forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall gen, graph_has_gen g1 gen <-> graph_has_gen g2 gen.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_relation.
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

Lemma do_gen_graph_has_gen: forall from to roots roots' g g',
    graph_has_gen g to ->
    do_generation_relation from to roots roots' g g' ->
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

Lemma do_gen_graph_unmarked: forall from to roots roots' g g',
    graph_has_gen g to ->
    do_generation_relation from to roots roots' g g' ->
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
  rewrite graph_has_v_reset, get_edges_reset. intuition auto.
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
    forward_relation from to O (exterior2forward r) g g' ->
    forall e, graph_has_v g (fst e) -> dst g e = dst g' e.
Proof.
  intros. destruct r; simpl in H; inversion H; subst; try reflexivity;
   (simpl; rewrite pcv_dst_old; [ reflexivity |  destruct e as [[gen vidx] eidx]];
    unfold graph_has_v in H0; unfold new_copied_v; simpl in *; destruct H0; intro;
     inversion H2; subst; red in H1; lia).
Qed.

Lemma frr_dst_unchanged: forall from to roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall e, graph_has_v g1 (fst e) -> dst g1 e = dst g2 e.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_relation.
  - eapply fr_O_dst_unchanged_root; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_graph_has_v; eauto.
Qed.

Lemma fr_O_graph_has_v_inv: forall from to p g g',
    graph_has_gen g to -> forward_relation from to O p g g' ->
    forall v, graph_has_v g' v -> graph_has_v g v \/ v = new_copied_v g to.
Proof.
  intros. inversion H0; subst;try (left; assumption);
   try (subst new_g; rewrite <- lgd_graph_has_v in H1);
   apply lcv_graph_has_v_inv in H1; assumption.
Qed.

Definition gen_v_num (g: LGraph) (gen: nat): nat := number_of_vertices (nth_gen g gen).

Definition nth_gen_size (n: nat) := NURSERY_SIZE * two_p (Z.of_nat n).

(* TODO available_size needs to be changed to gen_size *)
Definition nth_gen_size_spec (h: heap) (n: nat): Prop :=
  if Val.eq (nth_space h n).(space_start) nullval
  then True
  else available_size h n = nth_gen_size n.

Definition ti_size_spec (h: heap): Prop :=
  Forall (nth_gen_size_spec h) (nat_inc_list (Z.to_nat MAX_SPACES)).

(* TODO nth_gen_size to needs to be changed to available size*)
Definition safe_to_copy_gen g from to: Prop :=
  nth_gen_size from <= nth_gen_size to - graph_gen_size g to.

Lemma ngs_range: forall i,
    0 <= i < MAX_SPACES -> 0 <= nth_gen_size (Z.to_nat i) <= MAX_SPACE_SIZE.
Proof.
  intros. unfold nth_gen_size. rewrite MAX_SPACES_eq in H.
  rewrite Z2Nat.id, NURSERY_SIZE_eq, Zbits.Zshiftl_mul_two_p,
  Z.mul_1_l, <- two_p_is_exp by lia. split.
  - cut (two_p (16 + i) > 0). 1: intros; lia. apply two_p_gt_ZERO. lia.
  - unfold MAX_SPACE_SIZE.
  rewrite Zbits.Zshiftl_mul_two_p by lia. rewrite two_p_is_exp by lia.
  rewrite Z.mul_1_l.
  match goal with |- two_p ?k * _ <= two_p ?m =>
     change m with (k + (m-k))
  end.
  rewrite two_p_is_exp by lia.
  simpl Z.sub.
  apply Z.mul_le_mono_pos_l. reflexivity.
  apply two_p_monotone. simpl. lia.
Qed.

Lemma ngs_int_signed_range: forall i,
    0 <= i < MAX_SPACES ->
    (if Archi.ptr64 then Int64.min_signed else Int.min_signed) <=
    nth_gen_size (Z.to_nat i) <=
    (if Archi.ptr64 then Int64.max_signed else Int.max_signed).
Proof.
  intros. apply ngs_range in H. destruct H. split.
  - transitivity 0. 2: assumption. vm_compute. intro HS; inversion HS.
  - transitivity MAX_SPACE_SIZE. 1: assumption.
    intro; discriminate.
Qed.

Lemma ngs_S: forall i,
    0 <= i -> 2 * nth_gen_size (Z.to_nat i) = nth_gen_size (Z.to_nat (i + 1)).
Proof.
  intros. unfold nth_gen_size. rewrite !Z2Nat.id by lia.
  rewrite Z.mul_comm, <- Z.mul_assoc, (Z.mul_comm (two_p i)), <- two_p_S by assumption.
  reflexivity.
Qed.

Lemma space_start_isptr: forall (g: LGraph) (h: heap) i,
    graph_heap_compatible g h ->
    0 <= i < Zlength (spaces h) ->
    graph_has_gen g (Z.to_nat i) ->
    isptr (space_start (Znth i (spaces h))).
Proof.
  intros. destruct (gt_gs_compatible _ _ H _ H1) as [? _].
  rewrite nth_space_Znth in H2. rewrite Z2Nat.id in H2 by lia. rewrite <- H2.
  apply start_isptr.
Qed.

Lemma space_start_isnull: forall (g: LGraph) (h: heap) i,
    graph_heap_compatible g h ->
    0 <= i < Zlength (spaces h) ->
    ~ graph_has_gen g (Z.to_nat i) ->
    space_start (Znth i (spaces h)) = nullval.
Proof.
  intros. unfold graph_has_gen in H1. destruct H as [_ [? ?]].
  rewrite Forall_forall in H. symmetry. apply H. rewrite <- map_skipn.
  apply List.in_map. remember (g_gen (glabel g)).
  replace i with (i - Zlength l + Zlength l) by lia.
  assert (length l <= Z.to_nat i)%nat by lia. clear H1.
  assert (0 <= i - Zlength l) by
      (rewrite <- ZtoNat_Zlength, <- Z2Nat.inj_le in H3; rep_lia).
  rewrite <- Znth_skipn by rep_lia. rewrite ZtoNat_Zlength.
  apply Znth_In. split. 1: assumption. rewrite <- ZtoNat_Zlength, Zlength_skipn.
  rewrite (Z.max_r 0 (Zlength l)) by rep_lia. rewrite Z.max_r; rep_lia.
Qed.

Lemma space_start_is_pointer_or_null: forall (g: LGraph) (h: heap) i,
    graph_heap_compatible g h ->
    0 <= i < Zlength (spaces h) ->
    is_pointer_or_null (space_start (Znth i (spaces h))).
Proof.
  intros. destruct (graph_has_gen_dec g (Z.to_nat i)).
  - apply val_lemmas.isptr_is_pointer_or_null. eapply space_start_isptr; eauto.
  - cut (space_start (Znth i (spaces h)) = nullval).
    + intros. rewrite H1. apply mapsto_memory_block.is_pointer_or_null_nullval.
    + eapply space_start_isnull; eauto.
Qed.

Lemma space_start_isptr_iff: forall (g: LGraph) (h: heap) i,
    graph_heap_compatible g h ->
    0 <= i < Zlength (spaces h) ->
    graph_has_gen g (Z.to_nat i) <->
    isptr (space_start (Znth i (spaces h))).
Proof.
  intros. split; intros.
  - eapply space_start_isptr; eauto.
  - destruct (graph_has_gen_dec g (Z.to_nat i)). 1: assumption. exfalso.
    eapply space_start_isnull in n; eauto. rewrite n in H1. inversion H1.
Qed.

Lemma space_start_isnull_iff: forall (g: LGraph) (h: heap) i,
    graph_heap_compatible g h ->
    0 <= i < Zlength (spaces h) ->
    ~ graph_has_gen g (Z.to_nat i) <->
    space_start (Znth i (spaces h)) = nullval.
Proof.
  intros. split; intros. 1: eapply space_start_isnull; eauto.
  destruct (graph_has_gen_dec g (Z.to_nat i)). 2: assumption. exfalso.
  eapply space_start_isptr in g0; eauto. rewrite H1 in g0. inversion g0.
Qed.

(* TODO Change later *)
Lemma ti_size_gen: forall (g : LGraph) (h : heap) (gen : nat),
    graph_heap_compatible g h ->
    graph_has_gen g gen -> ti_size_spec h ->
    available_size h gen = nth_gen_size gen.
Proof.
  intros. red in H1. rewrite Forall_forall in H1.
  assert (0 <= (Z.of_nat gen) < Zlength (spaces h)). {
    split. 1: rep_lia. rewrite Zlength_correct. apply inj_lt.
    destruct H as [_ [_ ?]]. red in H0. lia. }
  assert (nth_gen_size_spec h gen). {
    apply H1. rewrite nat_inc_list_In_iff. destruct H as [_ [_ ?]]. red in H0.
    rewrite <- (spaces_size h), ZtoNat_Zlength. lia. } red in H3.
  destruct (Val.eq (space_start (nth_space h gen)) nullval). 2: assumption.
  rewrite nth_space_Znth in e. erewrite <- space_start_isnull_iff in e; eauto.
  unfold graph_has_gen in e. exfalso; apply e. rewrite Nat2Z.id. assumption.
Qed.

(* TODO *)
Lemma ti_size_gt_0: forall (g : LGraph) (h : heap) (gen : nat),
    graph_heap_compatible g h ->
    graph_has_gen g gen -> ti_size_spec h -> 0 < available_size h gen.
Proof.
  intros. erewrite ti_size_gen; eauto. unfold nth_gen_size. apply Z.mul_pos_pos.
  - rewrite NURSERY_SIZE_eq. vm_compute. reflexivity.
  - cut (two_p (Z.of_nat gen) > 0). 1: lia. apply two_p_gt_ZERO. lia.
Qed.

Local Close Scope Z_scope.

Lemma lcv_gen_v_num_to: forall g v to,
    graph_has_gen g to -> gen_v_num g to <= gen_v_num (lgraph_copy_v g v to) to.
Proof.
  intros. unfold gen_v_num, nth_gen; simpl. rewrite cvmgil_eq by assumption.
  simpl. lia.
Qed.

Lemma lgd_gen_v_num_to: forall g e v to,
    gen_v_num (labeledgraph_gen_dst g e v) to = gen_v_num g to.
Proof. intros. reflexivity. Qed.

Lemma fr_O_gen_v_num_to: forall from to p g g',
    graph_has_gen g to -> forward_relation from to O p g g' ->
    gen_v_num g to <= gen_v_num g' to.
Proof.
  intros. inversion H0; subst; try lia; try subst new_g.
  - apply lcv_gen_v_num_to; auto.
  - rewrite lgd_gen_v_num_to. lia.
  - rewrite lgd_gen_v_num_to. apply lcv_gen_v_num_to. assumption.
Qed.

Lemma frr_gen_v_num_to: forall from to roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to roots1 g1 roots2 g2 ->
    gen_v_num g1 to <= gen_v_num g2 to.
Proof.
  intros. induction H0. 1: lia. transitivity (gen_v_num g2 to).
  - eapply fr_O_gen_v_num_to; eauto.
  - apply IHforward_roots_relation; rewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma frr_graph_has_v_inv: forall from to roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall v, graph_has_v g2 v -> graph_has_v g1 v \/
                                  (vgeneration v = to /\
                                   gen_v_num g1 to <= vindex v < gen_v_num g2 to).
Proof.
  intros. induction H0. 1: left; assumption.
  assert (graph_has_gen g2 to) by (rewrite <- fr_graph_has_gen; eauto).
  specialize (IHforward_roots_relation H3 H1). destruct IHforward_roots_relation.
  - eapply (fr_O_graph_has_v_inv from to _ g1 g2) in H0; eauto. destruct H0.
    1: left; assumption. right. unfold new_copied_v in H0. subst v.
    clear H2. destruct H1. red in H1. simpl in *. unfold gen_v_num. lia.
  - right. destruct H4. split. 1: assumption. destruct H5. split. 2: assumption.
    apply fr_O_gen_v_num_to in H0; [lia | assumption].
Qed.

Lemma frr_raw_fields: forall from to roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall v, graph_has_v g1 v -> raw_fields (vlabel g1 v) = raw_fields (vlabel g2 v).
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_relation.
  - eapply fr_raw_fields; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_graph_has_v; eauto.
Qed.

Lemma frr_gen2gen_no_edge: forall from to roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to roots1 g1 roots2 g2 ->
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
    (0 <= Z.of_nat n < Zlength (raw_fields (vlabel g v)))%Z ->
    forward_relation from to O (field2forward (Znth (Z.of_nat n) (make_fields g v))) g g' ->
    forall e, graph_has_v g (fst e) -> e <> (v, n) -> dst g e = dst g' e.
Proof.
  intros. remember (Znth (Z.of_nat n) (make_fields g v)).
  assert (forall e0, FieldEdge e0 = Znth (Z.of_nat n) (make_fields g v) -> e0 <> e). {
    intros. symmetry in H3. apply make_fields_Znth_edge in H3. 2: assumption.
    rewrite Nat2Z.id in H3. rewrite <- H3 in H2. auto. }
  destruct f; simpl in H0; inversion H0; subst; try reflexivity.
  - subst new_g. rewrite lgd_dst_old. 1: reflexivity. apply H3; assumption.
  - subst new_g. rewrite lgd_dst_old. 2: apply H3; assumption. simpl.
    rewrite pcv_dst_old. 1: reflexivity. intro. rewrite H4 in H1. destruct H1.
    unfold new_copied_v in H5. simpl in H5. red in H5. lia.
Qed.

Lemma svfl_dst_unchanged: forall from to v l g1 g2,
    graph_has_v g1 v -> raw_mark (vlabel g1 v) = false ->
    (raw_tag (vlabel g1 v) < NO_SCAN_TAG)%Z -> vgeneration v <> from ->
    (forall i,  In i l -> i < length (raw_fields (vlabel g1 v))) ->
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall e, graph_has_v g1 (fst e) -> (forall i, In i l -> e <> (v, i)) ->
              dst g1 e = dst g2 e.
Proof.
  intros ? ? ? ?. induction l; intros; inversion H5; subst. 1: reflexivity.
  transitivity (dst g3 e).
  - eapply fr_O_dst_unchanged_field; eauto.
    + simpl. intuition auto with *. rewrite Zlength_correct. apply inj_lt. apply H3.
      left; reflexivity.
    + apply H7. left; reflexivity.
  - apply IHl; auto.
    + eapply fr_graph_has_v; eauto.
    + erewrite <- fr_raw_mark; eauto.
    + erewrite <- fr_raw_tag; eauto.
    + intros. erewrite <- fr_raw_fields; eauto. apply H3. right; assumption.
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_graph_has_v; eauto.
    + intros. apply H7. right; assumption.
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
      * unfold no_scan in H5. lia.
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
  intros ? ? ? ?. induction l; intros; inversion H0; subst. 1: lia.
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
    destruct H1. unfold gen_v_num. simpl in *. red in H0. lia.
  - right. destruct H3. split. 1: assumption. destruct H5. split; auto.
    eapply fr_O_gen_v_num_to in H4; [lia | assumption].
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
  intros ? ? ?. induction l; intros; inversion H0; subst. 1: lia.
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
    apply svwl_gen_v_num_to in H9; [lia | assumption].
  - right. destruct H3 as [? [? ?]]. split; [|split]; try assumption.
    apply svfl_gen_v_num_to in H6; [lia | assumption].
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

Lemma frr_graph_has_v: forall from to roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall v, graph_has_v g1 v -> graph_has_v g2 v.
Proof.
  intros. induction H0; subst. 1: assumption. cut (graph_has_v g2 v).
  - intros. apply IHforward_roots_relation; auto. erewrite <- fr_graph_has_gen; eauto.
  - eapply fr_graph_has_v; eauto.
Qed.

Lemma fr_O_dst_changed_field: forall from to v n g g',
    copy_compatible g -> no_dangling_dst g -> from <> to -> graph_has_gen g to ->
    interior_compatible g from (InteriorVertexPos v (Z.of_nat n)) ->
    forward_relation from to O
      (interior2forward (InteriorVertexPos v (Z.of_nat n)) g) g g' ->
    forall e, Znth (Z.of_nat n) (make_fields g' v) = FieldEdge e -> vgeneration (dst g' e) <> from.
Proof.
  intros. simpl in *. destruct H3 as [? [? [? ?]]].
  assert (make_fields g v = make_fields g' v) by
      (unfold make_fields; erewrite fr_raw_fields; eauto). rewrite <- H9 in *.
  clear H9. remember (Znth (Z.of_nat n) (make_fields g v)). destruct f; inversion H5.
  subst. clear H5. symmetry in Heqf. pose proof Heqf.
  apply make_fields_Znth_edge in Heqf. 2: assumption. simpl in H4. subst.
  rewrite Nat2Z.id in *.
  inversion H4; subst; try assumption; subst new_g; rewrite lgd_dst_new.
  - apply H in H12. 1: destruct H12; auto. specialize (H0 _ H3). apply H0.
    rewrite get_edges_In_iff, <- H5. apply Znth_In.
    rewrite make_fields_eq_length. assumption.
  - unfold new_copied_v. simpl. auto.
Qed.

Definition forward_t_compatible (p: forward_t) (g: LGraph) :=
  match p with
  | ForwardVertex v => graph_has_v g v
  | ForwardEdge e => graph_has_e g e
  | _ => True
  end.

Lemma fr_O_no_dangling_dst: forall from to p g g',
    forward_t_compatible p g ->
    graph_has_gen g to ->
    copy_compatible g ->
    forward_relation from to O p g g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  intros. destruct p; inversion H2; subst; clear H2; try assumption.
  - apply lcv_no_dangling_dst; assumption.
  - subst new_g. apply lgd_no_dangling_dst; [|assumption]. destruct H.
    specialize (H3 _ H _ H2). destruct (H1 (dst g e) H3 H7). assumption.
  - subst new_g. apply lgd_no_dangling_dst.
    + apply lcv_graph_has_v_new. assumption.
    + apply lcv_no_dangling_dst; [assumption..|]. destruct H. apply (H3 _ H _ H2).
Qed.

Lemma vertex_pos_forward_t_compatible: forall g v i,
    graph_has_v g v -> (0 <= i < Zlength (raw_fields (vlabel g v)))%Z ->
    forward_t_compatible (field2forward (Znth i (make_fields g v))) g.
Proof.
  intros. destruct (Znth i (make_fields g v)) eqn: ?H; simpl; [exact I..|]. pose proof H1.
  apply make_fields_Znth_edge in H1; [|assumption]. subst. hnf. simpl. split; [assumption|].
  rewrite get_edges_In_iff, <- H2. apply Znth_In; rewrite make_fields_eq_length. assumption.
Qed.

Definition is_field_same_v (g: LGraph) (v: VType) (p: interior_t) : Prop :=
  exists i : Z, p = InteriorVertexPos v i /\ (0 <= i < Zlength (make_fields g v))%Z.

Lemma fr_is_field_same_v: forall (from to depth: nat) p (g1 g2: LGraph) (v: VType) l,
    graph_has_gen g1 to ->
    graph_has_v g1 v ->
    forward_relation from to depth p g1 g2 ->
    Forall (is_field_same_v g1 v) l <-> Forall (is_field_same_v g2 v) l.
Proof.
  intros. cut (Zlength (make_fields g1 v) = Zlength (make_fields g2 v)).
  - intros. unfold is_field_same_v. rewrite H2. tauto.
  - rewrite !make_fields_eq_length. f_equal. eapply fr_raw_fields; eassumption.
Qed.

Lemma fl_no_dangling_dst_helper: forall (from to depth: nat) (g' : LGraph) (vv : VType)
                                   (l : list interior_t) (gg : LGraph),
    from <> to ->
    (forall (p : forward_t) (g g' : LGraph),
        forward_t_compatible p g -> graph_has_gen g to -> copy_compatible g ->
        forward_relation from to depth p g g' -> no_dangling_dst g -> no_dangling_dst g') ->
    graph_has_gen gg to ->
    graph_has_v gg vv ->
    copy_compatible gg ->
    no_dangling_dst gg ->
    Forall (is_field_same_v gg vv) l ->
    forward_loop from to depth l gg g' -> no_dangling_dst g'.
Proof.
  intros from to depth g' vv l gg Hft IHdepth. revert gg g'.
  induction l; intros; inversion H4; subst; clear H4; auto. apply (IHl g2); auto.
  - rewrite <- fr_graph_has_gen; eassumption.
  - eapply fr_graph_has_v; eassumption.
  - eapply fr_copy_compatible; eassumption.
  - specialize (IHdepth (interior2forward a gg) gg g2). apply IHdepth; try assumption.
    inversion H3. subst. destruct H6 as [i [? ?]]. subst. simpl.
    apply vertex_pos_forward_t_compatible; auto. now rewrite <- make_fields_eq_length.
  - rewrite Forall_cons_iff in H3. destruct H3. rewrite <- fr_is_field_same_v; eassumption.
Qed.

Lemma vertex_pos_pairs_in_range: forall (v : VType) (g : LGraph),
    Forall (is_field_same_v g v) (vertex_pos_pairs g v).
Proof.
  intros. rewrite Forall_forall. intros. apply In_Znth in H. destruct H as [idx [? ?]].
  rewrite vpp_Zlength in H. hnf. rewrite make_fields_eq_length.
  rewrite vpp_Znth in H0; [|assumption]. exists idx. split; easy.
Qed.

Lemma fr_no_dangling_dst: forall from to depth p g g',
    from <> to ->
    forward_t_compatible p g ->
    graph_has_gen g to ->
    copy_compatible g ->
    forward_relation from to depth p g g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  intros from to depth p g g' Hft. revert depth p g g'.
  induction depth; [ apply fr_O_no_dangling_dst |].
  destruct p; intros; inversion H2; subst; clear H2; try assumption.
  - eapply fl_no_dangling_dst_helper with (gg := new_g); try eassumption; subst new_g.
    + apply lcv_graph_has_gen; assumption.
    + apply lcv_graph_has_v_new. assumption.
    + apply lcv_copy_compatible; assumption.
    + apply lcv_no_dangling_dst; assumption.
    + apply vertex_pos_pairs_in_range.
  - apply lcv_no_dangling_dst; assumption.
  - subst new_g. apply lgd_no_dangling_dst; [|assumption]. destruct H.
    specialize (H3 _ H _ H2). destruct (H1 (dst g e) H3 H7). assumption.
  - eapply fl_no_dangling_dst_helper with (gg := new_g); try eassumption; subst new_g.
    + rewrite lgd_graph_has_gen. apply lcv_graph_has_gen; assumption.
    + rewrite <- lgd_graph_has_v. apply lcv_graph_has_v_new. assumption.
    + apply lgd_copy_compatible. apply lcv_copy_compatible; assumption.
    + apply lgd_no_dangling_dst; [apply lcv_graph_has_v_new; assumption|].
      apply lcv_no_dangling_dst; [assumption..|]. destruct H. apply (H3 _ H _ H2).
    + apply vertex_pos_pairs_in_range.
  - subst new_g. apply lgd_no_dangling_dst.
    * apply lcv_graph_has_v_new. assumption.
    * apply lcv_no_dangling_dst; [assumption..|]. destruct H. apply (H3 _ H _ H2).
Qed.

Lemma fr_O_no_dangling_dst': forall from to p g g',
    forward_p_compatible' p g from ->
    graph_has_gen g to ->
    copy_compatible g ->
    forward_relation from to O (forward_p2forward_t p g) g g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  intros. eapply fr_O_no_dangling_dst; eauto. destruct p; simpl.
  - destruct extr; simpl; auto.
  - destruct intr as [v i].  simpl in H. destruct H as [? [? [? [? ?]]]]. simpl.
    apply vertex_pos_forward_t_compatible; assumption.
Qed.

Lemma svfl_dst_changed: forall from to v l g1 g2,
    graph_has_v g1 v -> raw_mark (vlabel g1 v) = false ->
    (raw_tag (vlabel g1 v) < NO_SCAN_TAG)%Z ->
    vgeneration v <> from ->
    copy_compatible g1 -> no_dangling_dst g1 -> from <> to ->
    (forall i,  In i l -> i < length (raw_fields (vlabel g1 v))) -> NoDup l ->
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall e i, In i l -> Znth (Z.of_nat i) (make_fields g2 v) = FieldEdge e ->
           vgeneration (dst g2 e) <> from.
Proof.
  intros ? ? ? ?. induction l; intros ? ? ? ? SCAN; intros; inversion H8; subst.
  1: inversion H9.
  assert (e = (v, i)). {
    apply make_fields_Znth_edge in H10. 1: rewrite Nat2Z.id in H10; assumption.
    split. 1: lia. rewrite Zlength_correct. apply inj_lt.
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
      * erewrite <- fr_raw_tag; eauto.
      * subst e; simpl; assumption.
      * intros. subst e. intro. inversion H11. subst. apply NoDup_cons_2 in H6.
        contradiction.
    + eapply (fr_O_dst_changed_field from to); eauto.
      * simpl. intuition auto with *. rewrite Zlength_correct. apply inj_lt. apply H5.
        left; reflexivity.
      * unfold make_fields in H8 |-*. erewrite svfl_raw_fields; eauto.
  - eapply (IHl g3); eauto.
    + erewrite <- fr_raw_tag; eauto.
    + eapply (fr_copy_compatible _ _ _ _ g1); eauto.
    + eapply (fr_O_no_dangling_dst' from to
                (FwdPntIntr (InteriorVertexPos v (Z.of_nat a))) g1); eauto. simpl.
      intuition auto with *. rewrite Zlength_correct. apply inj_lt. apply H5. now left.
    + apply NoDup_cons_1 in H6; assumption.
Qed.

Lemma svfl_no_edge2from: forall from to v g1 g2,
    graph_has_v g1 v -> raw_mark (vlabel g1 v) = false ->
    (raw_tag (vlabel g1 v) < NO_SCAN_TAG)%Z ->
    vgeneration v <> from ->
    copy_compatible g1 -> no_dangling_dst g1 -> from <> to -> graph_has_gen g1 to ->
    scan_vertex_for_loop
      from to v (nat_inc_list (length (raw_fields (vlabel g1 v)))) g1 g2 ->
    forall e, In e (get_edges g2 v) -> vgeneration (dst g2 e) <> from.
Proof.
  intros ? ? ?  ? ? ? ? SCAN; intros. rewrite get_edges_In_iff in H7.
  apply In_Znth in H7. destruct H7 as [i [? ?]].
  rewrite <- (Z2Nat.id i) in H8 by lia. eapply svfl_dst_changed; eauto.
  - intros. rewrite nat_inc_list_In_iff in H9. assumption.
  - apply nat_inc_list_NoDup.
  - rewrite nat_inc_list_In_iff. rewrite make_fields_eq_length in H7.
    erewrite svfl_raw_fields; eauto. rewrite <- ZtoNat_Zlength.
    apply Z2Nat.inj_lt; lia.
Qed.

Lemma no_scan_no_edge: forall g v, no_scan g v -> get_edges g v = nil.
Proof.
  intros. unfold no_scan in H. apply tag_no_scan in H. unfold get_edges.
  destruct (filter_proj field_proj_edge (make_fields g v)) eqn:? . 1: reflexivity. exfalso.
  assert (In e (e :: l)) by (left; auto).
  rewrite <- Heql, <- (filter_proj_In_iff field_proj_edge_spec) in H0. clear l Heql.
  apply H. clear H. unfold make_fields in H0. remember (raw_fields (vlabel g v)). clear Heql.
  remember O. clear Heqn. revert n H0. induction l; simpl; intros; auto.
  destruct a; simpl in H0;
    [left | right; destruct H0; [inversion H | eapply IHl; eauto]..]; auto.
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
    graph_has_v g1 v -> raw_mark (vlabel g1 v) = false ->
    (raw_tag (vlabel g1 v) < NO_SCAN_TAG)%Z ->
    vgeneration v <> from ->
    copy_compatible g1 -> graph_has_gen g1 to -> from <> to ->
    scan_vertex_for_loop from to v l g1 g2 ->
    (forall i,  In i l -> i < length (raw_fields (vlabel g1 v))) ->
    no_dangling_dst g1 -> no_dangling_dst g2.
Proof.
  do 4 intro. induction l; intros; inversion H6; subst. 1: assumption.
  cut (no_dangling_dst g3).
  - intros. apply (IHl g3); auto.
    + eapply fr_graph_has_v; eauto.
    + erewrite <- fr_raw_mark; eauto.
    + erewrite <- fr_raw_tag; eauto.
    + eapply (fr_copy_compatible O from to); eauto.
    + erewrite <- fr_graph_has_gen; eauto.
    + intros. erewrite <- fr_raw_fields; eauto. apply H7. right; assumption.
  - apply (fr_O_no_dangling_dst' from to
             (FwdPntIntr (InteriorVertexPos v (Z.of_nat a))) g1); auto.
    simpl. intuition auto with *. rewrite Zlength_correct. apply inj_lt. apply H7. now left.
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
        eapply svfl_no_edge2from; eauto.
        unfold no_scan in H11; lia.
        unfold get_edges, make_fields in H7 |-*.
        erewrite svwl_raw_fields; eauto. eapply (svfl_graph_has_v _ _ _ _ g1); eauto.
    + eapply (IHl g3); eauto.
      * eapply (svfl_copy_compatible _ _ _ _ g1); eauto.
      * eapply (svfl_no_dangling_dst from to); eauto.
        -- split; simpl; assumption.
        -- unfold no_scan in H11. lia.
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
  - cut (vgeneration (dst g e) <> gen). 1: intuition auto. unfold gen2gen_no_edge in H0.
    destruct e as [[vgen vidx] eidx]. pose proof H2. apply get_edges_fst in H2.
    simpl in H2. subst v. simpl in *. apply H0;  intuition auto. split; simpl; assumption.
Qed.

Lemma frr_copy_compatible: forall from to roots g roots' g',
    from <> to -> graph_has_gen g to ->
    forward_roots_relation from to roots g roots' g' ->
    copy_compatible g -> copy_compatible g'.
Proof.
  intros. induction H1. 1: assumption. apply IHforward_roots_relation.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_copy_compatible; eauto.
Qed.

(*
Lemma frl_no_dangling_dst: forall from to l roots g roots' g',
    graph_has_gen g to -> copy_compatible g -> from <> to ->
    (forall i, In i l -> i < length roots) ->
    roots_graph_compatible roots g ->
    forward_roots_loop from to l roots g roots' g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  do 3 intro. induction l; intros * ? ? ? ?; pose proof I; intros;
   inversion H5; subst. 1: assumption.
  assert (forward_p_compatible (inl (Z.of_nat a)) roots g from). {
    simpl. split. 1: lia. rewrite Zlength_correct. apply inj_lt.
    apply H2; left; reflexivity. } cut (no_dangling_dst g2).
  - intros. eapply (IHl (upd_roots from to (inl (Z.of_nat a)) g roots)
                        g2 roots'); eauto.
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply (fr_copy_compatible O from to _ g); eauto.
    + intros. rewrite <- ZtoNat_Zlength, upd_roots_Zlength, ZtoNat_Zlength; auto.
      apply H2. right; assumption.
    + eapply fr_roots_graph_compatible; eauto.
  - fold (forward_p2forward_t (inl (Z.of_nat a)) roots g) in H9.
    eapply fr_O_no_dangling_dst'; eauto.
Qed.
*)

Lemma frr_no_dangling_dst: forall from to roots g roots' g',
    graph_has_gen g to -> copy_compatible g -> from <> to ->
    roots_graph_compatible roots g ->
    forward_roots_relation from to roots g roots' g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  intros.
  induction H3; auto.
  apply IHforward_roots_relation; clear IHforward_roots_relation.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_copy_compatible; eauto.
  - cut (roots_graph_compatible roots1 g1).
    + eapply fr_roots_graph_compatible; eassumption.
    + eapply roots_graph_compatible_inv; eassumption.
  - apply (fr_O_no_dangling_dst from to (exterior2forward r) g1 g2); auto.
    destruct r; simpl; auto. hnf in H2. rewrite filter_proj_cons in H2; simpl in H2.
    rewrite Forall_cons_iff in H2. destruct H2; assumption.
Qed.

Lemma frr_dsr_no_edge2gen: forall from to roots roots' g g1 g2,
    graph_has_gen g to -> from <> to -> gen_unmarked g to ->
    copy_compatible g -> no_dangling_dst g ->
    roots_graph_compatible roots g ->
    forward_roots_relation from to roots g roots' g1 ->
    do_scan_relation from to (number_of_vertices (nth_gen g to)) g1 g2 ->
    no_edge2gen g from -> no_edge2gen g2 from.
Proof.
  intros. unfold no_edge2gen in *. intros. specialize (H7 _ H8).
  destruct (Nat.eq_dec another to).
  - subst. unfold gen2gen_no_edge in *. intros.
    destruct H9. simpl fst in *. destruct H6 as [m [? ?]].
    assert (graph_has_gen g1 to) by (erewrite <- frr_graph_has_gen; eauto).
    assert (graph_has_v g (to, vidx) \/ gen_v_num g to <= vidx < gen_v_num g2 to). {
      eapply (svwl_graph_has_v_inv from to _ g1 g2) in H9; eauto. simpl in H9.
      destruct H9.
      - eapply (frr_graph_has_v_inv from _ _ g) in H9; eauto.
        simpl in H9. destruct H9. 1: left; assumption.
        right. destruct H9 as [_ [? ?]]. split; auto.
        apply svwl_gen_v_num_to in H6; [lia | assumption].
      - right. destruct H9 as [_ [? ?]]. split; auto.
        apply frr_gen_v_num_to in H5; [lia | assumption]. } destruct H13.
    + assert (graph_has_v g1 (to, vidx)) by
          (eapply (frr_graph_has_v from to _ g); eauto).
      assert (get_edges g (to, vidx) = get_edges g2 (to, vidx)). {
        transitivity (get_edges g1 (to, vidx)); unfold get_edges, make_fields.
        - erewrite frr_raw_fields; eauto.
        - erewrite svwl_raw_fields; eauto. } rewrite <- H15 in H10.
      assert (graph_has_e g (to, vidx, eidx)) by (split; simpl; assumption).
      specialize (H7 _ _ H16).
      erewrite (frr_dst_unchanged _ _ _ _ _ g1) in H7; eauto.
      erewrite (svwl_dst_unchanged) in H7; eauto; simpl.
      * eapply (frr_gen_unmarked _ _ _ g); eauto.
      * repeat intro. rewrite in_seq in H18. destruct H18 as [? _].
        destruct H13. simpl in H19. red in H19. lia.
    + eapply svwl_no_edge2from; eauto.
      * eapply (frr_gen_unmarked _ _ _ g); eauto.
      * eapply (frr_copy_compatible from to _ g); eauto.
      * eapply (frr_no_dangling_dst _ _ _ g); eauto.
      * apply seq_NoDup.
      * rewrite in_seq. unfold gen_has_index in H11.
        unfold gen_v_num in H13. lia.
  - eapply (frr_gen2gen_no_edge _ _ _ g _ g1) in H7; eauto.
    destruct H6 as [m [? ?]]. eapply (svwl_gen2gen_no_edge from to _ g1 g2); eauto.
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
    + unfold no_scan in H8; lia.
    + intros. rewrite nat_inc_list_In_iff in H5. assumption.
Qed.

Lemma frr_Zlength_roots: forall from to roots1 g1 roots2 g2,
    forward_roots_relation from to roots1 g1 roots2 g2 ->
    Zlength roots1 = Zlength roots2.
Proof.
  intros. induction H; subst; auto.
  list_solve.
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
    red in H4. rewrite H in H4. lia.
  - assert (another > n) by lia. specialize (H0 _ _ H4). apply H0.
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

Inductive garbage_collect_loop
  : list nat -> roots_t -> LGraph -> roots_t -> LGraph -> Prop :=
  gcl_nil: forall g roots, garbage_collect_loop nil roots g roots g
| gcl_cons: forall (g1 g2 g3 g4: LGraph) (i: nat) (il: list nat)
                   (roots1 roots2 roots3: roots_t),
    new_gen_relation (S i) g1 g2 ->
    do_generation_relation i (S i) roots1 roots2 g2 g3 ->
    garbage_collect_loop il roots2 g3 roots3 g4 ->
    garbage_collect_loop (i :: il) roots1 g1 roots3 g4.

Definition garbage_collect_relation
           (roots1 roots2: roots_t) (g1 g2: LGraph): Prop :=
  exists n, garbage_collect_loop (nat_inc_list (S n)) roots1 g1 roots2 g2 /\
            safe_to_copy_gen g2 n (S n).

Definition garbage_collect_condition (g: LGraph) (h : heap) : Prop :=
  graph_unmarked g /\ no_backward_edge g /\ no_dangling_dst g
   /\ ti_size_spec h.

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
                    (ti_args ti) (arg_size ti) (ti_frames ti) (ti_nalloc ti).

Lemma ang_nth_old: forall g gi gen,
    graph_has_gen g gen -> nth_gen (lgraph_add_new_gen g gi) gen = nth_gen g gen.
Proof. intros. unfold nth_gen. simpl. rewrite app_nth1; [reflexivity|assumption]. Qed.

Lemma ang_nth_new: forall g gi,
    nth_gen (lgraph_add_new_gen g gi) (length (g_gen (glabel g))) = gi.
Proof.
  intros. unfold nth_gen. simpl. rewrite app_nth2 by lia. rewrite Nat.sub_diag.
  simpl. reflexivity.
Qed.

Lemma ans_nth_old: forall h sp i (Hs: 0 <= i < MAX_SPACES) gen,
    gen <> Z.to_nat i -> nth_space (add_new_space h sp i Hs) gen =
                         nth_space h gen.
Proof.
  intros. rewrite !nth_space_Znth. simpl. rewrite upd_Znth_diff_strong.
  - reflexivity.
  - rewrite spaces_size. assumption.
  - intro. apply H. subst. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma ans_nth_new: forall h sp i (Hs: 0 <= i < MAX_SPACES),
    nth_space (add_new_space h sp i Hs) (Z.to_nat i) = sp.
Proof.
  intros. rewrite nth_space_Znth. simpl. rewrite Z2Nat.id by lia.
  rewrite upd_Znth_same; [reflexivity | rewrite spaces_size; assumption].
Qed.

Lemma ang_graph_has_gen: forall g gi gen,
    graph_has_gen (lgraph_add_new_gen g gi) gen <->
    graph_has_gen g gen \/ gen = length (g_gen (glabel g)).
Proof.
  intros. unfold graph_has_gen. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma gti_compatible_add: forall g h gi sp i (Hs: 0 <= i < MAX_SPACES),
    graph_heap_compatible g h->
    ~ graph_has_gen g (Z.to_nat i) -> graph_has_gen g (Z.to_nat (i - 1)) ->
    (forall (gr: LGraph), generation_space_compatible gr (Z.to_nat i, gi, sp)) ->
    graph_heap_compatible (lgraph_add_new_gen g gi) (add_new_space h sp i Hs).
Proof.
  intros. unfold graph_heap_compatible in *. destruct H as [? [? ?]].
  assert (length (g_gen (glabel g)) = Z.to_nat i). {
    clear -H0 H1. unfold graph_has_gen in *.
    rewrite Z2Nat.inj_sub in H1 by lia. simpl in H1. lia. }
  pose proof (spaces_size h).
  assert (length (g_gen (glabel (lgraph_add_new_gen g gi))) <=
          length (spaces (add_new_space h sp i Hs)))%nat. {
    simpl. rewrite <- !ZtoNat_Zlength, upd_Znth_Zlength by lia.
    rewrite H6, ZtoNat_Zlength, app_length, H5. simpl. change (S O) with (Z.to_nat 1).
    rewrite <- Z2Nat.inj_add, <- Z2Nat.inj_le by lia. lia. }
  split; [|split]; auto.
  - rewrite gsc_iff in H |- * by assumption. intros.
    apply ang_graph_has_gen in H8. destruct H8.
    + rewrite ang_nth_old by assumption. rewrite ans_nth_old.
      1: apply H; assumption. red in H8. rewrite H5 in H8. lia.
    + subst gen. rewrite ang_nth_new, H5, ans_nth_new. apply H2.
  - simpl. rewrite <- upd_Znth_map. rewrite app_length. rewrite H5 in *. simpl.
    change (S O) with (Z.to_nat 1).
    rewrite <- Z2Nat.inj_add, <- sublist_skip in * by lia.
    rewrite upd_Znth_Zlength; rewrite Zlength_map, spaces_size in *. 2: assumption.
    rewrite sublist_upd_Znth_r. 2: lia. 2: rewrite Zlength_map, spaces_size; lia.
    apply Forall_incl with
        (sublist i MAX_SPACES (map space_start (spaces h))). 2: assumption.
    rewrite Z.add_comm. replace MAX_SPACES with (MAX_SPACES - i + i) at 1 by (clear; lia).
    rewrite <- sublist_sublist with (j := MAX_SPACES) by lia.
    unfold incl. intro a. apply sublist_In.
Qed.

Lemma ang_graph_has_v: forall g gi v,
    graph_has_v g v -> graph_has_v (lgraph_add_new_gen g gi) v.
Proof.
  intros. destruct v as [gen idx]. destruct H; split; simpl in *.
  - unfold graph_has_gen in *. simpl. rewrite app_length. simpl. lia.
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
    rewrite ang_nth_new, H in H1. lia.
  - apply ang_graph_has_gen in H0. red in H1. destruct H0.
    + rewrite ang_nth_old in H1; assumption.
    + exfalso. subst. rewrite ang_nth_new, H in H1. lia.
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

Lemma fta_compatible_add: forall g rootpairs gi roots,
    rootpairs_compatible g rootpairs roots -> roots_graph_compatible roots g ->
    rootpairs_compatible (lgraph_add_new_gen g gi) rootpairs roots.
Proof.
  intros. unfold rootpairs_compatible in *. simpl. rewrite <- H. clear H.
  apply map_ext_in. intros. destruct a; simpl; try reflexivity.
  apply ang_vertex_address_old. red in H0. rewrite Forall_forall in H0. apply H0.
  rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec). assumption.
Qed.

Lemma super_compatible_add: forall g ti gi sp i (Hs: 0 <= i < MAX_SPACES) roots out,
    ~ graph_has_gen g (Z.to_nat i) -> graph_has_gen g (Z.to_nat (i - 1)) ->
    (forall (gr: LGraph), generation_space_compatible gr (Z.to_nat i, gi, sp)) ->
    number_of_vertices gi = O ->
    super_compatible g (ti_heap ti) (frames2rootpairs (ti_frames ti)) roots out ->
    super_compatible (lgraph_add_new_gen g gi) (add_new_space (ti_heap ti) sp i Hs)
                                     (frames2rootpairs (ti_frames ti)) roots out.
Proof.
  intros. destruct H3 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply gti_compatible_add; assumption.
  - apply fta_compatible_add; [|destruct H5]; assumption.
  - apply ang_roots_compatible; assumption.
  - apply ang_outlier_compatible; assumption.
Qed.

(* TODO *)
Lemma ti_size_spec_add: forall h sp i (Hs: 0 <= i < MAX_SPACES),
    available_space sp = nth_gen_size (Z.to_nat i) -> ti_size_spec h ->
    ti_size_spec (add_new_space h sp i Hs).
Proof.
  intros. unfold ti_size_spec in *. rewrite Forall_forall in *. intros.
  specialize (H0 _ H1). unfold nth_gen_size_spec in *.
  destruct (Nat.eq_dec x (Z.to_nat i)); unfold available_size.
  - subst x. rewrite !ans_nth_new. if_tac; auto.
  - rewrite !ans_nth_old; assumption.
Qed.

Lemma firstn_gen_clear_add: forall g gi i,
    graph_has_gen g (Z.to_nat i) -> firstn_gen_clear g (Z.to_nat i) ->
    firstn_gen_clear (lgraph_add_new_gen g gi) (Z.to_nat i).
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros. specialize (H0 _ H1).
  rewrite ang_nth_old; auto. unfold graph_has_gen in *. lia.
Qed.

(*
Lemma ans_space_address: forall h heap_p sp i (Hs: 0 <= i < MAX_SPACES) j,
    space_address heap_p (add_new_space h sp i Hs) (Z.to_nat j) =
    space_address heap_p (Z.to_nat j).
Proof. intros. unfold space_address. simpl. reflexivity. Qed.
*)

Lemma ang_make_header: forall g gi v,
    make_header g v = make_header (lgraph_add_new_gen g gi) v.
Proof. intros. unfold make_header. reflexivity. Qed.

Lemma ang_make_fields_vals_old: forall g gi v,
    graph_has_v g v -> copy_compatible g -> no_dangling_dst g ->
    make_fields_vals g v = make_fields_vals (lgraph_add_new_gen g gi) v.
Proof.
  intros. unfold make_fields_vals. simpl.
  assert (map (field2val (raw_tag (vlabel g v)) g) (make_fields g v) =
          map (field2val (raw_tag (vlabel g v)) (lgraph_add_new_gen g gi))
              (make_fields (lgraph_add_new_gen g gi) v)). {
    unfold make_fields. simpl. apply map_ext_in. intros.
    destruct a; simpl; auto. rewrite ang_vertex_address_old; auto.
    red in H1. apply (H1 v); auto. rewrite get_edges_In_iff. assumption. } rewrite <- H2.
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
  intros n. unfold nth_gen_size. rewrite Nat2Z.inj_succ, two_p_S by lia.
  assert (two_p (Z.of_nat n) > 0) by (apply two_p_gt_ZERO; lia).
  assert (0 < NURSERY_SIZE) by (vm_compute; reflexivity).
  rewrite Z.mul_assoc, (Z.mul_comm NURSERY_SIZE 2).
  assert (0 < NURSERY_SIZE * two_p (Z.of_nat n)). apply Z.mul_pos_pos; lia.
  rewrite <- Z.add_diag, Z.mul_add_distr_r. lia.
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

Lemma gcc_add: forall g h gi sp i (Hs: 0 <= i < MAX_SPACES),
    number_of_vertices gi = O -> available_space sp = nth_gen_size (Z.to_nat i) ->
    garbage_collect_condition g h ->
    garbage_collect_condition (lgraph_add_new_gen g gi)
                              (add_new_space h sp i Hs).
Proof.
  intros. destruct H1 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply graph_unmarked_add; assumption.
  - apply no_backward_edge_add; assumption.
  - apply no_dangling_dst_add; assumption.
  - apply ti_size_spec_add; assumption.
Qed.

Lemma ngs_0_lt: forall i, 0 < nth_gen_size i.
Proof.
  intros. unfold nth_gen_size.
  rewrite NURSERY_SIZE_eq, Zbits.Zshiftl_mul_two_p, Z.mul_1_l,
  <- two_p_is_exp by lia.
  cut (two_p (16 + Z.of_nat i) > 0); [|apply two_p_gt_ZERO]; lia.
Qed.

Lemma gc_cond_implies_do_gen_cons: forall g h i,
    safe_to_copy_to_except g i ->
    graph_has_gen g (S i) ->
    graph_heap_compatible g h ->
    garbage_collect_condition g h ->
    do_generation_condition g h i (S i).
Proof.
  intros. destruct H2 as [? [? [? ?]]].
  assert (graph_has_gen g i) by (unfold graph_has_gen in H0 |-*; lia).
  split; [|split; [|split; [|split; [|split; [|split(*; [ | split]*)]]]]]; auto.
  - unfold safe_to_copy_to_except, safe_to_copy_gen in H. red.
    unfold rest_gen_size. specialize (H (S i)). simpl in H.
    destruct (gt_gs_compatible _ _ H1 _ H0) as [_ [_ ?]].
    destruct (gt_gs_compatible _ _ H1 _ H6) as [_ [_ ?]].
    fold (graph_gen_size g (S i)) in H7. fold (graph_gen_size g i) in H8.
    rewrite <- H7. fold (available_size h (S i)).
    destruct (used_leq_available (nth_space h i)) as [_ ?].
    fold (available_size h i) in H9. rewrite <- H8 in H9.
    transitivity (available_size h i). 1: assumption.
    rewrite (ti_size_gen _ _ _ H1 H6 H5), (ti_size_gen _ _ _ H1 H0 H5).
    apply H; [lia.. | assumption].
  - apply graph_unmarked_copy_compatible; assumption.
  - rewrite (ti_size_gen _ _ _ H1 H0 H5). apply ngs_0_lt.
  - rewrite graph_gen_unmarked_iff in H2. apply H2.
Qed.

Lemma do_gen_no_dangling_dst: forall g1 g2 roots1 roots2 from to,
  graph_has_gen g1 to -> copy_compatible g1 -> gen_unmarked g1 to ->
  from <> to ->
  roots_graph_compatible roots1 g1 -> firstn_gen_clear g1 from ->
  no_backward_edge g1 ->
  do_generation_relation from to roots1 roots2 g1 g2 ->
  no_dangling_dst g1 -> no_dangling_dst g2.
Proof.
  intros until 3. pose proof I; intros. destruct H7 as [g3 [g4 [? [? ?]]]].
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

Lemma frr_nth_gen_unchanged: forall from to roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall gen, gen <> to -> nth_gen g1 gen = nth_gen g2 gen.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_relation.
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

Lemma frr_firstn_gen_clear: forall from to roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall gen, (gen <= to)%nat ->
                firstn_gen_clear g1 gen -> firstn_gen_clear g2 gen.
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros.
  erewrite <- frr_nth_gen_unchanged; eauto. lia.
Qed.

Lemma svwl_firstn_gen_clear: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall gen, (gen <= to)%nat ->
                firstn_gen_clear g1 gen -> firstn_gen_clear g2 gen.
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros.
  erewrite <- (svwl_nth_gen_unchanged from); eauto. lia.
Qed.

Lemma firstn_gen_clear_reset: forall g i,
    firstn_gen_clear g i -> firstn_gen_clear (reset_graph i g) (S i).
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros.
  assert (i0 < i \/ i0 = i)%nat by lia. destruct H1.
  - rewrite reset_nth_gen_diff by lia. apply H; assumption.
  - subst i0. unfold nth_gen. simpl. rewrite reset_nth_gen_info_same.
    simpl. reflexivity.
Qed.

Lemma do_gen_firstn_gen_clear: forall g1 g2 roots1 roots2 i,
    do_generation_relation i (S i) roots1 roots2 g1 g2 ->
    graph_has_gen g1 (S i) -> firstn_gen_clear g1 i -> firstn_gen_clear g2 (S i).
Proof.
  intros. destruct H as [g3 [g4 [? [? ?]]]].
  eapply frr_firstn_gen_clear in H1; eauto. destruct H2 as [n [? ?]].
  eapply svwl_firstn_gen_clear in H1; eauto. 2: erewrite <- frr_graph_has_gen; eauto.
  subst g2. apply firstn_gen_clear_reset. assumption.
Qed.

Lemma do_gen_no_backward_edge: forall g1 g2 roots1 roots2 i,
    do_generation_relation i (S i) roots1 roots2 g1 g2 ->
    no_dangling_dst g2 -> graph_has_gen g1 (S i) -> gen_unmarked g1 (S i) ->
    firstn_gen_clear g1 i -> no_backward_edge g1 -> no_backward_edge g2.
Proof.
  intros. unfold no_backward_edge in *. intros. destruct (Nat.eq_dec gen1 (S i)).
  - red. intros. destruct H6. simpl in *. eapply do_gen_firstn_gen_clear in H3; eauto.
    subst. specialize (H0 _ H6 _ H7). destruct H0. red in H8. intro. rewrite H9 in H8.
    red in H3. assert (gen2 < S i)%nat by lia. specialize (H3 _ H10). red in H3.
    rewrite H3 in H8. lia.
  - destruct H as [g3 [g4 [? [? ?]]]]. subst g2. apply gen2gen_no_edge_reset.
    assert (gen2gen_no_edge g3 gen1 gen2) by (eapply frr_gen2gen_no_edge; eauto).
    destruct H6 as [m [? ?]]. eapply (svwl_gen2gen_no_edge i _ _ g3); eauto.
    + rewrite <- frr_graph_has_gen; eauto.
    + eapply frr_gen_unmarked; eauto.
Qed.

Lemma heap_relation_size_spec: forall h1 h2 : heap,
    heap_relation h1 h2 ->
    ti_size_spec h1 -> ti_size_spec h2.
Proof.
  intros. unfold ti_size_spec in *. rewrite Forall_forall in *. intros.
  specialize (H0 _ H1). unfold nth_gen_size_spec in *. destruct H as [H2 H3].
  rewrite <- H2, <- H3. assumption.
Qed.

Lemma do_gen_gcc: forall g1 h1 roots1 g2 h2 roots2 i out,
    graph_heap_compatible g1 h1 ->
    roots_compatible g1 out roots1 ->
    outlier_compatible g1 out ->
    firstn_gen_clear g1 i -> graph_has_gen g1 (S i) ->
    heap_relation h1 h2 ->
    garbage_collect_condition g1 h1 ->
    do_generation_relation i (S i) roots1 roots2 g1 g2 ->
    garbage_collect_condition g2 h2.
Proof.
  intros. destruct H5 as [? [? [? ?]]].
  assert (gen_unmarked g1 (S i)) by (rewrite graph_gen_unmarked_iff in H5; apply H5).
  assert (no_dangling_dst g2). {
    eapply do_gen_no_dangling_dst; eauto.
    - apply graph_unmarked_copy_compatible; assumption.
    - apply H0.
  }
  split; [|split; [|split]]; auto.
  - eapply do_gen_graph_unmarked; eauto.
  - eapply do_gen_no_backward_edge; eauto.
  - eapply heap_relation_size_spec; eauto.
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

Lemma frr_stcg: forall from to roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to roots1 g1 roots2 g2 ->
    forall gen1 gen2, graph_has_gen g1 gen2 -> gen2 <> to ->
                      safe_to_copy_gen g1 gen1 gen2 -> safe_to_copy_gen g2 gen1 gen2.
Proof.
  intros. induction H0. 1: assumption. apply IHforward_roots_relation.
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

Lemma do_gen_stcte: forall g1 roots1 g2 roots2 i,
    safe_to_copy_to_except g1 i -> graph_has_gen g1 (S i) ->
    do_generation_relation i (S i) roots1 roots2 g1 g2 ->
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
    eapply (frr_stcg i (S i) _ g1); eauto.
Qed.

Lemma gcl_add_tail: forall l g1 roots1 g2 roots2 g3 roots3 g4 i,
    garbage_collect_loop l roots1 g1 roots2 g2 ->
    new_gen_relation (S i) g2 g3 ->
    do_generation_relation i (S i) roots2 roots3 g3 g4 ->
    garbage_collect_loop (l +:: i) roots1 g1 roots3 g4.
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

Lemma Int64_eq_false: forall x y : int64, Int64.eq x y = false -> x <> y.
Proof.
  intros. destruct x, y. unfold Int64.eq in H. simpl in H.
  destruct (zeq intval intval0). 1: inversion H. intro. inversion H0. easy.
Qed.

Lemma raw_fields_range2: forall r,
    Zlength (raw_fields r) <= if Archi.ptr64 then Int64.max_signed else Int.max_signed.
Proof.
  intros. pose proof (raw_fields_range r). remember (Zlength (raw_fields r)).
  clear Heqz. cbv delta[Archi.ptr64]. simpl. rewrite <- Z.lt_succ_r. destruct H.
  transitivity (two_p (WORD_SIZE * 8 - 10)); auto. now vm_compute.
Qed.

Lemma ltu64_repr_false: forall x y,
    0 <= y <= Int64.max_unsigned -> 0 <= x <= Int64.max_unsigned ->
    Int64.ltu (Int64.repr x) (Int64.repr y) = false -> x >= y.
Proof.
  intros. unfold Int64.ltu in H1. rewrite !Int64.unsigned_repr in H1; auto.
  if_tac in H1; auto. inversion H1.
Qed.


Lemma frames2rootpairs_update_frames: forall frames r,
   Zlength r = Zlength (frames2rootpairs frames) ->
   map rp_val (frames2rootpairs (update_frames frames r)) = r.
Proof.
  induction frames as [ | [a b s] ?]; simpl in *; intros;
    autorewrite with sublist in *.
  - list_solve.
  - rewrite map_app, IHframes; clear IHframes.
    + autorewrite with sublist. simpl in *. list_solve.
    + simpl in H. autorewrite with sublist. lia.
Qed.

Lemma update_update_frames: forall frames r1 r2,
  Zlength r1 = Zlength (frames2rootpairs frames) ->
  Zlength r1 = Zlength r2 ->
  update_frames (update_frames frames r1) r2 = update_frames frames r2.
Proof.
  induction frames as [ | [a r s] ?]; simpl; intros; auto.
  autorewrite with sublist in H. simpl in H.
  f_equal. f_equal. list_solve.
  rewrite IHframes; clear IHframes; auto; list_solve.
Qed.

Lemma ptrofs_divs_repr
	 : forall i j : Z,
       Ptrofs.min_signed <= i <= Ptrofs.max_signed ->
       Ptrofs.min_signed <= j <= Ptrofs.max_signed ->
       Ptrofs.divs (Ptrofs.repr i) (Ptrofs.repr j) =
       Ptrofs.repr (i ÷ j).
Proof.
  intros.
  unfold Ptrofs.divs.
  rewrite ?Ptrofs.signed_repr by rep_lia;
  auto.
Qed.

Lemma int64_lt_ptrofs_to_int_64:
  forall x y, Archi.ptr64 = true ->
    Int64.lt (Ptrofs.to_int64 x) (Ptrofs.to_int64 y) =  Ptrofs.lt x y.
Proof.
  intros.
  unfold Int64.lt, Ptrofs.lt.
  rewrite <- (Ptrofs.repr_signed x), <- (Ptrofs.repr_signed y).
  rewrite !ptrofs_to_int64_repr by auto.
  pose proof Ptrofs.signed_range.
  unfold Ptrofs.min_signed, Ptrofs.max_signed in H0.
  unfold Ptrofs.half_modulus, Ptrofs.modulus, Ptrofs.wordsize,
    Wordsize_Ptrofs.wordsize in H0. rewrite H in H0.
  rewrite !Int64.signed_repr by apply H0.
  rewrite !Ptrofs.signed_repr by apply Ptrofs.signed_range.
  auto.
Qed.

Lemma int_lt_ptrofs_to_int_:
  forall x y, Archi.ptr64 = false ->
    Int.lt (Ptrofs.to_int x) (Ptrofs.to_int y) =  Ptrofs.lt x y.
Proof.
  intros.
  unfold Int.lt, Ptrofs.lt.
  rewrite <- (Ptrofs.repr_signed x), <- (Ptrofs.repr_signed y).
  rewrite !ptrofs_to_int_repr by auto.
  pose proof Ptrofs.signed_range.
  unfold Ptrofs.min_signed, Ptrofs.max_signed in H0.
  unfold Ptrofs.half_modulus, Ptrofs.modulus, Ptrofs.wordsize,
    Wordsize_Ptrofs.wordsize in H0. rewrite H in H0.
  rewrite !Int.signed_repr by apply H0.
  rewrite !Ptrofs.signed_repr by apply Ptrofs.signed_range.
  auto.
Qed.

#[export] Instance Inh_rootpair : Inhabitant rootpair := {| rp_adr:=Vundef; rp_val:=Vundef|}.

Lemma Znth_frame2rootpairs' :
forall z r s,
  0 <= z < Zlength s ->
  Znth z (frame2rootpairs' r 0 s) =
   {| rp_adr := offset_val (z * WORD_SIZE) r; rp_val := Znth z s|}.
 Proof.
 intros.
 rewrite <- (Z.add_0_l z) at 2.
 set (i:=0). clearbody i.
 revert i z H; induction s; simpl; intros.
 list_solve.
 destruct (zeq z 0).
 list_solve.
 rewrite Znth_pos_cons by lia.
 specialize (IHs (i+1) (z-1) ltac:(list_solve)).
 unfold Z.succ.
 rewrite IHs. f_equal. f_equal. lia. list_solve.
Qed.

Lemma Znth_frame2rootpairs:
 forall z f, 0 <= z < Zlength (fr_roots f) ->
   Znth z (frame2rootpairs f) =
   {| rp_adr := offset_val (z * WORD_SIZE) (fr_root f); rp_val := Znth z (fr_roots f)|}.
Proof.
intros.
apply Znth_frame2rootpairs'; auto.
Qed.

#[export] Hint Rewrite Znth_frame2rootpairs Znth_frame2rootpairs' using Zlength_solve : sublist Znth.

Lemma Znth_frames2rootpairs_update_frames:
forall fr z roots,
 Zlength roots = Zlength (frames2rootpairs fr) ->
 0 <= z < Zlength roots ->
 Znth z (frames2rootpairs (update_frames fr roots)) =
  {| rp_adr := rp_adr (Znth z (frames2rootpairs fr));
     rp_val := Znth z roots|}.
Proof.
  induction fr as [ | [ a r s ] fr']; simpl; intros; autorewrite with sublist in *.
  - list_solve.
  - destruct (zlt z (Zlength s)).
   + rewrite !Znth_app1 by (autorewrite with sublist; simpl in *; list_solve).
    rewrite !Znth_frame2rootpairs by (simpl in *; list_solve).
    simpl. f_equal. list_solve.
   + rewrite !Znth_app2 by  (autorewrite with sublist; simpl in *; list_solve).
     autorewrite with sublist. simpl.
     autorewrite with sublist.
     simpl in H.
     rewrite IHfr'; try list_solve.
Qed.

Lemma Znth_update_rootpairs: forall rootpairs roots z,
0 <= z < Zlength rootpairs ->
Zlength rootpairs = Zlength roots ->
Znth z (update_rootpairs rootpairs roots) = {| rp_adr := rp_adr (Znth z rootpairs); rp_val := Znth z roots |}.
Proof.
induction rootpairs; destruct roots; simpl; intros; try list_solve.
 destruct a.
 destruct (zeq z 0).
 subst. rewrite !Znth_0_cons. simpl. auto.
 rewrite !Znth_pos_cons by rep_lia.
 rewrite (IHrootpairs roots (z-1)) by list_solve.
 f_equal.
Qed.

Lemma Zlength_update_rootpairs: forall rootpairs roots,
Zlength rootpairs = Zlength roots ->
Zlength (update_rootpairs rootpairs roots) = Zlength rootpairs.
Proof.
induction rootpairs as [ | [ ? ? ] ? ]; destruct roots; simpl; intros; try list_solve.
rewrite !Zlength_cons. rewrite IHrootpairs by list_solve. auto.
Qed.

Lemma rp_val_update_rootpairs:
forall rootpairs roots,
  Zlength rootpairs = Zlength roots ->
  map rp_val (update_rootpairs rootpairs roots) = roots.
Proof.
 induction rootpairs as [ | [? ?] ? ]; destruct roots; simpl; intros; try list_solve.
 f_equal. apply IHrootpairs; list_solve.
Qed.

Fixpoint frame_root_address (frames: list frame) (i: Z) : val :=
  match frames with
  | nil => nullval (* oops! *)
  | {|fr_adr:=a; fr_root:=r; fr_roots:=s |}::rest =>
     if zlt i (Zlength s)
     then offset_val (i * WORD_SIZE) r
     else frame_root_address rest (i-Zlength s)
  end.

Lemma frame_root_address_eq:
 forall frames i,
 0 <= i < Zlength (frames2rootpairs frames) ->
 frame_root_address frames i = rp_adr (Znth i (frames2rootpairs frames)).
 Proof.
  unfold frames2rootpairs.
  induction frames as [ | [ a r s] fr']; simpl; intros.
  - list_solve.
  -
    pose proof (Zlength_frame2rootpairs' r 0 s).
    unfold frame2rootpairs at 1.
    unfold frame2rootpairs at 1 in H.
    simpl in H|-*.
    if_tac.
    rewrite Znth_app1 by list_solve.
    assert (0 <= i < Zlength s) by lia.
    clear - H2.
    change i with (0+i) at 1.
    set (j:=0). clearbody j.
    revert i j H2; induction s; simpl; intros.
    list_solve.
    destruct (zeq i 0).
    subst. list_simplify.
    rewrite Znth_pos_cons by list_solve.
    rewrite <- IHs by list_solve.
    f_equal. lia.
    rewrite Znth_app2 by list_solve.
    rewrite IHfr' by list_solve.
    f_equal.
    f_equal.
    list_solve.
Qed.

Lemma update_rootpairs_frames2rootpairs:
forall frames roots,
Zlength roots = Zlength (frames2rootpairs frames) ->
update_rootpairs (frames2rootpairs frames) roots =
frames2rootpairs (update_frames frames roots).
Proof.
induction frames as [ | [ a r s ] rest] ;[ destruct roots; auto | ].
intros.
simpl.
autorewrite with sublist in *. simpl in *.
rewrite <- IHrest by list_solve; clear IHrest.
unfold frame2rootpairs. simpl.
  set (i:=0) at 1 2. (* assert (0 <= i) by list_solve.*) clearbody i.
 revert roots i H; induction s; destruct roots; simpl; intros; auto.
 - autorewrite with sublist. auto.
 - list_solve.
 - autorewrite with sublist in H.
   rewrite IHs by list_solve; clear IHs.
   rewrite sublist_0_cons by list_solve.
   autorewrite with sublist. unfold Z.succ.
    rewrite (sublist_pos_cons (_ + _)) by list_solve.
    rewrite !Z.add_simpl_r.
    unfold frame2rootpairs' at 2; fold frame2rootpairs'.
    simpl. auto.
Qed.

 Lemma frame_root_address_same: forall frames roots z,
 Zlength roots = Zlength (frames2rootpairs frames) ->
 0 <= z < Zlength (frames2rootpairs frames) ->
 frame_root_address (update_frames frames roots) z = frame_root_address frames z.
Proof.
unfold frames2rootpairs.
induction frames as [|[a r s ] fr]; simpl; intros; auto.
autorewrite with sublist in *. simpl in *.
if_tac.
-
rewrite if_true; auto.
list_solve.
-
autorewrite with sublist in *.
rewrite IHfr; clear IHfr; try list_solve.
rewrite if_false; try list_solve.
Qed.

Lemma frr_app_inv: forall from to ra g1 ra' rb rb' g3,
   forward_roots_relation from to (ra++rb) g1 (ra'++rb') g3 ->
   Zlength ra = Zlength ra' ->
   exists g2, forward_roots_relation from to ra g1 ra' g2 /\
        forward_roots_relation from to rb g2 rb' g3.
Proof.
 intros.
 remember (ra++rb) as rab. remember (ra'++rb') as rab'.
   revert ra ra' rb rb' Heqrab Heqrab' H0.
   induction H; intros; destruct ra, ra'; inv Heqrab; inv  Heqrab'; simpl in *; subst.
   + exists g; split; constructor.
   + exists g1; split. constructor. econstructor; eauto.
   + list_solve.
   + list_solve.
   + edestruct IHforward_roots_relation as [g4 [? ?]].
     4:{ exists g4. split; try eassumption. econstructor; eauto. }
     auto. auto. list_solve.
Qed.

Lemma frr_app: forall from to ra g1 ra' g2 rb rb' g3,
  forward_roots_relation from to ra g1 ra' g2 ->
  forward_roots_relation from to rb g2 rb' g3 ->
  forward_roots_relation from to (ra++rb) g1 (ra'++rb') g3.
Proof.
 intros.
 revert rb' g3 H0; induction H; intros; auto.
 simpl.
 econstructor; eauto.
Qed.

Lemma sc_Zlength:  forall [g h rps rs outliers],
    super_compatible g h rps rs outliers -> Zlength rs = Zlength rps.
Proof.
  intros.
  destruct H as [_ [? _]].
  apply (f_equal (@Zlength _)) in H.
  list_solve.
Qed.

Lemma forward_graph_and_heap_O_gestc: forall from to p g h size,
    from <> to ->
    forward_t_compatible p g ->
    no_dangling_dst g ->
    graph_has_gen g to ->
    general_enough_space_to_copy g h from to size -> 0 <= size ->
    forall g' h',
    (g', h') = forward_graph_and_heap from to O p g h ->
    general_enough_space_to_copy g' h' from to size.
Proof.
  simpl. intros from to p g h size H H0 H1 H2 H3 Hs g' h' H4.
 destruct p; [inversion H4; assumption..| |]; destruct (Nat.eq_dec _ _);
   [|inversion H4; assumption | | inversion H4; assumption]; destruct (raw_mark _) eqn: ? ;
   [inversion H4; assumption| | |]; subst; inversion H4.
  - apply lcv_general_enough_space_to_copy; assumption.
  - apply lgd_general_enough_space_to_copy. assumption.
  - apply lgd_general_enough_space_to_copy.
    apply lcv_general_enough_space_to_copy; auto. destruct H0. apply (H1 _ H0 _ H5).
Qed.

Lemma forward_graph_and_heap_O_estc: forall from to p g h,
    from <> to ->
    forward_t_compatible p g ->
    no_dangling_dst g ->
    graph_has_gen g to ->
    enough_space_to_copy g h from to ->
    forall g' h',
    (g', h') = forward_graph_and_heap from to O p g h ->
    enough_space_to_copy g' h' from to.
Proof. intros; eapply forward_graph_and_heap_O_gestc; eauto. apply Z.le_refl. Qed.

Lemma forward_gh_loop_gestc: forall (from to depth : nat) (vv : VType)
                              (l : list interior_t) (gg : LGraph) (hh : heap) (size: Z),
    from <> to -> 0 <= size ->
    (forall (p : forward_t) (g : LGraph) (h : heap),
        forward_t_compatible p g ->
        no_dangling_dst g ->
        graph_has_gen g to ->
        copy_compatible g ->
        general_enough_space_to_copy g h from to size ->
        forall g' h', (g', h') = forward_graph_and_heap from to depth p g h ->
                 general_enough_space_to_copy g' h' from to size) ->
    no_dangling_dst gg ->
    copy_compatible gg ->
    graph_has_gen gg to ->
    graph_has_v gg vv ->
    Forall (is_field_same_v gg vv) l ->
    general_enough_space_to_copy gg hh from to size ->
    forall g' h', (g', h') = forward_gh_loop forward_graph_and_heap from to depth l (gg, hh) ->
             general_enough_space_to_copy g' h' from to size.
Proof.
  intros from to depth vv l gg hh size Hft Hs IHdepth. revert l gg hh.
  induction l; intros gg hh H H0 H1 H2 Hi H4 g' h' Hgh'; simpl in *;
    [inversion Hgh'; assumption | ].
  rewrite Forall_cons_iff in Hi. destruct Hi as [[i [Ha Hi]] Hl]. subst a.
  simpl interior2forward in *. remember (forward_graph_and_heap _ _ _ _ _ _).
  rewrite (surjective_pairing p) in Hgh'.
  assert (Hc: forward_t_compatible (field2forward (Znth i (make_fields gg vv))) gg). {
    apply vertex_pos_forward_t_compatible; auto. now rewrite <- make_fields_eq_length. }
  assert (forward_relation from to depth (field2forward (Znth i (make_fields gg vv)))
            gg (fst p)) by (subst p; apply fr_forward_graph_and_heap).
  apply (IHl (fst p) (snd p)); auto.
  - eapply fr_no_dangling_dst; eassumption.
  - eapply fr_copy_compatible; eassumption.
  - rewrite <- fr_graph_has_gen; eassumption.
  - eapply fr_graph_has_v; eassumption.
  - rewrite <- fr_is_field_same_v; eassumption.
  - specialize (IHdepth (field2forward (Znth i (make_fields gg vv))) gg hh).
    rewrite <- Heqp in IHdepth. apply IHdepth; auto. now rewrite <- surjective_pairing.
Qed.

Lemma forward_graph_and_heap_gestc: forall from to depth p g h size,
    from <> to -> 0 <= size ->
    forward_t_compatible p g ->
    no_dangling_dst g ->
    graph_has_gen g to ->
    copy_compatible g ->
    general_enough_space_to_copy g h from to size ->
    forall g' h', (g', h') = forward_graph_and_heap from to depth p g h ->
             general_enough_space_to_copy g' h' from to size.
Proof.
  intros from to depth p g h size Hft Hs. revert depth p g h. induction depth;
    intros p g h H H0 H1 H2 H3 g' h' Hgh'.
  1: eapply forward_graph_and_heap_O_gestc; eassumption.
  destruct p; simpl in Hgh'; [inversion Hgh'; assumption..| |]; destruct (Nat.eq_dec _ _);
    [|inversion Hgh'; assumption | | inversion Hgh'; assumption];
    destruct (raw_mark _) eqn:?;
      [inversion Hgh'; assumption | |
        inversion Hgh'; now apply lgd_general_enough_space_to_copy |];
    destruct (Z_lt_ge_dec _ _); subst.
  - eapply (forward_gh_loop_gestc (vgeneration v) to depth (new_copied_v g to)).
    10: apply Hgh'. all: auto.
    + apply lcv_no_dangling_dst; assumption.
    + apply lcv_copy_compatible; assumption.
    + rewrite <- lcv_graph_has_gen; assumption.
    + apply lcv_graph_has_v_new. assumption.
    + apply vertex_pos_pairs_in_range.
    + apply lcv_general_enough_space_to_copy; assumption.
  - inversion Hgh'. apply lcv_general_enough_space_to_copy; assumption.
  - assert (graph_has_v g (dst g e)) by (destruct H; apply (H0 _ H _ H4)).
    eapply (forward_gh_loop_gestc (vgeneration (dst g e)) to depth (new_copied_v g to)).
    10: apply Hgh'. all: auto.
    + apply lgd_no_dangling_dst.
      * apply lcv_graph_has_v_new. assumption.
      * apply lcv_no_dangling_dst; assumption.
    + apply lgd_copy_compatible. apply lcv_copy_compatible; assumption.
    + rewrite lgd_graph_has_gen. apply lcv_graph_has_gen; assumption.
    + rewrite <- lgd_graph_has_v. apply lcv_graph_has_v_new. assumption.
    + apply vertex_pos_pairs_in_range.
    + apply lgd_general_enough_space_to_copy.
      apply lcv_general_enough_space_to_copy; assumption.
  - inversion Hgh'. apply lgd_general_enough_space_to_copy.
    apply lcv_general_enough_space_to_copy; auto. destruct H. apply (H0 _ H _ H4).
Qed.

Lemma forward_graph_and_heap_estc: forall from to depth p g h,
    from <> to ->
    forward_t_compatible p g ->
    no_dangling_dst g ->
    graph_has_gen g to ->
    copy_compatible g ->
    enough_space_to_copy g h from to ->
    forall g' h', (g', h') = forward_graph_and_heap from to depth p g h ->
             enough_space_to_copy g' h' from to.
Proof. intros; eapply forward_graph_and_heap_gestc; eauto. apply Z.le_refl. Qed.

Lemma forward_graph_and_heap_O_ghc: forall from to p g h,
    forward_t_compatible p g ->
    no_dangling_dst g ->
    graph_has_gen g to ->
    enough_space_to_copy g h from to ->
    graph_heap_compatible g h ->
    forall g' h', (g', h') = forward_graph_and_heap from to O p g h ->
             graph_heap_compatible g' h'.
Proof.
  simpl; intros from to p g h H H0 H1 H2 H3 g' h' Hgh'.
  destruct p; [inversion Hgh'; assumption..| |]; destruct (Nat.eq_dec _ _);
    [|inversion Hgh'; assumption | | inversion Hgh'; assumption ];
    destruct (raw_mark _) eqn: ? ; inversion Hgh'; [assumption| | |]; subst.
  - apply lcv_graph_heap_compatible; auto. apply estc_has_space; assumption.
  - now apply lgd_graph_heap_compatible.
  - apply lgd_graph_heap_compatible, lcv_graph_heap_compatible; [|assumption..].
    apply estc_has_space; [|assumption..]. destruct H. apply (H0 _ H _ H4).
Qed.

Lemma forward_gh_loop_ghc_helper: forall (from to depth: nat) (vv : VType)
                             (l : list interior_t) (gg : LGraph) (hh : heap),
    from <> to ->
    (forall (p : forward_t) (g : LGraph) (h : heap),
        forward_t_compatible p g ->
        no_dangling_dst g ->
        graph_has_gen g to ->
        enough_space_to_copy g h from to ->
        copy_compatible g ->
        graph_heap_compatible g h ->
        forall g' h', (g', h') = forward_graph_and_heap from to depth p g h ->
                 graph_heap_compatible g' h') ->
    no_dangling_dst gg ->
    enough_space_to_copy gg hh from to ->
    graph_has_gen gg to ->
    graph_has_v gg vv ->
    copy_compatible gg ->
    Forall (is_field_same_v gg vv) l ->
    graph_heap_compatible gg hh ->
    forall g' h', (g', h') = forward_gh_loop forward_graph_and_heap from to depth l (gg, hh) ->
             graph_heap_compatible g' h'.
Proof.
  intros from to depth vv l gg hh Hft IHdepth. revert l gg hh.
  induction l; intros gg hh H H0 H1 H2 H3 Hi H5 g' h' Hgh';
    simpl in *; [inversion Hgh'; assumption |].
  rewrite Forall_cons_iff in Hi. destruct Hi as [[i [Ha Hi]] Hl]. subst a.
  simpl interior2forward in *. remember (forward_graph_and_heap _ _ _ _ _ _).
  rewrite (surjective_pairing p) in Hgh'.
  assert (Hcmpt: forward_t_compatible (field2forward (Znth i (make_fields gg vv))) gg). {
    apply vertex_pos_forward_t_compatible; auto. now rewrite <- make_fields_eq_length. }
  assert (forward_relation from to depth (field2forward (Znth i (make_fields gg vv)))
            gg (fst p)) by (subst p; apply fr_forward_graph_and_heap).
  apply (IHl (fst p) (snd p)); auto.
  - eapply fr_no_dangling_dst; eassumption.
  - pose proof (forward_graph_and_heap_estc _ _ depth _ _ _ Hft Hcmpt H H1 H3 H0).
    apply H6. rewrite <- surjective_pairing. assumption.
  - rewrite <- fr_graph_has_gen; eassumption.
  - eapply fr_graph_has_v; eassumption.
  - eapply fr_copy_compatible; eassumption.
  - rewrite <- fr_is_field_same_v; eassumption.
  - specialize (IHdepth (field2forward (Znth i (make_fields gg vv))) gg hh).
    rewrite <- Heqp in IHdepth. apply IHdepth; try assumption.
    now rewrite <- surjective_pairing.
Qed.

Lemma forward_graph_and_heap_ghc: forall from to depth p g h,
    from <> to ->
    forward_t_compatible p g ->
    no_dangling_dst g ->
    graph_has_gen g to ->
    enough_space_to_copy g h from to ->
    copy_compatible g ->
    graph_heap_compatible g h ->
    forall g' h', (g', h') = forward_graph_and_heap from to depth p g h ->
             graph_heap_compatible g' h'.
Proof.
  intros from to depth p g h Hft. revert depth p g h.
  induction depth; [intros; eapply forward_graph_and_heap_O_ghc; eassumption|].
  simpl; intros p g h H H0 H1 H2 H3 H4 g' h' Hgh'.
  destruct p; [inversion Hgh'; assumption..| |]; destruct (Nat.eq_dec _ _);
    [|inversion Hgh'; assumption | | inversion Hgh'; assumption];
  destruct (raw_mark _) eqn: ?H ;
    [inversion Hgh'; assumption| | inversion Hgh'; now apply lgd_graph_heap_compatible |];
    destruct (Z_lt_ge_dec _ _); subst.
  - eapply (forward_gh_loop_ghc_helper (vgeneration v) to depth (new_copied_v g to)).
    10: apply Hgh'. all: auto.
    + apply lcv_no_dangling_dst; assumption.
    + apply lcv_enough_space_to_copy; assumption.
    + rewrite <- lcv_graph_has_gen; assumption.
    + apply lcv_graph_has_v_new. assumption.
    + apply lcv_copy_compatible; assumption.
    + apply vertex_pos_pairs_in_range.
    + apply lcv_graph_heap_compatible; [|assumption..]. apply estc_has_space; assumption.
  - inversion Hgh'. apply lcv_graph_heap_compatible; [|assumption..].
    apply estc_has_space; assumption.
  - assert (graph_has_v g (dst g e)) by (destruct H; apply (H0 _ H _ H6)).
    eapply (forward_gh_loop_ghc_helper (vgeneration (dst g e)) to depth (new_copied_v g to)).
    10: apply Hgh'. all: auto.
    + apply lgd_no_dangling_dst.
      * apply lcv_graph_has_v_new; assumption.
      * apply lcv_no_dangling_dst; assumption.
    + apply lgd_enough_space_to_copy. apply lcv_enough_space_to_copy; assumption.
    + rewrite lgd_graph_has_gen. apply lcv_graph_has_gen; assumption.
    + rewrite <- lgd_graph_has_v. apply lcv_graph_has_v_new. assumption.
    + apply lgd_copy_compatible. apply lcv_copy_compatible; assumption.
    + apply vertex_pos_pairs_in_range.
    + apply lgd_graph_heap_compatible, lcv_graph_heap_compatible; [|assumption..].
      apply estc_has_space; assumption.
  - inversion Hgh'.
    apply lgd_graph_heap_compatible, lcv_graph_heap_compatible; [|assumption..].
    apply estc_has_space; [|assumption..]. destruct H; apply (H0 _ H _ H6).
Qed.

Lemma raw_tag_biteq: forall (g: LGraph) (v: VType),
    raw_mark (vlabel g v) = false ->
    Int64.unsigned (Int64.and (Int64.repr (make_header g v)) (Int64.repr 255)) =
      (raw_tag (vlabel g v)) mod 256.
Proof.
  intros g v Hrm.
  pose proof raw_fields_range (vlabel g v). pose proof raw_color_range (vlabel g v).
  pose proof raw_tag_range (vlabel g v). unfold make_header. rewrite Hrm.
  forget (raw_color (vlabel g v)) as c.
  forget (Zlength (raw_fields (vlabel g v))) as f.
  forget (raw_tag (vlabel g v)) as tag.
  rewrite !Z.shiftl_mul_pow2 by (intro; discriminate).
  change WORD_SIZE with 8 in *. simpl in *.
  change (Z.pow_pos 2 8) with 256. change (Z.pow_pos 2 10) with 1024.
  rewrite and64_repr. change 255 with (Z.ones 8).
  rewrite Z.land_ones by (intro; discriminate). simpl.
  change (Z.pow_pos 2 8) with 256.
  rewrite Z.add_mod by (intro; discriminate).
  change 1024 with (4 * 256)%Z.
  rewrite Z.mul_assoc, Z_mod_mult, Z.add_0_r, Z.mod_mod by (intro; discriminate).
  rewrite Z.add_mod by (intro; discriminate).
  rewrite Z_mod_mult, Z.add_0_r, Z.mod_mod by (intro; discriminate).
  assert (0 <= tag mod 256 < 256) by (apply Z_mod_lt; reflexivity).
  rewrite Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma raw_tag_lt_noscan: forall (g: LGraph) (v: VType),
    raw_mark (vlabel g v) = false ->
    Int.repr
      (Z.b2z
         (negb
            (Int.ltu
               (Int.repr (Int64.unsigned
                            (Int64.and (Int64.repr (make_header g v)) (Int64.repr 255))))
               (Int.repr 251)))) = Int.zero ->
    raw_tag (vlabel g v) < NO_SCAN_TAG.
Proof.
  intros g v Hrm HI. rewrite raw_tag_biteq in HI; auto.
  destruct (Int.ltu _ _) eqn:?HL in HI; try discriminate. clear HI.
  pose proof raw_tag_range (vlabel g v).
  forget (raw_tag (vlabel g v)) as tag.
  assert (0 <= tag mod 256 < 256) by (apply Z_mod_lt; reflexivity).
  apply ltu_repr in HL; auto; try rep_lia.
  rewrite Zmod_small in HL by auto. assumption.
Qed.

Lemma raw_tag_ge_noscan: forall (g: LGraph) (v: VType),
    raw_mark (vlabel g v) = false ->
    Int.repr
      (Z.b2z
         (negb
            (Int.ltu
               (Int.repr (Int64.unsigned
                            (Int64.and (Int64.repr (make_header g v)) (Int64.repr 255))))
               (Int.repr 251)))) <> Int.zero ->
    raw_tag (vlabel g v) >= NO_SCAN_TAG.
Proof.
  intros g v Hrm HI. rewrite raw_tag_biteq in HI; auto.
  destruct (Int.ltu _ _) eqn:?HL in HI; try contradiction. clear HI.
  pose proof raw_tag_range (vlabel g v).
  forget (raw_tag (vlabel g v)) as tag.
  assert (0 <= tag mod 256 < 256) by (apply Z_mod_lt; reflexivity).
  apply ltu_repr_false in HL; auto; try rep_lia.
  rewrite Zmod_small in HL by auto. assumption.
Qed.

Lemma forward_graph_and_heap_fc: forall from to depth p g h,
    from <> to ->
    forward_t_compatible p g ->
    forward_condition g h from to ->
    forall g' h', (g', h') = forward_graph_and_heap from to depth p g h ->
             forward_condition g' h' from to.
Proof.
  intros. pose proof fr_forward_graph_and_heap from to depth p g h. rewrite <- H2 in H3.
  simpl in H3. destruct H1 as [? [? [? [? ?]]]]. split; [|split; [|split; [|split]]].
  - eapply forward_graph_and_heap_estc; eassumption.
  - rewrite <- (fr_graph_has_gen depth from to); eassumption.
  - rewrite <- (fr_graph_has_gen depth from to); eassumption.
  - eapply fr_copy_compatible; eassumption.
  - eapply fr_no_dangling_dst; eassumption.
Qed.

Lemma cut_heap_relation: forall h i s, heap_relation h (cut_heap h i s).
Proof.
  intros. split; intros m;
    [rewrite cti_available_size | rewrite cti_space_start]; reflexivity.
Qed.

Lemma heaprel_forward_graph_and_heap: forall from to depth p g h,
    heap_relation h (snd (forward_graph_and_heap from to depth p g h)).
Proof.
  intros from to depth. induction depth; intros; pose proof (hr_refl h).
  - destruct p; simpl; [assumption..| |].
    + destruct (Nat.eq_dec _ _); simpl; [|assumption].
      destruct (raw_mark _) eqn:? ; simpl; [assumption | apply cut_heap_relation].
    + destruct (Nat.eq_dec _ _); simpl; [| assumption].
      destruct (raw_mark _) eqn:? ; simpl; [assumption | apply cut_heap_relation].
  - assert (Hloop: forall l gh,
               heap_relation (snd gh)
                 (snd (forward_gh_loop forward_graph_and_heap from to depth l gh))). {
      induction l; intros; simpl. apply hr_refl. destruct gh as [gg hh].
      eapply hr_trans; [apply IHdepth | apply IHl]. }
    destruct p; simpl; [assumption..| |].
    + destruct (Nat.eq_dec _ _); simpl; [|assumption].
      destruct (raw_mark _) eqn:? ; simpl; [assumption |].
      destruct (Z_lt_ge_dec _ _); [| apply cut_heap_relation].
      eapply hr_trans; [| apply Hloop]. simpl. apply cut_heap_relation.
    + destruct (Nat.eq_dec _ _); simpl; [|assumption].
      destruct (raw_mark _) eqn:? ; simpl; [assumption |].
      destruct (Z_lt_ge_dec _ _); [| apply cut_heap_relation].
      eapply hr_trans; [| apply Hloop]. simpl. apply cut_heap_relation.
Qed.

Lemma forward_gh_loop_ghc: forall from to depth v l g h,
    from <> to ->
    no_dangling_dst g ->
    graph_has_gen g to ->
    enough_space_to_copy g h from to ->
    copy_compatible g ->
    graph_has_v g v ->
    graph_heap_compatible g h ->
    Forall (is_field_same_v g v) l ->
    forall g' h', (g', h') = forward_gh_loop forward_graph_and_heap from to depth l (g, h) ->
             graph_heap_compatible g' h'.
Proof.
  intros from to depth v.
  induction l; intros g h H H0 H1 H2 H3 H4 H5 Hl g' h' Hgh'; simpl in *.
  1: inversion Hgh'; assumption.
  remember (forward_graph_and_heap from to _ _ _ _) as gh. destruct gh as [gg hh].
  pose proof (fr_forward_graph_and_heap from to depth (interior2forward a g) g h) as Hfr.
  rewrite <- Heqgh in Hfr. simpl fst in Hfr. rewrite Forall_cons_iff in Hl.
  destruct Hl as [Ha Hl]. destruct Ha as [i [Ha Hi]]. subst a. simpl interior2forward in *.
  assert (Ha: forward_t_compatible (field2forward (Znth i (make_fields g v))) g). {
    apply vertex_pos_forward_t_compatible; auto.
    rewrite <- make_fields_eq_length. assumption. }
  apply (IHl gg hh); auto.
  - eapply fr_no_dangling_dst; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply forward_graph_and_heap_estc; eauto.
  - eapply fr_copy_compatible; eauto.
  - eapply fr_graph_has_v; eauto.
  - apply (forward_graph_and_heap_ghc from to depth
             (field2forward (Znth i (make_fields g v))) g h); auto.
  - rewrite <- fr_is_field_same_v; eassumption.
Qed.

Lemma forward_gh_loop_fc: forall from to depth v l g h,
    from <> to ->
    graph_has_v g v ->
    forward_condition g h from to ->
    Forall (is_field_same_v g v) l ->
    forall g' h', (g', h') = forward_gh_loop forward_graph_and_heap from to depth l (g, h) ->
             forward_condition g' h' from to.
Proof.
  intros from to depth v l. induction l; intros g h H H0 Hfc Hl g' h' Hgh'; simpl in *.
  1: inversion Hgh'; assumption.
  remember (forward_graph_and_heap from to _ _ _ _) as gh. destruct gh as [gg hh].
  pose proof (fr_forward_graph_and_heap from to depth (interior2forward a g) g h) as Hfr.
  rewrite <- Heqgh in Hfr. simpl fst in Hfr. rewrite Forall_cons_iff in Hl.
  destruct Hl as [Ha Hl]. destruct Ha as [i [Ha Hi]]. subst a. simpl interior2forward in *.
  assert (Ha: forward_t_compatible (field2forward (Znth i (make_fields g v))) g). {
    apply vertex_pos_forward_t_compatible; auto.
    rewrite <- make_fields_eq_length. assumption. } apply (IHl gg hh); auto.
  - destruct Hfc as [? [? [? [? ?]]]]. eapply fr_graph_has_v; eauto.
  - eapply forward_graph_and_heap_fc; eauto.
  - destruct Hfc as [? [? [? [? ?]]]]. rewrite <- fr_is_field_same_v; eassumption.
Qed.

Lemma fl_outlier_compatible_helper:
  forall (from to depth: nat) outlier (g g' : LGraph) (v : VType) (l : list interior_t),
    from <> to ->
    (forall (p : forward_t) (g1 g2 : LGraph),
        graph_has_gen g1 to ->
        copy_compatible g1 ->
        no_dangling_dst g1 ->
        forward_t_compatible p g1 ->
        forward_relation from to depth p g1 g2 ->
        outlier_compatible g1 outlier -> outlier_compatible g2 outlier) ->
    graph_has_gen g to ->
    copy_compatible g ->
    no_dangling_dst g ->
    graph_has_v g v ->
    Forall (is_field_same_v g v) l ->
    forward_loop from to depth l g g' ->
    outlier_compatible g outlier -> outlier_compatible g' outlier.
Proof.
  intros from to depth outlier g g' v l Hft IHdepth. revert g g'.
  induction l; intros g g' Hgen Hcp Hndg Hv Hl Hfl Ho; inversion Hfl; subst; clear Hfl; auto.
  rewrite Forall_cons_iff in Hl. destruct Hl as [[i [Ha Hi]] Hl]. subst a.
  simpl interior2forward in *.
  assert (Hc: forward_t_compatible (field2forward (Znth i (make_fields g v))) g). {
    apply vertex_pos_forward_t_compatible; auto. now rewrite <- make_fields_eq_length. }
  apply (IHl g2); auto.
  - rewrite <- fr_graph_has_gen; eassumption.
  - eapply fr_copy_compatible; eassumption.
  - eapply fr_no_dangling_dst; eassumption.
  - eapply fr_graph_has_v; eassumption.
  - rewrite <- fr_is_field_same_v; eassumption.
  - specialize (IHdepth (field2forward (Znth i (make_fields g v))) g g2).
    apply IHdepth; assumption.
Qed.

Lemma fr_outlier_compatible: forall from to outlier depth p g1 g2,
    from <> to ->
    graph_has_gen g1 to ->
    copy_compatible g1 ->
    no_dangling_dst g1 ->
    forward_t_compatible p g1 ->
    forward_relation from to depth p g1 g2 ->
    outlier_compatible g1 outlier -> outlier_compatible g2 outlier.
Proof.
  intros from to outlier depth p g1 g2 Hft. revert p g1 g2.
  induction depth; intros p g1 g2 Hgen Hcp Hndg Hfc Hfr Ho.
  - destruct p; simpl in Hfc; inversion Hfr; subst; clear Hfr; try assumption.
    + apply lcv_outlier_compatible; assumption.
    + subst new_g. apply lgd_outlier_compatible. destruct Hfc as [Hf Hin].
      specialize (Hndg _ Hf _ Hin). apply lcv_outlier_compatible; assumption.
  - destruct p; simpl in Hfc; inversion Hfr; subst; clear Hfr; try assumption.
    + eapply fl_outlier_compatible_helper with (g := new_g); try eassumption; subst new_g.
      * apply lcv_graph_has_gen; assumption.
      * apply lcv_copy_compatible; assumption.
      * apply lcv_no_dangling_dst; assumption.
      * apply lcv_graph_has_v_new. assumption.
      * apply vertex_pos_pairs_in_range.
      * apply lcv_outlier_compatible; assumption.
    + apply lcv_outlier_compatible; assumption.
    + assert (graph_has_v g1 (dst g1 e)) by
        (destruct Hfc as [Hf Hin]; apply (Hndg _ Hf _ Hin)).
      eapply fl_outlier_compatible_helper with (g := new_g); try eassumption; subst new_g.
      * apply lgd_graph_has_gen. apply lcv_graph_has_gen; assumption.
      * apply lgd_copy_compatible. apply lcv_copy_compatible; assumption.
      * apply lgd_no_dangling_dst.
        -- apply lcv_graph_has_v_new. assumption.
        -- apply lcv_no_dangling_dst; assumption.
      * apply lgd_graph_has_v. apply lcv_graph_has_v_new. assumption.
      * apply vertex_pos_pairs_in_range.
      * apply lgd_outlier_compatible. apply lcv_outlier_compatible; assumption.
    + subst new_g. apply lgd_outlier_compatible. destruct Hfc as [Hf Hin].
      specialize (Hndg _ Hf _ Hin). apply lcv_outlier_compatible; assumption.
Qed.

Lemma fl_outlier_compatible: forall from to outlier v depth l g1 g2,
    from <> to ->
    graph_has_gen g1 to ->
    copy_compatible g1 ->
    no_dangling_dst g1 ->
    graph_has_v g1 v ->
    Forall (is_field_same_v g1 v) l ->
    forward_loop from to depth l g1 g2 ->
    outlier_compatible g1 outlier -> outlier_compatible g2 outlier.
Proof.
  intros from to outlier v depth l g1 g2 Hft. revert g1 g2.
  induction l; intros g1 g2 Hgen Hcp Hndg Hv Hl Hfl Ho;
    inversion Hfl; subst; clear Hfl; auto. rewrite Forall_cons_iff in Hl.
  destruct Hl as [[i [Ha Hi]] Hl]. subst a. simpl interior2forward in *.
  assert (Ha: forward_t_compatible (field2forward (Znth i (make_fields g1 v))) g1). {
    apply vertex_pos_forward_t_compatible; auto.
    rewrite <- make_fields_eq_length. assumption. }
  apply (IHl g3); auto.
  - rewrite <- fr_graph_has_gen; eassumption.
  - eapply fr_copy_compatible; eassumption.
  - eapply fr_no_dangling_dst; eassumption.
  - eapply fr_graph_has_v; eassumption.
  - rewrite <- fr_is_field_same_v; eassumption.
  - eapply fr_outlier_compatible; eassumption.
Qed.

Lemma forward_gh_loop_app: forall f from to depth l1 l2 gh,
    forward_gh_loop f from to depth (l1 ++ l2) gh =
      forward_gh_loop f from to depth l2 (forward_gh_loop f from to depth l1 gh).
Proof. intros. unfold forward_gh_loop. apply fold_left_app. Qed.

Lemma forward_gh_loop_add_tail: forall f from to depth l intr gh1 g2 h2 gh3,
    (g2, h2) = forward_gh_loop f from to depth l gh1 ->
    gh3 = f from to depth (interior2forward intr g2) g2 h2 ->
    gh3 = forward_gh_loop f from to depth (l +:: intr) gh1.
Proof. intros. rewrite forward_gh_loop_app. rewrite <- H. assumption. Qed.

Lemma forward_gh_loop_add_tail_vpp: forall from to depth g x i gh1 g2 h2 gh3,
    0 <= i < Zlength (raw_fields (vlabel g x)) ->
    (g2, h2) = forward_gh_loop forward_graph_and_heap
                 from to depth (sublist 0 i (vertex_pos_pairs g x)) gh1 ->
    gh3 = forward_graph_and_heap from to depth
            (field2forward (Znth i (make_fields g2 x))) g2 h2 ->
    gh3 = forward_gh_loop forward_graph_and_heap from to depth
            (sublist 0 (i + 1) (vertex_pos_pairs g x)) gh1.
Proof.
  intros. rewrite <- vpp_Zlength in H. rewrite sublist_last_1; [|lia..].
  rewrite vpp_Zlength in H. rewrite vpp_Znth by assumption.
  eapply forward_gh_loop_add_tail with (g2 := g2); eassumption.
Qed.

Lemma gen_range: forall g h gen,
    graph_heap_compatible g h -> graph_has_gen g gen -> 0 <= Z.of_nat gen < MAX_SPACES.
Proof.
  intros g h gen Hghc Hgen. destruct Hghc as [_ [_ ?]]. red in Hgen.
  pose proof spaces_size h as Hsp. rewrite Zlength_correct in Hsp. lia.
Qed.

Lemma lcv_rootpairs_compatible':
  forall (g : LGraph) (to : nat) (rootpairs : list rootpair) (roots : list exterior_t) (i : Z),
    graph_has_gen g to ->
    roots_graph_compatible roots g ->
    rootpairs_compatible g rootpairs roots ->
    forall v : VType,
      rootpairs_compatible (lgraph_copy_v g v to)
        (update_rootpairs rootpairs
           (map (exterior2val (lgraph_copy_v g v to))
              (upd_Znth i roots (ExteriorVertex (new_copied_v g to)))))
        (upd_Znth i roots (ExteriorVertex (new_copied_v g to))).
Proof.
  intros g to rootpairs roots i Hghg Hrgc Hrc v.
  assert (map (exterior2val (lgraph_copy_v g v to)) roots = map rp_val rootpairs). {
    hnf in Hrc. rewrite <- Hrc. rewrite map_ext_in_iff. intros. destruct a; simpl; auto.
    apply lcv_vertex_address_old; auto. hnf in Hrgc. rewrite Forall_forall in Hrgc.
    apply Hrgc. now rewrite <- (filter_proj_In_iff exterior_proj_vertex_spec). }
  destruct (Sumbool.sumbool_and (0 <= i)%Z (0 > i)%Z (i < Zlength roots)%Z
              (~ (i < Zlength roots)%Z)
              (Z_le_gt_dec 0 i) (Z_lt_dec i (Zlength roots))).
  - rewrite <- upd_Znth_map. simpl exterior2val. rewrite lcv_vertex_address_new, H; auto.
    apply lcv_rootpairs_compatible; assumption.
  - rewrite !upd_Znth_out_of_range by list_solve. rewrite H, update_rootpairs_same.
    apply lcv_rootpairs_compatible_unchanged; assumption.
Qed.

Lemma fr_O_rootpairs_compatible: forall g g' from to rootpairs roots roots' i,
    graph_has_gen g to ->
    roots_graph_compatible roots g ->
    rootpairs_compatible g rootpairs roots ->
    forward_relation from to O (exterior2forward (Znth i roots)) g g' ->
    roots' = upd_roots from to i g roots ->
    rootpairs_compatible g'
      (update_rootpairs rootpairs (map (exterior2val g') roots')) roots'.
Proof.
  unfold upd_roots. intros g g' from to rootpairs roots roots' i Hghg Hrgc Hrc Hfr Hr.
  destruct (Znth i roots) eqn: Heqr; simpl in *.
  - inversion Hfr; subst g'; subst. apply upd_rootpairs_compatible'; assumption.
  - inversion Hfr; subst g'; subst. apply upd_rootpairs_compatible'; assumption.
  - unfold update_vertex in Hr. inversion Hfr; subst g' g0 v0.
    + destruct (Nat.eq_dec _ _); [contradiction |]. subst.
      apply upd_rootpairs_compatible'; assumption.
    + destruct (Nat.eq_dec _ _); [|contradiction]. rewrite H2 in Hr. subst.
      apply upd_rootpairs_compatible'; assumption.
    + destruct (Nat.eq_dec _ _); [|contradiction]. rewrite H1 in Hr. subst.
      apply upd_rootpairs_compatible', lcv_rootpairs_compatible_unchanged; assumption.
Qed.

Lemma map_rpval_update_rootpairs: forall (rp : list rootpair) (v : list val),
    Zlength v = Zlength rp -> map rp_val (update_rootpairs rp v) = v.
Proof.
  induction rp; simpl; intros.
  - destruct v; auto. list_solve.
  - destruct a. destruct v as [|v rest]; simpl; auto. f_equal. apply IHrp; list_solve.
Qed.

Lemma fr_O_rootpairs_compatible_unchanged: forall g g' from to rootpairs roots intr,
    graph_has_gen g to ->
    roots_graph_compatible roots g ->
    rootpairs_compatible g rootpairs roots ->
    forward_relation from to O (interior2forward intr g) g g' ->
    rootpairs_compatible g' rootpairs roots.
Proof.
  intros g g' from to rootpairs roots intr Hghg Hrgc Hrc Hfr.
  destruct intr eqn: Heqr; simpl in *. inversion Hfr; subst g'; subst; auto.
  - apply lcv_rootpairs_compatible_unchanged; assumption.
  - subst new_g.
    apply lgd_fun_thread_arg_compatible, lcv_rootpairs_compatible_unchanged; auto.
Qed.

Lemma svfl_roots_graph_compatible: forall from to v roots l g1 g2,
    graph_has_gen g1 to ->
    roots_graph_compatible roots g1 ->
    scan_vertex_for_loop from to v l g1 g2 ->
    roots_graph_compatible roots g2.
Proof.
  intros from to v roots l. induction l; intros g1 g2 Hghg Hrgc Hsvfl.
  - inversion Hsvfl; subst; auto.
  - inversion Hsvfl; subst; clear Hsvfl. eapply IHl with (g1 := g3); eauto.
    + rewrite <- fr_graph_has_gen; eassumption.
    + eapply fr_roots_graph_compatible; eassumption.
Qed.

Lemma do_scan_rootpairs_compatible: forall from to idx g1 g2 rootpairs roots,
    graph_has_gen g1 to ->
    roots_graph_compatible roots g1 ->
    rootpairs_compatible g1 rootpairs roots ->
    do_scan_relation from to idx g1 g2 ->
    rootpairs_compatible g2 rootpairs roots.
Proof.
  intros from to idx g1 g2 rootpairs roots Hghg Hrgc Hrc Hdsr.
  destruct Hdsr as [n [Hsvwl Hno]]. remember (seq _ _). clear Heql Hno n.
  revert g1 g2 Hghg Hrgc Hrc Hsvwl. induction l; intros.
  - inversion Hsvwl. subst. auto.
  - inversion Hsvwl; subst; clear Hsvwl.
    + eapply IHl; eauto.
    + eapply IHl with (g1 := g3); eauto.
      * rewrite <- svfl_graph_has_gen; eauto.
      * eapply svfl_roots_graph_compatible; eassumption.
      * clear dependent g2. clear l H1 H2 IHl. remember (nat_inc_list _). remember (to, a).
        clear Heql Heqp. revert g1 g3 H3 Hghg Hrgc Hrc. induction l; intros.
        -- inversion H3; subst; auto.
        -- inversion H3; subst; clear H3. eapply IHl; eauto.
           ++ rewrite <- fr_graph_has_gen; eauto.
           ++ eapply fr_roots_graph_compatible; eauto.
           ++ eapply fr_O_rootpairs_compatible_unchanged; eauto.
Qed.

Lemma do_scan_roots_compatible: forall from to idx g1 g2 outlier roots,
    graph_has_gen g1 to ->
    roots_compatible g1 outlier roots ->
    do_scan_relation from to idx g1 g2 ->
    roots_compatible g2 outlier roots.
Proof.
  intros from to idx g1 g2 outlier roots Hghg [Hroc Hrgc] Hdsr. split; auto.
  clear dependent outlier. destruct Hdsr as [n [Hsvwl Hno]]. remember (seq _ _).
  clear Heql Hno n. revert g1 g2 Hghg Hrgc Hsvwl.
  induction l; intros;  inversion Hsvwl; subst; clear Hsvwl; auto. 1: eapply IHl; eauto.
  eapply IHl with (g1 := g3); eauto.
  - rewrite <- svfl_graph_has_gen; eassumption.
  - eapply svfl_roots_graph_compatible; eassumption.
Qed.

Inductive remset_ext :=
| RemSetOutlier : GC_Pointer -> val -> remset_ext
| RemSetVertex: VType -> val -> remset_ext.

#[export] Instance remset_ext_inhabitant: Inhabitant remset_ext :=
  RemSetVertex (O, O) nullval.

Definition extract_address (rext: remset_ext) : val :=
  match rext with
  | RemSetOutlier _ adr
  | RemSetVertex _ adr => adr
  end.

Inductive remset_space_item :=
| RemSetExterior: val -> remset_space_item
| RemSetInterior: interior_t -> remset_space_item.

Definition remset_space := list remset_space_item.

Definition remset_heap := list remset_space.

Definition remset := list remset_ext.

Definition remset_nodup (rmst: remset) : Prop := NoDup (map extract_address rmst).

Definition remset_space_size_compatible (items: remset_space) (sp: space): Prop :=
  if (Val.eq sp.(space_start) nullval)
  then Zlength items = 0
  else Zlength items = total_space sp - available_space sp.

Definition remset_item_val (g: LGraph) (item: remset_space_item) : val :=
  match item with
  | RemSetExterior v => v
  | RemSetInterior (InteriorVertexPos v pos) =>
      offset_val (pos * WORD_SIZE) (vertex_address g v)
  end.

Definition remset_ext_compatible (g: LGraph) (outlier: outlier_t) (re: remset_ext) : Prop :=
  match re with
  | RemSetOutlier p _ => In p outlier
  | RemSetVertex vtx _ => graph_has_v g vtx
  end.

(* weaker version *)
Definition remset_ext_compatible' (g: LGraph) (re: remset_ext) : Prop :=
  match re with
  | RemSetOutlier p _ => True
  | RemSetVertex vtx _ => graph_has_v g vtx
  end.

Definition remset_item_compatible (g: LGraph) (from: nat)
  (rst: remset) (item: remset_space_item) : Prop :=
  match item with
  | RemSetExterior addr => In addr (map extract_address rst)
  | RemSetInterior (InteriorVertexPos vtx n) =>
      graph_has_v g vtx /\ 0 <= n < Zlength (raw_fields (vlabel g vtx)) /\
        (vgeneration vtx <> from -> raw_mark (vlabel g vtx) = false /\
                                  raw_tag (vlabel g vtx) < NO_SCAN_TAG)
  end.

Definition remset_space_compatible (g: LGraph) (from: nat) (rst: remset)
  (items: remset_space) (sp: space) : Prop :=
  Forall (remset_item_compatible g from rst) items /\ remset_space_size_compatible items sp.

Definition remset_heap_compatible (g: LGraph) (from: nat) (rst: remset)
  (rh: remset_heap) (h: heap) : Prop :=
  Forall2 (remset_space_compatible g from rst) rh (spaces h).

Definition remset_compatible (g: LGraph) (outlier: outlier_t) (rmst: remset) : Prop :=
  Forall (remset_ext_compatible g outlier) rmst.

Definition remset_compatible' (g: LGraph) (rmst: remset) : Prop :=
  Forall (remset_ext_compatible' g) rmst.

Definition remset_gen_size (h: heap) (gen: nat): Z :=
  total_space (nth_space h gen) - available_size h gen.

Definition enough_space_enhanced g h from to: Prop :=
  general_enough_space_to_copy g h from to (remset_gen_size h from).

Definition forward_remset_condition g h from to : Prop :=
  enough_space_enhanced g h from to /\ graph_has_gen g from /\ graph_has_gen g to /\
    copy_compatible g /\ no_dangling_dst g.

Lemma unmarked_gen_size_nonneg: forall g gen, 0 <= unmarked_gen_size g gen.
Proof. intros. unfold unmarked_gen_size. apply vs_accum_list_le. Qed.

Definition find_remset_ext (addr: val) (rmst: remset) : option remset_ext :=
  find (fun rext => if Val.eq (extract_address rext) addr then true else false) rmst.

Lemma find_remset_ext_In_some: forall addr rmst,
    In addr (map extract_address rmst) ->
    exists rext, find_remset_ext addr rmst = Some rext /\ extract_address rext = addr.
Proof.
  intros. unfold find_remset_ext. induction rmst; simpl in H. 1: contradiction. destruct H.
  - exists a. simpl. destruct (Val.eq (extract_address a) addr); auto. contradiction.
  - specialize (IHrmst H). simpl. destruct (Val.eq (extract_address a) addr); auto. exists a. tauto.
Qed.

Lemma find_remset_ext_some: forall addr rmst rext,
    find_remset_ext addr rmst = Some rext -> In rext rmst /\ extract_address rext = addr.
Proof.
  unfold find_remset_ext. intros. apply find_some in H. destruct H. split; auto.
  destruct (Val.eq _ _); auto. discriminate.
Qed.

Definition remset_item_in_gen (item: remset_space_item) (rmst: remset)
  (g: LGraph) (gen: nat): bool :=
  match item with
  | RemSetInterior intr => match interior2forward intr g with
                          | ForwardEdge e => Nat.eqb (vgeneration (dst g e)) gen
                          | _ => false
                          end
  | RemSetExterior v => match find_remset_ext v rmst with
                       | None => false (* would not happen *)
                       | Some rext => match rext with
                                     | RemSetOutlier _ _ => false
                                     | RemSetVertex vtx _ => Nat.eqb (vgeneration vtx) gen
                                     end
                       end
  end.

Lemma remain_ula: forall sp, used_space sp < available_space sp ->
                        0 <= used_space sp <= available_space sp - 1.
Proof. intros. pose proof used_leq_available sp. lia. Qed.

Lemma remain_alt: forall sp, available_space sp - 1 <= total_space sp.
Proof. intros. pose proof available_leq_total sp. lia. Qed.

Definition incr_remset_space (sp: space) : space :=
  match (Z_lt_ge_dec (used_space sp) (available_space sp)) with
  | left H => Build_space (space_start sp) (used_space sp) (available_space sp - 1)
               (total_space sp) (space_sh sp) (remain_ula sp H)
               (remain_alt sp) (space_upper_bound sp)
  | right _ => sp
  end.

Lemma incr_remset_heap_size: forall (h : heap) (i : Z) ,
    0 <= i < Zlength (spaces h) ->
    Zlength (upd_Znth i (spaces h) (incr_remset_space (Znth i (spaces h)))) = MAX_SPACES.
Proof. intros. rewrite upd_Znth_Zlength; [apply spaces_size | assumption]. Qed.

Definition incr_remset_heap (h: heap) (i: Z): heap :=
  match spaces_index_dec i h with
  | left H => Build_heap (upd_Znth i (spaces h) (incr_remset_space (Znth i (spaces h))))
               (incr_remset_heap_size h i H)
  | right _ => h
  end.

Definition upd_remset_ext (from to: nat) (g: LGraph) (rext: remset_ext) : remset_ext :=
  match rext with
  | RemSetVertex vertex v => RemSetVertex (update_vertex from to g vertex) v
  | _ => rext
  end.

Definition remset_ext2foward_t (rext: remset_ext) : forward_t :=
  match rext with
  | RemSetOutlier out _ => ForwardOutlier out
  | RemSetVertex v _ => ForwardVertex v
  end.

Definition remset_item2forward_t (item: remset_space_item) (rmst: remset)
  (g: LGraph) : forward_t :=
  match item with
  | RemSetInterior intr => interior2forward intr g
  | RemSetExterior v => match find_remset_ext v rmst with
                       | None => ForwardUnboxed 0 (* would not happen *)
                       | Some rext => remset_ext2foward_t rext
                       end
  end.

Definition upd_remset_heap (item: remset_space_item) (rh: remset_heap)
  (to: nat) : remset_heap := upd_Znth (Z.of_nat to) rh (cons item (Znth (Z.of_nat to) rh)).

Fixpoint upd_remset_addr (from to: nat) (g: LGraph) (addr: val) (rmst: remset) : remset :=
  match rmst with
  | [] => []
  | rext :: rest => if Val.eq addr (extract_address rext)
                  then upd_remset_ext from to g rext :: rest
                  else rext :: upd_remset_addr from to g addr rest
  end.

Definition upd_remset (from to: nat) (g: LGraph) (item: remset_space_item)
  (rmst: remset) : remset :=
  match item with
  | RemSetExterior addr => upd_remset_addr from to g addr rmst
  | _ => rmst
  end.

Definition forward_remset_item (from to: nat) (ghrr: LGraph * heap * remset_heap * remset)
  (item: remset_space_item) : (LGraph * heap * remset_heap * remset) :=
  let '(g, h, rh, rmst) := ghrr in
  if negb (remset_item_in_gen item rmst g from) then
    let (new_g, new_h) :=
      forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h in
    (new_g, incr_remset_heap new_h (Z.of_nat to), upd_remset_heap item rh to,
      upd_remset from to g item rmst)
  else (g, h, rh, rmst).

Definition forward_remset_gh (from to : nat) (g: LGraph) (h: heap) (rh: remset_heap)
  (rmst: remset) : (LGraph * heap * remset_heap * remset) :=
  fold_left (forward_remset_item from to) (nth from rh []) (g, h, rh, rmst).

Lemma remset_ext_compatible_weakened: forall g outlier re,
    remset_ext_compatible g outlier re -> remset_ext_compatible' g re.
Proof. intros g outlier re Hrec. destruct re; simpl in *; auto. Qed.

Lemma remset_compatible_weakened: forall g outlier rmst,
    remset_compatible g outlier rmst -> remset_compatible' g rmst.
Proof.
  unfold remset_compatible, remset_compatible'. intros g outlier rmst Hrec.
  rewrite Forall_forall in *. intros x Hin. specialize (Hrec _ Hin).
  eapply remset_ext_compatible_weakened; eassumption.
Qed.

Lemma remset_item2forward_t_ftc: forall g item rmst from,
    remset_compatible' g rmst ->
    remset_item_compatible g from rmst item ->
    forward_t_compatible (remset_item2forward_t item rmst g) g.
Proof.
  intros g item rmst from Hrc Hric. destruct item; simpl in *.
  - apply find_remset_ext_In_some in Hric. destruct Hric as [rext [? ?]]. rewrite H.
    apply find_remset_ext_some in H. destruct rext; simpl; auto.
    hnf in Hrc. rewrite Forall_forall in Hrc. destruct H as [H _]. apply Hrc in H. simpl in H. assumption.
  - destruct i. simpl. apply vertex_pos_forward_t_compatible; tauto.
Qed.

Lemma irs_space_start: forall sp,
    space_start (incr_remset_space sp) = space_start sp.
Proof. intros. unfold incr_remset_space. destruct (Z_lt_ge_dec _ _); reflexivity. Qed.

Lemma incr_remset_heap_ghc: forall g h i,
    graph_heap_compatible g h ->
    graph_heap_compatible g (incr_remset_heap h i).
Proof.
  unfold incr_remset_heap. intros. destruct (spaces_index_dec i h); auto.
  unfold graph_heap_compatible in *. simpl.
  destruct H as [? [? ?]]. split; [|split].
  - rewrite gsc_iff in H by assumption.
    rewrite gsc_iff' by (rewrite <- !ZtoNat_Zlength, Zlength_upd_Znth,
                          !ZtoNat_Zlength; assumption). intros. specialize (H _ H2).
    change null_space with (@default space space_inhabitant). rewrite (nth_Znth' gen).
    assert (generation_space_compatible g (gen, nth_gen g gen, Znth (Z.of_nat gen) (spaces h)))
             by (rewrite <- nth_Znth'; assumption).
    destruct (Z.eq_dec (Z.of_nat gen) i).
    + subst. rewrite upd_Znth_same by assumption. unfold incr_remset_space.
      destruct (Z_lt_ge_dec _ _); auto.
    + rewrite Znth_upd_Znth_diff; auto.
  - now rewrite <- upd_Znth_map, irs_space_start, upd_Znth_map, upd_Znth_unchanged'.
  - rewrite <- !ZtoNat_Zlength, Zlength_upd_Znth, !ZtoNat_Zlength; assumption.
Qed.

Lemma fgh_O_graph_has_v_update_vertex: forall from to g vtx h newg newh,
    graph_has_gen g to ->
    graph_has_v g vtx ->
    copy_compatible g ->
    forward_graph_and_heap from to 0 (ForwardVertex vtx) g h = (newg, newh) ->
    graph_has_v newg (update_vertex from to g vtx).
Proof.
  intros from to g vtx h newg newh Hghg Hghv Hcc Hfgh. simpl in *. unfold update_vertex.
  destruct (Nat.eq_dec _ _).
  - destruct (raw_mark _) eqn:?H; inversion Hfgh; subst.
    + hnf in Hcc. specialize (Hcc _ Hghv H). destruct Hcc; assumption.
    + apply lcv_graph_has_v_new. assumption.
  - inversion Hfgh. subst. assumption.
Qed.

Lemma remset_gen_size_noneg: forall h gen, 0 <= remset_gen_size h gen.
Proof.
  intros. unfold remset_gen_size, available_size.
  pose proof available_leq_total (nth_space h gen). lia.
Qed.

Lemma ese_has_space: forall to g h v,
    graph_has_v g v -> raw_mark (vlabel g v) = false ->
    enough_space_enhanced g h (vgeneration v) to ->
    has_space (Znth (Z.of_nat to) (spaces h)) (vertex_size g v).
Proof. intros. eapply gestc_has_space; eauto. apply remset_gen_size_noneg. Qed.

Lemma lacv_ese: forall g t_info from to v,
    from <> to -> graph_has_gen g to ->
    enough_space_enhanced g t_info from to ->
    enough_space_enhanced (lgraph_add_copied_v g v to) t_info from to.
Proof. intros. apply lacv_gestc; auto. Qed.

Lemma cut_heap_remset_gen_size_the_same: forall h i s gen,
    remset_gen_size (cut_heap h i s) gen = remset_gen_size h gen.
Proof.
  intros. unfold remset_gen_size. rewrite cti_available_size, cti_total_space. reflexivity.
Qed.

Lemma lmc_enough_space_enhanced:
  forall (g : LGraph) (h : heap) (v v': VType) (to : nat),
    enough_space_enhanced g h (vgeneration v) to ->
    graph_has_v g v -> raw_mark (vlabel g v) = false ->
    enough_space_enhanced (lgraph_mark_copied g v v')
      (cut_heap h (Z.of_nat to) (vertex_size g v)) (vgeneration v) to.
Proof.
  intros. apply lmc_general_enough_space_to_copy; auto.
  - rewrite cut_heap_remset_gen_size_the_same; assumption.
  - apply remset_gen_size_noneg.
Qed.

Lemma lcv_enough_space_enhanced: forall g h v to,
    vgeneration v <> to -> graph_has_gen g to ->
    graph_has_v g v -> raw_mark (vlabel g v) = false ->
    enough_space_enhanced g h (vgeneration v) to ->
    enough_space_enhanced (lgraph_copy_v g v to)
         (cut_heap h (Z.of_nat to) (vertex_size g v)) (vgeneration v) to.
Proof.
  intros. apply lcv_general_enough_space_to_copy; auto.
  - rewrite cut_heap_remset_gen_size_the_same; assumption.
  - apply remset_gen_size_noneg.
Qed.

Lemma lgd_enough_space_enhanced: forall g e v' t_info gen sp,
    enough_space_enhanced g t_info gen sp ->
    enough_space_enhanced (labeledgraph_gen_dst g e v') t_info gen sp.
Proof. intros. apply lgd_general_enough_space_to_copy; auto. Qed.

Lemma fgah_O_remset_gen_size: forall from to p g h g' h',
    (g', h') = forward_graph_and_heap from to O p g h ->
    remset_gen_size h' from = remset_gen_size h from.
Proof.
  simpl. intros. destruct p; [inversion H; reflexivity.. | |];
    destruct (Nat.eq_dec _ _); [| inversion H; reflexivity | | inversion H; reflexivity];
    destruct (raw_mark _); inversion H; try reflexivity;
    rewrite cut_heap_remset_gen_size_the_same; reflexivity.
Qed.

Lemma forward_gh_loop_remset_gen_size: forall (from to depth : nat)
                              (l : list interior_t) (gg : LGraph) (hh : heap),
    (forall (p : forward_t) (g : LGraph) (h : heap) (g' : LGraph) (h' : heap),
        (g', h') = forward_graph_and_heap from to depth p g h ->
        remset_gen_size h' from = remset_gen_size h from) ->
    forall g' h', (g', h') = forward_gh_loop forward_graph_and_heap from to depth l (gg, hh) ->
        remset_gen_size h' from = remset_gen_size hh from.
Proof.
  intros from to depth l gg hh IHdepth. revert l gg hh. induction l; intros; simpl in H.
  1: inversion H; reflexivity. remember (forward_graph_and_heap _ _ _ _ _ _).
  destruct p as [newg newh]. apply IHl in H; auto.
  apply IHdepth in Heqp. transitivity (remset_gen_size newh from); assumption.
Qed.

Lemma fgah_remset_gen_size: forall from to depth p g h g' h',
    (g', h') = forward_graph_and_heap from to depth p g h ->
    remset_gen_size h' from = remset_gen_size h from.
Proof.
  intros from to depth. induction depth; intros.
  1: eapply fgah_O_remset_gen_size; eassumption.
  destruct p; simpl in H; [inversion H; reflexivity..| |]; destruct (Nat.eq_dec _ _);
    try (inversion H; reflexivity); destruct (raw_mark _); try (inversion H; reflexivity);
  destruct (Z_lt_ge_dec _ _).
  - apply forward_gh_loop_remset_gen_size in H; auto.
    rewrite cut_heap_remset_gen_size_the_same in H. assumption.
  - inversion H. rewrite cut_heap_remset_gen_size_the_same; reflexivity.
  - apply forward_gh_loop_remset_gen_size in H; auto.
    rewrite cut_heap_remset_gen_size_the_same in H. assumption.
  - inversion H. rewrite cut_heap_remset_gen_size_the_same; reflexivity.
Qed.

Lemma forward_graph_and_heap_O_ese: forall from to p g h,
    from <> to ->
    forward_t_compatible p g ->
    no_dangling_dst g ->
    graph_has_gen g to ->
    enough_space_enhanced g h from to ->
    forall g' h',
      (g', h') = forward_graph_and_heap from to O p g h ->
      enough_space_enhanced g' h' from to.
Proof.
  intros. eapply forward_graph_and_heap_O_gestc; eauto.
  - apply fgah_O_remset_gen_size in H4. rewrite H4. assumption.
  - apply remset_gen_size_noneg.
Qed.

Lemma forward_graph_and_heap_ese: forall from to depth p g h,
    from <> to ->
    forward_t_compatible p g ->
    no_dangling_dst g ->
    graph_has_gen g to ->
    copy_compatible g ->
    enough_space_enhanced g h from to ->
    forall g' h',
      (g', h') = forward_graph_and_heap from to depth p g h ->
      enough_space_enhanced g' h' from to.
Proof.
  intros. eapply forward_graph_and_heap_gestc; eauto.
  - apply remset_gen_size_noneg.
  - apply fgah_remset_gen_size in H5. rewrite H5. assumption.
Qed.

Opaque forward_graph_and_heap.

Lemma forward_remset_item_ghc: forall from to g h rh rmst item g' h' rh' rmst',
    graph_heap_compatible g h ->
    no_dangling_dst g ->
    graph_has_gen g to ->
    enough_space_to_copy g h from to ->
    remset_compatible' g rmst ->
    remset_item_compatible g from rmst item ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    graph_heap_compatible g' h'.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' Hghc Hndd Hghg Hestc Hrc Hric Hfri.
  simpl in Hfri. destruct (negb _) eqn:?H. 2: inversion Hfri; assumption.
  destruct (forward_graph_and_heap _ _ _ _ _ _) as [newg newh] eqn:?H.
  pose proof remset_item2forward_t_ftc g item rmst from Hrc Hric.
  symmetry in H0. eapply forward_graph_and_heap_O_ghc in H0; eauto.
  inversion Hfri. subst. apply incr_remset_heap_ghc. assumption.
Qed.

Lemma gestc_estc: forall (g: LGraph) (h: heap) from to size,
    0 <= size -> general_enough_space_to_copy g h from to size -> enough_space_to_copy g h from to.
Proof. unfold enough_space_to_copy, general_enough_space_to_copy. intros. lia. Qed.

Lemma forward_remset_item_ghg: forall from to g h rh rmst item g' h' rh' rmst',
    graph_has_gen g to ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    forall gen, graph_has_gen g gen <-> graph_has_gen g' gen.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' Hghg Hfri gen. simpl in Hfri.
  destruct (negb _) eqn:?H. 2: inversion Hfri; tauto.
  destruct (forward_graph_and_heap _ _ _ _ _ _) as [newg newh] eqn:?H.
  pose proof fr_forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h.
  rewrite H0 in H1. simpl in H1. inversion Hfri. eapply fr_graph_has_gen; eauto.
Qed.

Lemma fri_copy_compatible: forall from to g h rh rmst item g' h' rh' rmst',
    from <> to -> graph_has_gen g to -> copy_compatible g ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    copy_compatible g'.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' Hfr Hghg Hcc Hfri. simpl in Hfri.
  destruct (negb _) eqn:?H. 2: inversion Hfri; tauto.
  destruct (forward_graph_and_heap _ _ _ _ _ _) as [newg newh] eqn:?H.
  pose proof fr_forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h.
  rewrite H0 in H1. simpl in H1. inversion Hfri. eapply fr_copy_compatible; eauto.
Qed.

Lemma fri_no_dangling_dst: forall from to g h rh rmst item g' h' rh' rmst',
    graph_has_gen g to -> copy_compatible g ->
    remset_compatible' g rmst ->
    remset_item_compatible g from rmst item ->
    no_dangling_dst g ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    no_dangling_dst g'.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' Hghg Hcc Hrc Hric Hndd Hfri. simpl in Hfri.
  destruct (negb _) eqn:?H. 2: inversion Hfri; tauto.
  destruct (forward_graph_and_heap _ _ _ _ _ _) as [newg newh] eqn:?H.
  pose proof fr_forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h.
  rewrite H0 in H1. simpl in H1. inversion Hfri. eapply fr_O_no_dangling_dst ; eauto.
  eapply remset_item2forward_t_ftc; eauto.
Qed.

Lemma irh_used_space: forall h i gen,
    used_space (nth_space (incr_remset_heap h i) gen) = used_space (nth_space h gen).
Proof.
  intros. rewrite !nth_space_Znth. unfold incr_remset_heap.
  destruct (spaces_index_dec _ _); auto. simpl.
  destruct (Z.eq_dec i (Z.of_nat gen)).
  - subst. rewrite upd_Znth_same; auto. unfold incr_remset_space.
    destruct (Z_lt_ge_dec _ _); simpl; reflexivity.
  - rewrite upd_Znth_diff_strong by lia. reflexivity.
Qed.

Lemma irh_rest_gen_size: forall h gen,
    rest_gen_size (incr_remset_heap h (Z.of_nat gen)) gen = rest_gen_size h gen - 1 \/
      rest_gen_size (incr_remset_heap h (Z.of_nat gen)) gen =  rest_gen_size h gen.
Proof.
  unfold rest_gen_size. intros. rewrite irh_used_space.
  rewrite !nth_space_Znth. unfold incr_remset_heap. destruct (spaces_index_dec _ _); auto.
  simpl. rewrite upd_Znth_same; auto. unfold incr_remset_space. destruct (Z_lt_ge_dec _ _).
  - simpl. left. lia.
  - right. reflexivity.
Qed.

Lemma forward_remset_item_gestc: forall from to g h rh rmst item g2 h2 rh2 rmst2 size,
    0 < size -> from <> to -> graph_has_gen g to ->
    remset_compatible' g rmst ->
    remset_item_compatible g from rmst item ->
    no_dangling_dst g ->
    general_enough_space_to_copy g h from to size ->
    (g2, h2, rh2, rmst2) = forward_remset_item from to (g, h, rh, rmst) item ->
    general_enough_space_to_copy g2 h2 from to (size - 1) \/
    general_enough_space_to_copy g2 h2 from to size.
Proof.
  intros from to g h rh rmst item g2 h2 rh2 rmst2 size Hsz Hfr Hghg Hrc Hric Hndg Hestc Hfri.
  simpl in Hfri. destruct (negb _). 2: inversion Hfri; right; assumption.
  destruct (forward_graph_and_heap _ _ _ _ _ _) as [newg newh] eqn:Hfgh. symmetry in Hfgh.
  inversion Hfri; subst; clear Hfri. eapply forward_graph_and_heap_O_gestc in Hfgh; eauto.
  3: lia. 2: eapply remset_item2forward_t_ftc; eassumption. unfold general_enough_space_to_copy in *.
  pose proof irh_rest_gen_size newh to. lia.
Qed.

Lemma upd_remset_addr_not_In: forall from to g addr rmst,
    ~ In addr (map extract_address rmst) -> upd_remset_addr from to g addr rmst = rmst.
Proof.
  intros. revert rmst H. induction rmst; intros; simpl. 1: reflexivity.
  destruct (Val.eq addr _).
  - exfalso. apply H. simpl. left; auto.
  - rewrite IHrmst; auto. intro. apply H. simpl. right; assumption.
Qed.

Lemma upd_remset_addr_outlier: forall out from to g addr rmst,
    In (RemSetOutlier out addr) rmst ->
    remset_nodup rmst -> upd_remset_addr from to g addr rmst = rmst.
Proof.
  intros. revert rmst H H0. unfold remset_nodup. induction rmst; intros; simpl. 1: reflexivity.
  simpl in H, H0. rewrite NoDup_cons_iff in H0. destruct H0. destruct (Val.eq addr _).
  - destruct H.
    + subst a. simpl. reflexivity.
    + rewrite <- e in H0. apply (in_map extract_address) in H. simpl in H. contradiction.
  - destruct H; [| now rewrite IHrmst]. rewrite H in n. simpl in n. contradiction.
Qed.

Lemma remset_nodup_cons_tail: forall rext rmst, remset_nodup (rext :: rmst) -> remset_nodup rmst.
Proof. unfold remset_nodup. simpl. intros. apply NoDup_cons_1 in H. assumption. Qed.

Lemma remset_nodup_cons_head: forall rext rmst,
    remset_nodup (rext :: rmst) -> ~ In (extract_address rext) (map extract_address rmst).
Proof. unfold remset_nodup. simpl. intros. apply NoDup_cons_2 in H. assumption. Qed.

Lemma remset_nodup_cons_iff: forall rext rmst,
    remset_nodup (rext :: rmst) <-> ~ In (extract_address rext) (map extract_address rmst) /\ remset_nodup rmst.
Proof. intros. unfold remset_nodup in *. simpl. rewrite NoDup_cons_iff. tauto. Qed.

Lemma remset_nodup_perm: forall l1 l2, Permutation l1 l2 -> remset_nodup l1 -> remset_nodup l2.
Proof.
  intros. revert H0. induction H; intros; auto.
  - rewrite remset_nodup_cons_iff in H0 |- *. destruct H0. split; auto.
    intro. apply H0. apply (Permutation_map extract_address) in H. symmetry in H.
    eapply Permutation_in; eassumption.
  - rewrite remset_nodup_cons_iff in *. simpl map in *. destruct H0.
    rewrite remset_nodup_cons_iff in *. destruct H0. split; [|split]; auto.
    + simpl. intro. destruct H2.
      * apply H. simpl. left; auto.
      * apply H0; assumption.
    + intro. apply H. simpl. right. assumption.
Qed.

Lemma upd_remset_addr_perm: forall from to g addr rmst1 rmst2,
    Permutation rmst1 rmst2 -> remset_nodup rmst1 ->
    Permutation (upd_remset_addr from to g addr rmst1) (upd_remset_addr from to g addr rmst2).
Proof.
  intros from to g addr rmst1 rmst2 H. induction H; intros; simpl.
  - constructor.
  - destruct (Val.eq _ _); constructor; [assumption|]. apply IHPermutation.
    apply remset_nodup_cons_tail in H0. assumption.
  - rewrite remset_nodup_cons_iff in H. simpl map in H. destruct H.
    rewrite remset_nodup_cons_iff in H0. destruct H0.
    do 2 destruct (Val.eq _ _); try (now constructor).
    exfalso. rewrite e in e0. apply H. simpl. left; auto.
  - transitivity (upd_remset_addr from to g addr l').
    + apply IHPermutation1. assumption.
    + apply IHPermutation2. eapply remset_nodup_perm; eassumption.
Qed.

Lemma remset_compatible'_perm: forall (g: LGraph) rmst1 rmst2,
    Permutation rmst1 rmst2 -> remset_compatible' g rmst1 -> remset_compatible' g rmst2.
Proof. unfold remset_compatible'. intros. eapply Forall_permutation; eassumption. Qed.

Lemma fr_remset_compatible': forall from to depth p g g',
    graph_has_gen g to ->
    forward_relation from to depth p g g' ->
    forall rmst, remset_compatible' g rmst -> remset_compatible' g' rmst.
Proof.
  unfold remset_compatible'. intros. rewrite Forall_forall in *. intros. specialize (H1 _ H2).
  destruct x; simpl in *; auto. eapply fr_graph_has_v; eassumption.
Qed.

Lemma remset_compatible'_cons_iff: forall g rext rmst,
    remset_compatible' g (rext :: rmst) <-> remset_ext_compatible' g rext /\ remset_compatible' g rmst.
Proof. intros. unfold remset_compatible'. rewrite Forall_cons_iff. tauto. Qed.

Lemma fri_remset_compatible: forall from to g h rh rmst item g' h' rh' rmst',
    graph_has_gen g to ->
    copy_compatible g ->
    remset_nodup rmst ->
    remset_compatible' g rmst ->
    remset_item_compatible g from rmst item ->
    (g', h', rh', rmst') = forward_remset_item from to (g, h, rh, rmst) item ->
    remset_compatible' g' rmst'.
Proof.
  intros from to g h rh rmst item g' h' rh' rmst' Hghg Hcc Hrnd Hrc Hric Hfri.
  simpl in Hfri. destruct (negb _) eqn:?H. 2: inversion Hfri; assumption.
  destruct (forward_graph_and_heap _ _ _ _ _ _) as [newg newh] eqn:Hfgh.
  pose proof fr_forward_graph_and_heap from to 0 (remset_item2forward_t item rmst g) g h as Hfr.
  rewrite Hfgh in Hfr. simpl in Hfr. inversion Hfri. clear H Hfri. subst. destruct item as [addr | intr]; simpl in *.
  - clear Hfr. apply find_remset_ext_In_some in Hric. destruct Hric as [rext [Hfre Heae]].
    rewrite Hfre in Hfgh. Transparent forward_graph_and_heap. destruct rext as [gpv | vtx].
    + simpl in *. inversion Hfgh. subst. apply find_remset_ext_some in Hfre. destruct Hfre as [Hfre _].
      erewrite upd_remset_addr_outlier; eauto.
    + simpl in Heae. subst v. apply find_remset_ext_some in Hfre. destruct Hfre as [Hfre _].
      apply In_Permutation_cons in Hfre. destruct Hfre as [l Hperm].
      pose proof upd_remset_addr_perm from to g addr _ _ Hperm Hrnd as Hupdp. symmetry in Hupdp.
      eapply (remset_compatible'_perm) in Hupdp; eauto.
      pose proof fr_forward_graph_and_heap from to 0 (remset_ext2foward_t (RemSetVertex vtx addr)) g h as Hfr.
      rewrite Hfgh in Hfr. simpl in Hfr. apply (remset_compatible'_perm _ _ _ Hperm) in Hrc.
      rewrite remset_compatible'_cons_iff in Hrc. destruct Hrc as [Hrec Hrc]. simpl. destruct (Val.eq _ _).
      2: contradiction. clear e. rewrite remset_compatible'_cons_iff. split.
      2: eapply fr_remset_compatible'; eassumption. Opaque forward_graph_and_heap. simpl in *.
      eapply fgh_O_graph_has_v_update_vertex; eauto.
  - clear -Hrc Hfr Hghg. revert rmst Hrc. induction rmst; intros.
    + apply Forall_nil.
    + hnf in Hrc. unfold remset_compatible' in IHrmst, Hrc |- *.
      rewrite Forall_cons_iff in Hrc |- *. destruct Hrc as [Hrec Hrc]. split; auto.
      destruct a; simpl in *; auto. eapply fr_graph_has_v; eauto.
Qed.

Lemma upd_remset_address_same: forall from to g item rmst,
    map extract_address (upd_remset from to g item rmst) = map extract_address rmst.
Proof.
  intros. induction rmst; destruct item; simpl; auto. destruct (Val.eq _ _); simpl in *; f_equal; auto.
  destruct a; simpl in *; reflexivity.
Qed.

Lemma upd_remset_nodup: forall from to g rmst item,
    remset_nodup rmst -> remset_nodup (upd_remset from to g item rmst).
Proof. unfold remset_nodup. intros. rewrite upd_remset_address_same. assumption. Qed.

Lemma compatible_remset_gen_size: forall (g: LGraph) (h: heap) from rmst rh gen,
    graph_heap_compatible g h ->
    graph_has_gen g gen ->
    remset_heap_compatible g from rmst rh h ->
    remset_gen_size h gen = Zlength (Znth (Z.of_nat gen) rh).
Proof.
  intros g h from rmst rh gen Hghc Hghg Hrhc.
  assert (Hghg': graph_has_gen g (Z.to_nat (Z.of_nat gen))) by now rewrite Nat2Z.id.
  assert (Hgenr: 0 <= Z.of_nat gen < Zlength (spaces h)). {
    destruct Hghc as [_ [_ ?]]. hnf in Hghg. assert (gen < length (spaces h))%nat by lia.
    pose proof Zlength_correct (spaces h). list_solve. }
  pose proof space_start_isptr _ _ _ Hghc Hgenr Hghg'. hnf in Hghc, Hghg, Hrhc.
  pose proof Forall2_Zlength Hrhc as Hlenrh. destruct Hghc as [Hgsc [Heqnull Hlen]].
  apply Forall2_Znth with (i := Z.of_nat gen) in Hrhc. 2: now rewrite Hlenrh.
  destruct Hrhc as [_ Hrhc]. hnf in Hrhc.
  remember (space_start (Znth (Z.of_nat gen) (spaces h))) as sps. destruct (Val.eq _ _).
  1: destruct sps; simpl in H; try contradiction; inversion e.
  symmetry. unfold remset_gen_size, available_size. rewrite nth_space_Znth. assumption.
Qed.

Lemma gestc_decay: forall s1 s2 g h from to,
    s2 < s1 -> general_enough_space_to_copy g h from to s1 ->
    general_enough_space_to_copy g h from to s2.
Proof. unfold general_enough_space_to_copy. intros. lia. Qed.

Lemma remset_item_compatible_perm: forall g from rmst1 rmst2 item,
    Permutation rmst1 rmst2 -> remset_item_compatible g from rmst1 item ->
    remset_item_compatible g from rmst2 item.
Proof.
  intros g from rmst1 rmst2 item Hperm Hric. destruct item; simpl in *; auto.
  apply (Permutation_map extract_address) in Hperm. eapply Permutation_in; eassumption.
Qed.

Lemma remset_item_compatible_vertex_cons: forall g from vtx1 vtx2 addr l r,
    remset_item_compatible g from (RemSetVertex vtx1 addr :: l) r <->
      remset_item_compatible g from (RemSetVertex vtx2 addr :: l) r.
Proof. intros. destruct r; simpl; tauto. Qed.

Lemma interior2forward_not_vertex: forall i g v, interior2forward i g <> ForwardVertex v.
Proof. intros; destruct i; simpl; destruct (Znth _ _); simpl; discriminate. Qed.

Lemma fri_remset_item_compatible: forall g h rh rmst from to r g2 h2 rh2 rmst2 item,
    remset_nodup rmst ->
    remset_item_compatible g from rmst item ->
    remset_item_compatible g from rmst r ->
    graph_has_gen g to ->
    (g2, h2, rh2, rmst2) = forward_remset_item from to (g, h, rh, rmst) item ->
    remset_item_compatible g2 from rmst2 r.
Proof.
  intros g h rh rmst from to r g2 h2 rh2 rmst2 item Hrn Hrici Hricr Hto Hfri.
  simpl in Hfri. destruct (negb _). 2: inversion Hfri; assumption.
  destruct (forward_graph_and_heap _ _ _ _ _ _) as [newg newh] eqn:Hfgh. inversion Hfri.
  subst. clear Hfri. Transparent forward_graph_and_heap. destruct item; simpl in Hfgh.
  - simpl in Hrici. apply find_remset_ext_In_some in Hrici. destruct Hrici as [rext [Hfre Hear]].
    rewrite Hfre in Hfgh. simpl. destruct rext as [gptr | vtx]; simpl in *; subst v0;
      apply find_remset_ext_some in Hfre; destruct Hfre as [Hfre _].
    + erewrite upd_remset_addr_outlier; eauto. inversion Hfgh. subst. assumption.
    + apply In_Permutation_cons in Hfre. destruct Hfre as [l Hperm]. rename v into addr.
      pose proof upd_remset_addr_perm from to g addr _ _ Hperm Hrn as Hupdp. symmetry in Hupdp.
      eapply remset_item_compatible_perm in Hupdp; eauto. simpl. destruct (Val.eq _ _).
      2: contradiction. clear e. unfold update_vertex. destruct (Nat.eq_dec _ _).
      * destruct (raw_mark _) eqn: Hrmark; inversion Hfgh; subst newg newh; clear Hfgh.
        -- eapply remset_item_compatible_perm in Hperm; eassumption.
        -- destruct r.
           ++ simpl in Hricr |- *. apply (Permutation_map extract_address) in Hperm. simpl in Hperm.
              eapply Permutation_in in Hperm; eassumption.
           ++ Opaque lgraph_copy_v. simpl in Hricr |- *. destruct i as [vertex n].
              destruct Hricr as [Hghv [Hlen Hmark]]. split; [|split].
              ** apply lcv_graph_has_v_old; auto.
              ** pose proof lcv_vertex_size_old _ vtx _ _ Hto Hghv as Hvs.
                 unfold vertex_size in Hvs. lia.
              ** intros Hvn. specialize (Hmark Hvn).
                 assert (vertex <> vtx) by (intro; subst; contradiction).
                 rewrite <- lcv_raw_mark; auto. rewrite <- lcv_raw_tag; auto.
      * inversion Hfgh. subst. eapply remset_item_compatible_perm; eassumption.
  - simpl. destruct (interior2forward i g) eqn:Hintr; try (inversion Hfgh; subst; simpl; assumption).
    1: apply interior2forward_not_vertex in Hintr; contradiction. simpl. destruct (Nat.eq_dec _ _).
    2: inversion Hfgh; subst; assumption.
    destruct (raw_mark _) eqn: Hmark; inversion Hfgh; subst newg newh; clear Hfgh.
    + destruct r; simpl in Hricr |- *. 1: assumption. destruct i0 as [vertex n].
      rewrite <- lgd_graph_has_v. assumption.
    + destruct r; simpl in Hricr |- *. 1: assumption. destruct i0 as [vertex n].
      rewrite <- lgd_graph_has_v. destruct Hricr as [Hghv [Hlen Hrmark]]. split; [|split].
      * apply lcv_graph_has_v_old; auto.
      * pose proof lcv_vertex_size_old _ (dst g e) _ _ Hto Hghv as Hvs. unfold vertex_size in Hvs. lia.
      * intros Hvn. specialize (Hrmark Hvn). assert (vertex <> dst g e) by (intro; subst; contradiction).
        rewrite <- lcv_raw_mark; auto. rewrite <- lcv_raw_tag; auto.
    Opaque forward_graph_and_heap. Transparent lgraph_copy_v.
Qed.

Lemma forward_remset_item_fold_ghc:
    forall (from to : nat) (g : LGraph) (h : heap) (rh : remset_heap) (rmst : remset) (g' : LGraph)
           (h' : heap) (rh' : remset_heap) (rmst' : remset) (r : remset_space) ,
      from <> to ->
      remset_nodup rmst ->
      graph_heap_compatible g h ->
      copy_compatible g ->
      no_dangling_dst g ->
      graph_has_gen g from ->
      graph_has_gen g to ->
      remset_compatible' g rmst ->
      Forall (remset_item_compatible g from rmst) r ->
      (g', h', rh', rmst') = fold_left (forward_remset_item from to) r (g, h, rh, rmst) ->
      general_enough_space_to_copy g h from to (Zlength r) -> graph_heap_compatible g' h'.
Proof.
  intros from to g h rh rmst g' h' rh' rmst' r Hfr Hrnd. revert g h rh rmst g' h' rh' rmst' Hrnd.
  Opaque forward_remset_item. induction r;
    intros g h rh rmst g' h' rh' rmst' Hrnd Hghc Hcc Hndd Hgfrom Hgto Hrc Hrhc Hfrg Hese; simpl in Hfrg.
  1: inversion Hfrg; assumption. Transparent forward_remset_item.
  destruct (forward_remset_item from to (g, h, rh, rmst) a) as [[[g2 h2] rh2] rmst2] eqn:Hfri2.
  symmetry in Hfri2. rewrite Forall_cons_iff in Hrhc. destruct Hrhc as [Hrica Hricr].
  assert (Hrnd2: remset_nodup rmst2). {
    clear -Hfri2 Hrnd. simpl in Hfri2. destruct (negb _).
    - remember (forward_graph_and_heap _ _ _ _ _ _). destruct p as [newg newh]; inversion Hfri2.
      apply upd_remset_nodup; assumption.
    - inversion Hfri2; assumption. }
  eapply (IHr g2 h2 rh2 rmst2 _ _ _ _ Hrnd2); eauto.
  - eapply forward_remset_item_ghc; eauto. eapply gestc_estc; eauto. list_solve.
  - eapply (fri_copy_compatible from to); eauto.
  - eapply fri_no_dangling_dst; eauto.
  - eapply forward_remset_item_ghg with (g:=g); eauto.
  - eapply forward_remset_item_ghg with (g:=g); eauto.
  - eapply (fri_remset_compatible _ _ g h rh rmst); eauto.
  - rewrite Forall_forall in Hricr |- *. intros x Hin. specialize (Hricr _ Hin).
    eapply fri_remset_item_compatible with (rmst := rmst) (item := a); eassumption.
  - eapply forward_remset_item_gestc in Hfri2; eauto. 2: list_solve. destruct Hfri2. 1: list_solve.
    apply (gestc_decay (Zlength (a :: r))); [list_solve | assumption].
Qed.

Lemma rhc_forall_ric: forall g from rmst rh h,
    remset_heap_compatible g from rmst rh h -> Forall (remset_item_compatible g from rmst) (nth from rh []).
Proof.
  intros g from rmst rh h Hrhc. destruct (le_lt_dec (length rh) from). 1: rewrite nth_overflow; auto.
  hnf in Hrhc. rewrite Forall2_forall_Znth in Hrhc. destruct Hrhc as [_ Hrhc].
  assert (Hrg: 0 <= Z.of_nat from < Zlength rh) by (rewrite Zlength_correct; lia).
  change [] with (@default _ (@Inhabitant_list remset_space_item)). rewrite nth_Znth'. specialize (Hrhc _ Hrg).
  destruct Hrhc as [Hrhc _]. assumption.
Qed.

Lemma forward_remset_gh_ghc: forall from to g h rh rmst g' h' rh' rmst',
    from <> to ->
    graph_heap_compatible g h ->
    copy_compatible g ->
    no_dangling_dst g ->
    graph_has_gen g from ->
    graph_has_gen g to ->
    enough_space_enhanced g h from to ->
    remset_compatible' g rmst ->
    remset_heap_compatible g from rmst rh h ->
    remset_nodup rmst ->
    (g', h', rh', rmst') = forward_remset_gh from to g h rh rmst ->
    graph_heap_compatible g' h'.
Proof.
  intros from to g h rh rmst g' h' rh' rmst' Hfr Hghc Hcc Hndd Hgfrom Hgto Hese Hrc Hrhc Hrnd Hfrg.
  unfold forward_remset_gh in Hfrg. destruct (le_lt_dec (length rh) from).
  1: rewrite (nth_overflow _ _ l) in Hfrg; simpl in Hfrg; inversion Hfrg; assumption.
  unfold enough_space_enhanced in Hese. erewrite compatible_remset_gen_size in Hese; eauto.
  hnf in Hrhc. rewrite Forall2_forall_Znth in Hrhc. destruct Hrhc as [Hlrh Hrhc].
  change [] with (@default _ (@Inhabitant_list remset_space_item)) in Hfrg.
  rewrite nth_Znth' in Hfrg. assert (Hrg: 0 <= Z.of_nat from < Zlength rh) by
    (rewrite Zlength_correct; lia). specialize (Hrhc _ Hrg).
  remember (Znth (Z.of_nat from) rh). remember (Znth (Z.of_nat from) (spaces h)) as sp.
  clear Heqr Heqsp l Hrg. destruct Hrhc as [Hrhc Hrsize]. clear dependent sp.
  eapply forward_remset_item_fold_ghc; eassumption.
Qed.
