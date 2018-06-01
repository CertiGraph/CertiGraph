Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Export Coq.Program.Basics.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.val_lemmas.
Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
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

Local Close Scope Z_scope.

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

Definition Z2val (x: Z) : val := Vint (Int.repr x).

Definition GC_Pointer2val (x: GC_Pointer) : val :=
  match x with | GCPtr b z => Vptr b z end.

Definition raw_data2val (x: Z + GC_Pointer) : val :=
  match x with
  | inl n => Z2val n
  | inr p => GC_Pointer2val p
  end.
  
Record raw_vertex_block : Type :=
  {
    raw_mark: bool;
    raw_fields: list raw_field;
    raw_color: Z;
    raw_tag: Z;
  }.

Record generation_info: Type :=
  {
    start_address: val;
    number_of_vertices: nat;
    limit_of_generation: Z;
    start_isptr: isptr start_address;
  }.

Definition IMPOSSIBLE_VAL := Vptr xH Ptrofs.zero.
Lemma IMPOSSIBLE_ISPTR: isptr IMPOSSIBLE_VAL. Proof. exact I. Qed.
Global Opaque IMPOSSIBLE_VAL.

Definition null_info: generation_info :=
  Build_generation_info IMPOSSIBLE_VAL O Z.zero IMPOSSIBLE_ISPTR.

Definition graph_info := list generation_info.

Definition LGraph := LabeledGraph VType EType raw_vertex_block unit graph_info.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Record space: Type :=
  {
    space_start: val;
    used_space: Z;
    total_space: Z;
  }.

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

Lemma single_vertex_size_gt_zero: forall g v, (0 < single_vertex_size g v)%Z.
Proof.
  intros. unfold single_vertex_size.
  pose proof (Zlength_nonneg (raw_fields (vlabel g v))). omega.
Qed.

Fixpoint previous_vertices_size (g: LGraph) (gen i: nat): Z :=
  match i with
  | O => 0
  | S n => single_vertex_size g (gen, n) + previous_vertices_size g gen n
  end.

Lemma previous_size_ge_zero: forall g gen i, (0 <= previous_vertices_size g gen i)%Z.
Proof.
  intros. induction i; simpl. 1: omega.
  pose proof (single_vertex_size_gt_zero g (gen, i)). omega.
Qed.

Definition generation_space_compatible (g: LGraph)
           (tri: nat * generation_info * space) : Prop :=
  match tri with
  | (gen, gi, sp) =>
    gi.(start_address) = sp.(space_start) /\
    previous_vertices_size g gen gi.(number_of_vertices) = sp.(used_space) /\
    gi.(limit_of_generation) = sp.(total_space)
  end.

Fixpoint nat_seq (s: nat) (total: nat): list nat :=
  match total with
  | O => nil
  | S n => s :: nat_seq (S s) n
  end.

Lemma nat_seq_S: forall i num, nat_seq i (S num) = nat_seq i num ++ [num + i].
Proof.
  intros. revert i. induction num; intros. 1: simpl; reflexivity.
  remember (S num). simpl. rewrite (IHnum (S i)). subst. simpl. repeat f_equal. omega.
Qed.

Definition nat_inc_list (n: nat) : list nat := nat_seq O n.

Lemma nat_inc_list_S: forall num, nat_inc_list (S num) = nat_inc_list num ++ [num].
Proof. intros. unfold nat_inc_list. rewrite nat_seq_S. repeat f_equal. omega. Qed.

Definition graph_thread_info_compatible (g: LGraph) (ti: thread_info): Prop :=
  (g.(glabel) = nil <-> ti.(ti_heap_p) = nullval) /\
  Forall (generation_space_compatible g)
         (combine (combine (nat_inc_list (length g.(glabel))) g.(glabel))
                  ti.(ti_heap).(spaces)) /\
  Forall (eq nullval)
         (skipn (length g.(glabel)) (map space_start ti.(ti_heap).(spaces))).

Record fun_info : Type :=
  {
    fun_word_size: Z;
    live_roots_indices: list Z;
    fi_index_range: forall i, In i live_roots_indices -> (0 <= i < MAX_ARGS)%Z;
  }.

Definition vertex_offset (g: LGraph) (v: VType): Z :=
  previous_vertices_size g (vgeneration v) (vindex v) + 1.

Definition gen_start (g: LGraph) (gen: nat): val :=
  (nth gen g.(glabel) null_info).(start_address).

Definition vertex_address (g: LGraph) (v: VType): val :=
  offset_val (WORD_SIZE * vertex_offset g v) (gen_start g (vgeneration v)).

Definition ptr_or_v_2val (g: LGraph) (e: GC_Pointer + VType) : val :=
  match e with
  | inl (GCPtr b z) => Vptr b z
  | inr v => vertex_address g v
  end.

Definition roots_t: Type := list (GC_Pointer + VType).

Definition outlier_t: Type := list GC_Pointer.

Instance Inhabitant_val: Inhabitant val := nullval.

Definition fun_thread_arg_compatible
           (g: LGraph) (ti: thread_info) (fi: fun_info) (roots: roots_t) : Prop :=
  map (ptr_or_v_2val g) roots = map ((flip Znth) ti.(ti_args)) fi.(live_roots_indices).

Definition roots_compatible (g: LGraph) (outlier: outlier_t) (roots: roots_t): Prop :=
  incl (filter_sum_left roots) outlier /\ Forall (vvalid g) (filter_sum_right roots).

Definition outlier_compatible (g: LGraph) (outlier: outlier_t): Prop :=
  forall v,
    vvalid g v ->
    incl (filter_sum_right (filter_option (vlabel g v).(raw_fields))) outlier.

Definition
  super_compatible
  (g: LGraph) (ti: thread_info) (fi: fun_info) (r: roots_t) (out: outlier_t) : Prop :=
  graph_thread_info_compatible g ti /\
  fun_thread_arg_compatible g ti fi r /\
  roots_compatible g out r /\
  outlier_compatible g out.

(*

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

Fixpoint make_fields' (g: LGraph) (l_raw: list raw_field) (v: VType) (n: nat) :=
  match l_raw with
  | nil => nil
  | Some d :: l => raw_data2val d :: make_fields' g l v (n + 1)
  | None :: l => vertex_address g (dst g (v, n)) :: make_fields' g l v (n + 1)
  end.

Lemma make_fields'_eq_length: forall g l v n, length (make_fields' g l v n) = length l.
Proof.
  intros. revert n. induction l; intros; simpl. 1: reflexivity.
  destruct a; simpl; rewrite IHl; reflexivity.
Qed.

Definition make_fields (g: LGraph) (v: VType): list val :=
  make_fields' g (vlabel g v).(raw_fields) v O.

Lemma fields_eq_length: forall g v,
    Zlength (make_fields g v) = Zlength (raw_fields (vlabel g v)).
Proof.
  intros. rewrite !Zlength_correct. f_equal. unfold make_fields.
  rewrite make_fields'_eq_length. reflexivity.
Qed.
