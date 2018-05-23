Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.val_lemmas.
Require Import VST.msl.seplog.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.msl_ext.iter_sepcon.

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

Inductive raw_field : Type :=
| raw_data : Z + GC_Pointer -> raw_field
| raw_pointer : raw_field.

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
  }.

Definition null_info: generation_info := Build_generation_info nullval O Z.zero.

Definition graph_info := list generation_info.

Definition LGraph := LabeledGraph VType EType raw_vertex_block unit graph_info.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition single_vertex_size (g: LGraph) (v: VType): Z :=
  Zlength (vlabel g v).(raw_fields) + 1.

Fixpoint previous_vertices_size (g: LGraph) (gen i: nat): Z :=
  match i with
  | O => 0
  | S n => single_vertex_size g (gen, n) + previous_vertices_size g gen n
  end.

Definition vertex_offset (g: LGraph) (v: VType): Z :=
  previous_vertices_size g (vgeneration v) (vindex v) + 1.

Definition all_occupied (g: LGraph) (v: VType): Z :=
  previous_vertices_size g (vgeneration v) (vindex v + 1).

Definition vertex_start_address (g: LGraph) (v: VType): val :=
  (nth (vgeneration v) g.(glabel) null_info).(start_address).

Definition vertex_address (g: LGraph) (v: VType): val :=
  offset_val (WORD_SIZE * vertex_offset g v) (vertex_start_address g v).

Definition make_header (g: LGraph) (v: VType): Z:=
  let vb := vlabel g v in if vb.(raw_mark)
                          then 0 else
                            vb.(raw_tag) + (Z.shiftl vb.(raw_color) 8) +
                            (Z.shiftl (Zlength vb.(raw_fields)) 10).

Fixpoint make_fields' (g: LGraph) (l_raw: list raw_field) (v: VType) (n: nat) :=
  match l_raw with
  | nil => nil
  | x :: l => match x with
              | raw_data d => raw_data2val d :: make_fields' g l v (n + 1)
              | raw_pointer =>
                vertex_address g (dst g (v, n)) :: make_fields' g l v (n + 1)
              end
  end.

Definition make_fields (g: LGraph) (v: VType): list val :=
  make_fields' g (vlabel g v).(raw_fields) v O.

Fixpoint get_edges' (lf: list raw_field) (v: VType) (n: nat) : list EType :=
  match lf with
  | nil => nil
  | cons x lf' => match x with
                  | raw_data _ => get_edges' lf' v (n + 1)
                  | raw_pointer => (v, n) :: get_edges' lf' v (n + 1)
                  end
  end.

Definition get_edges (g: LGraph) (v: VType): list EType :=
  get_edges' (raw_fields (vlabel g v)) v O.

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

Class SpatialGCGraphAssum (Pred : Type):=
  {
    SGP_ND: NatDed Pred;
    SGP_SL : SepLog Pred;
    SGP_ClSL: ClassicalSep Pred;
    SGP_CoSL: CorableSepLog Pred
  }.

Existing Instances SGP_ND SGP_SL SGP_ClSL SGP_CoSL.

Class SpatialGCGraph (Pred: Type) := vertex_at: val -> Z -> list val -> Pred.

Fixpoint nat_inc_list (n: nat) : list nat :=
  match n with
  | O => nil
  | S n' => nat_inc_list n' ++ (n' :: nil)
  end.

Lemma nat_inc_list_in_iff: forall n v, In v (nat_inc_list n) <-> 0 <= v < n.
Proof.
  induction n; intros; [simpl; intuition|]. simpl. rewrite in_app_iff.
  assert (0 <= v < S n <-> 0 <= v < n \/ v = n) by omega. rewrite H. clear H.
  rewrite IHn. simpl. intuition.
Qed.

Lemma nat_inc_list_NoDup: forall n, NoDup (nat_inc_list n).
Proof.
  induction n; simpl; [constructor|]. apply NoDup_app_inv; auto.
  - constructor; auto. constructor.
  - intros. rewrite nat_inc_list_in_iff in H. simpl. omega.
Qed.

Lemma nat_inc_list_length: forall n, length (nat_inc_list n) = n.
Proof.
  induction n; simpl; auto. rewrite app_length. simpl. rewrite IHn. intuition.
Qed.

Section SpaceGCGraph.

  Context {Pred: Type}.
  Context {SGGAP: SpatialGCGraphAssum Pred}.
  Context {SGGP: SpatialGCGraph Pred}.

  Definition vertex_rep (g: Graph) (v: VType): Pred :=
    vertex_at (vertex_address g v) (make_header g v) (make_fields g v).

  Definition generation_rep (g: Graph) (gen_and_num: nat * nat): Pred :=
    match gen_and_num with
    | pair gen num =>
      iter_sepcon (map (fun x => (gen, x)) (nat_inc_list num)) (vertex_rep g)
    end.

  Definition graph_rep (g: Graph): Pred :=
    let up := map number_of_vertices g.(glabel) in 
    iter_sepcon (combine (nat_inc_list (length up)) up) (generation_rep g).

End SpaceGCGraph.

Lemma get_edges'_range: forall v n l m,
    In (v, n) (get_edges' l v m) -> m <= n < m + length l.
Proof.
  intros v n l. revert v n. induction l; simpl; intros. 1: exfalso; auto.
  specialize (IHl v n (m + 1)). destruct a. 1: apply IHl in H; omega.
  simpl in H. destruct H. 1: inversion H; omega. apply IHl in H. omega.
Qed.

Lemma get_edges'_nth: forall n l a m v,
    n < length l -> nth n l a = raw_pointer <-> In (v, n + m) (get_edges' l v m).
Proof.
  induction n.
  - induction l; simpl; intros. 1: inversion H. destruct a.
    + split; intros. inversion H0. apply get_edges'_range in H0. exfalso; omega.
    + simpl. intuition.
  - destruct l; simpl; intros. 1: inversion H. assert (n < length l) by omega.
    specialize (IHn l a (m + 1) v H0).
    replace (n + (m + 1)) with (S (n + m)) in IHn by omega. rewrite IHn.
    destruct r; intuition. simpl in H3. destruct H3; auto. inversion H3. omega.
Qed.

Record space: Type :=
  { 
    space_start: val;
    used_space: Z;
    total_space: Z;
    space_order: (0 <= used_space < total_space)%Z;
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

Record thread_info: Type :=
  {
    ti_used_space: Z;
    ti_heap_p: val;
    ti_heap: heap;
    ti_args: list val;
  }.

Definition graph_thread_info_compatible (g: Graph) (ti: thread_info): Prop :=
  (g.(glabel) = nil <-> ti.(ti_heap_p) = nullval) 
  (* /\ MORE CONDITIONS *).
