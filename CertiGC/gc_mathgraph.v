(* General includes? *)
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.

(* Mathematical model for graphs *)
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.MathGraph.
Require Import RamifyCoq.graph.FiniteGraph.

Section GC_Graph.

Local Coercion pg_lg : LabeledGraph >-> PreGraph.

Context {V : Type} {EV : EquivDec.EqDec V eq}.
Context {null : V}.

(* We should make this a common definition maybe? *)
Definition is_null : DecidablePred V := 
  existT (fun P => forall a, {P a} + {~P a}) (fun x => x = null) (fun x => EV x null).

Definition E : Type := V * nat.
Instance EE : EquivDec.EqDec E eq := prod_eqdec EV nat_eq_eqdec.

Inductive field_type : Type :=
  | data : nat -> field_type (* eventually change this to CompCert value? *)
  | pointer : field_type.

(* There's probably a better way to write this definition... *)
Definition is_pointer : DecidablePred field_type :=
  existT (fun P => forall a, {P a} + {~P a}) (fun x => x = pointer)
  (fun x => match x with 
     | pointer => left eq_refl
     | data n => right (fun H : data n = pointer => 
                          eq_ind (data n) (fun e => match e with data _ => True | pointer => False end)
                          I pointer H)
   end).

Record LV : Type := {
  mark   : bool;
  fields : list field_type;
  non_empty : List.length fields > 0
}.

Definition num_fields (l : LV) : nat :=
  List.length (fields l).

Definition num_edges (l : LV) : nat :=
  List.length (List.filter (fun x => match projT2 is_pointer x with left _ => true | right _ => false end) (fields l)).

Definition num_data (l : LV) : nat :=
  num_fields l - num_edges l.

Definition LE : Type := unit.

Definition raw_GC_graph : Type := LabeledGraph V E LV LE.

Definition copied_pointer_active (g : raw_GC_graph) : Prop :=
  (* If we've been copied then our first field must be a pointer *)
  forall x, 
    vvalid g x -> 
    mark (vlabel g x) = true ->
    List.nth_error (fields (vlabel g x)) 0 = Some pointer.

Definition right_number_edges (g : raw_GC_graph) (lfg : LocalFiniteGraph g) : Prop :=
  forall x,
    vvalid g x ->
    num_edges (vlabel g x) = List.length (edge_func g x).

Context {le : V -> V -> Prop}.
Local Notation "v1 <= v2" := (le v1 v2).
Local Notation "v1 <= v2 <= v3" := (v1 <= v2 /\ v2 <= v3).
Local Notation "v1 < v2" := (v1 <= v2 /\ v1 <> v2).

Context {sub : V -> V -> nat}.
Local Notation "v1 - v2" := (sub v1 v2).

Record space : Type := {
  start : V;
  next : V;
  limit : V;
  space_order : Prop := start <= next <= limit (* should we force start < limit? *)
}.

Definition size (s : space) : nat :=
  sub (limit s) (start s). (* Notation doesn't work for some reason *)

Definition allocated (s : space) (x : V) : Prop :=
  start s <= x /\ x < next s.

Definition available (s : space) (x : V) : Prop :=
  next s <= x /\ x < limit s.

Definition in_space (s : space) (x : V) : Prop :=
  allocated s x \/ available s x.

Lemma in_space_bounds: forall s x,
  in_space s x ->
  start s <= x /\ x < limit s.
Proof.
  destruct s. unfold in_space, allocated, available. simpl.
(* destruct space_order0. *)
  admit.
Admitted.

Lemma not_allocated_available: forall s x,
  ~(allocated s x /\ available s x).
Proof.
  intros ? ? [[_ ?] [? _]].
  admit.
Admitted.

Definition spaces_ok (l : list space) : Prop :=
  (* Spaces are disjoint *)
  (forall i j s1 s2,
    List.nth_error l i = Some s1 ->
    List.nth_error l j = Some s2 ->
      limit s1 <= start s2 \/
      limit s2 <= start s1 \/
      i = j) /\
  (* Spaces double in size *)
  (forall i s1 s2,
    List.nth_error l i = Some s1 ->
    List.nth_error l (S i) = Some s2 ->
    size s2 = size s1 + size s1).

Lemma only_in_one_space : forall l,
  spaces_ok l ->
  forall x i j s1 s2,
    List.nth_error l i = Some s1 ->
    List.nth_error l j = Some s2 ->
    in_space s1 x ->
    in_space s2 x ->
    s1 = s2.
Proof.
  intros.
  destruct H as [? _].
  specialize (H i j s1 s2 H0 H1).
  apply in_space_bounds in H2.
  apply in_space_bounds in H3.
  destruct H.
  admit.
  destruct H.
  admit.
  subst. rewrite H1 in H0. inversion H0.
  trivial.
Admitted.

(* Between START and NEXT *)
Definition in_generation (l : list space) (x : V) (n : nat) : Prop :=
  exists s, List.nth_error l n = Some s /\ allocated s x.

Definition valid_in_generation (g : raw_GC_graph) (l : list space) : Prop :=
  forall x, vvalid g x -> exists n, in_generation l x n.

Lemma unallocated_not_valid: forall g l n s,
  spaces_ok l ->
  valid_in_generation g l ->
  List.nth_error l n = Some s ->
  forall x, available s x ->
    ~vvalid g x.
Proof.
  repeat intro.
  specialize (H0 x H3). destruct H0 as [n' [s' [? ?]]].
  generalize (only_in_one_space l H x n n' s s' H1 H0); intro.
  assert (in_space s x) by (right; trivial).
  assert (in_space s' x) by (left; trivial).
  specialize (H5 H6 H7).
  subst s'.
  eapply not_allocated_available; eauto.
Qed.

Definition acyclic_generations (g : raw_GC_graph) (l : list space) : Prop :=
  forall x, vvalid g x -> 
    forall e, src g e = x ->
      is_null (dst g e) \/ forall n n',
        in_generation l x n ->
        in_generation l (dst g e) n' ->
        (n <= n')%nat.
(* This won't be true in the middle of a collection.  Maybe allow it to be marked? *)

Class GC_graph (g : raw_GC_graph) : Type := {
  ma : MathGraph g is_null; (* Is this general enough for the subgraphs, edges can be external but non-null? *)
  fin: FiniteGraph g;
  cpa : copied_pointer_active g;
  rne : right_number_edges g (LocalFiniteGraph_FiniteGraph g fin);
  spaces : list space;
  sok : spaces_ok spaces;
  vig : valid_in_generation g spaces;
  acycg : acyclic_generations g spaces
}.

Definition Graph : Type := GeneralGraph V E LV LE GC_graph.

Require Import Omega.

Lemma filter_length_le: forall A P (l : list A),
  List.length l >= List.length (List.filter P l).
Proof.
  induction l; auto. simpl.
  case (P a); simpl; auto.
  apply le_n_S. trivial.
Qed.

Lemma edges_le_fields: forall l,
  num_edges l <= num_fields l.
Proof.
  intro. unfold num_edges, num_fields.
  apply filter_length_le.
Qed.

Lemma num_edges_data: forall l,
  num_edges l + num_data l = num_fields l.
Proof.
  intro. generalize (edges_le_fields l). unfold num_data. omega.
Qed.

Local Open Scope logic.
