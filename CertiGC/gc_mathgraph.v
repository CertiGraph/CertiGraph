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

Require Import RamifyCoq.CertiGC.orders.

Section GC_Graph.

Local Coercion pg_lg : LabeledGraph >-> PreGraph.
Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.
Local Coercion LocalFiniteGraph_FiniteGraph : FiniteGraph >-> LocalFiniteGraph.

Open Local Scope ord.

(* RawGraph: Vertices, Edges, Labels *)

(* These will be CompCert addresses. *)
Context {V : Type} {EV : EquivDec.EqDec V eq}.
Context {null : V}.

Context {OLE : Ord V}. Existing Instance OLE.
Context {CTV: ComparableTrans V}. Existing Instance CTV.

(* These might be CompCert addresses, or perhaps other choices. *)
Context {E : Type} {EE : EquivDec.EqDec E eq}.
(*
Definition E : Type := V * nat.
Instance EE : EquivDec.EqDec E eq := prod_eqdec EV nat_eq_eqdec.
*)

Context {val : Type}. (* CompCert val, plus perhaps other information e.g. shares *)

Inductive field_type : Type :=
  | data : val -> field_type
  | pointer : field_type.

Record LV : Type := {
(* We might need to have a share here. *)
  mark   : bool;
  fields : list field_type;
  non_empty : List.length fields > 0
}.

Definition LE : Type := unit.

Record space : Type := {
  start : V;
  next : V;
  limit : V;
  space_order : start <= next <= limit
}.

Definition LG : Type := list space.

Definition raw_GC_graph : Type := LabeledGraph V E LV LE LG.

(* General GC graph *)

Definition copied_pointer_active (g : raw_GC_graph) : Prop :=
  (* If we've been copied then our first field must be a pointer *)
  forall x, 
    vvalid g x -> 
    mark (vlabel g x) = true ->
    List.nth_error (fields (vlabel g x)) 0 = Some pointer.

Definition num_fields (l : LV) : nat :=
  List.length (fields l).

Definition num_edges (l : LV) : nat :=
  List.length (List.filter (fun x => match x with pointer => true | _ => false end) (fields l)).

Definition num_data (l : LV) : nat :=
  num_fields l - num_edges l.

Definition right_number_edges (g : raw_GC_graph) (lfg : LocalFiniteGraph g) : Prop :=
  forall x,
    vvalid g x ->
    num_edges (vlabel g x) = List.length (edge_func g x).

Definition allocated (s : space) (x : V) : Prop :=
  start s <= x /\ x < next s.

Definition available (s : space) (x : V) : Prop :=
  next s <= x /\ x < limit s.

Definition in_space (s : space) (x : V) : Prop :=
  allocated s x \/ available s x.

Lemma in_space_bounds: forall s x,
  in_space s x ->
  start s <= x < limit s.
Proof.
  destruct s. unfold in_space, allocated, available. simpl. intros.
  destruct H as [[? ?] | [? ?]]; split; trivial.
  apply sord_ord_trans1 with next0. tauto.
  rewrite <- H. tauto.
Qed.

Lemma bounds_in_space: forall s x,
  start s <= x < limit s ->
  in_space s x.
Proof.
  intros.
  destruct H.
  destruct s.
  red. unfold available, allocated. simpl in *.
  destruct space_order0.
  case (EV x next0); unfold equiv, complement; intro.
  subst. right.
  auto with ord.
  assert (x ~ start0) by (red; tauto).
  assert (start0 ~ next0) by (red; tauto).
  rewrite <- H3 in H4.
  destruct H4.
  left; split; red; tauto.
  right. tauto.
Qed.

Lemma not_allocated_available: forall s x,
  ~(allocated s x /\ available s x).
Proof.
  intros ? ? [[_ ?] [? _]].
  apply sord_antirefl with x.
  eauto with ord.
Qed.

(* There's probably a better way to write this definition... *)
Definition is_pointer : DecidablePred field_type :=
  existT (fun P => forall a, {P a} + {~P a}) (fun x => x = pointer)
  (fun x => match x with 
     | pointer => left eq_refl
     | data n => right (fun H : data n = pointer => 
                          eq_ind (data n) (fun e => match e with data _ => True | pointer => False end)
                          I pointer H)
   end).

(* Facts about size? *)
Context {size : V -> V -> nat -> Prop}.
Lemma size_ord {A} `{Ord A} : forall v1 v2 v3 n1 n2,
  v1 <= v2 <= v3 ->
  size v1 v3 (n1 + n2) <-> size v1 v2 n1 /\ size v2 v3 n2.
Admitted.

Definition allocated_size (s : space) (n : nat) : Prop :=
  size (start s) (next s) n.
Definition space_size (s : space) (n : nat) : Prop :=
  size (start s) (limit s) n.
Definition free_size (s : space) (n : nat) : Prop :=
  size (next s) (limit s) n.

(*
Definition size (s : space) : nat :=
  sub (limit s) (start s). (* Notation doesn't work for some reason *)
*)

Definition spaces_disjoint (g : raw_GC_graph) : Prop :=
  (* Spaces are disjoint *)
  forall i j s1 s2,
    List.nth_error (glabel g) i = Some s1 ->
    List.nth_error (glabel g) j = Some s2 ->
    forall x, 
      in_space s1 x ->
      in_space s2 x ->
      i = j.

Definition spaces_double (g : raw_GC_graph) : Prop :=
  (* Spaces double in size *)
  forall i s1 s2,
    List.nth_error (glabel g) i = Some s1 ->
    List.nth_error (glabel g) (S i) = Some s2 ->
    forall n1 n2,
    space_size s1 n1 ->
    space_size s2 n2 ->
    n2 = n1 + n1.

Lemma spaces_empty_intersection: forall g,
  spaces_disjoint g ->
  forall i j s1 s2,
    List.nth_error (glabel g) i = Some s1 ->
    List.nth_error (glabel g) j = Some s2 ->
    ~(in_space s1 (start s2)).
Proof.
  repeat intro.
  assert (in_space s2 (start s2)). 
    { apply bounds_in_space. split. reflexivity.
      destruct s2. simpl in *. 
  apply in_space_bounds in H2.
  admit. }
  specialize (H i j s1 s2 H0 H1 _ H2 H3). subst j.
  admit.
Admitted.

(* Between START and NEXT *)
Definition in_generation (l : list space) (x : V) (n : nat) : Prop :=
  exists s, List.nth_error l n = Some s /\ allocated s x.

Definition valid_in_generation (g : raw_GC_graph) : Prop :=
  forall x, vvalid g x -> exists n, in_generation (glabel g) x n.

Lemma unallocated_not_valid: forall g n s,
  spaces_disjoint g ->
  valid_in_generation g ->
  List.nth_error (glabel g) n = Some s ->
  forall x, available s x ->
    ~vvalid g x.
Proof.
  repeat intro.
  specialize (H0 x H3). destruct H0 as [n' [s' [? ?]]].
  specialize (H n n' s s' H1 H0 x).
  assert (in_space s x) by (right; trivial).
  assert (in_space s' x) by (left; trivial).
  specialize (H H5 H6).
  subst n'. rewrite H1 in H0. inversion H0. subst s'.
  eapply not_allocated_available; eauto.
Qed.

(* We should make this a common definition maybe? *)
Definition is_null : DecidablePred V := 
  existT (fun P => forall a, {P a} + {~P a}) (fun x => x = null) (fun x => EV x null).

Definition acyclic_generations (g : raw_GC_graph) : Prop :=
  forall x, vvalid g x -> 
    forall e, src g e = x ->
      is_null (dst g e) \/ forall n n',
        in_generation (glabel g) (src g e) n ->
        in_generation (glabel g) (dst g e) n' ->
        (n <= n')%nat.
(* This won't be true in the middle of a collection.  Maybe allow it to be marked? *)

Class GC_graph (g : raw_GC_graph) : Type := {
  ma : MathGraph g is_null; (* Is this general enough for the subgraphs, edges can be external but non-null? *)
  fin: FiniteGraph g;
  cpa : copied_pointer_active g;
  rne : right_number_edges g fin;
  ssj : spaces_disjoint g;
  ssz : spaces_double g;
  vig : valid_in_generation g;
  acycg : acyclic_generations g
}.

Definition Graph : Type := GeneralGraph V E LV LE LG GC_graph.

Definition g_lfg (g : Graph) : LocalFiniteGraph g :=
  @fin g (sound_gg g).
Local Coercion g_lfg : Graph >-> LocalFiniteGraph.

Lemma copyEdge_contr: forall (g : Graph) x,
  vvalid g x ->
  mark (vlabel g x) = true ->
  nil = (@edge_func _ _ _ _ g (g_lfg g) x) ->
  False.
Proof.
  destruct g; simpl. destruct sound_gg.
  intros.
  generalize (rne0 x H); intro.
  simpl in *.
  replace (g_lfg
             (@Build_GeneralGraph V E EV EE LV LE
                LG GC_graph lg_gg
                (Build_GC_graph lg_gg ma0 fin0
                   cpa0 rne0 ssj0 ssz0 vig0
                   acycg0))) with
        (@LocalFiniteGraph_FiniteGraph V E
                EV EE
                (@pg_lg V E EV EE LV LE LG lg_gg)
                fin0) in H1.
  rewrite <- H1 in H2.
  simpl in H2.
  generalize (cpa0 x H H0); intro.
  unfold num_edges in H2.
  remember (fields (vlabel lg_gg x)).
  destruct l. discriminate.
  inversion H3. subst f.
  simpl in H2. discriminate.
  admit. (* Shengyi? *)
Admitted.

Definition copyEdge (g : Graph) (x : V) (Pf0 : vvalid g x) (Pf1 : mark (vlabel g x) = true) : E :=
  match edge_func g x as l return l = edge_func g x -> E with
   | (e :: _)%list => fun _ => e
   | nil => fun Pf2 => match (copyEdge_contr _ _ Pf0 Pf1 Pf2) with end
  end eq_refl.

Section Cheney.

Variables (G G' : Graph).

Variables (PV : V -> Prop) (PE : E -> Prop) (vmap : V -> V) (emap : E -> E).

Record guarded_Cheney_morphism: Prop := {
  vvalid_Cpreserved: forall v, PV v -> (vvalid G v <-> vvalid G' (vmap v));
  evalid_Cpreserved: forall e, PE e -> (evalid G e <-> evalid G' (emap e));
  src_Cpreserved: forall e, PE e -> PV (src G e) -> evalid G e ->
                   vmap (src G e) = src G' (emap e);
  dst_Cpreserved: forall e, PE e -> PV (dst G e) -> evalid G e -> vmap (dst G e) = dst G' (emap e)
}.


  vvalid_preserved: forall v, PV v -> (vvalid G v <-> vvalid G' (vmap v));
  evalid_preserved: forall e, PE e -> (evalid G e <-> evalid G' (emap e));


  forall v, vvalid g1 v -> 

Print reachable_subgraph.

Print reachable_through_set.

Print reachable.

Print reachable_by.

Definition CheneyIsomorphic (g1 g2 : Graph) 
                            (roots : list V) : Prop :=
  forall v, vvalid g1 v ->


Record subspaces : Type := {
  inspace : space;
  init_scan : V;
  scan : V;
  subspace_order : start inspace <= init_scan /\
                   init_scan <= scan /\
                   scan <= next inspace
}.

Definition 

(*
Definition P0 (n: nat) (g: Graph) (s: subspaces) : Prop := spaces
*)


Definition P0 (n : nat) (s1 s2 : subspaces) (g : Graph) (g' : Graph) : Prop :=
  exists s, exists s',
    List.nth_error (glabel g) n = Some s /\ 
    List.nth_error (glabel g') n = Some s' /\
    start s = start s' /\
    limit s = limit s' /\
    next s <= next s' /\    
    inspace s1 = s /\
    inspace s2 = s' /\
    init_scan s1 = init_scan s2 /\
    scan s1 <= scan s2 /\
    forall x,
      start s <= x < init_scan s1 -> (* also in s', s2 by equalities above *)
      ( (vvalid g x <-> vvalid g' x) /\
        (vlabel g x = vlabel g' x) /\
        (@edge_func _ _ _ _ g g x = @edge_func _ _ _ _ g' g' x) /\
        (forall e, src g e = x -> dst g e = dst g' e) ).

Require Import Omega.

Lemma filter_length_le: forall A P (l : list A),
  List.length l >= List.length (List.filter P l).
Proof.
  induction l; auto. simpl.
  case (P a); simpl; auto.
  apply le_n_S. trivial.
Qed.

Lemma edges_le_fields: forall l,
  (num_edges l <= num_fields l)%nat.
Proof.
  intro. unfold num_edges, num_fields.
  apply filter_length_le.
Qed.

Lemma num_edges_data: forall l,
  num_edges l + num_data l = num_fields l.
Proof.
  intro. generalize (edges_le_fields l). unfold num_data. omega.
Qed.

End GC_Graph.
