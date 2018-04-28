(* General includes? *)
Require Import ZArith.
Require Import List.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.

(* Mathematical model for graphs *)
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.msl_application.Graph.

Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.MathGraph.
Require Import RamifyCoq.graph.FiniteGraph.

Require Import RamifyCoq.CertiGC.orders.
Require Import RamifyCoq.CertiGC.bounded_numbers.

Section GC_Graph.

Local Open Scope ord.

(* RawGraph: Vertices, Edges, Labels *)

(* These will be CompCert addresses. *)
Context {V : Type} {EV : EquivDec.EqDec V eq}.
Context {null : V}.

Context {OLE : Ord V}. Existing Instance OLE.
Context {COLE : @COrd V OLE}. Existing Instance COLE.
Context {CTV: @ComparableTrans V OLE}. Existing Instance CTV.

Context {size : V -> V -> nat -> Prop}.

(*
Lemma size_ord {A} `{Ord A} : forall v1 v2 v3 n1 n2,
  v1 <= v2 <= v3 ->
  size v1 v3 (n1 + n2) <-> size v1 v2 n1 /\ size v2 v3 n2.
Admitted.
*)

Context {val : Type}. (* CompCert val, plus perhaps other info, e.g. shares *)
Context {max_fields : nat}.
Context {max_tags : nat}.
Context {tagnum_ty : Type}.
Context {max_spaces : nat}.

(* NO MORE CONTEXTS *)
 
Definition E : Type := V * nat.
Instance EE : EquivDec.EqDec E eq := prod_eqdec EV nat_eq_eqdec.
Definition LE : Type := unit.

Inductive raw_field : Type :=
  | raw_data : val -> raw_field
  | raw_pointer : raw_field.

Local Open Scope nat_scope.

Record LV : Type := {
(* We might need to have a share here. *)
  raw_mark   : bool;
  raw_fields : list raw_field;
  raw_fieldsbound : 0 < List.length raw_fields < max_fields;
  raw_tag : tagnum_ty
}.

Local Close Scope nat_scope.

Record space : Type := {
  start : V;
  next : V;
  limit : V;
  space_order : start <= next <= limit;
  non_empty: start < limit
}.

Record heap : Type := {
  spaces : list space;
  spaces_bound : length spaces <= max_spaces
}.

(* the type of args is not exactly right. 
   ideally it would be something like ''list (Type_OR V nat)'' 
*)
Record thread_info : Type := {
    args: list V;
    argc: nat;
    ti_alloc: V;
    ti_limit: V;
    ti_heap: heap
}.

Definition LG : Type := list space.

Definition raw_GCgraph : Type := LabeledGraph V E LV LE LG.

(* Pointwise GC graph *)

Definition mark (g : raw_GCgraph) (v : V) : bool := 
  raw_mark (vlabel g v).

Inductive field : Type :=
  | pointer : E -> field (* reminder: E := V * nat *)
  | data : val -> field.

Fixpoint make_fields (lf : list raw_field) (v : V) (n : nat) : list field :=
  match lf with
   | nil => nil
   | raw_data d :: lf' => data d :: make_fields lf' v (n+1)
   | raw_pointer :: lf' => pointer (v, n) :: make_fields lf' v (n+1)
  end.

Definition fields (g : raw_GCgraph) (v : V) : list field :=
  make_fields (raw_fields (vlabel g v)) v 0.

Lemma make_fields_length: forall lf v n,
    length (make_fields lf v n) = length lf.
Proof.
  induction lf.
  - reflexivity.
  - intros; simpl; destruct a; simpl; rewrite IHlf; reflexivity. 
Qed.

Definition label (g : raw_GCgraph) (v : V) : bool * list field :=
  (mark g v, fields g v).

Local Open Scope nat_scope.

(* there probably exists a lemma for this; just hacking it up for now *)
Lemma succ_is_plus_one: forall n : nat, S n = n + 1.
  induction n; omega.
  Qed.

Lemma fields_nth_pointer: forall g v n e,
  nth_error (fields g v) n = Some (pointer e) ->
  e = (v,n).
Proof.
  unfold fields. intros.
  cut (forall n m l, nth_error (make_fields l v m) n = Some (pointer e) -> e = (v, m + n)); intro.  
  specialize (H0 n 0 (raw_fields (vlabel g v))); auto.
  clear. induction n0; intros.
  icase l. simpl in H. icase r. inversion H. auto with arith.
  icase l; icase r; specialize (IHn0 (S m) l); simpl in H; rewrite IHn0; f_equal; try rewrite <- plus_n_Sm; trivial; rewrite <- succ_is_plus_one in H; apply H. 
Qed.


Instance SGBA_GCgraph: PointwiseGraphBasicAssum V E.
  constructor. apply EV. apply EE.
Defined.

Record node_rep : Type :=
{
  nr_color : bool;
  nr_tag : tagnum_ty;
  nr_fields: list field;
  nr_fields_bound : 0 < List.length nr_fields < max_fields;
  (* nr_numfields: fieldnum *)
}.

Local Close Scope nat_scope.

(* just writing out the type of the pointwise graph that will soon be generated *)
Definition SG_GCgraph := PointwiseGraph V E node_rep unit.

(* This is for the use of PointwiseGraphConstructor, by way of "exact" *)
Definition make_rpa (g: raw_GCgraph) (v: V) : node_rep.
  refine (Build_node_rep (raw_mark (vlabel g v)) (raw_tag (vlabel g v)) (fields g v) _).
  (* we've filled all holes but one. now we must provide a proof of length bound. it is below.*)
  remember (vlabel g v) as l.
  unfold fields.
  rewrite make_fields_length.
  rewrite <- Heql.
  generalize (raw_fieldsbound l); intro. apply H.
Defined.

Instance SGC_GCgraph: PointwiseGraphConstructor V E LV LE LG node_rep unit.
  constructor. exact make_rpa. exact (fun _ _ => tt).
Defined.

Definition rawGCgraph_SGgraph (G : raw_GCgraph) : SG_GCgraph := Graph_PointwiseGraph G.

Instance LSGC_GCgraph : Local_PointwiseGraphConstructor V E LV LE LG node_rep unit.
refine (Build_Local_PointwiseGraphConstructor _ _ _ _ _ _ _
          SGBA_GCgraph SGC_GCgraph 
          (fun G v => True) _
          (fun G e => True) _); trivial.
  simpl in *. intros.
  unfold make_rpa. simpl.
  unfold fields. rewrite H1.
  trivial.
Qed.

Global Existing Instances SGC_GCgraph LSGC_GCgraph.

(* General GC graph *)

Local Coercion pg_lg : LabeledGraph >-> PreGraph.
Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.
Local Coercion LocalFiniteGraph_FiniteGraph : FiniteGraph >-> LocalFiniteGraph.
(*
Local Identity Coercion SGGCgraph : SG_GCgraph >-> PointwiseGraph.
*)

Definition copied_pointer_active (g : raw_GCgraph) : Prop :=
  (* If we've been copied then our first field must be a pointer *)
  forall x, 
    vvalid g x -> 
    raw_mark (vlabel g x) = true ->
    List.nth_error (raw_fields (vlabel g x)) 0 = Some raw_pointer.

Definition num_fields (l : LV) : nat :=
  List.length (raw_fields l).

Definition num_edges (l : LV) : nat :=
  List.length (List.filter (fun x => match x with raw_pointer => true | _ => false end) (raw_fields l)).

Definition num_data (l : LV) : nat :=
  num_fields l - num_edges l.

Definition right_number_edges (g : raw_GCgraph) (lfg : LocalFiniteGraph g) : Prop :=
  forall x,
    vvalid g x ->
    num_edges (vlabel g x) = List.length (edge_func g x).

Definition allocated (s : space) (x : V) : Prop :=
  start s <= x /\ x < next s.

Definition available (s : space) (x : V) : Prop :=
  next s <= x /\ x < limit s.

Definition in_space (s : space) (x : V) : Prop :=
  allocated s x \/ available s x.

(*
(* There's probably a better way to write this definition... *)
Definition is_pointer : DecidablePred raw_field :=
  existT (fun P => forall a, {P a} + {~P a}) (fun x => x = raw_pointer)
  (fun x => match x with 
     | raw_pointer => left eq_refl
     | raw_data n => right (fun H : raw_data n = raw_pointer => 
                          eq_ind (data n) (fun e => match e with data _ => True | pointer _ => False end)
                          I raw_pointer H)
   end).
*)

(* Facts about size? *)

Definition allocated_size (s : space) (n : nat) : Prop :=
  size (start s) (next s) n.
Definition space_size (s : space) (n : nat) : Prop :=
  size (start s) (limit s) n.
Definition free_size (s : space) (n : nat) : Prop :=
  size (next s) (limit s) n.

(*
Definition size (s : space) : nat :=
  sub (limit s) (start s).
*)

Definition spaces_disjoint (g : raw_GCgraph) : Prop :=
  (* Spaces are disjoint *)
  forall i j s1 s2,
    List.nth_error (glabel g) i = Some s1 ->
    List.nth_error (glabel g) j = Some s2 ->
    forall x, 
      in_space s1 x ->
      in_space s2 x ->
      i = j.

Local Open Scope nat_scope. 

Definition spaces_double (g : raw_GCgraph) : Prop :=
  (* Spaces double in size *)
  forall i s1 s2,
    List.nth_error (glabel g) i = Some s1 ->
    List.nth_error (glabel g) (S i) = Some s2 ->
    forall n1 n2,
    space_size s1 n1 ->
    space_size s2 n2 ->
    n2 = n1 + n1.

(* Between START and NEXT *)
Definition in_generation (l : list space) (x : V) (n : nat) : Prop :=
  exists s, List.nth_error l n = Some s /\ allocated s x.

Definition valid_in_generation (g : raw_GCgraph) : Prop :=
  forall x, vvalid g x -> 
    exists n, in_generation (glabel g) x n.

(* We should make this a common definition maybe? *)
Definition is_null : DecidablePred V := 
  existT (fun P => forall a, {P a} + {~P a}) (fun x => x = null) (fun x => EV x null).

Definition acyclic_generations (g : raw_GCgraph) : Prop :=
  forall x, vvalid g x -> 
    forall e, src g e = x ->
      is_null (dst g e) \/ forall n n',
        in_generation (glabel g) (src g e) n ->
        in_generation (glabel g) (dst g e) n' ->
        (n <= n')%nat.
(* This won't be true in the middle of a collection.  Maybe allow it to be marked? *)

Parameter (addl_condition: LG -> (V -> LV) -> Prop).
  
Class GC_graph (g : raw_GCgraph)  : Type := {
  ma : MathGraph g is_null; (* Is this general enough for the subgraphs, edges can be external but non-null? *)
  fin: FiniteGraph g;
  cpa : copied_pointer_active g;
  rne : right_number_edges g fin;
  ssj : spaces_disjoint g;
  ssz : spaces_double g;
  vig : valid_in_generation g;
  acycg : acyclic_generations g;
  addl : addl_condition (glabel g) (vlabel g) 
}.

Definition Graph : Type := @GeneralGraph V E _ _ LV LE LG GC_graph.
 
Definition g_fg (g : Graph) : FiniteGraph g :=
  @fin g (sound_gg g).
Local Coercion g_fg : Graph >-> FiniteGraph.

Definition g_lfg (g : Graph) : LocalFiniteGraph g :=
  @fin g (sound_gg g).
Local Coercion g_lfg : Graph >-> LocalFiniteGraph.
Existing Instance g_lfg.

Definition get_space (g: Graph) (gen : nat) : option space := List.nth_error (glabel g) gen.             
(* TODO: 
 * 1. Maybe we can have a lemma saying that this will always return Some. That way we can remove the option. 
 *)

Local Close Scope nat_scope.

Lemma in_space_bounds: forall s x,
  in_space s x ->
  start s <= x < limit s.
Proof.
  destruct s. unfold in_space, allocated, available. simpl. intros.
  destruct H as [[? ?] | [? ?]]; split; trivial.
  apply sord_ord_trans1 with next0. tauto.
  rewrite <- H. tauto.
Qed.

Lemma bounds_in_space: forall (s:space) x,
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
  assert (comparable x start0) by (red; tauto).
  assert (comparable start0 next0) by (red; tauto).
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

Lemma in_space_start: forall (g: Graph),
    forall i s1,
      List.nth_error (glabel g) i = Some s1 ->
      in_space s1 (start s1).
Proof.
  intros. apply bounds_in_space.
  split; try reflexivity.
  destruct s1. apply non_empty0.
Qed.

Lemma spaces_empty_intersection: forall (g : Graph),
  forall i j s1 s2,
    List.nth_error (glabel g) i = Some s1 ->
    List.nth_error (glabel g) j = Some s2 ->
    i <> j -> 
    ~(in_space s1 (start s2)).
Proof.
  repeat intro.
  assert (in_space s2 (start s2)) by 
    (apply (in_space_start g j); auto).
  assert (i = j).
  {
    destruct g; destruct sound_gg; simpl in H, H0.
    apply (ssj0 i j s1 s2 H H0 (start s2)); auto.
  }
  auto.
Qed.
  
Lemma unallocated_not_valid: forall (g : Graph) n s,
  List.nth_error (glabel g) n = Some s ->
  forall x, available s x ->
    ~vvalid g x.
Proof.
  repeat intro.
  destruct g; destruct sound_gg; simpl in *.
(*
  generalize (ssj n H).
  destruct g. destruct sound_gg. simpl in *.
  specialize (H0 x H3). destruct H0 as [n' [s' [? ?]]].
  specialize (H n n' s s' H1 H0 x).
  assert (in_space s x) by (right; trivial).
  assert (in_space s' x) by (left; trivial).
  specialize (H H5 H6).
  subst n'. rewrite H1 in H0. inversion H0. subst s'.
  eapply not_allocated_available; eauto.
Qed.
*)
Admitted.

Lemma copyEdge_contr: forall (g : Graph) x,
  vvalid g x ->
  raw_mark (vlabel g x) = true ->
  nil = (@edge_func _ _ _ _ g (g_lfg g) x) ->
  False.
Proof.
  destruct g; simpl. destruct sound_gg.
  intros.
  generalize (rne0 x H); intro.
  simpl in *.
  change (g_lfg
             (@Build_GeneralGraph V E EV EE LV LE
                LG GC_graph lg_gg
                (Build_GC_graph lg_gg ma0 fin0
                   cpa0 rne0 ssj0 ssz0 vig0
                   acycg0 addl0))) with
        (@LocalFiniteGraph_FiniteGraph V E
                EV EE
                (@pg_lg V E EV EE LV LE LG lg_gg)
                fin0) in H1.
  rewrite <- H1 in H2.
  simpl in H2.
  generalize (cpa0 x H H0); intro.
  unfold num_edges in H2.
  remember (raw_fields (vlabel lg_gg x)).
  destruct l. discriminate.
  inversion H3. subst r.
  simpl in H2. discriminate.
Qed.

Local Open Scope nat_scope.
Definition copyEdge (x : V) : E := (x,0).

(*
Definition copyEdge (g : Graph) (x : V) (Pf0 : vvalid g x) (Pf1 : mark (vlabel g x) = true) : E :=
  match edge_func g x as l return l = edge_func g x -> E with
   | (e :: _)%list => fun _ => e
   | nil => fun Pf2 => match copyEdge_contr _ _ Pf0 Pf1 Pf2 with end
  end eq_refl.

Lemma copyEdge_src: forall (g : Graph) x Pf0 Pf1,
  src g (copyEdge g x Pf0 Pf1) = x.
Proof.
Admitted.
*)

Definition in_gen (g : Graph) (n : nat) (x : V) : Prop :=
  exists s, List.nth_error (glabel g) n = Some s /\ allocated s x.

Lemma in_gen_dec (g : Graph) (n : nat) (x : V) :
  {in_gen g n x} + {~ in_gen g n x}.
Proof.
  unfold in_gen. remember (glabel g). clear Heql. rename l into y.
  revert n. induction y; intro.
  + right. intro. destruct H as [? [? _]].
    destruct n; inversion H.
  + destruct n.
    * simpl. clear IHy.
      destruct a; simpl in *.
      case (ord_dec start0 x); intro.
      - case (sord_dec x next0); intro.
        left. eexists. split. reflexivity.
        red. simpl. split; trivial.
        right. intro. destruct H as [s [? ?]].
        inversion H. subst s. red in H0. 
        simpl in H0. destruct H0; contradiction.
      - right. intro. destruct H as [s [? ?]].
        inversion H. subst s. red in H0.
        simpl in H0. destruct H0. contradiction.
    * simpl. apply IHy.
Qed.

Definition from_space (gen : nat) : nat := gen.
Definition to_space (gen : nat) : nat := S gen.

Definition in_from (g : Graph) (n : nat) (x : V) :=
  in_gen g (from_space n) x.
Lemma in_from_dec: forall g n x,
  {in_from g n x} + {~in_from g n x}.
Proof. apply in_gen_dec. Qed.

Definition in_to (g : Graph) (n : nat) (x : V) :=
  in_gen g (to_space n) x.
Lemma in_to_dec: forall g n x,
  {in_to g n x} + {~in_to g n x}.
Proof. intros. apply in_gen_dec. Qed.

Section Cheney.
Require Import RamifyCoq.lib.Morphisms_ext.

Variables (G G' : Graph).

Variables (PV : V -> Prop) (PE : E -> Prop) (vmap : V -> V) (emap : E -> E).

(*
Variables (vmap_inj : is_guarded_inj PV vmap) (emap_inj : is_guarded_inj PE emap).
 *)

Local Close Scope nat_scope.

Record guarded_Cheney_morphism (gen : nat) : Prop := {
  Cvvalid_preserved: forall v, PV v -> vvalid G v -> vvalid G' v /\ vvalid G' (vmap v);

  Cevalid_preserved: forall e, PE e -> evalid G e -> evalid G' e /\ evalid G' (emap e);

  Csrc_preserved: forall e, PE e -> PV (src G e) -> evalid G e ->
                   vmap (src G e) = src G' (emap e);

  Cdst_preserved: forall e, PE e -> PV (dst G e) -> evalid G e -> 
                   vmap (dst G e) = dst G' (emap e) \/
                   dst G e        = dst G' (emap e);

  Cnon_from_vmap: forall v, PV v -> vvalid G v -> 
                   ~in_from G gen v -> 
                    vmap v = v;

  Cmarked_nodes: forall v, PV v -> vvalid G' v -> raw_mark (vlabel G' v) = true ->
                   vmap v = dst G' (copyEdge v);
(*  marked_nodes: forall v (H: PV v) (H0 : vvalid G v) (H1 : mark (vlabel G' v) = true),
                   vmap v = dst G' (copyEdge G' v (proj1 (vvalid_Cpreserved v H H0)) H1) *)

  Cvlabels_preserved: forall v, PV v -> vvalid G v -> 
                   vlabel G v = vlabel G' (vmap v);

(* We might comment this one out
  Celabels_preserved: forall e, PE e -> evalid G e ->
                   elabel G e = elabel G' (emap e);
*)
  Cglabel_preserved:
    (forall n, n <> to_space gen -> List.nth_error (glabel G) n = List.nth_error (glabel G') n) /\
    (exists s, exists s', List.nth_error (glabel G) (to_space gen) = Some s /\
                          List.nth_error (glabel G') (to_space gen) = Some s' /\
                          start s = start s' /\
                          limit s = limit s' /\
                          next s <= next s')
}.

End Cheney.

Definition unmarked_everywhere (g : Graph) : Prop :=
  forall v, vvalid g v -> raw_mark (vlabel g v) = false.

Definition generation_valid_from_space (g : Graph) (gen : nat) : Prop :=
  List.nth_error (glabel g) (to_space gen) <> None.

Lemma guarded_Cheney_morphism_refl: forall G PV PE gen,
  unmarked_everywhere G ->
  generation_valid_from_space G gen ->
  guarded_Cheney_morphism G G PV PE id id gen.
Proof.
  unfold id. intros. constructor; intros; intuition.
  * specialize (H v H2). rewrite H3 in H. discriminate.
  * red in H0. destruct (List.nth_error (glabel G) (to_space gen)).
    exists s. exists s. intuition. 
    destruct H0. trivial.
Qed.

Inductive stepish (g g' : Graph) (gen : nat) : Prop :=
  | copyitem: forall v v',
      in_from g gen v -> (* target is in from space *)
      ~vvalid g v' ->    (* v' unused *)
      vvalid g' v' ->
      vvalid g' v ->
      raw_mark (vlabel g' v) = true ->
      dst g' (copyEdge v) = v' ->
      vlabel g v = vlabel g' v' ->
(*      fields (vlabel g v) = fields (vlabel g' v) -> (* too strong *) *)
      (forall v'', v'' <> v -> v'' <> v' -> 
         (vvalid g v'' <-> vvalid g' v'') /\
         vlabel g v'' = vlabel g' v'' /\
         edge_func g v'' = edge_func g' v'') ->
      stepish g g' gen.

Lemma stepish_guarded_Cheney_morphism: forall Ga G G' PV PE vmap emap gen,
  guarded_Cheney_morphism Ga G PV PE vmap emap gen ->
  stepish G G' gen ->
  exists vmap', exists emap',
    guarded_Cheney_morphism Ga G' PV PE vmap' emap' gen.
Proof.
  (*
  intros.
  destruct H.
  destruct H0.
  exists (fun v0 => if EV v0 v then v' else vmap v0).
  exists emap.
  constructor.
  * intros.
    case (EV v0 v'); intro.
    + red in e. subst v0.
      destruct (Cvvalid_preserved0 v'); tauto.
    + compute in c.
      case (EV v0 v); intro.
      - red in e. subst v0.
        split; trivial.
      - split. specialize (H4, v0, c0, c). 
               specialize (Cvvalid_preserved0 v0). 
               tauto.
        case (EV (vmap v0) v); intro.
        compute in e. rewrite e. trivial.
        case (EV (vmap v0) v'); intro.
        compute in e. rewrite e. trivial.
        specialize (H4 (vmap v0)).
        specialize (Cvvalid_preserved0 v0). 
        tauto.
  * admit.
  * admit.
  * admit.
  * intros.
    case (EV v0 v); intro. red in e. subst v0.
    destruct Cglabel_preserved0.
    specialize (H8 (from_space gen)).
    unfold in_from, in_gen in H, H7.
    rewrite H8 in H7.
    contradiction.
    unfold from_space, to_space. intro. clear -H10. induction gen; auto. discriminate.
    admit.
  * admit.
  * intros.
    case (EV v0 v); intro.
    red in e. subst v0. rewrite <- H3.
    admit.
(*
    apply Cvlabels_preserved0.
*)
    admit.
  * admit.
*)
Admitted.

Require Import RamifyCoq.graph.graph_morphism.

Goal forall G G' PV PE vmap emap gen,
  guarded_Cheney_morphism G G' PV PE vmap emap gen ->
  GraphMorphism.guarded_morphism 
    (fun v => PV v /\ vvalid G v) 
    (fun e => PE e /\ evalid G e) vmap emap G G'.
Proof.
  intros.
  destruct H.
  constructor. firstorder. firstorder. firstorder.
  intros ? [? ?] [? ?] ?.
  specialize (Cdst_preserved0 _ H H1 H3).
  destruct Cdst_preserved0; auto.
  case (in_from_dec G gen (dst G e)); intro.
  * (* dst G e in from space, but dst G' (emap e) must not be in from space *)
    admit.
  * specialize (Cnon_from_vmap0 _ H1 H2 n).
    rewrite Cnon_from_vmap0.
    rewrite H4.
    trivial.
Admitted.


(* From graph morphisms:

Record guarded_morphism: Prop := {
  vvalid_preserved: forall v, PV v -> (vvalid G v <-> vvalid G' (vmap v));
  evalid_preserved: forall e, PE e -> (evalid G e <-> evalid G' (emap e));
  src_preserved: forall e, PE e -> PV (src G e) -> evalid G e ->
                   vmap (src G e) = src G' (emap e);
  dst_preserved: forall e, PE e -> PV (dst G e) -> evalid G e -> vmap (dst G e) = dst G' (emap e)
}.

Record guarded_bij: Prop := {
  vmap_inj: is_guarded_inj PV vmap;
  emap_inj: is_guarded_inj PE emap;
  bij_is_morphism :> guarded_morphism
}.
*)

Local Close Scope nat_scope.

Record subspaces : Type := {
  inspace : space;
  init_scan : V;
  scan : V;
  subspace_order : start inspace <= init_scan /\
                   init_scan <= scan /\
                   scan <= next inspace
}.

(*
Definition P0 (n: nat) (g: Graph) (s: subspaces) : Prop := spaces

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
*)

Require Import Omega.

Local Open Scope nat_scope.

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

End GC_Graph.
