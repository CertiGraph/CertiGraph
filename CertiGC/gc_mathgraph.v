(* General includes? *)
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

Open Local Scope ord.

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

Context {val : Type}. (* CompCert val, plus perhaps other information e.g. shares *)
Context {max_fields : nat}.

(* NO MORE CONTEXTS *)

Definition E : Type := V * nat.
Instance EE : EquivDec.EqDec E eq := prod_eqdec EV nat_eq_eqdec.

Inductive raw_field : Type :=
  | raw_data : val -> raw_field
  | raw_pointer : raw_field.

Record LV : Type := {
(* We might need to have a share here. *)
  raw_mark   : bool;
  raw_fields : list raw_field;
  raw_fieldsbound : 0 < List.length raw_fields < max_fields
}.

Definition LE : Type := unit.

Record space : Type := {
  start : V;
  next : V;
  limit : V;
  space_order : start <= next <= limit
}.

Definition LG : Type := list space.

Definition raw_GCgraph : Type := LabeledGraph V E LV LE LG.

(* Spatial GC graph *)

Definition mark (g : raw_GCgraph) (v : V) : bool :=
  raw_mark (vlabel g v).

Inductive field : Type :=
  | pointer : E -> field
  | data : val -> field.

Fixpoint make_fields (lf : list raw_field) (v : V) (n : nat) : list field :=
  match lf with
   | nil => nil
   | raw_data d :: lf' => data d :: make_fields lf' v (1 + n)
   | raw_pointer :: lf' => pointer (v, n) :: make_fields lf' v (1 + n)
  end.

Definition fields (g : raw_GCgraph) (v : V) : list field :=
  make_fields (raw_fields (vlabel g v)) v 0.

Definition label (g : raw_GCgraph) (v : V) : bool * { list field :=
  (mark g v, fields g v).

Section size.
Import ZArith.

Definition nodesize (rpa : bool * list field) : Z :=
  1 + Z.of_nat (length (snd rpa)). (* We need 1 word for the header *)

End size.

Lemma fields_nth_pointer: forall g v n e,
  nth_error (fields g v) n = Some (pointer e) ->
  e = (v,n).
Proof.
  unfold fields. intros.
  cut (forall n m l, nth_error (make_fields l v m) n = Some (pointer e) -> e = (v, m + n)); intro.  
  specialize (H0 n 0 (raw_fields (vlabel g v))); auto.
  clear. induction n0; intros.
  icase l. simpl in H. icase r. inversion H. auto with arith.
  icase l; icase r; specialize (IHn0 (S m) l H); rewrite IHn0; f_equal; 
  rewrite <- plus_n_Sm; trivial.
Qed.

Instance SGBA_GCgraph: SpatialGraphBasicAssum V E.
  constructor. apply EV. apply EE.
Defined.

Instance SGC_GCgraph: SpatialGraphConstructor V E LV LE LG (bool * list field) unit.
  constructor. exact label. exact (fun _ _ => tt).
Defined.

Definition SG_GCgraph := SpatialGraph V E (bool * list field) unit.
Definition rawGCgraph_SGgraph (G : raw_GCgraph) : SG_GCgraph := Graph_SpatialGraph G.

Instance LSGC_GCgraph : Local_SpatialGraphConstructor V E LV LE LG (bool * list field) unit.
  refine (Build_Local_SpatialGraphConstructor _ _ _ _ _ _ _ SGBA_GCgraph SGC_GCgraph 
          (fun G v => True) _
          (fun G e => True) _); trivial.
  simpl in *. unfold label, mark, fields. intros. rewrite H1. auto.
Defined.

Global Existing Instances SGC_GCgraph LSGC_GCgraph.

(* General GC graph *)

Local Coercion pg_lg : LabeledGraph >-> PreGraph.
Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.
Local Coercion LocalFiniteGraph_FiniteGraph : FiniteGraph >-> LocalFiniteGraph.
(*
Local Identity Coercion SGGCgraph : SG_GCgraph >-> SpatialGraph.
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
  sub (limit s) (start s). (* Notation doesn't work for some reason *)
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

Class GC_graph (g : raw_GCgraph) : Type := {
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
Existing Instance g_lfg.

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

Lemma spaces_empty_intersection: forall (g : Graph),
  forall i j s1 s2,
    List.nth_error (glabel g) i = Some s1 ->
    List.nth_error (glabel g) j = Some s2 ->
    ~(in_space s1 (start s2)).
Proof.
(*
  repeat intro.
  assert (in_space s2 (start s2)). 
    { apply bounds_in_space. split. reflexivity.
      destruct s2. simpl in *. 
  apply in_space_bounds in H2.
  admit. }
  specialize (H i j s1 s2 H0 H1 _ H2 H3). subst j.
  admit.
*)
Admitted.

Lemma unallocated_not_valid: forall (g : Graph) n s,
  List.nth_error (glabel g) n = Some s ->
  forall x, available s x ->
    ~vvalid g x.
Proof.
  repeat intro.
(*  generalize (ssj n H).
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
                   acycg0))) with
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
  unfold in_gen. remember (glabel g). clear Heqy.
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
      - split. specialize (H4 v0 c0 c). 
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
