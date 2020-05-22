(*Looted from msl_application/DijkstraArrayGraph
Should try abstracting it if possible from an EdgeListGraph*)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
(*Require Import RamifyCoq.msl_application.ArrayGraph.*) (*I probably need this to transform this graph to the ArrayGraph?*)
Require Import RamifyCoq.graph.FiniteGraph.
Require Import Coq.Lists.List.

Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

Local Open Scope logic.
Local Open Scope Z_scope.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).

(*
 Concretizing the EdgelistGraph with array-specific types.
 |  V  |    E    |    DV   |  DE |  DG  | soundness |
 |-----|---------|---------|-----|------|-----------| 
 |  Z  |  Z * Z  |    ?    |  Z  | unit |  Finite   |
 *)

Definition VType : Type := Z. (*0...V-1*)
Definition EType : Type := VType * VType.
Definition LE : Type := Z. (*weight*)
Definition LV: Type := unit. (*I don't think we need this*)
Definition LG: Type := unit.

Instance V_EqDec: EqDec VType eq.
Proof. hnf. apply Z.eq_dec. Qed.

Instance E_EqDec: EqDec EType eq.
Proof.
  hnf. intros [x] [y].
  destruct (equiv_dec x y).
  - hnf in e. destruct (Z.eq_dec v v0); subst.
    + left; reflexivity.
    + right. intro. apply n. inversion H. reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

Definition WEdgeListGraph := LabeledGraph VType EType LV LE LG.
(*
Print Build_PreGraph.
Print Build_LabeledGraph.

Definition Build_WEdgeListGraph := Build_LabeledGraph LV LE LG.
*)
 
Class Fin (g: WEdgeListGraph) :=
  { fin: FiniteGraph g; }.

Definition FiniteWEdgeListGraph := (GeneralGraph VType EType LV LE LG (fun g => Fin g)).

(* Later, we'll need ways to fish out the LG from the GG, 
   and we'll need to show that the specialized 
   LG you have is, at heart, an LG 
 *)
Definition FiniteWEdgeListGraph_WEdgeListGraph
           (g: FiniteWEdgeListGraph) : WEdgeListGraph := lg_gg g.
Local Coercion FiniteWEdgeListGraph_WEdgeListGraph: FiniteWEdgeListGraph >-> WEdgeListGraph.
Local Identity Coercion WEdgeListGraph_LabeledGraph: WEdgeListGraph >-> LabeledGraph.

(* This is the main thing you needed: an existing instance of 
   how to drag out FiniteGraph properties from your 
   existing GeneralGraph
 *)
Instance finGraph (g: FiniteWEdgeListGraph): FiniteGraph g := @fin g (@sound_gg _ _ _ _ _ _ _ _ g).
(* Nice. Now your definitions will be cleaner. *)


Definition src_edge (g : WEdgeListGraph): Prop :=
  forall e, src g e = fst e.

Definition dst_edge (g: WEdgeListGraph): Prop :=
  forall e, dst g e = snd e.

Definition vertex_valid (g: WEdgeListGraph): Prop :=
  forall v, vvalid g v -> 0 <= v < Int.max_signed.

Definition edge_valid (g: WEdgeListGraph): Prop :=
  forall a b, evalid g (a,b) -> (vvalid g a /\ vvalid g b).

Definition weight_valid (g: WEdgeListGraph): Prop :=
  forall e, evalid g e -> Int.min_signed <= elabel g e <= Int.max_signed. (*< IFTY*)

Definition sound_weighted_edge_graph (g: WEdgeListGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ src_edge g /\ dst_edge g /\ weight_valid g.

Definition numV (g: FiniteWEdgeListGraph) : Z := Zlength (VList g).
Definition numE (g: FiniteWEdgeListGraph) : Z := Zlength (EList g).

(* from Graph to list of edges *)
Definition graph_to_wedgelist (g: FiniteWEdgeListGraph) : list (LE * EType) :=
  map (fun e => (elabel g e, e)) (EList g). (*ordering?*)


(*Example of a WEdgeListGraph (returned by init_empty_graph*)
(*ASDF: Change this into a FiniteWEdgeListGraph (the generalgraph as defined above)
so we don't have to lug {FiniteGraph g} around *)
Definition empty_WEdgeListGraph : WEdgeListGraph :=
  (empty_labeledgraph (fun e => fst e) (fun e => snd e) (tt: LV) (0: LE) (tt: LG)).

(* Okay, so you have an empty LabeledGraph above. 
   Now we'll use that to construct a relevant 
   empty GeneralGraph.
 *)

(* First we need an instance to show that such an 
   empty LabeledGraph would satisfy the soundness condition
   of the GeneralGraph. 
 *)
Definition empty_WEdgeListGraph_finite:
  FiniteGraph empty_WEdgeListGraph.
Proof.
constructor; unfold EnumEnsembles.Enumerable, In; exists nil; split; intros; simpl.
apply NoDup_nil. reflexivity. apply NoDup_nil. reflexivity.
Qed.

Instance Sound_empty_WEdgeListGraph:
  Fin empty_WEdgeListGraph.
Proof.
  constructor.
  apply empty_WEdgeListGraph_finite.
Qed.

(* Next we can build an empty GeneralGraph 
   using the two pieces above
 *)
Definition empty_FiniteWEdgeListGraph : FiniteWEdgeListGraph :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG Fin
                      (WEdgeListGraph_LabeledGraph empty_WEdgeListGraph) Sound_empty_WEdgeListGraph.

(* and now a quick fact about the new GeneralGraph *)
Definition empty_FiniteWEdgeListGraph_finite:
  FiniteGraph empty_FiniteWEdgeListGraph.
Proof.
constructor; unfold EnumEnsembles.Enumerable, In; exists nil; split; intros; simpl.
apply NoDup_nil. reflexivity. apply NoDup_nil. reflexivity.
Qed.

Lemma empty_WEdgeListGraph_sound:
  sound_weighted_edge_graph empty_WEdgeListGraph.
Proof.
  repeat split; contradiction.
Qed.

(* Tada, these are all cleaner! *)
Lemma empty_WEdgeListGraph_VList: VList empty_FiniteWEdgeListGraph = nil.
Proof.
  unfold VList.
  destruct finiteV.
  destruct a.
  unfold proj1_sig.
  destruct x; [trivial | exfalso].
  assert (In v (v::x)) by (apply in_eq).
  apply i in H.
  contradiction.
Qed.

Lemma empty_WEdgeListGraph_EList: EList empty_FiniteWEdgeListGraph = nil.
Proof.
  unfold EList.
  destruct finiteE.
  destruct a.
  unfold proj1_sig. 
  destruct x; [trivial | exfalso].
  assert (In e (e::x)) by (apply in_eq).
  apply i in H.
  contradiction.
Qed.

Corollary empty_WEdgeListGraph_numV: numV empty_FiniteWEdgeListGraph = 0.
Proof.
unfold numV. rewrite empty_WEdgeListGraph_VList. apply Zlength_nil.
Qed.

Corollary empty_WEdgeListGraph_numE: numE empty_FiniteWEdgeListGraph = 0.
Proof.
unfold numE. rewrite empty_WEdgeListGraph_EList. apply Zlength_nil.
Qed.

Corollary empty_WEdgeListGraph_graph_to_wedgelist:
  graph_to_wedgelist empty_FiniteWEdgeListGraph = nil.
Proof.
unfold graph_to_wedgelist. rewrite empty_WEdgeListGraph_EList. reflexivity.
Qed.

(* Moving on to Spatial Rep *)

Section SpatialWEdgeListGraph.
  
  Class SpatialWEdgeListGraphAssum (Pred : Type):= (*what is this?*)
    {
    SGP_ND: NatDed Pred;
    SGP_SL : SepLog Pred;
    SGP_ClSL: ClassicalSep Pred;
    SGP_CoSL: CorableSepLog Pred
    }.
  
  Class SpatialWEdgeListGraph (Addr: Type) (Pred: Type) :=
    abstract_data_at: Addr -> list (LE*EType) -> Pred.

  Context {Pred: Type}.
  Context {Addr: Type}.
  Context {SAGP: SpatialWEdgeListGraphAssum Pred}.
  Context {SAG: SpatialWEdgeListGraph Addr Pred}.
  
End SpatialWEdgeListGraph.


Lemma if_true_bool:
  forall (T : Type) (a : T) (b : bool) (c : T),
    b = true -> (if b then a else c) = a.
Proof. intros. rewrite H. trivial. Qed.

Lemma if_false_bool:
  forall (T : Type) (a : T) (b : bool) (c : T),
    b = false -> (if b then a else c) = c.
Proof. intros. rewrite H. trivial. Qed.
