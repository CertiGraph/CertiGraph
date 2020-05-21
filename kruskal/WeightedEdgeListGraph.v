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

Definition src_edge (g: WEdgeListGraph): Prop :=
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

Definition numV (g: WEdgeListGraph) {fg : FiniteGraph g} : Z := Zlength (VList g).
Definition numE (g: WEdgeListGraph) {fg : FiniteGraph g} : Z := Zlength (EList g).

(* from Graph to list of edges *)
Definition graph_to_wedgelist (g: WEdgeListGraph) {fg: FiniteGraph g} : list (LE*EType) :=
  map (fun e => (elabel g e, e)) (EList g). (*ordering?*)


(*Example of a WEdgeListGraph (returned by init_empty_graph*)
(*ASDF: Change this into a FiniteWEdgeListGraph (the generalgraph as defined above)
so we don't have to lug {FiniteGraph g} around *)
Definition empty_WEdgeListGraph : WEdgeListGraph :=
(empty_labeledgraph (fun e => fst e) (fun e => snd e) tt 0 tt).

Definition empty_WEdgeListGraph_finite:
  FiniteGraph empty_WEdgeListGraph.
Proof.
constructor; unfold EnumEnsembles.Enumerable, In; exists nil; split; intros; simpl.
apply NoDup_nil. reflexivity. apply NoDup_nil. reflexivity.
Qed.

Lemma empty_WEdgeListGraph_sound:
  sound_weighted_edge_graph empty_WEdgeListGraph.
Proof.
repeat split; try contradiction.
Qed.

Lemma empty_WEdgeListGraph_VList {fg: FiniteGraph empty_WEdgeListGraph}:
  VList empty_WEdgeListGraph = nil.
Proof.
unfold VList. destruct fg. simpl in finiteV. unfold EnumEnsembles.Enumerable in finiteV.
destruct finiteV. destruct a.
unfold proj1_sig. unfold finiteV.
destruct x. reflexivity.
assert (In v (v::x)) by (apply in_eq). specialize i with v. destruct i. contradiction.
Qed.

Lemma empty_WEdgeListGraph_EList {fg: FiniteGraph empty_WEdgeListGraph}:
  EList empty_WEdgeListGraph = nil.
Proof.
unfold EList. destruct fg. simpl in finiteE; unfold EnumEnsembles.Enumerable in finiteE.
destruct finiteE. destruct a.
unfold proj1_sig; unfold finiteE.
destruct x. reflexivity.
assert (In e (e::x)) by (apply in_eq). specialize i with e. destruct i. contradiction.
Qed.

Corollary empty_WEdgeListGraph_numV {fg: FiniteGraph empty_WEdgeListGraph}:
  numV empty_WEdgeListGraph = 0.
Proof.
unfold numV. rewrite empty_WEdgeListGraph_VList. apply Zlength_nil.
Qed.

Corollary empty_WEdgeListGraph_numE {fg: FiniteGraph empty_WEdgeListGraph}:
  numE empty_WEdgeListGraph = 0.
Proof.
unfold numE. rewrite empty_WEdgeListGraph_EList. apply Zlength_nil.
Qed.

Corollary empty_WEdgeListGraph_graph_to_wedgelist {fg: FiniteGraph empty_WEdgeListGraph}:
  graph_to_wedgelist empty_WEdgeListGraph = nil.
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