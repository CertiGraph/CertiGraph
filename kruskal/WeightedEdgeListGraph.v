(*Looted from msl_application/DijkstraArrayGraph
Should try abstracting it if possible from an EdgeListGraph*)
Require Export VST.floyd.proofauto.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
(*Require Import RamifyCoq.msl_application.ArrayGraph.*) (*I probably need this to transform this graph to the ArrayGraph?*)
Require Import RamifyCoq.graph.FiniteGraph.
Require Import Coq.Lists.List.

Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

Local Open Scope logic.
Local Open Scope Z_scope.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).

(*Definition SIZE := 8.
Definition IFTY := Int.max_signed - Int.max_signed / SIZE.*)

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

Definition LGraph := LabeledGraph VType EType LV LE LG.

Class Fin (g: LGraph) :=
  { fin: FiniteGraph g; }.

Definition Graph := (GeneralGraph VType EType LV LE LG (fun g => Fin g)).

Definition src_edge (g: LGraph): Prop :=
  forall e, src g e = fst e.

Definition dst_edge (g: LGraph): Prop :=
  forall e, dst g e = snd e.

Definition vertex_valid (g: LGraph): Prop :=
  forall v, vvalid g v <-> 0 <= v < Int.max_signed.

Definition edge_valid (g: LGraph): Prop :=
  forall a b, evalid g (a,b) <-> (vvalid g a /\ vvalid g b).

Definition weight_valid (g: LGraph): Prop :=
  forall e, evalid g e -> Int.min_signed <= elabel g e <= Int.max_signed. (*< IFTY*)

Definition sound_weighted_edge_graph (g: LGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ src_edge g /\ dst_edge g /\ weight_valid g.

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
  
  Definition numV (g: LGraph) {fg : FiniteGraph g} : Z := Zlength (VList g).
  Definition numE (g: LGraph) {fg : FiniteGraph g} : Z := Zlength (EList g).

  (* from Graph to list of edges *)
  Definition graph_to_wedgelist (g: LGraph) {fg: FiniteGraph g} : list (LE*EType) :=
    map (fun e => (elabel g e, e)) (EList g). (*ordering?*)

End SpatialWEdgeListGraph.

Lemma if_true_bool:
  forall (T : Type) (a : T) (b : bool) (c : T),
    b = true -> (if b then a else c) = a.
Proof. intros. rewrite H. trivial. Qed.

Lemma if_false_bool:
  forall (T : Type) (a : T) (b : bool) (c : T),
    b = false -> (if b then a else c) = c.
Proof. intros. rewrite H. trivial. Qed.

Lemma vvalid2_evalid:
  forall g a b,
    sound_weighted_edge_graph g ->
    vvalid g a ->
    vvalid g b ->
    evalid g (a,b).
Proof.
  intros. destruct H as [_ [? _]].
  red in H; rewrite H; split; trivial.
Qed.

Lemma vvalid_range:
  forall g v,
    sound_weighted_edge_graph g ->
    vvalid g v <-> 0 <= v < Int.max_signed.
Proof.
  intros. destruct H as [? _]. red in H. trivial.
Qed.