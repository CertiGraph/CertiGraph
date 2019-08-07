Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import Coq.ZArith.ZArith.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import compcert.lib.Integers.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Export RamifyCoq.graph.FiniteGraph.
Require Export RamifyCoq.graph.MathGraph.
Require Export RamifyCoq.graph.LstGraph.
Require Import RamifyCoq.msl_application.DijkstraGraph.
(* TODO: Narrow the above to be minimal *)

Local Open Scope logic.
Local Open Scope Z_scope.
Definition inf := Integers.Int.max_signed.
Definition size := 8%nat.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).


(* 
 Concretizing the DijkstraGraph with array-specific types.
 |  V  |  E  |    DV   |     DE     |  DG  | soundness |
 |-----|-----|---------|------------|------|-----------| 
 |  Z  |  Z  | list DE | option nat | unit |  Finite   |  
 *)

Definition VType : Type := Z.
Definition EType : Type := Z.
Definition LE : Type := option nat.
Definition LV: Type := list LE.
Definition LG: Type := unit.
(*Record LG: Type := (* may be unnecessary? *)
  {
  vertices : list LV;
  size: nat;
  vertices_range: length vertices = size
  }. *)

Definition Graph := (@Graph VType EType _ _ LV LE LG).
Definition LGraph := (@LGraph VType EType _ _ LV LE LG).


(* Moving on to Spatial Rep *)

Section SpaceDijkstraArrayGraph.

  Class SpatialDijkstraArrayGraphAssum (Pred : Type):=
  {
    SGP_ND: NatDed Pred;
    SGP_SL : SepLog Pred;
    SGP_ClSL: ClassicalSep Pred;
    SGP_CoSL: CorableSepLog Pred
  }.
  
  Class SpatialDijkstraArrayGraph (Addr: Type) (Pred: Type) := abstract_data_at: Addr -> list Z -> Pred.

  Context {Pred: Type}.
  Context {Addr: Type}.
  Context {SAGP: SpatialDijkstraArrayGraphAssum Pred}.
  Context {SAG: SpatialDijkstraArrayGraph Addr Pred}.

(* TODO: move this to vvalid of a Dijk path *)
Definition allTrue {A : Type} (l : list (option A)) : bool :=
  fold_right (fun x acc => match x with Some _ => acc | _ => false end) true l.

(* assuming that allTrue will be in the vvalid of path *)
Definition path_cost (g: Graph) (p : @path VType EType) : nat :=
  match p with
  | (v, nil) => 0
  | (v, edges) => fold_left Nat.add (choose (map (elabel g) edges)) 0%nat
  end.

Fixpoint Z_inc_list (n: nat) : list Z :=
  match n with
  | O => nil
  | S n' => Z_inc_list n' ++ (Z.of_nat n' :: nil)
  end.

Definition vert_rep (g : Graph) (v : LV) : list Z :=
  map (fun x => match x with Some x => (Z.of_nat x) | None => inf end) v.

(* from Graph to list (list Z) *)
Definition graph_rep (g : Graph) : list (list Z) :=
  map (vert_rep g) (map (vlabel g) (Z_inc_list size)).

(* from list (list Z) to list Z of n^2 size *)
Definition graph_rep_contiguous (g : Graph) : list Z :=
  List.concat (graph_rep g).

(* spatial representation of the DijkstraGraph *)
Definition graph_rep_spatial (g : Graph) (a : Addr)  :=
  abstract_data_at a (graph_rep_contiguous g).

End SpaceDijkstraArrayGraph.