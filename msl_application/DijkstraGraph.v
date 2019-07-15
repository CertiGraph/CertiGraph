Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.FiniteGraph.

Section DijkstraGraph.

  Definition SIZE := 8.

  Context {V E: Type}.
  Context {VE: EqDec V eq}.
  Context {EE: EqDec E eq}.

  Definition LE : Type := option nat.
  Record LV: Type := { edges: list LE; edges_range: 0 <= length edges < SIZE }.
  Record LG: Type := { src: LV; size: nat }.
      
  Coercion pg_lg: LabeledGraph >-> PreGraph.
  Coercion lg_gg: GeneralGraph >-> LabeledGraph. 
  Class FinNat (g: LabeledGraph V E LV LE LG) :=
    {
      fin: FiniteGraph g;
    }.

  Context {DV DE DG: Type}.

  Definition LGraph := LabeledGraph V E LV LE LG.
  Definition Graph := (GeneralGraph V E LV LE LG (fun g => FinNat g)).

  Fixpoint choose {A : Type} (l : list (option A)) : list A :=
    match l with
    | nil => nil
    | Some x :: tl => x :: choose tl
    | None :: tl => choose tl
    end.

  Definition allTrue {A : Type} (l : list (option A)) : bool :=
    fold_right (fun x acc => match x with Some _ => acc | _ => false end) true l.

  (* assuming that allTrue will be in the vvalid of path *)
  Definition path_cost (g: Graph) (p : @path V E) : nat :=
    match p with
    | (v, nil) => 0
    | (v, edges) => fold_left Nat.add (choose (map (elabel g) edges)) 0
    end.

End DijkstraGraph.