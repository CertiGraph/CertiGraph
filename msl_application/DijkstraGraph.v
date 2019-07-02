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

  Context {V E: Type}.
  Context {VE: EqDec V eq}.
  Context {EE: EqDec E eq}.

  Definition LV: Type := nat.
  Definition LE : Type := nat.
  Definition LG: Type := unit.
  
  Local Coercion pg_lg: LabeledGraph >-> PreGraph.
  Local Coercion lg_gg: GeneralGraph >-> LabeledGraph.
  
  Class FinNat (g: LabeledGraph V E LV LE LG) :=
    {
      fin: FiniteGraph g;
    }.

  Context {DV DE DG: Type}.

  Definition LGraph := LabeledGraph V E LV LE LG.
  Definition Graph := (GeneralGraph V E LV LE LG (fun g => FinNat g)).

  Definition path_cost (g: Graph) (p : @path V E) : LE :=
    match p with
    | (v, nil) => 0
    | (v, edges) => fold_left Nat.add (map (elabel g) edges) 0
    end.

End DijkstraGraph.