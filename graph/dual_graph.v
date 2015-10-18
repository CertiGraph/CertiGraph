Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.

Section DualGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context (g: PreGraph V E).

Definition dual_src e := dst g e.
Definition dual_dst e := src g e.
Definition dualgraph: PreGraph V E :=
  Build_PreGraph EV EE (vvalid g) (evalid g) dual_src dual_dst.

End DualGraph.
