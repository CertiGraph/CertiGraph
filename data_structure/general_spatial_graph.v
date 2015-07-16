Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.Coqlib.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.marked_graph.
Require Import RamifyCoq.graph.graph_gen.
Require Import Coq.Logic.Classical.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Local Open Scope logic.

Class SpatialGraph (V E DV DE: Type): Type := {
  pg: PreGraph V E;
  vgamma: V -> DV;
  egamma: E -> DE
}.

Arguments vgamma {V E DV DE} _ _.
Arguments egamma {V E DV DE} _ _.

Class SpatialGraphPred (V E DV DE Pred: Type): Type := {
  vertex_at: V -> DV -> Pred;
  edge_at: E -> DE -> Pred
}.

Class SpatialGraphAssum {V E DV DE Pred: Type} (SGP: SpatialGraphPred V E DV DE Pred) := {
  SGP_ND: NatDed Pred;
  SGP_SL : SepLog Pred;
  SGP_ClSL: ClassicalSep Pred;
  SGP_CoSL: CorableSepLog Pred
}.

Existing Instances SGP_ND SGP_SL SGP_ClSL SGP_CoSL.

Class SpatialGraphStrongAssum {V E DV DE Pred: Type} (SGP: SpatialGraphPred V E DV DE Pred) := {
  SGA: SpatialGraphAssum SGP;
  SGP_PSL: PreciseSepLog Pred;
  SGP_OSL: OverlapSepLog Pred;
  SGP_DSL: DisjointedSepLog Pred;
  SGP_COSL: CorableOverlapSepLog Pred;

  AAV: AbsAddr V DV;
  AAE: AbsAddr E DE;
  VP_MSL: MapstoSepLog AAV vertex_at;
  VP_sMSL: StaticMapstoSepLog AAV vertex_at;
  EP_MSL: MapstoSepLog AAE edge_at;
  EP_sMSL: StaticMapstoSepLog AAE edge_at
}.

Existing Instances SGA SGP_PSL SGP_OSL SGP_DSL SGP_COSL VP_MSL VP_sMSL EP_MSL EP_sMSL.

Coercion pg : SpatialGraph >-> PreGraph.

Section SpatialGraph.

  Context {V E DV DE Pred: Type}.
  Context {SGP: SpatialGraphPred V E DV DE Pred}.
  Context {SGA: SpatialGraphAssum SGP}.
  Notation Graph := (SpatialGraph V E DV DE).

  Definition graph_cell (g: Graph) (v : V) : Pred := vertex_at v (vgamma g v).

  Definition graph (x : V) (g: Graph) : Pred :=
    EX l : list V, !!reachable_list g x l && iter_sepcon l (graph_cell g).

End SpatialGraph.