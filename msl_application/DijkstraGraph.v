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
Require Import Coq.ZArith.ZArith.
Section DijkstraGraph.

 
  Context {V E: Type}.
  Context {VE: EqDec V eq}.
  Context {EE: EqDec E eq}.
  Context {DV DE DG: Type}.

  Coercion pg_lg: LabeledGraph >-> PreGraph.
  Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

  (* Local Open Scope Z_scope. *)
  
  (* Class PosEdgeGraph (pg: LabeledGraph V E DV DE DG) := *)
    (* { *)
      (* posEdge: (fun x  => x > 0) (evalid pg) *)
    (* }. *)


  (* Definition LGraph := LabeledGraph V E DV DE DG. *)
  (* Definition Graph := (GeneralGraph V E DV DE DG (fun g => Fin g)). *)

End DijkstraGraph.