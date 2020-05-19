Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
(*are these needed?*)
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.reachable_computable.
(*edgelist*)
Require Import RamifyCoq.kruskal.WeightedEdgeListGraph.
Require Import RamifyCoq.kruskal.env_kruskal_edgelist.
Require Import RamifyCoq.kruskal.spatial_wedgearray_graph.
(*for unionfind*)
Require Import RamifyCoq.graph.UnionFind.
Require Import RamifyCoq.msl_application.UnionFindGraph.
Require Import RamifyCoq.msl_application.ArrayGraph.
Require Import RamifyCoq.sample_mark.env_unionfind_arr.
Require Import RamifyCoq.sample_mark.spatial_array_graph.
(*spanning tree definition*)
Require Import RamifyCoq.kruskal.mst.
(*Require Import RamifyCoq.graph.spanning_tree.*)
(*priority queue*)
Require Import RamifyCoq.sample_mark.priorityqueue.

(*Taken from VST's queue*)
Definition kruskal_mallocN_spec :=
 DECLARE kruskal_edgelist._mallocN
  WITH sh:wshare, n: Z
  PRE [tint]
     PROP (4 <= n <= Int.max_unsigned)
     PARAMS (Vint (Int.repr n))
     GLOBALS ()
     SEP ()
  POST [ tptr tvoid ]
     EX v: pointer_val,
     PROP (malloc_compatible n (pointer_val_val v))
     LOCAL (temp ret_temp (pointer_val_val v))
     SEP (memory_block sh n (pointer_val_val v)).

(*It'll be useful if we can come up with some freeN spec, then centralize these in some header*)

(* AM: You have a bug in the calls to graph_rep. *)

(*
Definition init_empty_graph_spec :=
  DECLARE _kruskal
  WITH sh: wshare
  PRE []
     PROP ()
     PARAMS ()
     GLOBALS ()
     SEP ()
  POST [ tptr t_wedgearray_graph ]
     EX (g: WeightedEdgeListGraph.LGraph) {fg: FiniteGraph g},
     EX pointer_g pointer_e: pointer_val,
     PROP (sound_weighted_edge_graph g;
           numV g = 0;
           numE g = 0
          )
     LOCAL (temp ret_temp (pointer_val_val pointer_g))
     SEP (graph_rep sh g (pointer_val_val pointer_g) (pointer_val_val pointer_e)).

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog : funspecs := ltac:(with_library prog
                                                  [kruskal_mallocN_spec; init_empty_graph_spec]).

Lemma body_init_empty_graph: semax_body Vprog Gprog f_init_empty_graph init_empty_graph_spec.
Proof.
start_function.
forward_call (sh, 12).
(*yay what is this ._.*)
set (j := Int64.max_unsigned) in *; compute in j; subst j.
Abort.

Definition kruskal_spec :=
  DECLARE _kruskal
  WITH sh: wshare, g: WeightedEdgeListGraph.LGraph, pointer_g : pointer_val
  PRE [tptr t_wedgearray_graph]
   PROP (sound_weighted_edge_graph g;
         (numE g) <= SIZE
        )
   PARAMS ((pointer_val_val pointer_g))
   GLOBALS ()
   SEP (graph_rep sh g (pointer_val_val pointer_g))
  POST [tptr t_wedgearray_graph]
   EX pointer_msf: pointer_val,
   EX (msf: WeightedEdgeListGraph.LGraph) {f_msf: FiniteGraph msf},
   PROP (sound_weighted_edge_graph msf;
         minimum_spanning_forest g msf)
   LOCAL (temp ret_temp pointer_msf)
   SEP (graph_rep sh g (pointer_val_val pointer_g);
        graph_rep sh msf pointer_msf).

*)
