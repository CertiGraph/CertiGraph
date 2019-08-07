Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.sample_mark.env_dijkstra_arr.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.msl_application.DijkstraGraph.
Require Import RamifyCoq.msl_application.DijkstraArrayGraph.
Require Import RamifyCoq.sample_mark.spatial_dijkstra_array_graph.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Definition whole_graph sh g x := (@graph_rep_spatial mpred pointer_val (SDAG_VST sh) g x).

(* Spec:  *)
(* 	\exists mypath. path_ends g mypath src dst, *)
(* 		\forall path. path_ends g path src dest ->  *)
(* 			path_cost path <= past_cost mypath -> *)
(* 				mypath = path *)


Definition dijkstra_correct (g: Graph) p src dst : Prop :=
    path_ends g p src dst ->
    forall p', path_ends g p' src dst ->
               Nat.lt (path_cost g p') (path_cost g p) ->
               p = p'.
         
Definition dijkstra_spec :=
  DECLARE _dijkstra
  WITH sh: wshare, g: Graph, arr: pointer_val,
       dist: pointer_val, prev: pointer_val,
       i: Z, src: Z, dst: Z
  PRE []
    PROP ()
    LOCAL () (* temp _pq (pointer_val_val arr); temp _i (Vint (Int.repr i))) *)
    SEP (whole_graph sh g arr)
  POST [tvoid]
      EX p : (@path VType EType),
      PROP (dijkstra_correct g p src dst)
      LOCAL ()
      SEP (whole_graph sh g arr).

Definition Gprog : funspecs := ltac:(with_library prog [dijkstra_spec]).

Lemma body_find: semax_body Vprog Gprog f_dijkstra dijkstra_spec.
Proof.
  start_function.
  forward.
  forward_for_simple_bound 8 
    (EX i: Z,
    PROP  ()
    LOCAL (lvar _pq (tptr (Tstruct _Node noattr)) v_pq)
    SEP (data_at Tsh (tptr (Tstruct _Node noattr)) (Vint (Int.repr 0)) v_pq;
         whole_graph sh g arr)).
  - entailer!.
    Abort.