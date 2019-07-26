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


                                           
