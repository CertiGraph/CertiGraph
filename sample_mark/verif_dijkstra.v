
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.sample_mark.dijkstra.
Require Import RamifyCoq.msl_application.DijkstraGraph.

Notation Graph := (@Graph pSGG_VST).


(* First, refer to spatial gc graph to figure out a spatial representation *)

(* Spec:  *)
(* 	\exists mypath. path_ends g mypath src dst, *)
(* 		\forall path. path_ends g path src dest ->  *)
(* 			path_cost path <= past_cost mypath -> *)
(* 				mypath = path *)


                                           
