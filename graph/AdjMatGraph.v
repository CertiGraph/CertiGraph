Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Classes.EquivDec.
Require Import Coq.ZArith.ZArith_dec.

Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.Coqlib.

(*
  AdjMat wishlist
  0. some distinguished inf value
  1. V: Z, E: Z, Elabel: Z
  2. forall e, elabel_inrange: e -> Pred
     customizably explains the upper and lower bounds
  3. forall e, elabel_lt_inf: e -> Pred
     elabel e < inf


  4. vert to list function

  5. graph to mat function --> elsewhere?
  6. proof that length of this is "size" --> elsewhere?

  7. graph to list function
  8. proof that length of this is "size"^2
  9. graph_rep (if you provide me with a list -> addr -> mpred function)
 *)

(* vvalid --> 0 <= v < size *)
(* strong_evalid *)
(* evalid --> 0 <= v < size *)

(* Most of the types are constrained because we want easy
   AdjMat representation. *)

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition AdjMatLG := (@LabeledGraph Z (Z*Z) _ _ unit Z unit).

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

(* eventually, this will return:
   if evalid e then (elabel e) else inf
 *)
Definition elabel_w_inf (g: AdjMatLG) (inf: Z) e :=
  elabel g e.

(* Assumption: (v,0), (v,1) ... (v, size-1) are valid edges.
   What it does: makes a list containing each edge's elabel.
 *)  
Definition vert_to_list (g: AdjMatLG) (size inf: Z) (v : Z) :=
  map (elabel_w_inf g inf)
      (map (fun x => (v,x))
           (nat_inc_list (Z.to_nat size))).

(* Assumptions: 
   1. 0, 1, ... (size-1) are valid vertices
   2. for any vertex v,
          (v,0), (v,1) ... (v, SIZE-1) are valid edges.

      What it does: 
      Makes a list of lists, where each member list 
      is a vertex's edge-label-list (see helper above).
 *)
Definition graph_to_mat_gen
           (g: AdjMatLG)
           (size inf : Z) : list (list Z) :=
  map
    (vert_to_list g size inf)
    (nat_inc_list (Z.to_nat size)).

Definition graph_to_list_gen
           (g: AdjMatLG)
           (size inf : Z) : list Z :=
  (concat (graph_to_mat_gen g size inf)).

Class SpaceAdjMatGraph (Addr: Type) (Pred: Type) :=
  abstract_data_at: Addr -> list Z -> Pred.

Context {Pred: Type}.
Context {Addr: Type}.
Context {SAMG : SpaceAdjMatGraph Addr Pred}.

(* 
Assumptions: 
See above

What it does: 
Uses abstract_data_at to create a spatial representation.

This is not currently used by SpaceDijkGraph because 
iter_sepcon is cleaner. However, just keep it around 
because it is a general model.

For a (better?) example of this in use for VST, see out
dijkstra/SpaceDijkGraph.v
 *)
Definition AdjMatGraph_rep
           (g: AdjMatLG)
           (size inf : Z) 
           (a : Addr) : Pred :=
  abstract_data_at a (graph_to_list_gen g size inf).
