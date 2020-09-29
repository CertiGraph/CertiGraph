Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zcomplements.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Znat.

Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.exportclight.Clightdefs.

Require Import VST.veric.expr.
Require Import VST.veric.mpred.
Require Import VST.floyd.forward.
Require Import VST.floyd.sublist.
Require Import VST.floyd.field_at.
Require Import VST.floyd.coqlib3.
Require Import VST.msl.iter_sepcon.
Require Import VST.msl.seplog.

Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.MathAdjMatGraph.

Section SpaceAdjMatGraph2.

  Context {size : Z}. 
  
  
  (* SPATIAL REPRESENTATION *)

  (* Assumption: (v,0), (v,1) ... (v, size-1) are edges.
   Action: makes a list containing each edge's elabel.
   The argument f is an opportunity to tweak the edges as needed
   *)  
  Definition vert_to_list (g: AdjMatLG) (f : E -> E) (v : V) :=
    map (elabel g)
        (map (fun x => f (v,x))
             (nat_inc_list (Z.to_nat size))).

  (* Assumptions: 
   1. 0, 1, ... (size-1) are vertices
   2. for any vertex v,
          (v,0), (v,1) ... (v, size-1) are edges.
          
      Action:
      Makes a list of lists, where each member list 
      is a vertex's edge-label-list (see helper above).
   *)
  Definition graph_to_mat (g: AdjMatLG) (f : E -> E) : list (list Z) :=
    map (vert_to_list g f)
        (nat_inc_list (Z.to_nat size)).

  Lemma graph_to_mat_Zlength:
    forall g (f : E -> E),
      0 <= size ->
      Zlength (graph_to_mat g f) = size.
  Proof.
    intros. unfold graph_to_mat.
    rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; trivial.
  Qed.

  Lemma elabel_Znth_graph_to_mat:
    forall (g: AdjMatLG) (f: E -> E) src dst,
      0 <= size ->
      0 <= src < size ->
      0 <= dst < size ->
      elabel g (f (src, dst)) =
      Znth dst (Znth src (graph_to_mat g f)).
  Proof.
    intros. 
    unfold graph_to_mat.
    rewrite Znth_map, nat_inc_list_i.
    unfold vert_to_list. rewrite Znth_map.
    rewrite Znth_map. rewrite nat_inc_list_i.
    reflexivity.
    3: rewrite Zlength_map.
    2, 3, 5: rewrite nat_inc_list_Zlength.
    all: rewrite Z2Nat.id; trivial.
  Qed.

  Definition concat {A: Type} (l: list (list A)) : list A :=
    fold_left (@List.app A) l (@nil A).

  Definition l := (1 :: 2 :: nil) :: (3 :: 4 :: nil) ::  nil.
  
  Definition graph_to_list (g: AdjMatLG) (f : E -> E) : list Z :=
    (concat (graph_to_mat g f)).

  Lemma graph_to_list_Zlength:
    forall g (f : E -> E),
      0 <= size ->
      Zlength (graph_to_list g f) = size * size.
  Proof.
  Admitted.

  Lemma graph_to_list_to_mat:
    forall g (f : E -> E) u i,
      0 <= u < size ->
      0 <= i < size ->
      Znth (u * size + i) (graph_to_list g id) =
      Znth i (Znth u (graph_to_mat g id)).
  Proof.
  Admitted.

  Definition SpaceAdjMatGraph sh (cs: compspecs) (f : E -> E) g gaddr : mpred :=
    data_at sh (tarray tint (size * size))
            (map Vint (map Int.repr (graph_to_list g id)))
            gaddr.

(*
  The below is not currently used by SpaceDijkGraph because 
  iter_sepcon is cleaner. However, just keep it around 
  because it is a general model.
  For a (better?) example of this in use for VST, see above.
 *)

(* 
  What it does:        
  Uses abstract_data_at to create a spatial representation.
 *)
  Class SpaceAdjMatGraph_abstract (Addr: Type) (Pred: Type) :=
    abstract_data_at: Addr -> list Z -> Pred.
  
  Context {Pred: Type}.
  Context {Addr: Type}.
  Context {SAMG : SpaceAdjMatGraph_abstract Addr Pred}.
  
  Definition AdjMatGraph_rep
             (g: AdjMatLG)
             (f : E -> E)
             (a : Addr) : Pred :=
    abstract_data_at a (@graph_to_list g f).
  
End SpaceAdjMatGraph2.
