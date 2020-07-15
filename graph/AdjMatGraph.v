Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Classes.EquivDec.
Require Import Coq.ZArith.ZArith_dec.

Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.Coqlib.

(*
  AdjMat wishlist
  0. premised with some "size"
  1. V: Z, E: Z, Elabel: Z
  2. elabel_inrange: Z -> Pred
  3. it's "square"
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

Local Open Scope Z_scope.

(* Specific to Adjacency Matrix representations. *)
(*
 |  V  |    E    |    DV   |  DE |  DG  | soundness |
 |-----|---------|---------|-----|------|-----------| 
 |  Z  |  Z * Z  | list DE |  Z  | unit |  Finite   | 
 *)

Definition VType : Type := Z.
Definition EType : Type := Z * Z.
Definition LE : Type := Z.
Definition LV: Type := list Z.
Definition LG: Type := unit.

Instance V_EqDec: EqDec VType eq.
Proof. hnf. apply Z.eq_dec. Qed.

Instance E_EqDec: EqDec EType eq.
Proof.
  hnf. intros [x] [y].
  destruct (equiv_dec x y).
  - hnf in e. destruct (Z.eq_dec z z0); subst.
    + left; reflexivity.
    + right. intro. apply n. inversion H. reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).

(* Assumption: (v,0), (v,1) ... (v, size-1) are valid edges.
   What it does: makes a list containing each edge's elabel.
 *)  
Definition vert_to_list
           (g: LabeledGraph VType (VType * Z) LV LE LG)
           (size : Z)
           (v : VType) : list LE :=
  map (elabel g) (map (fun x => (v,x)) (nat_inc_list (Z.to_nat size))).


(* Assumptions: 
   1. 0, 1, ... (size-1) are valid vertices
   2. for any vertex v,
          (v,0), (v,1) ... (v, SIZE-1) are valid edges.

      What it does: 
      Makes a list of lists, where each member list 
      is a vertex's edge-label-list (see helper above).
 *)
Definition graph_to_mat_gen
           (g: LabeledGraph VType EType LV LE LG)
           (size : Z) : list (list LE) :=
  map (vert_to_list g size) (nat_inc_list (Z.to_nat size)).

Definition graph_to_list_gen
           (g: LabeledGraph VType EType LV LE LG)
           (size : Z) : list LE :=
  (concat (graph_to_mat_gen g size)).

Class SpaceAdjMatGraph (Addr: Type) (Pred: Type) :=
  abstract_data_at: Addr -> list LE -> Pred.

Context {Pred: Type}.
Context {Addr: Type}.
Context {SAMG : SpaceAdjMatGraph Addr Pred}.

(* Assumptions: 
   See above

   What it does: 
   Flattens the list of lists into one list, and then uses
    abstract_data_at to create a spatial representation.

   This is not currently used by SpaceDijkGraph because iter_sepcon 
   is cleaner. However, just keep it around because it is a general model.

   For a (better?) example of this in use for VST, see out
   dijkstra/SpaceDijkGraph.v
 *)
Definition AdjMatGraph_rep
           (g: LabeledGraph VType EType LV LE LG)
           (size : Z) 
           (a : Addr) : Pred :=
  abstract_data_at a (graph_to_list_gen g size).
