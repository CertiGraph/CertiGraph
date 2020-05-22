Require Import Coq.ZArith.ZArith.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Equivalence_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.FiniteGraph.
Require Import RamifyCoq.kruskal.undirected_graph.

Context {V E: Type} {EV: EqDec V eq} {EE: EqDec E eq}.
Context {DV DE DG: Type}.
Local Open Scope Z_scope.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).

(*Too many coercions running around?*)
Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

(*
  TBH I'm not 100% sure I fixed this in the 
  best possible way. Here's how I proceeded:

  1. You were using a context for many fields but then
     implicitly asserting that LE = Z when it was 
     convenient. I understand that impulse, but I 
     think a better approach is to leave it unspecified
     and create holes for the use to fill. See 
     DEint, DEadd, DEcomp below, and see how I used them
     on the client side.
     At first, those three lines were all that I added.

  2. I thought that making this edit would be enough, 
     but the client was still getting confused between
     its own VType, EType, etc. and the MST context's 
     V, E, etc. So then came back and explicitly 
     edited ```Definition minimum_spanning_forest```
     to look like you see it now. 
     i.e., I got it personally work for all V, E, etc. 

  3. Then there was the exact some confusion between 
     ```Definition minimum_spanning_forest```'s parameter
     values and ```sum_DE```'s context values, and so on. 
     That's why I ended up making all three
     Definitions take paramters, as you see them now.
 *)

Definition DEList
           {V E}
           {EV: EqDec V eq} {EE: EqDec E eq}
           {DV DE DG}
           (g: LabeledGraph V E DV DE DG)
           {fg: FiniteGraph g} : list DE :=
  map (elabel g) (EList g).

Definition sum_DE
           {V E}
           {EV: EqDec V eq} {EE: EqDec E eq}
           {DV DE DG}
           (g: LabeledGraph V E DV DE DG)
           (DEadd: DE -> DE -> DE)
           (DEinit : DE)
           {fg: FiniteGraph g} : DE :=
  fold_left DEadd (DEList g) DEinit.

Definition minimum_spanning_forest
           {V E EV EE DV DE DG}
           (g t : LabeledGraph V E DV DE DG)
           (DEadd: DE -> DE -> DE)
           (DEinit : DE)
           (DEComp : DE -> DE -> Prop)
           {fg: FiniteGraph g}
           {ft: FiniteGraph t} :=
  @spanning_uforest V E EV EE g t /\
  forall (t': LabeledGraph V E DV DE DG) {ft': FiniteGraph t'},
    @spanning_uforest V E EV EE g t' ->
    DEComp (sum_DE t DEadd DEinit) (sum_DE t' DEadd DEinit).
