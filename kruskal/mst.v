Require Import Coq.ZArith.ZArith.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Equivalence_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.FiniteGraph.
Load "./kruskal/undirected_graph.v".

Context {V E: Type} {EV: EqDec V eq} {EE: EqDec E eq}.
Context {DV DG: Type}.

Local Open Scope Z_scope.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).

(*Too many coercions running around?*)
Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

Definition DEList (g: LabeledGraph V E DV Z DG) {fg: FiniteGraph g} : list Z :=
  map (elabel g) (EList g).

Definition sum_DE (g: LabeledGraph V E DV Z DG) {fg: FiniteGraph g} : Z :=
  fold_left Z.add (DEList g) 0.

Definition MSF (g t: LabeledGraph V E DV Z DG) {fg: FiniteGraph g} {ft: FiniteGraph t}:=
  spanning_uforest g t /\ forall (t': LabeledGraph V E DV Z DG) {ft': FiniteGraph t'}, spanning_uforest g t' -> sum_DE t <= sum_DE t'.