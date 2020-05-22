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
