Require Import msl.msl_classical.
Require Import msl.corec.
Require Import overlapping.
Require Import heap_model.
Require Import graph.

Open Local Scope pred.

Instance natEqDec : EqDec nat := { t_eq_dec := eq_nat_dec }.

Definition graph_node x d l r :=
  (mapsto x d) * (mapsto (x+1) l) * (mapsto (x+2) r).

Section SpatialGraph.
  Variable VV : Valid nat.
  Variable pg : @PreGraph nat nat natEqDec VV.
  Variable bi : BiGraph pg.
  
  Definition graph_fun (Q: adr -> pred world) (x: adr) :=
    (!!(x = 0) && emp) ||
    (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r)) && graph_node x d l r ⊗ ((|> Q l) ⊗ (|> Q r))).

  Definition graph := HORec graph_fun.

End SpatialGraph.
