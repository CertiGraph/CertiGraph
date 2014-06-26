Require Import msl.msl_classical.
Require Import msl.corec.
Require Import overlapping.
Require Import heap_model.
Require Import graph.

Local Open Scope pred.

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

  Lemma graph_fun_HOcontractive : HOcontractive graph_fun.
  Proof.
    apply prove_HOcontractive. intros.
    unfold graph_fun.
    apply subp_orp. apply subp_refl.
    apply subp_exp. intro d. apply subp_exp. intro l. apply subp_exp. intro r.
    apply subp_ocon. apply subp_refl.
    apply subp_ocon; apply eqp_subp; eapply allp_left; eauto.
  Qed.

  Lemma graph_unfold:
    forall x,
      graph x = (!!(x = 0) && emp) ||
                (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r)) && graph_node x d l r ⊗
                                                 ((|> graph l) ⊗ (|> graph r))).
  Proof.
    intros. unfold graph at 1. rewrite HORec_fold_unfold. trivial. apply graph_fun_HOcontractive.
  Qed.

End SpatialGraph.
