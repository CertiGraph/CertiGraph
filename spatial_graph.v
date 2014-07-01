Require Import msl.msl_classical.
Require Import msl.corec.
Require Import overlapping.
Require Import heap_model.
Require Import graph.

Local Open Scope pred.

Instance natEqDec : EqDec nat := { t_eq_dec := eq_nat_dec }.

Definition trinode x d l r :=
  (mapsto x d) * (mapsto (x+1) l) * (mapsto (x+2) r).

Section SpatialGraph.
  Variable VV : Valid nat.
  Variable pg : @PreGraph nat nat natEqDec VV.
  Variable bi : BiGraph pg.
  
  Definition graph_fun (Q: adr -> pred world) (x: adr) :=
    (!!(x = 0) && emp) ||
    (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r)) && trinode x d l r ⊗ (|> Q l) ⊗ (|> Q r)).

  Lemma graph_fun_HOcontractive : HOcontractive graph_fun.
  Proof.
    apply prove_HOcontractive. intros.
    unfold graph_fun.
    apply subp_orp. apply subp_refl.
    apply subp_exp. intro d. apply subp_exp. intro l. apply subp_exp. intro r.
    apply subp_ocon. apply subp_ocon. apply subp_refl.
    apply eqp_subp; eapply allp_left; eauto.
    apply eqp_subp; eapply allp_left; eauto.
  Qed.

  Definition graph := HORec graph_fun.

  Lemma graph_unfold:
    forall x,
      graph x = (!!(x = 0) && emp) ||
                (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r)) && trinode x d l r ⊗
                                                 (|> graph l) ⊗ (|> graph r)).
  Proof.
    intros. unfold graph at 1. rewrite HORec_fold_unfold. trivial. apply graph_fun_HOcontractive.
  Qed.

  Definition dag_fun (Q: adr -> pred world) (x: adr) :=
    (!!(x = 0) && emp) ||
    (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r)) && trinode x d l r * ((|> Q l) ⊗ (|> Q r))).
                                                                                                        
  Lemma dag_fun_HOcontractive : HOcontractive dag_fun.
  Proof.
    apply prove_HOcontractive. intros.
    unfold dag_fun.
    apply subp_orp. apply subp_refl.
    apply subp_exp. intro d. apply subp_exp. intro l. apply subp_exp. intro r.
    apply subp_sepcon. apply subp_refl.
    apply subp_ocon; apply eqp_subp; eapply allp_left; eauto.
  Qed.

  Definition dag := HORec dag_fun.

  Lemma dag_unfold:
    forall x,
      dag x = (!!(x = 0) && emp) ||
              (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r)) && trinode x d l r * ((|> dag l) ⊗ (|> dag r))).
  Proof.
    intros. unfold dag at 1. rewrite HORec_fold_unfold. trivial. apply dag_fun_HOcontractive.
  Qed.

  (* Lemma dag_eq_graph: forall x, dag x |-- graph x && !!(graph_is_acyclic (reachable_subgraph pg (x :: nil))). *)
  (* Proof. *)
  (*   admit. *)
  (* Qed. *)

  Fixpoint graphs (l : list var) :=
    match l with
      | nil => emp
      | v :: l' => graph v ⊗ graphs l'
    end.

  Fixpoint dags (l : list var) :=
    match l with
      | nil => emp
      | v :: l' => dag v ⊗ dags l'
    end.

  Lemma graph_precise: forall x, precise (graph x).
  Proof.
    intros; admit.
  Qed.

  Lemma graphs_precise: forall S, precise (graphs S).
  Proof. induction S; simpl; [apply precise_emp | apply precise_ocon; [apply graph_precise | trivial]]. Qed.
    
End SpatialGraph.
