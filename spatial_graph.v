Require Import msl.msl_direct.
Require Import overlapping.
Require Import heap_model.
Require Import graph.
Require Import msl_ext.

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
    (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r) /\ valid x) && trinode x d l r ⊗ (Q l) ⊗ (Q r)).

  Lemma graph_fun_covariant : covariant graph_fun.
  Proof.
    unfold graph_fun. apply covariant_orp.
    apply covariant_const.
    apply covariant_exp; intro d.
    apply covariant_exp; intro l.
    apply covariant_exp; intro r.
    repeat apply covariant_ocon.
    apply covariant_andp. apply covariant_const.
    repeat apply covariant_sepcon; apply covariant_const.
    apply covariant_const'. apply covariant_const'.
  Qed.

  Definition graph := corec graph_fun.

  Lemma graph_unfold:
    forall x,
      graph x = (!!(x = 0) && emp) ||
                (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r) /\ valid x) && trinode x d l r ⊗
                                                 (graph l) ⊗ (graph r)).
  Proof.
    intros. unfold graph at 1. rewrite corec_fold_unfold. trivial. apply graph_fun_covariant.
  Qed.

  Definition dag_fun (Q: adr -> pred world) (x: adr) :=
    (!!(x = 0) && emp) ||
    (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r) /\ valid x) && trinode x d l r * ((Q l) ⊗ (Q r))).

  Lemma dag_fun_covariant : covariant dag_fun.
  Proof.
    unfold dag_fun.
    apply covariant_orp. apply covariant_const.
    apply covariant_exp. intro d. apply covariant_exp. intro l. apply covariant_exp. intro r.
    apply covariant_sepcon. apply covariant_const.
    apply covariant_ocon; apply covariant_const'. 
  Qed.

  Definition dag := corec dag_fun.

  Lemma dag_unfold:
    forall x,
      dag x = (!!(x = 0) && emp) ||
              (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r) /\ valid x) && trinode x d l r * ((dag l) ⊗ (dag r))).
  Proof.
    intros. unfold dag at 1. rewrite corec_fold_unfold. trivial. apply dag_fun_covariant.
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
End SpatialGraph.
