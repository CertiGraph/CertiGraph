Require Import msl.msl_classical.
Require Import msl.corec.
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

  Lemma graph_precise_eq: (forall x, precise (graph x)) <-> (TT |-- ALL x : adr, !!(precise (graph x))).
  Proof.
    split; intros;
    [hnf; simpl; intros; apply H |
     hnf in H; simpl in H; apply H; auto; apply (0, (fun (x : var) => Some x, fun (y : adr) => Some y))].
  Qed.

  Lemma precise_exp_mapsto: forall x, precise (EX d : adr, mapsto x d).
  Proof.
    repeat intro. destruct H as [d1 [? [ax1 [? [ay1 [? [? ?]]]]]]], H0 as [d2 [? [ax2 [? [ay2 [? [? ?]]]]]]].
    destruct w1 as [n1 [r1 m1]], w2 as [n2 [r2 m2]]. simpl in *.
    destruct w as [n [r m]].
    destruct H1. destruct x0 as [nx [rx mx]].
    destruct H2. destruct x0 as [ny [ry my]].
    destruct H1 as [? [? ?]]. destruct H2 as [? [? ?]].
    simpl in *.
    destruct H1, H2.
    assert (n1 = n2) by intuition.
    destruct H11, H13.
    assert (r1 = r2) by (rewrite H11, H18, H13, H19; auto).
    rewrite H17 in *; rewrite H20 in *.
    rewrite H3 in H7; injection H7; intro; rewrite H21 in *.
    assert (m1 = m2). extensionality mm.
    specialize (H12 mm); specialize (H14 mm).
    destruct (eq_dec mm ax2). rewrite e in *. rewrite H6 in *. rewrite H10 in *.
    destruct (mx ax2); destruct(my ax2); destruct (m ax2).
    inversion H12; hnf in H25; exfalso; auto.
    inversion H12.
    inversion H12; hnf in H25; exfalso; auto.
    inversion H12.
    inversion H14; hnf in H25; exfalso; auto.
    inversion H12.
    inversion H12; inversion H14; auto.
    inversion H12.
    specialize (H5 mm n0); specialize (H9 mm n0); rewrite H5, H9; auto.
    repeat f_equal; trivial.
  Qed.
  
  Lemma graph_precise: forall x, precise (graph x).
  Proof.
    rewrite graph_precise_eq; apply loeb; rewrite later_allp; apply allp_derives; intro.
    intro; intros; simpl in *.
    rewrite graph_unfold.
    apply precise_orp.
    repeat intro; destruct H0 as [[? ?] [d [l [r [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]]]]]];
    destruct H5 as [x1 [x2 [x3 [x12 [x13 [? [? [? [[? ?] ?]]]]]]]]]; destruct H10 as [y1 [y2 [? [[y11 [y12 [? [? ?]]]] ?]]]];
    destruct H13; simpl in H0; rewrite H0 in H13; apply H13; auto.
    apply precise_exp.
    admit. intros.
    apply precise_exp.
    admit. intros.
    apply precise_exp.
    admit. intros.
    apply precise_ocon.
    apply precise_ocon.
    apply precise_andp_right.
    repeat apply precise_sepcon; apply precise_mapsto.
    admit.
    admit.
    apply precise_andp_right, precise_emp.
  Qed.

  Lemma graphs_precise: forall S, precise (graphs S).
  Proof. induction S; simpl; [apply precise_emp | apply precise_ocon; [apply graph_precise | trivial]]. Qed.
    
End SpatialGraph.
