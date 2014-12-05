Require Import msl.msl_direct.
Require Import overlapping.
Require Import heap_model.
Require Import graph.
Require Import msl_ext.
Require Import ramify_tactics.
Require Import FunctionalExtensionality.
Require Import NPeano.
Require Import List.
Require Import Classical.

Local Open Scope pred.

Instance natEqDec : EqDec nat := { t_eq_dec := eq_nat_dec }.

Definition trinode x d l r :=
  (mapsto x d) * (mapsto (x+1) l) * (mapsto (x+2) r).

Section SpatialGraph.
  Variable VV : Valid nat.
  Definition GV : Valid nat := fun x => VV x /\ x <> 0.
  Variable pg : @PreGraph nat nat natEqDec GV.
  Variable bi : BiGraph pg.

  Definition nodesFrom (x : adr) : list adr := @edge_func adr adr natEqDec GV pg x.

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

  Fixpoint graphs (l : list adr) :=
    match l with
      | nil => emp
      | v :: l' => graph v ⊗ graphs l'
    end.

  Fixpoint dags (l : list adr) :=
    match l with
      | nil => emp
      | v :: l' => dag v ⊗ dags l'
    end.

  Lemma graph_path_in: forall p x y P, pg |= p is x ~o~> y satisfying P -> graph x |-- EX v : adr, (mapsto y v * TT).
  Proof.
    induction p; intros; destruct H as [[? ?] [? ?]].
    inversion H.
    simpl in H; inversion H; subst.
    destruct p. simpl in H0; inversion H0; subst. repeat intro.
    rewrite graph_unfold in H3. destruct H3. destruct H3. hnf in H3; destruct H1; intuition.
    destruct H3 as [d [l [r ?]]]. destruct_ocon H3 h. destruct_ocon H6 i.
    destruct H10. destruct_sepcon H12 j. destruct_sepcon H13 k. exists d.
    try_join k2 j2 m1; try_join m1 i3 m2; try_join m2 h3 m3. exists k1, m3; split; auto.

    assert (pg |= n :: p is n ~o~> y satisfying P).
    split; [split; [simpl; auto | auto] | split; [destruct H1; auto | repeat intro; apply H2; apply in_cons; auto]].

    repeat intro; hnf.
    rewrite graph_unfold in H4. destruct H4. destruct H4; hnf in H4; destruct H1; destruct H1; destruct H1; intuition.
    destruct H4 as [d [l [r ?]]].
    destruct_ocon H4 h. destruct_ocon H7 i. destruct H11 as [[? ?] ?].
    unfold gamma in H11.
    destruct_sepcon H14 j. destruct_sepcon H15 k. destruct H1 as [[? [? ?]] ?].
    revert H11. case_eq (biEdge bi x); intros.
    inversion H22; subst.
    generalize (biEdge_only2 bi _ _ _ _ H11 H20); intros.
    destruct H23; subst.
    specialize (IHp _ _ _ H3 _ H12). hnf in IHp. simpl in IHp.
    destruct IHp as [bb ?]. exists bb. apply join_sub_mapsto with i23; auto.
    try_join i2 i3 i23'; equate_join i23 i23'.
    assertSub i23 a S3; trivial.
    specialize (IHp _ _ _ H3 _ H8). hnf in IHp. simpl in IHp.
    destruct IHp as [bb ?]. exists bb. apply join_sub_mapsto with h23; auto.
    try_join h2 h3 h23'; equate_join h23 h23'.
    assertSub h23 a S1; trivial.
  Qed.

  Lemma graph_reachable_in: forall x y, reachable pg x y -> graph x |-- EX v : adr, (mapsto y v * TT).
  Proof. intros; destruct H; apply graph_path_in in H; trivial. Qed.

  Definition explode (x : adr) (w : world) (H : (graph x * TT)%pred w) :
    {l : adr & {r : adr | biEdge bi x = (l, r) /\ valid x /\ (graph l * TT)%pred w /\ (graph r * TT)%pred w}} + {x = 0}.
    destruct (eq_nat_dec x 0). right; auto. left.
    rewrite graph_unfold in H.
    assert (S : ((EX  d : adr,
                         (EX  l : adr,
                                  (EX  r : adr,
                                           !!(gamma bi x = (d, l, r) /\ valid x) && trinode x d l r
                                             ⊗ graph l ⊗ graph r))) * TT)%pred w).
    destruct_sepcon H h. hnf in H0. destruct H0. destruct H0. hnf in H0. exfalso; auto.
    exists h1, h2; split; auto. clear H. remember (gamma bi x). destruct p as [[d l] r]. exists l, r.
    destruct_sepcon S h. destruct H0 as [dd [ll [rr ?]]]. destruct_ocon H0 i. destruct_ocon H4 j.
    destruct H8 as [[? ?] ?]. injection H8; intros; subst; clear H8. unfold gamma in Heqp. destruct (biEdge bi x).
    injection Heqp; intros; subst; clear Heqp. repeat split; auto.
    try_join j2 j3 j23'. equate_join j23 j23'. try_join j1 i3 j1i3. try_join j1i3 h2 j1i3h2. exists j23, j1i3h2.
    repeat split; auto. try_join i2 i3 i23'; equate_join i23 i23'. try_join i1 h2 i1h2. exists i23, i1h2. repeat split; auto.
  Defined.
    
  Lemma graph_reachable_finite: forall x w, x <> 0 -> graph x w -> set_finite (reachable pg x).
  Proof.
    admit.
  Qed.

End SpatialGraph.
