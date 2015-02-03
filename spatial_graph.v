Require Import msl.msl_direct.
Require Import overlapping.
Require Import heap_model.
Require Import graph.
Require Import graph_reachable.
Require Import msl_ext.
Require Import ramify_tactics.
Require Import NPeano.
Require Import List.
Require Import utilities.

Local Open Scope pred.

Instance natEqDec : EqDec nat := { t_eq_dec := eq_nat_dec }.

Definition trinode x d l r := !!(3 | x) && ((mapsto x d) * (mapsto (x+1) l) * (mapsto (x+2) r)).

Module SpatialGraph.

  Definition graph_cell (bi : @BiGraph adr nat natEqDec) (v : adr) : pred world :=
    let (dl, r) := gamma bi v in let (d, l) := dl in trinode v d l r.

  Lemma precise_graph_cell: forall bi v, precise (graph_cell bi v).
  Proof.
    intros. unfold graph_cell. destruct (gamma bi v) as [dl r]. destruct dl as [d l]. unfold trinode. apply precise_andp_right.
    apply precise_sepcon. apply precise_mapsto. apply precise_sepcon. apply precise_mapsto. apply precise_mapsto.
  Qed.

  Lemma graph_cell_sepcon_unique: forall bi, sepcon_unique (graph_cell bi).
  Proof.
    repeat intro. unfold graph_cell in *. destruct (gamma bi x) as [dl r]. destruct dl as [d l]. unfold trinode in *.
    destruct_sepcon H w. destruct H0, H1. destruct_sepcon H2 w1. destruct_sepcon H3 w2. try_join w12 w2 w122.
    try_join w12 w22 w1222. assert ((mapsto (x+2) r * mapsto (x+2) r)%pred w1222) by (exists w22, w12; split; auto).
    apply mapsto_unique in H12. auto.
  Qed.

  Definition graph (x : adr) (bimg : @BiMathGraph adr nat 0 natEqDec): pred world :=
    (!!(x = 0) && emp) || EX l : list adr, !!reachable_list b_pg x l && iter_sepcon l (graph_cell bm_bi).

  Lemma graph_unfold:
    forall x bimg,
      graph x bimg = (!!(x = 0) && emp) || EX d:adr, EX l:adr, EX r:adr, !!(gamma bm_bi x = (d, l, r) /\ valid x) &&
                                                                           (trinode x d l r ⊗ graph l bimg ⊗ graph r bimg).
  Proof.
    intros; apply pred_ext; intro w; intros. unfold graph in H. destruct H. left; auto. right. destruct H as [li [[? ?] ?]].
    destruct (gamma bm_bi x) as [[d l] r] eqn: ?. exists d, l, r. split. split; auto. unfold gamma in Heqp.
    destruct (biEdge bm_bi x) as [v1 v2] eqn: ?. inversion Heqp. subst. clear Heqp. unfold biEdge in Heqp0.
    destruct (only_two_neighbours x) as [v1 [v2 ?]]. inversion Heqp0. subst. clear Heqp0. assert (reachable_list b_pg x li).
    split; auto. rewrite <- pg_the_same in H2. assert (In l (edge_func x)). rewrite e. apply in_eq. assert (In r (edge_func x)).
    rewrite e. apply in_cons. apply in_eq. rewrite <- pg_the_same in H, H3, H4. generalize (valid_graph x H l H3); intro.
    generalize (valid_graph x H r H4); intro. assert (reachable b_pg x x). apply reachable_by_reflexive. split.
    rewrite pg_the_same in H. auto. hnf; auto. rewrite <- H0 in H7. destruct H5, H6.

    admit.

    assert (reachable m_pg x r). exists (x :: r :: nil). split; split; simpl; auto. split; auto. split; auto. repeat intro.
    hnf. auto. destruct (compute_reachable bm_ma x li H2 r H8) as [listR ?].
    
    admit. admit. admit. admit.
    (* destruct H. unfold graph. left; auto. *)
    (* destruct H as [d [l [r [[? ?] ?]]]]. destruct_ocon H1 h. destruct_ocon H4 i. unfold graph in H9, H5. *)
    (* destruct H9; destruct H5. right. exists (x :: nil). split. split. trivial. intro. split; intros. *)
    (* apply in_inv in H10. destruct H10. subst. apply reachable_by_reflexive. split; auto. hnf; auto. inversion H10. admit. *)
    (* simpl. rewrite sepcon_comm, emp_sepcon. unfold graph_cell. rewrite H. admit. admit. admit. *)
    (* destruct H9 as [ll ?], H5 as [lr ?]. right. assert (NoDup (x :: ll ++ lr)) by admit. exists (x :: ll ++ lr). *)
    (* destruct H9, H5. split. split. trivial. intro y. destruct H9, H5. split; intro. apply in_inv in H15. destruct H15. *)
    (* subst. apply reachable_by_reflexive. split; auto. hnf; auto. apply in_app_or in H15. destruct H15. admit. admit. admit. *)
    (* admit. *)
  Qed.

End SpatialGraph.
