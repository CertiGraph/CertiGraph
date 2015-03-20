Require Import msl.msl_direct.
Require Import overlapping.
Require Import heap_model.
Require Import graph.
Require Import graph_reachable.
Require Import spatial_graph.
Require Import hip_graphmark.
Require Import utilities.
Require Import ramification.
Require Import Classical.
Require Import ramify_tactics.
Tactic Notation "LEM" constr(v) := (destruct (classic v); auto).


Module GraphMark <: Mgraphmark.
  Definition formula : Type := pred world.
  Definition valid : formula -> Prop := fun f => forall w, f w.
  Definition node : Type := adr.
  Definition null_node : node := 0.
  Definition ptto_node : node -> nat -> node -> node -> formula := trinode.
  Definition A : Type := @BiMathGraph adr nat 0 natEqDec.
  Definition graph : node -> A -> formula := spatial_graph.graph.
  Definition star : formula -> formula -> formula := sepcon.
  Definition and : formula -> formula -> formula := andp.
  Definition imp : formula -> formula -> formula := imp.
  Definition not : formula -> formula := fun f w => ~ f w.
  Definition eq : node -> node -> formula := fun a b w => a = b.
  Definition mwand : formula -> formula -> formula := ewand.
  Definition union : formula -> formula -> formula := ocon.
  Definition neq : nat -> nat -> formula := fun a b w => ~ a = b.
  Definition mark : A -> node -> A -> formula :=
    fun g1 n g2 w => mark adr nat natEqDec (fun d => d = 1) (b_pg_g g1) n (b_pg_g g2).
  Definition eq_notreach : A -> node -> A -> formula :=
    fun g1 n g2 w => (unreachable_subgraph (b_pg_g g1) (n :: nil)) -=- (unreachable_subgraph (b_pg_g g2) (n :: nil)).
  Definition subset_reach : A -> node -> A -> formula :=
    fun g1 n g2 w => subset (reachable (b_pg_g g1) n) (reachable (b_pg_g g2) n).
  Definition lookup : A -> node -> nat -> node -> node -> formula :=
    fun g x d l r w => @node_label _ _ _ (b_pg_g g) x = d /\ @graph.valid _ _ _ (b_pg_g g) x /\
                       @graph.valid _ _ _ (b_pg_g g) l /\ @graph.valid _ _ _ (b_pg_g g) r /\
                       @edge_func _ _ _ (b_pg_g g) x = l :: r :: nil.
  Definition update : A -> node -> nat -> node -> node -> A -> formula :=
    fun g1 x d l r g2 w => exists (Hn : x <> 0) (Hi : in_math (bm_ma_g g1) x l r), update_graph g1 x d l r Hi Hn = g2.

  Lemma axiom_1 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G r G1) (and (neq v 1) (and (mark G2 l G3) (update G1 x 1 l r G2))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Proof. admit. Qed.

  Lemma axiom_2 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G l G1) (and (neq v 1) (and (mark G2 r G3) (update G1 x 1 l r G2))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Proof. admit. Qed.

  Lemma axiom_3 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G r G1) (and (neq v 1) (and (mark G1 l G2) (update G2 x 1 l r G3))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Proof. admit. Qed.

  Lemma axiom_4 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (mark G l G1) (and (neq v 1) (and (mark G1 r G2) (update G2 x 1 l r G3))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Proof. admit. Qed.

  Lemma axiom_5 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (update G x 1 l r G1) (and (neq v 1) (and (mark G1 r G2) (mark G2 l G3))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Proof. admit. Qed.

  Lemma axiom_6 : forall v G1 G2 G G3 x l r, valid (imp (and (lookup G x v l r) (and (update G x 1 l r G1) (and (neq v 1) (and (mark G1 l G2) (mark G2 r G3))))) (and (mark G x G3) (lookup G3 x 1 l r))).
  Proof.
    intros; intro w; hnf; unfold and; hnf; intros. destruct H as [? [? [? [? ?]]]]. destruct H as [? [? [? [? ?]]]]. hnf in H1.
    assert (mark1 adr nat natEqDec (fun d : nat => d = 1) (b_pg_g G) x (b_pg_g G1)). destruct H0 as [Hi [Hn ?]].
    rewrite <- H0. split. intro z. split. destruct (t_eq_dec z x); split; intro. hnf. left; auto. hnf in H8. subst. auto.
    left; auto. hnf in H8. destruct H8. auto. exfalso; auto. simpl. unfold change_edge_func. destruct (t_eq_dec z x).
    subst. rewrite H7. auto. auto. split. auto. split. hnf. simpl. unfold change_node_label.
    destruct (@t_eq_dec adr natEqDec x x). auto. exfalso; auto. intros. simpl. unfold change_node_label.
    destruct (t_eq_dec n' x). exfalso; auto. auto. split.
    apply (mark_mark_mark1 _ _ _ _ (b_pg_g G) (b_pg_g G1) (b_pg_g G2) (b_pg_g G3) x l r). hnf; simpl. rewrite H. auto.
    split. do 2 (split; auto). rewrite H7. apply in_eq. split. do 2 (split; auto). rewrite H7. apply in_cons, in_eq.
    intros. destruct H9 as [?[? ?]]. rewrite H7 in H11. apply in_inv in H11; destruct H11. left; auto. apply in_inv in H11.
    destruct H11. right; auto. inversion H11. auto. apply H2. apply H3.

    destruct H8 as [? [? [? ?]]]. split. hnf in H10. assert (@node_label _ _ _ (b_pg_g G2) x = 1). destruct H2 as [? [? ?]].
    specialize (H12 x). specialize (H13 x). LEM ((b_pg_g G1) |= l ~o~> x satisfying (unmarked nat (fun d : nat => d = 1))).
    specialize (H12 H14). hnf in H12. rewrite H12; auto. specialize (H13 H14). rewrite <- H13. apply H10.
    destruct H3 as [? [? ?]]. specialize (H13 x). specialize (H14 x).
    LEM ((b_pg_g G2) |= r ~o~> x satisfying (unmarked nat (fun d : nat => d = 1))). specialize (H13 H15). hnf in H13. auto.
    specialize (H14 H15). rewrite <- H14. apply H12. destruct H2 as [? _]. destruct H3 as [? _].
    assert ((b_pg_g G) ~=~ (b_pg_g G2)). apply (si_trans H8 H2). assert ((b_pg_g G) ~=~ (b_pg_g G3)). apply (si_trans H12 H3).
    hnf in H13. split. destruct (H13 x). rewrite <- H14; auto. split. destruct (H13 l). rewrite <- H14; auto. split.
    destruct (H13 r). rewrite <- H14; auto. specialize (H13 x). destruct H13. rewrite <- H14. auto.
  Qed.

  Lemma axiom_7 : forall v G x G1 y v1 l r, valid (imp (and (mark G x G1) (lookup G y v l r)) (and (subset_reach G x G1) (and (eq_notreach G x G1) (lookup G1 y v1 l r)))).
  Proof.
    intros. intro w. unfold and. hnf. intros. destruct H. unfold mark in H. split. unfold subset_reach.
    apply mark_reachable with (marked := fun d => d = 1). auto. split. unfold eq_notreach. split. intro t. generalize H; intro.
    destruct H1 as [? _]. specialize (H1 t). destruct H1. simpl. unfold unreachable_valid. split; intro; destruct H3; split.
    rewrite <- H1. apply H3.

    admit.

    rewrite H1. apply H3. unfold reachable_through_set in *. intro; apply H4; clear H4. destruct H5 as [s [? ?]]. exists s.
    split; auto. apply mark_reachable in H. specialize (H t). apply in_inv in H4. destruct H4. subst. apply H. auto.
    inversion H4.

    admit.

    admit.

  Qed.

  Lemma axiom_8 : forall l r x G, valid (imp (lookup G x 1 l r) (mark G x G)).
  Proof.
    intros. intro. hnf. intros. destruct H as [?[? [? [? ?]]]]. split. apply si_refl. split; intros. hnf. unfold unmarked in H4.
    destruct H4 as [p [[? ?] [? ?]]]. unfold path_prop in H7. specialize (H7 x). assert (In x p). destruct p. simpl in H4.
    inversion H4. simpl in H4. inversion H4. subst. apply in_eq. specialize (H7 H8). hnf in H7. exfalso; auto. auto.
  Qed.

  Lemma axiom_9 : forall G, valid (mark G null_node G).
  Proof.
    intros. intro w. unfold null_node. split; clear w. apply si_refl. split; intros. hnf. unfold unmarked in H.
    destruct H as [p [[? ?] [? ?]]]. destruct p. inversion H. simpl in H. inversion H. subst. simpl in H1. destruct p.
    unfold b_pg_g in H1. rewrite <- pg_the_same in H1. apply valid_not_null in H1. exfalso; auto. destruct H1 as [[? _] _].
    unfold b_pg_g in H1. rewrite <- pg_the_same in H1. apply valid_not_null in H1. exfalso; auto. auto.
  Qed.

  Lemma lookup_graph_unfold: forall G v x l r w,
                               lookup G x v l r w -> (graph x G = trinode x v l r ⊗ graph l G ⊗ graph r G)%pred.
  Proof.
    intros. destruct H as [? [? [? [? ?]]]]. clear w. apply pred_ext; intro w; intro. rewrite graph_unfold in H4.
    destruct H4 as [[? ?] | [dd [ll [rr [[? ?] ?]]]]]. hnf in H4. unfold b_pg_g in H0. rewrite <- pg_the_same in H0.
    apply valid_not_null in H0. exfalso; auto. unfold gamma in H4. unfold biEdge in H4.
    destruct (@only_two_neighbours adr nat natEqDec (@bm_bi adr nat O natEqDec G) x) as [v1 [v2 ?]] in H4. unfold b_pg_g in H3.
    rewrite H3 in e. inversion e. subst. inversion H4. subst. apply H6. rewrite graph_unfold. right. exists v, l, r. split.
    split. unfold gamma, biEdge. destruct (@only_two_neighbours adr nat natEqDec (@bm_bi adr nat O natEqDec G)x) as [v1 [v2 ?]].
    unfold b_pg_g in H3. rewrite H3 in e. inversion e. subst. auto. auto. auto.
  Qed.

  Lemma graph_graphs_eq_l:
    forall G v x l r w, lookup G x v l r w ->
                        (trinode x v l r ⊗ (graph l G ⊗ graph r G) = graph l G ⊗ graphs (x :: l :: r :: nil) G)%pred.
  Proof.
    intros. apply lookup_graph_unfold in H. rewrite <- ocon_assoc. unfold graphs. rewrite ocon_emp. do 2 rewrite <- ocon_assoc.
    rewrite (ocon_comm (graph l G) (graph x G)). rewrite (ocon_assoc (graph x G) (graph l G) (graph l G)).
    rewrite ocon_precise_elim. rewrite (ocon_assoc (graph x G) (graph l G) (graph r G)). rewrite H.
    rewrite (ocon_assoc (trinode x v l r) (graph l G) (graph r G)).
    rewrite (ocon_assoc (trinode x v l r) (graph l G ⊗ graph r G) (graph l G ⊗ graph r G)). rewrite ocon_precise_elim. auto.
    apply precise_ocon; apply precise_graph. apply precise_graph.
  Qed.

  Lemma lem_subgraphupdate_l : forall G v G1 x v1 l r, valid (imp (and (star (graph l G1) (mwand (graph l G) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (subset_reach G l G1) (and (eq_notreach G l G1) (and (lookup G x v l r) (lookup G1 x v1 l r))))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Proof.
    intros. intro w; hnf. unfold and, star, union, mwand, subset_reach, eq_notreach, ptto_node. intros.
    destruct H as [? [? [? [? ?]]]].
    assert (subset (reachable_through_set (b_pg_g G) (l :: nil)) (reachable_through_set (b_pg_g G1) (l :: nil))).
    unfold reachable_through_set. intro n; intros. destruct H4 as [s [? ?]]; exists s. split; auto. apply in_inv in H4.
    destruct H4. subst. apply H0; auto. inversion H4. clear H0.
    generalize (subgraph_update_ewand G G1 (l :: nil) (l :: nil) (x :: l :: r :: nil) H4 H1). intro.
    unfold graphs in H0 at 1 2 3 5. do 2 rewrite ocon_emp in H0. apply graph_graphs_eq_l in H2. rewrite H2 in H.
    specialize (H0 w H).  apply graph_graphs_eq_l in H3. rewrite H3. auto.
  Qed.

  Lemma graph_graphs_eq_r:
    forall G v x l r w, lookup G x v l r w ->
                        (trinode x v l r ⊗ (graph l G ⊗ graph r G) = graph r G ⊗ graphs (x :: l :: r :: nil) G)%pred.
  Proof.
    intros. apply lookup_graph_unfold in H. rewrite <- ocon_assoc. unfold graphs. rewrite ocon_emp. do 2 rewrite <- ocon_assoc.
    rewrite (ocon_comm (graph r G) (graph x G)). rewrite H. rewrite (ocon_assoc (trinode x v l r ⊗ graph l G)).
    rewrite ocon_precise_elim. rewrite (ocon_assoc (trinode x v l r)) at 2.
    rewrite (ocon_assoc (trinode x v l r ⊗ (graph l G ⊗ graph r G))).
    rewrite (ocon_assoc (trinode x v l r) (graph l G ⊗ graph r G) (graph l G ⊗ graph r G)). rewrite ocon_precise_elim.
    rewrite ocon_assoc. auto. apply precise_ocon; apply precise_graph. apply precise_graph.
  Qed.

  Lemma lem_subgraphupdate_r : forall G v G1 x v1 l r, valid (imp (and (star (graph r G1) (mwand (graph r G) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (subset_reach G r G1) (and (eq_notreach G r G1) (and (lookup G x v l r) (lookup G1 x v1 l r))))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Proof.
    intros. intro w; hnf. unfold and, star, union, mwand, subset_reach, eq_notreach, ptto_node. intros.
    destruct H as [? [? [? [? ?]]]].
    assert (subset (reachable_through_set (b_pg_g G) (r :: nil)) (reachable_through_set (b_pg_g G1) (r :: nil))).
    unfold reachable_through_set. intro n; intros. destruct H4 as [s [? ?]]; exists s. split; auto. apply in_inv in H4.
    destruct H4. subst. apply H0; auto. inversion H4. clear H0.
    generalize (subgraph_update_ewand G G1 (r :: nil) (r :: nil) (x :: l :: r :: nil) H4 H1). intro.
    unfold graphs in H0 at 1 2 3 5. do 2 rewrite ocon_emp in H0. apply graph_graphs_eq_r in H2. rewrite H2 in H.
    specialize (H0 w H).  apply graph_graphs_eq_r in H3. rewrite H3. auto.
  Qed.

  Lemma lem_pttoupdate : forall v G x v1 l r G1, valid (imp (and (star (ptto_node x v1 l r) (mwand (ptto_node x v l r) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (lookup G x v l r) (update G x v1 l r G1))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Proof.
    intros. intro w; hnf. unfold and, star, union, mwand, subset_reach, eq_notreach, ptto_node. intros.
    destruct H as [? [? ?]]. generalize (lookup_graph_unfold _ _ _ _ _ _ H0); intro. destruct H1 as [Hn [Hi ?]].
    apply eq_sym in H1. rewrite ocon_assoc in H2. rewrite <- H2 in H. destruct H0 as [? [? [? [? ?]]]].
    assert (@gamma adr nat natEqDec (@bm_bi adr nat O natEqDec G) x = (v, l, r)). unfold gamma, biEdge.
    destruct (@only_two_neighbours adr nat natEqDec (@bm_bi adr nat O natEqDec G) x) as [t1 [t2 ?]]. unfold b_pg_g in H6.
    rewrite H6 in e. inversion e; subst. auto. generalize (single_graph_node_update_2_ewand G x v l r v1 G1 Hn Hi H7 H1 w H).
    intro. assert (lookup G1 x v1 l r w). subst. split; simpl. unfold change_node_label. destruct (@t_eq_dec adr natEqDec x x).
    auto. exfalso; auto. unfold change_valid. do 3 (split;auto). unfold change_edge_func. destruct (@t_eq_dec adr natEqDec x x).
    auto. exfalso; auto. apply lookup_graph_unfold in H9. rewrite <- ocon_assoc. rewrite <- H9. apply H8.
  Qed.

End GraphMark.
