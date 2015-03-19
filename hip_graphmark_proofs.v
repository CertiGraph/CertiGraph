Require Import msl.msl_direct.
Require Import overlapping.
Require Import heap_model.
Require Import graph.
Require Import graph_reachable.
Require Import spatial_graph.
Require Import hip_graphmark.
Require Import utilities.
Require Import Classical.
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
                       (@edge_func _ _ _ (b_pg_g g) x = l :: r :: nil \/ @edge_func _ _ _ (b_pg_g g) x = r :: l :: nil).
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
    left; auto. hnf in H8. destruct H8. auto. exfalso; auto. split; intro t; intros. simpl. unfold change_edge_func.
    destruct (t_eq_dec z x). destruct H7. subst. rewrite H7 in H8. auto. subst. rewrite H7 in H8. apply in_inv in H8.
    destruct H8. subst. apply in_cons, in_eq. apply in_inv in H; destruct H. subst. apply in_eq. inversion H. auto. simpl in H8.
    unfold change_edge_func in H8. destruct (t_eq_dec z x). subst. destruct H7. rewrite H. auto. rewrite H. apply in_inv in H8.
    destruct H8. subst. apply in_cons, in_eq. apply in_inv in H0; destruct H0. subst. apply in_eq. inversion H0. auto.
    split. auto. split. hnf. simpl. unfold change_node_label. destruct (@t_eq_dec adr natEqDec x x). auto. exfalso; auto.
    intros. simpl. unfold change_node_label. destruct (t_eq_dec n' x). exfalso; auto. auto. split.
    apply (mark_mark_mark1 _ _ _ _ (b_pg_g G) (b_pg_g G1) (b_pg_g G2) (b_pg_g G3) x l r). hnf; simpl. rewrite H. auto.
    split. do 2 (split; auto). destruct H7; rewrite H7. apply in_eq. apply in_cons, in_eq. split. do 2 (split; auto).
    destruct H7; rewrite H7. apply in_cons, in_eq. apply in_eq. intros. destruct H9 as [?[? ?]].
    destruct H7; rewrite H7 in H11; apply in_inv in H11; destruct H11. left; auto. apply in_inv in H11. destruct H11.
    right; auto. inversion H11. right; auto. apply in_inv in H11. destruct H11. left; auto. inversion H11. auto. apply H2.
    apply H3. destruct H8 as [? [? [? ?]]]. split. hnf in H10. assert (@node_label _ _ _ (b_pg_g G2) x = 1).
    destruct H2 as [? [? ?]]. specialize (H12 x). specialize (H13 x).
    LEM ((b_pg_g G1) |= l ~o~> x satisfying (unmarked nat (fun d : nat => d = 1))). specialize (H12 H14). hnf in H12.
    rewrite H12; auto. specialize (H13 H14). rewrite <- H13. apply H10. destruct H3 as [? [? ?]]. specialize (H13 x).
    specialize (H14 x). LEM ((b_pg_g G2) |= r ~o~> x satisfying (unmarked nat (fun d : nat => d = 1))). specialize (H13 H15).
    hnf in H13. auto. specialize (H14 H15). rewrite <- H14. apply H12. destruct H2 as [? _]. destruct H3 as [? _].
    assert ((b_pg_g G) ~=~ (b_pg_g G2)). apply (si_trans H8 H2). assert ((b_pg_g G) ~=~ (b_pg_g G3)). apply (si_trans H12 H3).
    hnf in H13. split. destruct (H13 x). rewrite <- H14; auto. split. destruct (H13 l). rewrite <- H14; auto. split.
    destruct (H13 r). rewrite <- H14; auto. specialize (H13 x). destruct H13.
    destruct H7; rewrite H7 in H14; destruct H14; hnf in H14, H15;
    destruct (@only_two_neighbours _ _ _ (bm_bi_g G3) x) as [v1 [v2 ?]]; unfold b_pg_g in *; unfold bm_bi_g in *;
    rewrite e in *; clear e. assert (In l (l :: r :: nil)). apply in_eq. assert (In r (l :: r :: nil)). apply in_cons, in_eq.
    generalize (H14 l H16); intro. apply in_inv in H18. destruct H18. subst. left. specialize (H14 r H17).
    destruct (eq_nat_dec v2 r). subst; auto. assert (In v2 (l :: v2 :: nil)) by apply in_cons, in_eq. specialize (H15 v2 H).
    clear H16 H17. apply in_inv in H14. apply in_inv in H15. destruct H14, H15; exfalso. rewrite H14 in H15. auto.
    apply in_inv in H15. destruct H15. auto. inversion H15. apply in_inv in H14. destruct H14. auto. inversion H14.
    apply in_inv in H14. destruct H14. auto. inversion H14. apply in_inv in H18. destruct H18. right. subst.
    specialize (H14 r H17). destruct (eq_nat_dec v1 r). subst; auto. assert (In v1 (v1 :: l :: nil)) by apply in_eq.
    specialize (H15 v1 H). clear H16 H17 H. exfalso. apply in_inv in H14. destruct H14. auto. apply in_inv in H.
    apply in_inv in H15. destruct H, H15. subst. auto. apply in_inv in H14. destruct H14. auto. inversion H14. inversion H.
    inversion H. inversion H18. assert (In l (r :: l :: nil)). apply in_cons, in_eq. assert (In r (r :: l :: nil)). apply in_eq.
    generalize (H14 l H16); intro. apply in_inv in H18. destruct H18. subst. left. specialize (H14 r H17).
    destruct (eq_nat_dec v2 r). subst; auto. assert (In v2 (l :: v2 :: nil)) by apply in_cons, in_eq. specialize (H15 v2 H).
    clear H16 H17 H. exfalso. apply in_inv in H15. destruct H15. auto. apply in_inv in H. apply in_inv in H14. destruct H, H14.
    subst. auto. apply in_inv in H14. destruct H14; [auto | inversion H14]. inversion H. inversion H. apply in_inv in H18.
    destruct H18. subst. right. specialize (H14 r H17). assert (In v1 (v1 :: l :: nil)). apply in_eq. specialize (H15 v1 H).
    clear H16 H17 H. destruct (eq_nat_dec v1 r). subst; auto. exfalso. apply in_inv in H14. destruct H14. auto.
    apply in_inv in H15. destruct H15. auto. apply in_inv in H. apply in_inv in H14. destruct H, H14. subst; auto.
    inversion H14. inversion H. inversion H14. inversion H18.
  Qed.
  Lemma axiom_7 : forall v G x G1 y v1 l r, valid (imp (and (mark G x G1) (lookup G y v l r)) (and (subset_reach G x G1) (and (eq_notreach G x G1) (lookup G1 y v1 l r)))).
  Proof. admit. Qed.
  
  Lemma axiom_8 : forall l r x G, valid (imp (lookup G x 1 l r) (mark G x G)).
  Proof. admit. Qed.
  
  Lemma axiom_9 : forall G, valid (mark G null_node G).
  Proof. admit. Qed.
  
  Lemma lem_subgraphupdate_l : forall G v G1 x v1 l r, valid (imp (and (star (graph l G1) (mwand (graph l G) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (subset_reach G l G1) (and (eq_notreach G l G1) (and (lookup G x v l r) (lookup G1 x v1 l r))))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Proof. admit. Qed.
  
  Lemma lem_subgraphupdate_r : forall G v G1 x v1 l r, valid (imp (and (star (graph r G1) (mwand (graph r G) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (subset_reach G r G1) (and (eq_notreach G r G1) (and (lookup G x v l r) (lookup G1 x v1 l r))))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Proof. admit. Qed.
  
  Lemma lem_pttoupdate : forall v G x v1 l r G1, valid (imp (and (star (ptto_node x v1 l r) (mwand (ptto_node x v l r) (union (ptto_node x v l r) (union (graph l G) (graph r G))))) (and (lookup G x v l r) (update G x v1 l r G1))) (union (ptto_node x v1 l r) (union (graph l G1) (graph r G1)))).
  Proof. admit. Qed.
    
End GraphMark.
