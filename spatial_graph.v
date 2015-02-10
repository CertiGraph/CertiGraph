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
Require Import Permutation.

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

  Lemma graph_cell_trinode: forall {g: BiGraph adr nat} x m1 m2 w,
                              edge_func x = m1 :: m2 :: nil -> graph_cell g x w -> trinode x (node_label x) m1 m2 w.
  Proof.
    intros. unfold graph_cell in H0. destruct (gamma g x) as [[dd ll] rr] eqn:? . unfold gamma in Heqp.
    unfold biEdge in Heqp. destruct (only_two_neighbours x) as [v1 [v2 ?]]. rewrite H in e. inversion e. subst.
    inversion Heqp; subst. auto.
  Qed.

  Definition graph (x : adr) (bimg : @BiMathGraph adr nat 0 natEqDec): pred world :=
    (!!(x = 0) && emp) || EX l : list adr, !!reachable_list b_pg x l && iter_sepcon l (graph_cell bm_bi).

  Lemma graph_unfold:
    forall x bimg,
      graph x bimg = (!!(x = 0) && emp) || EX d:adr, EX l:adr, EX r:adr, !!(gamma bm_bi x = (d, l, r) /\ valid x) &&
                                                                           (trinode x d l r ⊗ graph l bimg ⊗ graph r bimg).
  Proof.
    intros; apply pred_ext; intro w; intros. unfold graph in H. destruct H. left; auto. right. destruct H as [li [[? ?] ?]].
    destruct (gamma bm_bi x) as [[d l] r] eqn: ?. exists d, l, r. split. split; auto. assert (NoDup li) as Hn1.
    generalize (graph_cell_sepcon_unique bm_bi). intro. apply (iter_sepcon_unique_nodup H2 H1). unfold gamma in Heqp.
    destruct (biEdge bm_bi x) as [v1 v2] eqn: ?. inversion Heqp. subst. clear Heqp. unfold biEdge in Heqp0.
    destruct (only_two_neighbours x) as [v1 [v2 ?]]. inversion Heqp0. subst. clear Heqp0. assert (reachable_list b_pg x li).
    split; auto. rewrite <- pg_the_same in H2. assert (In l (edge_func x)). rewrite e. apply in_eq. assert (In r (edge_func x)).
    rewrite e. apply in_cons. apply in_eq. rewrite <- pg_the_same in H, H3, H4. generalize (valid_graph x H l H3); intro.
    generalize (valid_graph x H r H4); intro. assert (reachable b_pg x x). apply reachable_by_reflexive. split.
    rewrite pg_the_same in H. auto. hnf; auto. rewrite <- H0 in H7. destruct H5, H6.

    (* Both are 0 *)
    subst. assert (li = x :: nil). apply (reachable_all_zero bm_ma). split; auto. rewrite pg_the_same. apply H0. auto.
    rewrite Forall_forall. intro y; intros. rewrite pg_the_same in H5. rewrite e in H5. apply in_inv in H5. destruct H5; auto.
    apply in_inv in H5; destruct H5; auto. inversion H5. rewrite H5 in H1. simpl in H1. clear H3 H4 H5.
    rewrite sepcon_emp in H1. rewrite <- (ocon_emp (graph_cell bm_bi x)) in H1.
    rewrite <- (ocon_emp (graph_cell bm_bi x ⊗ emp)) in H1. destruct_ocon H1 w. exists w1, w2, w3, w12, w23. do 3 (split; auto).
    split. destruct_ocon H5 q. exists q1, q2, q3, q12, q23. do 3 (split; auto). split. apply graph_cell_trinode; auto.
    left; split; auto. left; split; auto.

    (* Left is zero *)
    subst. clear H3. assert (forall y, In y li -> x = y \/ reachable b_pg r y). intros.
    rewrite H0 in H3. apply (reachable_from_children b_pg) in H3. destruct H3 as [? | [z [[? [? ?]] ?]]]; [left | right]. auto.
    rewrite e in H8. apply in_inv in H8. destruct H8. rewrite <- pg_the_same in H5. apply valid_not_null in H5.
    exfalso; intuition. apply in_inv in H8. destruct H8. subst. auto. inversion H8. assert (reachable m_pg x r).
    exists (x :: r :: nil). split; split; simpl; auto. split; auto. split; auto. repeat intro. hnf. auto.
    destruct (compute_reachable bm_ma x li H2 r H5) as [listR [? Hn2]]. destruct H8.
    assert (forall y : adr, In y li -> x = y \/ In y listR). intros. apply H3 in H10. destruct H10; [left | right]; auto.
    rewrite <- pg_the_same in H10. rewrite H9; auto. destruct (in_dec t_eq_dec x listR). assert (li ~= listR).
    split; repeat intro. apply H10 in H11. destruct H11. subst; auto. auto. apply H9 in H11. assert (reachable b_pg x a).
    rewrite <- pg_the_same. apply reachable_by_cons with r. split; auto. hnf; auto. apply H11. rewrite <- H0 in H12. auto.
    assert (Permutation li listR). apply (eq_as_set_permutation t_eq_dec); auto.
    apply iter_sepcon_the_same with (p := graph_cell bm_bi) in H12. assert (iter_sepcon listR (graph_cell bm_bi) w).
    rewrite <- H12; auto. clear H12. apply in_split in i. destruct i as [ll1 [ll2 ?]]. generalize H13; intro.
    rewrite H12 in H14. rewrite iter_sepcon_app_comm in H14. rewrite <- app_comm_cons in H14. simpl in H14.
    destruct_sepcon H14 w. exists (core w1), w1, w2, w1, w. split. apply core_unit. do 2 (split; auto). split.
    apply sepcon_ocon. exists w1, (core w1). split. apply join_comm. apply core_unit. split. apply graph_cell_trinode; auto.
    left. split. auto. apply core_identity. right. exists listR. split. rewrite <- pg_the_same. split; auto. auto.
    assert (NoDup (x :: listR)). apply NoDup_cons; auto. assert (li ~= (x :: listR)). split; intro y; intros.
    specialize (H10 y H12). destruct H10. subst. apply in_eq. apply in_cons. auto. apply in_inv in H12. destruct H12. subst.
    auto. rewrite (H9 y) in H12. assert (reachable b_pg x y). rewrite <- pg_the_same. apply reachable_by_merge with r. apply H5.
    apply H12. rewrite <- H0 in H13. auto. assert (Permutation li (x :: listR)). apply (eq_as_set_permutation t_eq_dec); auto.
    apply iter_sepcon_the_same with (p := graph_cell bm_bi) in H13. assert (iter_sepcon (x :: listR) (graph_cell bm_bi) w).
    rewrite <- H13; auto. clear H13. simpl in H14. destruct_sepcon H14 w. apply sepcon_ocon. exists w1, w2. split; auto.
    split. apply sepcon_ocon. exists w1, (core w1). split. apply join_comm, core_unit. split. apply graph_cell_trinode; auto.
    left; split. auto. apply core_identity. right. exists listR. split. rewrite <- pg_the_same. split; auto. auto.

    (* Right is zero *)
    subst. clear H4. assert (forall y, In y li -> x = y \/ reachable b_pg l y). intros. rewrite H0 in H4.
    apply (reachable_from_children b_pg) in H4. destruct H4 as [? | [z [[? [? ?]] ?]]]; [left | right]. auto. rewrite e in H8.
    apply in_inv in H8. destruct H8. subst; auto. apply in_inv in H8; destruct H8. subst. rewrite <- pg_the_same in H6.
    apply valid_not_null in H6. exfalso; intuition. inversion H8. assert (reachable m_pg x l). exists (x :: l :: nil).
    split; split; simpl; auto. split; auto. split; auto. repeat intro. hnf. auto.
    destruct (compute_reachable bm_ma x li H2 l H6) as [listL [? Hn2]]. destruct H8.
    assert (forall y : adr, In y li -> x = y \/ In y listL). intros. apply H4 in H10. destruct H10; [left | right]; auto.
    rewrite <- pg_the_same in H10. rewrite H9; auto. destruct (in_dec t_eq_dec x listL). assert (li ~= listL).
    split; repeat intro. apply H10 in H11. destruct H11. subst; auto. auto. apply H9 in H11. assert (reachable b_pg x a).
    rewrite <- pg_the_same. apply reachable_by_cons with l. split; auto. hnf; auto. apply H11. rewrite <- H0 in H12. auto.
    assert (Permutation li listL). apply (eq_as_set_permutation t_eq_dec); auto.
    apply iter_sepcon_the_same with (p := graph_cell bm_bi) in H12. assert (iter_sepcon listL (graph_cell bm_bi) w).
    rewrite <- H12; auto. clear H12. apply in_split in i. destruct i as [ll1 [ll2 ?]]. generalize H13; intro.
    rewrite H12 in H14. rewrite iter_sepcon_app_comm in H14. rewrite <- app_comm_cons in H14. simpl in H14.
    destruct_sepcon H14 w. apply sepcon_ocon. exists w, (core w). split. apply join_comm, core_unit. split.
    exists (core w1), w1, w2, w1, w. split. apply core_unit. do 2 (split; auto). split. apply graph_cell_trinode; auto.
    right. exists listL. split. rewrite <- pg_the_same. split; auto. auto. left; split; auto. apply core_identity.
    assert (NoDup (x :: listL)). apply NoDup_cons; auto. assert (li ~= (x :: listL)). split; intro y; intros.
    specialize (H10 y H12). destruct H10. subst. apply in_eq. apply in_cons. auto. apply in_inv in H12. destruct H12. subst.
    auto. rewrite (H9 y) in H12. assert (reachable b_pg x y). rewrite <- pg_the_same. apply reachable_by_merge with l. apply H6.
    apply H12. rewrite <- H0 in H13. auto. assert (Permutation li (x :: listL)). apply (eq_as_set_permutation t_eq_dec); auto.
    apply iter_sepcon_the_same with (p := graph_cell bm_bi) in H13. assert (iter_sepcon (x :: listL) (graph_cell bm_bi) w).
    rewrite <- H13; auto. clear H13. simpl in H14. destruct_sepcon H14 w. apply sepcon_ocon. exists w, (core w). split.
    apply join_comm, core_unit. split. apply sepcon_ocon. exists w1, w2. split; auto. split. apply graph_cell_trinode; auto.
    right. exists listL. split. rewrite <- pg_the_same. split; auto. auto. left; split. auto. apply core_identity.

    (* Both are valid *)
    assert (forall y, In y li -> x = y \/ reachable b_pg l y \/ reachable b_pg r y). intros. rewrite H0 in H8.
    apply (reachable_from_children b_pg) in H8. destruct H8 as [? | [z [[? [? ?]] ?]]]; [left | right]. auto. rewrite e in H10.
    apply in_inv in H10. destruct H10. subst; left; auto. apply in_inv in H10; destruct H10. subst; right; auto. inversion H10.
    assert (reachable m_pg x l). exists (x :: l :: nil). split; split; simpl; auto. split; auto. split; auto. repeat intro. hnf.
    auto. assert (reachable m_pg x r). exists (x :: r :: nil). split; split; simpl; auto. split; auto. split; auto.
    repeat intro. hnf. auto. destruct (compute_reachable bm_ma x li H2 l H9) as [listL [? Hn2]]. destruct H11.
    destruct (compute_reachable bm_ma x li H2 r H10) as [listR [? Hn3]]. destruct H13.
    assert (forall y : adr, In y li -> x = y \/ In y listL \/ In y listR). intros. apply H8 in H15.
    destruct H15 as [? | [? | ?]]; [left | right; left | right; right ]; auto. rewrite H12. rewrite pg_the_same; auto.
    rewrite H14; rewrite pg_the_same; auto. destruct (in_dec t_eq_dec x listL).

    (* In x listL *)
    assert (li ~= (listL ++ listR)). split; intro y; intros. specialize (H15 y H16). apply in_or_app.
    destruct H15 as [? | [? | ?]]; [left | left | right]; auto. subst; auto. apply in_app_or in H16. destruct H16.
    rewrite H12 in H16. rewrite H0. rewrite <- pg_the_same. apply reachable_by_merge with l; auto.
    rewrite H14 in H16. rewrite H0. rewrite <- pg_the_same. apply reachable_by_merge with r; auto.
    destruct (tri_list_split t_eq_dec Hn1 Hn2 Hn3 H16) as [li1 [li2 [li3 [? [? ?]]]]].
    rewrite (iter_sepcon_the_same _ _ (graph_cell bm_bi) H19) in H1. do 2 rewrite iter_sepcon_app_sepcon in H1.
    destruct_sepcon H1 w. destruct_sepcon H21 w. rename w2 into w23. rename w0 into w2. try_join w1 w2 w12.
    exists w1, w2, w3, w12, w23. do 3 (split; auto). split. assert (iter_sepcon listL (graph_cell bm_bi) w12).
    rewrite (iter_sepcon_the_same _ _ (graph_cell bm_bi) H17). rewrite iter_sepcon_app_sepcon. exists w1, w2. split; auto.
    generalize H26; intro. apply in_split in i. destruct i as [ll1 [ll2 ?]]. rewrite H28 in H26.
    generalize (Permutation_middle ll1 ll2 x); intro. rewrite <- (iter_sepcon_the_same _ _ (graph_cell bm_bi) H29) in H26.
    clear H29. simpl in H26. destruct_sepcon H26 h. exists (core h1), h1, h2, h1, w12. split. apply core_unit.
    do 2 (split; auto). split. apply graph_cell_trinode; auto. right. exists listL. split; auto. rewrite <- pg_the_same.
    split; auto. right; exists listR; split. rewrite <- pg_the_same; split; auto.
    rewrite (iter_sepcon_the_same _ _ (graph_cell bm_bi) H18). rewrite iter_sepcon_app_sepcon. exists w2, w3. split; auto.

    (* ~ In x listL *)
    assert (NoDup (x :: listL)). apply NoDup_cons; auto. assert (li ~= ((x :: listL) ++ listR)). split; intro y; intros.
    specialize (H15 y H17). apply in_or_app. destruct H15 as [? | [? | ?]]. subst. left; apply in_eq. left; apply in_cons; auto.
    right; auto. apply in_app_or in H17. destruct H17. apply in_inv in H17. destruct H17. rewrite <- H17 in *. clear H17 y.
    rewrite H0. apply reachable_by_reflexive. rewrite <- pg_the_same. split. auto. hnf; auto. rewrite H12 in H17. rewrite H0.
    rewrite <- pg_the_same; apply reachable_by_merge with l; auto. rewrite H14 in H17. rewrite H0. rewrite <- pg_the_same.
    apply reachable_by_merge with r; auto. destruct (tri_list_split t_eq_dec Hn1 H16 Hn3 H17) as [li1 [li2 [li3 [? [? ?]]]]].
    rewrite (iter_sepcon_the_same _ _ (graph_cell bm_bi) H20) in H1. do 2 rewrite iter_sepcon_app_sepcon in H1.
    destruct_sepcon H1 w. destruct_sepcon H22 w. rename w2 into w23. rename w0 into w2. try_join w1 w2 w12.
    exists w1, w2, w3, w12, w23. do 3 (split; auto). split. assert (iter_sepcon (x :: listL) (graph_cell bm_bi) w12).
    rewrite (iter_sepcon_the_same _ _ (graph_cell bm_bi) H18). rewrite iter_sepcon_app_sepcon. exists w1, w2. split; auto.
    simpl in H27. destruct_sepcon H27 h. apply sepcon_ocon. exists h1, h2. split; auto. split. apply graph_cell_trinode; auto.
    right. exists listL. split; auto. rewrite <- pg_the_same. split; auto. right; exists listR; split. rewrite <- pg_the_same.
    split; auto. rewrite (iter_sepcon_the_same _ _ (graph_cell bm_bi) H19). rewrite iter_sepcon_app_sepcon. exists w2, w3.
    split; auto.

    (* <- direction *)
    
    destruct H. left; auto. destruct H as [d [l [r [[? ?] ?]]]]. destruct_ocon H1 h. destruct_ocon H4 i. unfold graph in H9, H5.
    destruct H9; destruct H5. right. exists (x :: nil). unfold gamma in H. destruct (biEdge bm_bi x) as [v1 v2] eqn:? .
    unfold biEdge in Heqp. inversion H. subst. destruct (only_two_neighbours x) as [v1 [v2 ?]]. inversion Heqp. subst.
    clear Heqp. destruct H9, H5. hnf in H9, H5. subst. clear H. split. split. trivial. intro. split; intros.
    apply in_inv in H. destruct H. subst. apply reachable_by_reflexive. split; auto. hnf; auto. inversion H.
    apply (reachable_from_children b_pg) in H. destruct H. subst; apply in_eq. destruct H as [z [[? [? ?]] ?]]. rewrite e in H9.
    rewrite <- pg_the_same in H5. apply valid_not_null in H5. exfalso. apply in_inv in H9; destruct H9. intuition.
    apply in_inv in H9; destruct H9. intuition. inversion H9. simpl.
    admit. admit. admit.
    (* simpl. rewrite sepcon_comm, emp_sepcon. unfold graph_cell. rewrite H. admit. admit. admit. *)
    (* destruct H9 as [ll ?], H5 as [lr ?]. right. assert (NoDup (x :: ll ++ lr)) by admit. exists (x :: ll ++ lr). *)
    (* destruct H9, H5. split. split. trivial. intro y. destruct H9, H5. split; intro. apply in_inv in H15. destruct H15. *)
    (* subst. apply reachable_by_reflexive. split; auto. hnf; auto. apply in_app_or in H15. destruct H15. admit. admit. admit. *)
    admit.
  Qed.

End SpatialGraph.
