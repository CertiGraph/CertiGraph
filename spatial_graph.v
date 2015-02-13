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

Section SpatialGraph.

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

  Lemma trinode_graph_cell: forall {g: BiGraph adr nat} m1 m2 x w,
                              @edge_func adr nat _ _ x = m1 :: m2 :: nil -> trinode x (node_label x) m1 m2 w ->
                              graph_cell g x w.
  Proof.
    intros. unfold graph_cell. destruct (gamma g x) as [[dd ll] rr] eqn:? . unfold gamma in Heqp. unfold biEdge in Heqp.
    destruct (only_two_neighbours x) as [v1 [v2 ?]]. inversion Heqp. subst. rewrite H in e. inversion e. subst. auto.
  Qed.

  Lemma joinable_mapsto:
    forall w x y a b, x <> y -> (mapsto x a * TT)%pred w -> (mapsto y b * TT)%pred w -> (mapsto x a * mapsto y b * TT)%pred w.
  Proof.
    intros. destruct H0 as [p [q [? [? ?]]]]. generalize H2; intro Hmap1. destruct p as [fp xp] eqn:? .
    destruct H1 as [m [n [? [? ?]]]]. generalize H4; intro Hmap2. destruct m as [fm xm] eqn:? .  hnf in H2. simpl in H2.
    hnf in H4. simpl in H4. destruct H2 as [? [? ?]]. destruct H4 as [? [? ?]].
    remember (fun xx : adr => if eq_nat_dec xx x then Some a else (if eq_nat_dec xx y then Some b else None)) as f.
    assert (finMap f). exists (x :: y :: nil). intro z. intros. rewrite Heqf. destruct (eq_nat_dec z x). rewrite e in *.
    exfalso. apply H10. apply in_eq. destruct (eq_nat_dec z y). rewrite e in *. exfalso. apply H10. apply in_cons. apply in_eq.
    trivial. remember (exist (finMap (B:=adr)) f H10) as ff. assert (join p m ff). rewrite Heqw0, Heqw1, Heqff.
    hnf; simpl. intro z. destruct (eq_nat_dec z x). rewrite e in *. rewrite H7. generalize (H8 x H); intro HS. rewrite HS.
    rewrite Heqf. destruct (eq_nat_dec x x). apply lower_None2. exfalso; auto. destruct (eq_nat_dec z y). rewrite e in *.
    rewrite H9. generalize (H6 y n0); intro HS. rewrite HS. rewrite Heqf. destruct (eq_nat_dec y x). intuition.
    destruct (eq_nat_dec y y). apply lower_None1. intuition. specialize (H6 z n0). specialize (H8 z n1). rewrite H6, H8.
    rewrite Heqf. destruct (eq_nat_dec z x). intuition. destruct (eq_nat_dec z y). intuition. apply lower_None1.
    rewrite <- Heqw0 in *. rewrite <- Heqw1 in *. destruct (join_together H0 H1 H11) as [qn ?]. exists ff, qn.
    repeat split; auto. exists p, m. split; auto.
  Qed.

  Definition emapsto (x : adr) : pred world := EX v : nat, mapsto x v.

  Lemma precise_emapsto: forall x, precise (emapsto x).
  Proof.
    repeat intro. destruct H1 as [w3 ?], H2 as [w4 ?]. destruct H as [? [? [? ?]]], H0 as [? [? [? ?]]]. destruct w1 as [v1 f1].
    destruct w2 as [v2 f2]. destruct w3 as [v3 f3]. destruct w4 as [v4 f4]. destruct w as [v f]. hnf in H1, H2. simpl in *.
    apply exist_ext. extensionality mm; destruct (eq_dec mm x). subst. specialize (H1 x). specialize (H2 x). rewrite H4 in *.
    rewrite H6 in *. inversion H1. subst. inversion H2. rewrite H10, H12. auto. subst. rewrite <- H8 in H2.
    rewrite <- H11 in H2. hnf in H2. inversion H2. subst. inversion H15. subst. rewrite <- H8 in H1. rewrite <- H9 in H1.
    hnf in H1. inversion H1. subst. inversion H13. specialize (H3 mm n). specialize (H5 mm n). rewrite H3, H5. auto.
  Qed.

  Lemma joinable_emapsto: forall w, joinable emapsto w.
  Proof.
    repeat intro. unfold emapsto in * |-. destruct_sepcon H0 p. destruct H2 as [v1 ?]. destruct_sepcon H1 q.
    destruct H4 as [v2 ?]. assert ((mapsto x v1 * TT)%pred w). exists p1, p2; split; auto. assert ((mapsto y v2 * TT)%pred w).
    exists q1, q2. split; auto. assert ((mapsto x v1 * mapsto y v2 * TT)%pred w). apply joinable_mapsto; auto.
    destruct_sepcon H8 h. rename h1 into h1h2; rename h2 into h3. destruct_sepcon H9 h. exists h1h2, h3. do 2 (split; auto).
    exists h1, h2. split; auto. split. exists v1; auto. exists v2; auto.
  Qed.

  Lemma emapsto_mapsto: forall x y w, mapsto x y w -> emapsto x w. Proof. intros. exists y; auto. Qed.

  Ltac assert_emapsto x := match goal with | [H: mapsto x ?b ?w |- _] => generalize (emapsto_mapsto x b w H); intro end.

  Lemma joinable_graph_cell: forall bg w, joinable (graph_cell bg) w.
  Proof.
    repeat intro. destruct_sepcon H0 p. destruct_sepcon H1 q. unfold graph_cell in *. destruct (gamma bg x) as [[dx lx] rx].
    destruct (gamma bg y) as [[dy ly] ry]. unfold trinode in *. destruct H2, H4. unfold prop in H2, H4. destruct_sepcon H6 h.
    rename h1 into h12. rename h2 into h3. destruct_sepcon H8 h. destruct_sepcon H7 i. rename i1 into i12. rename i2 into i3.
    destruct_sepcon H12 i. try_join i2 i3 i23. destruct H4 as [yd ?]. destruct H2 as [xd ?]. generalize (joinable_emapsto w).
    intro. assert (forall t, precise (emapsto t)). apply precise_emapsto.
    assert (iter_sepcon (y :: y + 1 :: y + 2 :: nil) emapsto q1). simpl. exists i1, i23. split; auto. split. exists dy; auto.
    exists i2, i3. split; auto. split. exists ly; auto. exists i3, (core i3). split. apply join_comm, core_unit. split.
    exists ry; auto. apply core_identity. remember (y :: y + 1 :: y + 2 :: nil) as l3.
    assert ((iter_sepcon (x + 2 :: l3) emapsto * TT)%pred w). apply iter_sepcon_joinable; auto. rewrite Heql3. simpl. intro.
    destruct H21 as [? | [? | [ ? | ?]]]. omega. omega. apply H. rewrite (plus_comm y) in H21. rewrite (plus_comm x) in H21.
    apply plus_reg_l in H21. auto. auto. assertSub h3 p1 HS1. assertSub p1 w HS2. assertSub h3 w HS3. destruct HS3 as [ht ?].
    exists h3, ht. do 2 (split; auto). exists rx; auto. assertSub q1 w HS. destruct HS as [ht ?]. exists q1, ht.
    do 2 (split; auto). remember (x + 2 :: l3) as l4. assert ((iter_sepcon (x + 1 :: l4) emapsto * TT)%pred w).
    apply iter_sepcon_joinable; auto. rewrite Heql4, Heql3. simpl; intro. destruct H22 as [? | [? | [? | [? | ?]]]]; try omega.
    apply H. rewrite (plus_comm y) in H22. rewrite (plus_comm x) in H22. apply plus_reg_l in H22. auto. assertSub h2 p1 HS1.
    assertSub p1 w HS2. assertSub h2 w HS3. destruct HS3 as [ht ?]. exists h2, ht. do 2 (split; auto). exists lx; auto.
    remember (x + 1 :: l4) as l5. assert ((iter_sepcon (x :: l5) emapsto * TT)%pred w). apply iter_sepcon_joinable; auto.
    rewrite Heql5, Heql4, Heql3. simpl; intro. destruct H23 as [?|[?|[?|[?|[?|?]]]]]; try omega. intuition. assertSub h1 p1 HS1.
    assertSub p1 w HS2. assertSub h1 w HS3. destruct HS3 as [ht ?]. exists h1, ht. do 2 (split; auto). exists dx; auto.
    rewrite Heql3, Heql4, Heql5 in *. clear Heql3 Heql4 Heql5 l3 l4 l5 H21 H22.
    assert (x :: x + 1 :: x + 2 :: y :: y + 1 :: y + 2 :: nil = (x :: x + 1 :: x + 2 :: nil) ++ (y :: y + 1 :: y + 2 :: nil)).
    intuition. rewrite H21 in H23. clear H21. rewrite iter_sepcon_app_sepcon in H23. try_join h2 h3 h23.
    assert (iter_sepcon (x :: x + 1 :: x + 2 :: nil) emapsto p1). simpl. exists h1, h23. split; auto. split. exists dx; auto.
    exists h2, h3. split; auto. split. exists lx; auto. exists h3, (core h3). split. apply join_comm, core_unit. split.
    exists rx; auto. apply core_identity. destruct_sepcon H23 w. rename w1 into w12; rename w2 into w3. destruct_sepcon H25 w.
    assertSub w1 w HS1. assertSub p1 w HS2. assert (precise (iter_sepcon (x :: x + 1 :: x + 2 :: nil) emapsto)).
    apply precise_iter_sepcon; auto. equate_precise_through (iter_sepcon (x :: x + 1 :: x + 2 :: nil) emapsto) p1 w1.
    assertSub w2 w HS1. assertSub q1 w HS2. assert (precise (iter_sepcon (y :: y + 1 :: y + 2 :: nil) emapsto)).
    apply precise_iter_sepcon; auto. equate_precise_through (iter_sepcon (y :: y + 1 :: y + 2 :: nil) emapsto) q1 w2.
    clear H29 H27. exists w12, w3. do 2 (split; auto). exists p1, q1. split; auto. split; split. exists xd; auto.
    rewrite sepcon_assoc. simpl in H24. rewrite sepcon_emp in H24. destruct_sepcon H24 j. assert_emapsto x.
    assertSub j1 p1 HS1. assertSub h1 p1 HS2. assert (precise (emapsto x)). apply H19. equate_precise_through (emapsto x) h1 j1.
    exists h1, j2. do 2 (split; auto). clear H29 H30. rename j2 into j23. destruct_sepcon H28 j. rename j2 into j3.
    rename j1 into j2. assert_emapsto (x + 1). assertSub j2 p1 HS1. assertSub h2 p1 HS2. assert (precise (emapsto (x + 1))).
    apply H19. equate_precise_through (emapsto (x + 1)) h2 j2. exists h2, j3. do 2 (split; auto). clear H30 H31.
    assert_emapsto (x + 2). assertSub j3 p1 HS1. assertSub h3 p1 HS2. assert (precise (emapsto (x + 2))). apply H19.
    equate_precise_through (emapsto (x + 2)) h3 j3. auto. exists yd; auto. clear H21 H22 H24. rewrite sepcon_assoc.
    simpl in H20. rewrite sepcon_emp in H20. destruct_sepcon H20 j. assert_emapsto y. assertSub j1 q1 HS1. assertSub i1 q1 HS2.
    assert (precise (emapsto y)). apply H19. equate_precise_through (emapsto y) i1 j1. exists i1, j2. do 2 (split; auto).
    clear H24 H27 h23 H26. rename j2 into j23. destruct_sepcon H22 j. rename j2 into j3; rename j1 into j2.
    assert_emapsto (y + 1). assertSub j2 q1 HS1. assertSub i2 q1 HS2. assert (precise (emapsto (y + 1))). apply H19.
    equate_precise_through (emapsto (y + 1)) i2 j2. exists i2, j3. do 2 (split; auto). clear H26 H27. assert_emapsto (y + 2).
    assertSub j3 q1 HS1. assertSub i3 q1 HS2. assert (precise (emapsto (y + 2))). apply H19.
    equate_precise_through (emapsto (y + 2)) i3 j3. auto.
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
    apply iter_sepcon_permutation with (p := graph_cell bm_bi) in H12. assert (iter_sepcon listR (graph_cell bm_bi) w).
    rewrite <- H12; auto. clear H12. apply in_split in i. destruct i as [ll1 [ll2 ?]]. generalize H13; intro.
    rewrite H12 in H14. rewrite iter_sepcon_app_comm in H14. rewrite <- app_comm_cons in H14. simpl in H14.
    destruct_sepcon H14 w. exists (core w1), w1, w2, w1, w. split. apply core_unit. do 2 (split; auto). split.
    apply sepcon_ocon. exists w1, (core w1). split. apply join_comm. apply core_unit. split. apply graph_cell_trinode; auto.
    left. split. auto. apply core_identity. right. exists listR. split. rewrite <- pg_the_same. split; auto. auto.
    assert (NoDup (x :: listR)). apply NoDup_cons; auto. assert (li ~= (x :: listR)). split; intro y; intros.
    specialize (H10 y H12). destruct H10. subst. apply in_eq. apply in_cons. auto. apply in_inv in H12. destruct H12. subst.
    auto. rewrite (H9 y) in H12. assert (reachable b_pg x y). rewrite <- pg_the_same. apply reachable_by_merge with r. apply H5.
    apply H12. rewrite <- H0 in H13. auto. assert (Permutation li (x :: listR)). apply (eq_as_set_permutation t_eq_dec); auto.
    apply iter_sepcon_permutation with (p := graph_cell bm_bi) in H13. assert (iter_sepcon (x :: listR) (graph_cell bm_bi) w).
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
    apply iter_sepcon_permutation with (p := graph_cell bm_bi) in H12. assert (iter_sepcon listL (graph_cell bm_bi) w).
    rewrite <- H12; auto. clear H12. apply in_split in i. destruct i as [ll1 [ll2 ?]]. generalize H13; intro.
    rewrite H12 in H14. rewrite iter_sepcon_app_comm in H14. rewrite <- app_comm_cons in H14. simpl in H14.
    destruct_sepcon H14 w. apply sepcon_ocon. exists w, (core w). split. apply join_comm, core_unit. split.
    exists (core w1), w1, w2, w1, w. split. apply core_unit. do 2 (split; auto). split. apply graph_cell_trinode; auto.
    right. exists listL. split. rewrite <- pg_the_same. split; auto. auto. left; split; auto. apply core_identity.
    assert (NoDup (x :: listL)). apply NoDup_cons; auto. assert (li ~= (x :: listL)). split; intro y; intros.
    specialize (H10 y H12). destruct H10. subst. apply in_eq. apply in_cons. auto. apply in_inv in H12. destruct H12. subst.
    auto. rewrite (H9 y) in H12. assert (reachable b_pg x y). rewrite <- pg_the_same. apply reachable_by_merge with l. apply H6.
    apply H12. rewrite <- H0 in H13. auto. assert (Permutation li (x :: listL)). apply (eq_as_set_permutation t_eq_dec); auto.
    apply iter_sepcon_permutation with (p := graph_cell bm_bi) in H13. assert (iter_sepcon (x :: listL) (graph_cell bm_bi) w).
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
    rewrite (iter_sepcon_permutation _ _ (graph_cell bm_bi) H19) in H1. do 2 rewrite iter_sepcon_app_sepcon in H1.
    destruct_sepcon H1 w. destruct_sepcon H21 w. rename w2 into w23. rename w0 into w2. try_join w1 w2 w12.
    exists w1, w2, w3, w12, w23. do 3 (split; auto). split. assert (iter_sepcon listL (graph_cell bm_bi) w12).
    rewrite (iter_sepcon_permutation _ _ (graph_cell bm_bi) H17). rewrite iter_sepcon_app_sepcon. exists w1, w2. split; auto.
    generalize H26; intro. apply in_split in i. destruct i as [ll1 [ll2 ?]]. rewrite H28 in H26.
    generalize (Permutation_middle ll1 ll2 x); intro. rewrite <- (iter_sepcon_permutation _ _ (graph_cell bm_bi) H29) in H26.
    clear H29. simpl in H26. destruct_sepcon H26 h. exists (core h1), h1, h2, h1, w12. split. apply core_unit.
    do 2 (split; auto). split. apply graph_cell_trinode; auto. right. exists listL. split; auto. rewrite <- pg_the_same.
    split; auto. right; exists listR; split. rewrite <- pg_the_same; split; auto.
    rewrite (iter_sepcon_permutation _ _ (graph_cell bm_bi) H18). rewrite iter_sepcon_app_sepcon. exists w2, w3. split; auto.

    (* ~ In x listL *)
    assert (NoDup (x :: listL)). apply NoDup_cons; auto. assert (li ~= ((x :: listL) ++ listR)). split; intro y; intros.
    specialize (H15 y H17). apply in_or_app. destruct H15 as [? | [? | ?]]. subst. left; apply in_eq. left; apply in_cons; auto.
    right; auto. apply in_app_or in H17. destruct H17. apply in_inv in H17. destruct H17. rewrite <- H17 in *. clear H17 y.
    rewrite H0. apply reachable_by_reflexive. rewrite <- pg_the_same. split. auto. hnf; auto. rewrite H12 in H17. rewrite H0.
    rewrite <- pg_the_same; apply reachable_by_merge with l; auto. rewrite H14 in H17. rewrite H0. rewrite <- pg_the_same.
    apply reachable_by_merge with r; auto. destruct (tri_list_split t_eq_dec Hn1 H16 Hn3 H17) as [li1 [li2 [li3 [? [? ?]]]]].
    rewrite (iter_sepcon_permutation _ _ (graph_cell bm_bi) H20) in H1. do 2 rewrite iter_sepcon_app_sepcon in H1.
    destruct_sepcon H1 w. destruct_sepcon H22 w. rename w2 into w23. rename w0 into w2. try_join w1 w2 w12.
    exists w1, w2, w3, w12, w23. do 3 (split; auto). split. assert (iter_sepcon (x :: listL) (graph_cell bm_bi) w12).
    rewrite (iter_sepcon_permutation _ _ (graph_cell bm_bi) H18). rewrite iter_sepcon_app_sepcon. exists w1, w2. split; auto.
    simpl in H27. destruct_sepcon H27 h. apply sepcon_ocon. exists h1, h2. split; auto. split. apply graph_cell_trinode; auto.
    right. exists listL. split; auto. rewrite <- pg_the_same. split; auto. right; exists listR; split. rewrite <- pg_the_same.
    split; auto. rewrite (iter_sepcon_permutation _ _ (graph_cell bm_bi) H19). rewrite iter_sepcon_app_sepcon. exists w2, w3.
    split; auto.

    (* <- direction *)
    
    destruct H. left; auto. destruct H as [d [l [r [[? ?] ?]]]]. destruct_ocon H1 h. destruct_ocon H4 i. unfold graph in H9, H5.
    unfold gamma in H. destruct (biEdge bm_bi x) as [v1 v2] eqn:? . unfold biEdge in Heqp. inversion H. subst.
    destruct (only_two_neighbours x) as [v1 [v2 ?]]. inversion Heqp. subst. clear Heqp H. destruct H9, H5.

    (* Both are 0 *)
    
    right. exists (x :: nil). destruct H, H5. hnf in H, H5. subst. split. split. trivial. intro. split; intros.
    apply in_inv in H. destruct H. subst. apply reachable_by_reflexive. split; auto. hnf; auto. inversion H.
    apply (reachable_from_children b_pg) in H. destruct H. subst; apply in_eq. destruct H as [z [[? [? ?]] ?]].
    rewrite e in H11. rewrite <- pg_the_same in H5. apply valid_not_null in H5. exfalso. apply in_inv in H11; destruct H11.
    intuition. apply in_inv in H11; destruct H11. intuition. inversion H11. simpl. try_join i2 i3 i23'; equate_join i23 i23'.
    apply join_comm in H5. assert (join i23 i1 i1). apply identity_unit; auto. exists h12; auto. equate_join i1 h12.
    apply join_comm in H2. generalize (split_identity h3 h2 H2 H10); intro. generalize (split_identity i2 i3 H6 H9). intro.
    assert (join i2 i1 i1). apply identity_unit; auto. exists i12. auto. equate_join i1 i12. exists i1, h3. split; auto.
    split; auto. apply (trinode_graph_cell 0 0); auto.

    (* Left is 0 *)
    
    destruct H; hnf in H; subst. destruct H5 as [listR [[? ?] ?]]. right. destruct (in_dec t_eq_dec x listR).
    exists listR. split. split. auto. intro y. rewrite H5. split; intro. apply reachable_by_merge with r.
    exists (x :: r :: nil). split; split; simpl; auto. do 3 (split; auto). rewrite e. apply in_cons, in_eq. repeat intro; hnf.
    auto. apply H11. apply (reachable_from_children b_pg) in H11. destruct H11. subst. rewrite <- H5. auto.
    destruct H11 as [z [[? [? ?]] ?]]. rewrite e in H13. apply in_inv in H13. destruct H13. rewrite <- pg_the_same in H12.
    apply valid_not_null in H12. exfalso; intuition. apply in_inv in H13; destruct H13. subst; auto. inversion H13.
    assert (join i2 i1 i1). apply identity_unit. apply (split_identity i2 i3 H6). auto. exists i12. auto. equate_join i1 i12.
    assert (join i3 i1 i1). apply identity_unit. apply join_comm in H6. apply (split_identity i3 i2 H6). auto. exists h12.
    auto. equate_join i1 h12. assert (join_sub i1 h23). apply in_split in i. destruct i as [ll1 [ll2 ?]]. subst.
    rewrite iter_sepcon_permutation with (l2 := x :: ll1 ++ ll2) in H10. simpl in H10. destruct_sepcon H10 j.
    apply (trinode_graph_cell _ _ _ _ e) in H8. try_join h2 h3 h23'; equate_join h23 h23'. assertSub j1 w Sub1.
    assertSub i1 w Sub2. assert (precise (graph_cell bm_bi x)) by apply precise_graph_cell.
    equate_precise_through (graph_cell bm_bi x) i1 j1. exists j2; auto. apply Permutation_sym, Permutation_middle.
    destruct H7 as [h4 ?]. assert (h23 = w). apply (overlapping_join_eq H1 H2 H3 H7). subst; auto. exists (x :: listR).
    split. split. auto. intros. split; intro. apply in_inv in H11. destruct H11. subst. apply reachable_by_reflexive.
    split. auto. hnf. auto. apply reachable_by_merge with r. exists (x :: r :: nil). split; split; simpl; auto.
    do 3 (split; auto). rewrite e. apply in_cons, in_eq. repeat intro; hnf; auto. rewrite H5 in H11. apply H11.
    apply (reachable_from_children b_pg) in H11. destruct H11. subst; apply in_eq. destruct H11 as [z [[? [? ?]] ?]].
    rewrite e in H13. apply in_inv in H13; destruct H13. rewrite <- pg_the_same in H12. apply valid_not_null in H12. exfalso.
    intuition. apply in_inv in H13; destruct H13. subst. apply in_cons. rewrite H5. auto. inversion H13.
    assert (join i2 i1 i1). apply identity_unit. apply (split_identity i2 i3 H6). auto. exists i12. auto. equate_join i1 i12.
    assert (join i3 i1 i1). apply identity_unit. apply join_comm in H6. apply (split_identity i3 i2 H6). auto. exists h12. auto.
    equate_join h12 i1. clear H6 H7 H9 H11 i2 i3 i23. apply (trinode_graph_cell _ _ _ _ e) in H8.
    assert ((iter_sepcon (x :: listR) (graph_cell bm_bi) * TT)%pred w). simpl. apply iter_sepcon_joinable.
    apply joinable_graph_cell. apply precise_graph_cell. auto. assertSub h12 w HSub. destruct HSub as [? ?]. exists h12, x0.
    split; auto. try_join h2 h3 h23'; equate_join h23 h23'. assertSub h23 w HSub. destruct HSub as [? ?]. exists h23, x0.
    split; auto. simpl in H4. destruct_sepcon H4 k. rename k1 into k12; rename k2 into k3. destruct_sepcon H6 k.
    assert (precise (graph_cell bm_bi x)) by apply precise_graph_cell. assertSub k1 w HS1. assertSub h12 w HS2.
    equate_precise_through (graph_cell bm_bi x) h12 k1. assert (precise (iter_sepcon listR (graph_cell bm_bi))).
    apply precise_iter_sepcon. apply precise_graph_cell. try_join h2 h3 h23'; equate_join h23 h23'. assertSub h23 w HS1.
    assertSub k2 w HS2. equate_precise_through (iter_sepcon listR (graph_cell bm_bi)) h23 k2. try_join h2 h23 ht.
    assert (emp h2). apply join_sub_joins_identity with h23. exists h3; auto. exists ht; auto.
    assert (join h2 h1 h1). apply identity_unit; auto. exists h12; auto. equate_join h1 h12. assert (join h2 h3 h3).
    apply identity_unit; auto. exists h23; auto. equate_join h3 h23. simpl. exists h1, h3. split; auto.
    
    (* Right is 0 *)
    
    destruct H5; hnf in H5; subst. destruct H as [listL [[? ?] ?]]. right. destruct (in_dec t_eq_dec x listL).
    exists listL. split. split. auto. intro y. rewrite H5. split; intro. apply reachable_by_merge with l.
    exists (x :: l :: nil). split; split; simpl; auto. do 3 (split; auto). rewrite e. apply in_eq. repeat intro; hnf; auto.
    apply H11. apply (reachable_from_children b_pg) in H11. destruct H11. subst. rewrite <- H5. auto.
    destruct H11 as [z [[? [? ?]] ?]]. rewrite e in H13. apply in_inv in H13; destruct H13. subst; auto. apply in_inv in H13.
    destruct H13. rewrite <- pg_the_same in H12. apply valid_not_null in H12. exfalso; intuition. inversion H13.
    assert (join h2 h1 h1). apply identity_unit. apply (split_identity h2 h3 H2). auto. exists h12. auto. equate_join h1 h12.
    assert (join h3 h1 h1). apply identity_unit. apply join_comm in H2. apply (split_identity h3 h2 H2). auto. exists w.
    auto. equate_join w h1. assert (join_sub i12 i23). apply in_split in i. destruct i as [ll1 [ll2 ?]]. subst.
    rewrite iter_sepcon_permutation with (l2 := x :: ll1 ++ ll2) in H10. simpl in H10. destruct_sepcon H10 j.
    apply (trinode_graph_cell _ _ _ _ e) in H8. try_join i2 i3 i23'; equate_join i23 i23'. assertSub j1 w Sub1.
    assertSub i12 w Sub2. assert (precise (graph_cell bm_bi x)) by apply precise_graph_cell.
    equate_precise_through (graph_cell bm_bi x) i12 j1. exists j2; auto. apply Permutation_sym, Permutation_middle.
    destruct H1 as [h4 ?]. assert (i23 = w). apply (overlapping_join_eq H4 H6 H7 H1). subst; auto. exists (x :: listL).
    split. split. auto. intros. split; intro. apply in_inv in H11. destruct H11. subst. apply reachable_by_reflexive.
    split. auto. hnf. auto. apply reachable_by_merge with l. exists (x :: l :: nil). split; split; simpl; auto.
    do 3 (split; auto). rewrite e. apply in_eq. repeat intro; hnf; auto. rewrite H5 in H11. apply H11.
    apply (reachable_from_children b_pg) in H11. destruct H11. subst; apply in_eq. destruct H11 as [z [[? [? ?]] ?]].
    rewrite e in H13. apply in_inv in H13; destruct H13. subst. apply in_cons. rewrite H5. auto. apply in_inv in H13.
    destruct H13. rewrite <- pg_the_same in H12. apply valid_not_null in H12. exfalso. intuition. inversion H13. 
    assert (join h2 h1 h1). apply identity_unit. apply (split_identity h2 h3 H2). auto. exists h12. auto. equate_join h1 h12.
    assert (join h3 h1 h1). apply identity_unit. apply join_comm in H2. apply (split_identity h3 h2 H2). auto. exists w. auto.
    equate_join w h1. clear H2 H3 H9 H11 h2 h3 h23. apply (trinode_graph_cell _ _ _ _ e) in H8.
    assert ((iter_sepcon (x :: listL) (graph_cell bm_bi) * TT)%pred w). simpl. apply iter_sepcon_joinable.
    apply joinable_graph_cell. apply precise_graph_cell. auto. assertSub i12 w HSub. destruct HSub as [? ?]. exists i12, x0.
    split; auto. try_join i2 i3 i23'; equate_join i23 i23'. assertSub i23 w HSub. destruct HSub as [? ?]. exists i23, x0.
    split; auto. simpl in H1. destruct_sepcon H1 k. rename k1 into k12; rename k2 into k3. destruct_sepcon H2 k.
    assert (precise (graph_cell bm_bi x)) by apply precise_graph_cell. assertSub k1 w HS1. assertSub i12 w HS2.
    equate_precise_through (graph_cell bm_bi x) i12 k1. assert (precise (iter_sepcon listL (graph_cell bm_bi))).
    apply precise_iter_sepcon. apply precise_graph_cell. try_join i2 i3 i23'; equate_join i23 i23'. assertSub i23 w HS1.
    assertSub k2 w HS2. equate_precise_through (iter_sepcon listL (graph_cell bm_bi)) i23 k2. try_join i2 i23 ht.
    assert (emp i2). apply join_sub_joins_identity with i23. exists i3; auto. exists ht; auto. assert (join i2 i1 i1).
    apply identity_unit; auto. exists i12; auto. equate_join i1 i12. assert (join i2 i3 i3). apply identity_unit; auto.
    exists i23; auto. equate_join i3 i23. simpl. exists i1, i3. split; auto.

    (* Both are not 0 *)
    destruct H as [listL [[? ?] ?]]. destruct H5 as [listR [[? ?] ?]]. right. assert (sepcon_unique (graph_cell bm_bi)).
    apply graph_cell_sepcon_unique. assert (NoDup listL). apply (iter_sepcon_unique_nodup H13 H10). assert (NoDup listR).
    apply (iter_sepcon_unique_nodup H13 H12). destruct (in_dec t_eq_dec x listL).

    (* In x listL *)
    
    destruct (double_list_split t_eq_dec H14 H15) as [l1 [l2 [l3 [? [? ?]]]]]. exists (l1 ++ l2 ++ l3). split. split. auto.
    intro; split; intros. apply in_app_or in H19. destruct H19. assert (In y listL). apply Permutation_in with (l1 ++ l2).
    apply Permutation_sym; auto. apply in_or_app. left; auto. apply H9 in H20. apply reachable_by_merge with l.
    exists (x :: l :: nil). split; split; simpl; auto. do 3 (split; auto). rewrite e. apply in_eq. repeat intro; hnf; auto.
    apply H20. assert (In y listR). apply Permutation_in with (l2 ++ l3). apply Permutation_sym; auto. auto. apply H11 in H20.
    apply reachable_by_merge with r. exists (x :: r :: nil). split; split; simpl; auto. do 3 (split; auto). rewrite e.
    apply in_cons, in_eq. repeat intro; hnf; auto. apply H20. apply (reachable_from_children b_pg) in H19. destruct H19. subst.
    apply (Permutation_in x) in H16. rewrite app_assoc. apply in_or_app. left; auto. auto. destruct H19 as [z [[? [? ?]] ?]].
    rewrite e in H21. apply in_inv in H21; destruct H21. subst. rewrite <- H9 in H22. rewrite app_assoc. apply in_or_app; left.
    apply (Permutation_in y H16 H22). apply in_inv in H21; destruct H21. subst. rewrite <- H11 in H22. apply in_or_app; right.
    apply (Permutation_in y H17 H22). inversion H21. assert ((iter_sepcon (l1 ++ l2 ++ l3) (graph_cell bm_bi) * TT)%pred w).
    apply iter_sepcon_app_joinable. apply joinable_graph_cell. apply precise_graph_cell. apply NoDup_app_not_in; auto.
    apply NoDup_app_l in H18; auto. rewrite (iter_sepcon_permutation _ _ _ H16) in H10. rewrite iter_sepcon_app_sepcon in H10.
    destruct_sepcon H10 h. try_join i2 i3 i23'; equate_join i23 i23'. assertSub h0 i23 HS1. assertSub i23 w HS2.
    assertSub h0 w HS3. destruct HS3. exists h0, x0. split; auto. rewrite (iter_sepcon_permutation _ _ _ H17) in H12.
    try_join h2 h3 h23'; equate_join h23 h23'. exists h23, h1. split; auto. destruct_sepcon H19 w. rename w1 into w123.
    rename w2 into w4. apply trinode_graph_cell in H8. assert (join_sub i12 i23). apply in_split in i.
    destruct i as [ll1 [ll2 ?]]. rewrite H22 in H10. rewrite (iter_sepcon_permutation _ (x :: ll1 ++ ll2) _) in H10.
    simpl in H10. destruct_sepcon H10 t. assert (precise (graph_cell bm_bi x)). apply precise_graph_cell.
    try_join i2 i3 i23'; equate_join i23 i23'. assertSub t1 h12 HS1. assertSub i12 h12 HS2.
    generalize (H25 h12 t1 i12 H23 H8 HS1 HS2); intro Heq. rewrite Heq in *. clear Heq. exists t2. auto. apply Permutation_sym.
    apply Permutation_middle. destruct H22 as [i4 ?]. generalize (overlapping_join_eq H4 H6 H7 H22). intro. rewrite H23 in *.
    clear H23 i23. rewrite (iter_sepcon_permutation _ _ _ H16) in H10. rewrite (iter_sepcon_permutation _ _ _ H17) in H12.
    rewrite iter_sepcon_app_sepcon in H10, H12. destruct_sepcon H10 j. destruct_sepcon H12 j. rename j0 into j2'.
    try_join h2 h3 h23'; equate_join h23 h23'. assert (precise (iter_sepcon l2 (graph_cell bm_bi))).
    apply precise_iter_sepcon, precise_graph_cell. assertSub j2 w HS1. assertSub j2' w HS2.
    equate_precise_through (iter_sepcon l2 (graph_cell bm_bi)) j2 j2'. rewrite iter_sepcon_app_sepcon in H20.
    destruct_sepcon H20 w. rename w2 into w23. rewrite iter_sepcon_app_sepcon in H29. destruct_sepcon H29 w.
    rename w2 into w3; rename w0 into w2. assert (precise (iter_sepcon l1 (graph_cell bm_bi))). apply precise_iter_sepcon.
    apply precise_graph_cell. assert (precise (iter_sepcon l3 (graph_cell bm_bi))). apply precise_iter_sepcon.
    apply precise_graph_cell. assertSub j1 w HS1. assertSub w1 w HS2.
    equate_precise_through (iter_sepcon l1 (graph_cell bm_bi)) j1 w1. assertSub j2 w HS1. assertSub w2 w123 HS2.
    assertSub w123 w HS3. assertSub w2 w HS4. clear HS2 HS3. equate_precise_through (iter_sepcon l2 (graph_cell bm_bi)) j2 w2.
    assertSub j3 w HS1. assertSub w3 w123 HS2. assertSub w123 w HS3. assertSub w3 w HS4. clear HS2 HS3.
    equate_precise_through (iter_sepcon l3 (graph_cell bm_bi)) j3 w3. equate_join h23 w23. try_join j1 j2 j12.
    equate_join h12 j12. apply join_comm in H29. assert (w123 = w). apply (overlapping_eq j1 j2 j3 h1 h2 h3 h12 h23); trivial.
    subst. rewrite iter_sepcon_app_sepcon. exists j1, h23. do 2 (split; auto). rewrite iter_sepcon_app_sepcon. exists j2, j3.
    split; auto. trivial.

    (* ~ In x listL *)

    assert (NoDup (x :: listL)). apply NoDup_cons; auto.
    destruct (double_list_split t_eq_dec H16 H15) as [l1 [l2 [l3 [? [? ?]]]]]. exists (l1 ++ l2 ++ l3). split. split. auto.
    intro; split; intros. apply in_app_or in H20. destruct H20. assert (In y (x :: listL)). apply Permutation_in with (l1++l2).
    apply Permutation_sym; auto. apply in_or_app. left; auto. apply in_inv in H21. destruct H21. subst.
    apply reachable_by_reflexive. do 2 (split; auto). apply H9 in H21. apply reachable_by_merge with l.
    exists (x :: l :: nil). split; split; simpl; auto. do 3 (split; auto). rewrite e. apply in_eq. repeat intro; hnf; auto.
    apply H21. assert (In y listR). apply Permutation_in with (l2 ++ l3). apply Permutation_sym; auto. auto. apply H11 in H21.
    apply reachable_by_merge with r. exists (x :: r :: nil). split; split; simpl; auto. do 3 (split; auto). rewrite e.
    apply in_cons, in_eq. repeat intro; hnf; auto. apply H21. apply (reachable_from_children b_pg) in H20. destruct H20. subst.
    apply (Permutation_in x) in H17. rewrite app_assoc. apply in_or_app. left;auto. apply in_eq. destruct H20 as [z[[?[? ?]]?]].
    rewrite e in H22. apply in_inv in H22; destruct H22. subst. rewrite <- H9 in H23. rewrite app_assoc. apply in_or_app; left.
    assert (In y (x :: listL)). apply in_cons; auto. apply (Permutation_in y H17 H22). apply in_inv in H22; destruct H22. subst.
    rewrite <- H11 in H23. apply in_or_app; right. apply (Permutation_in y H18 H23). inversion H22. try_join h2 h3 h23'.
    equate_join h23 h23'. try_join i2 i3 i23'; equate_join i23 i23'. apply trinode_graph_cell in H8; auto.
    assert (iter_sepcon (x::listL) (graph_cell bm_bi) h12). assert ((iter_sepcon (x::listL) (graph_cell bm_bi) * TT)%pred h12).
    apply iter_sepcon_joinable. apply joinable_graph_cell. apply precise_graph_cell. auto. assertSub i12 h12 HS. destruct HS.
    exists i12, x0. split; auto. assertSub i23 h12 HS. destruct HS. exists i23, x0. split; auto. destruct_sepcon H20 j.
    rename j2 into je; rename j1 into j12. simpl in H23. destruct_sepcon H23 j. assert (precise (graph_cell bm_bi x)).
    apply precise_graph_cell. assertSub i12 h12 HS1. assertSub j1 h12 HS2. generalize (H27 h12 j1 i12 H25 H8 HS2 HS1); intro.
    rewrite H28 in *; clear H25 HS2 HS1 H28 j1. assert (precise (iter_sepcon listL (graph_cell bm_bi))).
    apply precise_iter_sepcon, precise_graph_cell. assertSub i23 h12 HS1. assertSub j2 h12 HS2.
    equate_precise_through (iter_sepcon listL (graph_cell bm_bi)) i23 j2. try_join i2 i23 i2i23. assert (emp i2).
    apply join_sub_joins_identity with i23. exists i3; auto. exists i2i23; auto. apply join_unit2_e in H4; auto. subst.
    apply join_unit1_e in H6;auto. subst. simpl. exists i12, i23. split;auto. rewrite (iter_sepcon_permutation _ _ _ H17) in H20.
    rewrite iter_sepcon_app_sepcon in H20. destruct_sepcon H20 j. rewrite (iter_sepcon_permutation _ _ _ H18) in H12.
    assert ((iter_sepcon (l1 ++ l2 ++ l3) (graph_cell bm_bi) * TT)%pred w). apply iter_sepcon_app_joinable.
    apply joinable_graph_cell. apply precise_graph_cell. apply NoDup_app_not_in; auto. apply NoDup_app_l in H19; auto.
    assertSub j1 w HS. destruct HS. exists j1, x0. split; auto. assertSub h23 w HS. destruct HS. exists h23, x0. split; auto.
    rewrite iter_sepcon_app_sepcon in H12. destruct_sepcon H12 t. rename t1 into j2'; rename t2 into j3.
    assert (precise (iter_sepcon l2 (graph_cell bm_bi))). apply precise_iter_sepcon, precise_graph_cell. assertSub j2 w HS1.
    assertSub j2' w HS2. equate_precise_through (iter_sepcon l2 (graph_cell bm_bi)) j2 j2'.
    rewrite iter_sepcon_app_sepcon in H25. destruct_sepcon H25 w. rename w2 into w4. rename w1 into w123.
    destruct_sepcon H26 w. rename w2 into w23. rewrite iter_sepcon_app_sepcon in H31. destruct_sepcon H31 w.
    rename w2 into w3; rename w0 into w2. assert (precise (iter_sepcon l1 (graph_cell bm_bi))). apply precise_iter_sepcon.
    apply precise_graph_cell. assert (precise (iter_sepcon l3 (graph_cell bm_bi))). apply precise_iter_sepcon.
    apply precise_graph_cell. assertSub j1 w HS1. assertSub w1 w HS2.
    equate_precise_through (iter_sepcon l1 (graph_cell bm_bi)) j1 w1. assertSub j2 w HS1. assertSub w2 w123 HS2.
    assertSub w123 w HS3. assertSub w2 w HS4. clear HS2 HS3. equate_precise_through (iter_sepcon l2 (graph_cell bm_bi)) j2 w2.
    assertSub j3 w HS1. assertSub w3 w123 HS2. assertSub w123 w HS3. assertSub w3 w HS4. clear HS2 HS3.
    equate_precise_through (iter_sepcon l3 (graph_cell bm_bi)) j3 w3. equate_join h23 w23. try_join j1 j2 j12.
    equate_join h12 j12. apply join_comm in H31. assert (w123 = w). apply (overlapping_eq j1 j2 j3 h1 h2 h3 h12 h23); trivial.
    subst. rewrite iter_sepcon_app_sepcon. exists j1, h23. do 2 (split; auto). rewrite iter_sepcon_app_sepcon. exists j2, j3.
    split; auto. 
  Qed.

  Lemma precise_graph: forall x bimg, precise (graph x bimg).
  Proof.
    intros. apply precise_orp. repeat intro. destruct H as [[? ?] [l [[? ?] ?]]]. hnf in H. rewrite <- pg_the_same in H1.
    apply valid_not_null in H1. auto. apply precise_andp_right, precise_emp. repeat intro. destruct H as [l1 [? ?]].
    destruct H0 as [l2 [? ?]]. destruct H, H0. assert (sepcon_unique (graph_cell bm_bi)). apply graph_cell_sepcon_unique.
    assert (Permutation l1 l2). apply NoDup_Permutation. apply (iter_sepcon_unique_nodup H7 H3).
    apply (iter_sepcon_unique_nodup H7 H4). intros; split; intro. rewrite H5 in H8. rewrite H6. auto. rewrite H6 in H8.
    rewrite H5; auto. rewrite (iter_sepcon_permutation _ _ _ H8) in H3. assert (precise (iter_sepcon l2 (graph_cell bm_bi))).
    apply precise_iter_sepcon, precise_graph_cell. equate_precise_through (iter_sepcon l2 (graph_cell bm_bi)) w1 w2. auto.
  Qed.

  Fixpoint graphs (l : list adr) bimg :=
    match l with
      | nil => emp
      | v :: l' => graph v bimg ⊗ graphs l' bimg
    end.

  Lemma precise_graphs: forall S bimg, precise (graphs S bimg).
  Proof. intros; induction S; simpl. apply precise_emp. apply precise_ocon; auto. apply precise_graph. Qed.

  Lemma graphs_list_null_or_valid: forall S bimg w x, graphs S bimg w -> In x S -> x = 0 \/ valid x.
  Proof.
    induction S; intros. inversion H0. apply in_inv in H0. simpl in H. destruct_ocon H w. destruct H0. subst. 
    unfold graph in H3. destruct H3; [left | right]. hnf in H0; auto. destruct H0; hnf in H0; auto.
    destruct H0 as [l [[? ?] ?]]. auto. apply IHS with w23; auto.
  Qed.

  Lemma reachable_eq_graphs_eq:
    forall S S' bimg, set_eq (reachable_through_set b_pg S) (reachable_through_set b_pg S') -> graphs S bimg = graphs S' bimg.
  Proof.
    induction S. intros. assert (set_eq (reachable_through_set b_pg S') (empty_set adr)).
    transitivity (reachable_through_set b_pg nil). symmetry; auto. apply reachable_through_empty. unfold empty_set in H0.
    destruct H0. assert (forall x, ~ reachable_through_set b_pg S' x). intro x. specialize (H0 x). simpl in H0. hnf. apply H0.
    simpl. admit. admit.
  Qed.

End SpatialGraph.
