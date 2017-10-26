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
Require Import ramification.

Local Open Scope pred.

Instance natEqDec : EqDec nat := { t_eq_dec := eq_nat_dec }.

Definition trinode x d l r := !!(3 | x) && ((mapsto x d) * (mapsto (x+1) l) * (mapsto (x+2) r)).

Section PointwiseGraph.

  Definition graph_cell (bi : @BiGraph adr nat natEqDec) (v : adr) : pred world :=
    let (dl, r) := gamma bi v in let (d, l) := dl in trinode v d l r.

  Fixpoint consecutive_mapsto l x : pred world :=
    match l with
      | nil => emp
      | v :: l' => (mapsto x v) * consecutive_mapsto l' (x + 1)
    end.

  Definition algn_consec_mapsto l x : pred world := !!(length l | x) && consecutive_mapsto l x.

  Definition pregraph_cell (pg : @PreGraph adr nat natEqDec) (x : adr) : pred world :=
    algn_consec_mapsto (node_label x :: edge_func x) x.

  Lemma cells_are_the_same: forall (bi : @BiGraph adr nat natEqDec) (x : adr), graph_cell bi x = pregraph_cell b_pg x.
  Proof.
    intros; apply pred_ext; hnf; intro w; intros; unfold graph_cell in *; unfold pregraph_cell in *;
    unfold algn_consec_mapsto in *; unfold gamma in *; unfold biEdge in *; destruct (only_two_neighbours x) as [l [r He]] in *;
    unfold trinode in *; destruct H; rewrite He in *; simpl in *; split; auto; assert (1 + 1 = 2) by intuition.
    rewrite <- plus_assoc. rewrite H1. rewrite sepcon_emp. rewrite <- sepcon_assoc. auto. rewrite <- plus_assoc in H0.
    rewrite H1 in H0. rewrite <- sepcon_assoc in H0. rewrite sepcon_emp in H0. auto.
  Qed.

  Lemma precise_consecutive_mapsto: forall l x, precise (consecutive_mapsto l x).
  Proof. induction l; intro; simpl. apply precise_emp. apply precise_sepcon. apply IHl. apply precise_mapsto. Qed.

  Lemma precise_algn_consec_mapsto: forall l x, precise (algn_consec_mapsto l x).
  Proof. intros; unfold algn_consec_mapsto. apply precise_andp_right. apply precise_consecutive_mapsto. Qed.

  Lemma precise_pregraph_cell: forall pg v, precise (pregraph_cell pg v).
  Proof. intros. unfold pregraph_cell. apply precise_algn_consec_mapsto. Qed.

  Lemma precise_graph_cell: forall bi v, precise (graph_cell bi v).
  Proof. intros. rewrite cells_are_the_same. apply precise_pregraph_cell. Qed.

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

  Lemma alignable_mapsto: forall x y a b, mapsto x a ⊗ mapsto y b |--
                                                 mapsto x a && !!(x = y /\ a = b) || mapsto x a * mapsto y b && !!(x <> y).
  Proof.
    intros x y a b w; intros. destruct (eq_nat_dec x y). left. subst. destruct_ocon H w. destruct w12 as [f12 m12].
    destruct w23 as [f23 m23]. destruct w1 as [f1 m1]. destruct w2 as [f2 m2]. destruct w3 as [f3 m3]. destruct w as [fw mw].
    hnf in *. simpl in *. destruct H2 as [? [? ?]]. destruct H3 as [? [? ?]]. generalize (H y); intro. generalize (H0 y); intro.
    generalize (H1 y); intro. rewrite H5 in *. rewrite H7 in *. clear H5 H7. inversion H8. rewrite H12 in *; clear H12.
    rewrite <- H7 in *. clear H7. subst. inversion H9. rewrite <- H11 in *. clear H11. subst. inversion H10. unfold mapsto.
    simpl. rewrite <- H7 in *. split. do 2 (split; auto). intro z. intros. specialize (H4 z H11). specialize (H6 z H11).
    specialize (H1 z). rewrite H4 in *. specialize (H0 z). rewrite H6 in *. destruct (f3 z). inversion H0. inversion H1; auto.
    auto. inversion H12. rewrite H12 in *. clear H12. rewrite <- H11 in *. clear H11. inversion H9. rewrite H7 in *.
    inversion H10. inversion H15. inversion H12. right. split; auto.

    destruct_ocon H w. generalize H2; intro Hx. generalize H3; intro Hy. destruct w12 as [f12 x12] eqn:? .
    destruct w23 as [f23 x23] eqn:? . hnf in H2. simpl in H2. destruct H2 as [? [? ?]]. hnf in H3. simpl in H3.
    destruct H3 as [? [? ?]].
    remember (fun xx : adr => if eq_nat_dec xx x then Some a else (if eq_nat_dec xx y then Some b else None)) as f.
    assert (finMap f). exists (x :: y :: nil). intro z. intros. rewrite Heqf. destruct (eq_nat_dec z x). subst.
    exfalso. apply H8. apply in_eq. destruct (eq_nat_dec z y). subst. exfalso. apply H8. apply in_cons, in_eq.
    trivial. remember (exist (finMap (B:=adr)) f H8) as ff. assert (join w12 w23 ff). rewrite Heqw0, Heqw1, Heqff.
    hnf; simpl. intro z. destruct (eq_nat_dec z x). rewrite e in *. rewrite H5. generalize (H6 x n); intro HS. rewrite HS.
    rewrite Heqf. destruct (eq_nat_dec x x). apply lower_None2. exfalso; auto. destruct (eq_nat_dec z y). rewrite e in *.
    rewrite H7. generalize (H4 y n0); intro HS. rewrite HS. rewrite Heqf. destruct (eq_nat_dec y x). intuition.
    destruct (eq_nat_dec y y). apply lower_None1. intuition. specialize (H4 z n0). specialize (H6 z n1). rewrite H4, H6.
    rewrite Heqf. destruct (eq_nat_dec z x). intuition. destruct (eq_nat_dec z y). intuition. apply lower_None1.
    rewrite <- Heqw0 in *. rewrite <- Heqw1 in *. assert (emp w2). apply join_sub_joins_identity with w23. exists w3; auto.
    try_join w2 w23 t. exists t; auto. apply (join_unit2_e _ _ H10) in H. rewrite <- H in * |-. clear H w12.
    apply (join_unit1_e _ _ H10) in H0. rewrite <- H0 in *. clear H0 w23. equate_join w ff. exists w1, w3. split; auto.
  Qed.

  Lemma alignable_emapsto: alignable emapsto.
  Proof.
    intros x y w; intros. destruct_ocon H w. destruct H2 as [a ?]; destruct H3 as [b ?]. assert ((mapsto x a ⊗ mapsto y b) w).
    exists w1, w2, w3, w12, w23. split; auto. apply alignable_mapsto in H4. destruct H4 as [[? [? ?]] | [? ?]]; [left | right].
    split; auto. exists a; auto. split; auto. destruct_sepcon H4 h. exists h1,h2. split;auto. split; [exists a|exists b]; auto.
  Qed.

  Lemma divisible_distance: forall x y d, x > y -> (d | x) -> (d | y) -> x - y >= d.
  Proof.
    intros. destruct H0 as [dx ?]; destruct H1 as [dy ?]. subst. rewrite <- mult_minus_distr_r.
    destruct (mult_O_le d (dx - dy)). assert (dx * d - dy * d > 0). intuition. rewrite <- mult_minus_distr_r in H1.
    rewrite H0 in H1. simpl in H1; exfalso; intuition. intuition.
  Qed.

  Lemma disjoint_mapsto_consec:
    forall l x y v, (y > x \/ x >= y + length l) -> mapsto x v ⊗ consecutive_mapsto l y |-- mapsto x v * consecutive_mapsto l y.
  Proof.
    induction l; intros; intro w; intros; simpl in *. rewrite sepcon_emp. rewrite ocon_emp in H0. auto. destruct_ocon H0 w.
    destruct_sepcon H4 h. destruct_cross w23. rename w2h1 into i1; rename w3h1 into i2; rename w3h2 into i3; rename w2h2 into i4.
    try_join w1 i4 w1i4. try_join w12 i2 w12i2. assert ((mapsto x v ⊗ mapsto y a) w12i2). exists w1i4, i1, i2, w12, h1.
    split; auto. apply alignable_mapsto in H15. destruct H15 as [[? [? ?]] | [? ?]]. exfalso; intuition. assert (emp i1).
    apply (overlapping_precise_emp w1i4 i1 i2 w12 h1 w12i2 (mapsto x v) (mapsto y a)); auto. apply precise_mapsto.
    apply precise_mapsto. elim_emp. clear H17 i1. try_join w12 i3 w12i3.
    assert ((mapsto x v ⊗ consecutive_mapsto l (y + 1)) w12i3). exists w1, w2, i3, w12, h2. split; auto. apply IHl in H12.
    assert (emp w2). apply (overlapping_precise_emp w1 w2 i3 w12 h2 w12i3 (mapsto x v) (consecutive_mapsto l (y + 1))); auto.
    apply precise_mapsto. apply precise_consecutive_mapsto. elim_emp. exists w12, w23. do 2 (split; auto). exists h1, h2.
    split; auto. intuition.
  Qed.

  Lemma disjoint_consecutive_mapsto:
    forall l1 l2 x y,
      length l1 = length l2 -> x > y -> x - y >= length l2 ->
      (consecutive_mapsto l1 x ⊗ consecutive_mapsto l2 y) |-- (consecutive_mapsto l1 x * consecutive_mapsto l2 y).
  Proof.
    induction l1; intros; intro w; intros; simpl in H; destruct_ocon H2 w; rewrite <- H in *; destruct l2; simpl in *.
    rewrite sepcon_emp. apply alignable_emp. exists w1, w2, w3, w12, w23. split; auto. inversion H. inversion H.
    try_join w2 w3 w23'; equate_join w23 w23'. destruct_sepcon H5 h. rename h1 into hx. rename h2 into hxl.
    destruct_sepcon H6 h. rename h1 into hy; rename h2 into hyl. destruct_cross w12. destruct_cross w23. destruct_cross w2.
    rename w2hxw2hy into i1. rename w2hxw2hyl into i2. rename w2hxlw2hyl into i3. rename w2hxlw2hy into i4. rename w1hx into i5.
    rename w1hxl into i6. rename w3hy into i7. rename w3hyl into i8. rename w2hy into i14. rename w2hx into i12.
    rename w2hxl into i34. rename w2hyl into i23. try_join i2 i5 i25. try_join i4 i7 i47. rename hx into i125.
    rename hy into i147. try_join i3 i6 i36. try_join i3 i8 i38. try_join hxl w3 i34678. try_join i1 i34678 i134678.
    try_join hxl i8 i3468. try_join i36 i8 i368. try_join_through i3468 i4 i7 i47'. equate_join i47 i47'. try_join i1 i47 i147'.
    equate_join i147 i147'. try_join i25 i147 i12457. rewrite <- sepcon_assoc. rewrite (sepcon_assoc (mapsto x a)).
    rewrite (sepcon_comm (consecutive_mapsto l1 (x + 1))). rewrite <- (sepcon_assoc (mapsto x a)).
    rewrite (sepcon_assoc (mapsto x a * mapsto y a0)). exists i12457, i368. split; auto.
    assert ((mapsto y a0 ⊗ mapsto x a) i12457). exists i47, i1, i25, i147, i125. split; auto. apply alignable_mapsto in H44.
    destruct H44 as [[? [? ?]] | [? ?]]. exfalso; intuition. split. rewrite sepcon_comm; auto. apply IHl1; intuition. 
    assert (emp i2). try_join i1 i5 i15. try_join_through i36 i3 i8 i38'. equate_join i38 i38'. try_join i125 i368 i123568.
    try_join i125 i38 i12358. assert ((mapsto x a ⊗ consecutive_mapsto l2 (y + 1)) i12358). exists i15, i2, i38, i125, hyl.
    split; auto. apply disjoint_mapsto_consec in H53; [|intuition].
    apply (overlapping_precise_emp i15 i2 i38 i125 hyl i12358 (mapsto x a) (consecutive_mapsto l2 (y+1))); auto.
    apply precise_mapsto. apply precise_consecutive_mapsto. elim_emp. clear H46 i2. assert (emp i4). try_join i12 i7 i17.
    try_join i147 i36 i13467. assert ((mapsto y a0 ⊗ consecutive_mapsto l1 (x + 1)) i13467). exists i17, i4, i36, i147, hxl.
    split; auto. apply disjoint_mapsto_consec in H46; [|intuition].
    apply (overlapping_precise_emp i17 i4 i36 i147 hxl i13467 (mapsto y a0) (consecutive_mapsto l1 (x + 1))); auto.
    apply precise_mapsto. apply precise_consecutive_mapsto. elim_emp. exists i6, i34, i8, hxl, hyl. split; auto.
  Qed.

  Lemma merge_consecutive_mapsto: forall l x, consecutive_mapsto l x ⊗ consecutive_mapsto l x |-- consecutive_mapsto l x.
  Proof.
    intros; intro w; intros. destruct_ocon H w. revert x w w1 w2 w3 w12 w23 H H0 H1 H2 H3. induction l; intros. simpl in *.
    apply alignable_emp. exists w1, w2, w3, w12, w23. split; auto. simpl in *. destruct_sepcon H3 h. destruct_sepcon H2 h.
    assertSub h0 w HS1. try_join w2 w3 w23'; equate_join w23 w23'. assertSub h1 w HS2. assert (precise (mapsto x a)).
    apply precise_mapsto. equate_precise_through (mapsto x a) h1 h0. try_join h2 w1 h4. exists h1, h4. do 2 (split; auto).
    destruct_cross w12. destruct_cross w23. assert (emp w1h1). apply join_sub_joins_identity with h1. exists w2h1; auto.
    try_join w1h1 w23 t1. try_join w1h1 h1 t2. exists t2; auto. elim_emp. clear H19 w1h1. assert (emp w3h1).
    apply join_sub_joins_identity with h1. exists w2h0; auto. try_join w3h1 w12 t1. try_join w3h1 h1 t2. exists t2; auto.
    elim_emp. clear H11 w3h1. equate_canc w2h3 w2h2. try_join w2h3 w1 h3'. equate_join h3 h3'.
    specialize (IHl (x + 1) h4 w3 w2h3 w1 h2 h3). apply IHl; auto.
  Qed.

  Lemma alignable_acmapsto: forall n f, (forall x, length (f x) = n) -> alignable (fun x => algn_consec_mapsto (f x) x).
  Proof.
    intros; intros x y w; intros. destruct (eq_nat_dec x y); [left | right]; split; auto; destruct_ocon H0 w. subst.
    destruct H3, H4. split; auto. apply merge_consecutive_mapsto. exists w1, w2, w3, w12, w23. split; auto.

    destruct H3, H4. unfold algn_consec_mapsto. rewrite sepcon_andp_prop. split; auto. rewrite sepcon_comm, sepcon_andp_prop.
    split; auto. unfold prop in H3, H4. apply not_eq in n0. try_join w2 w3 w23'; equate_join w23 w23'. destruct n0.
    assert (y - x >= length (f x)). rewrite (H x) in *. rewrite (H y) in *. apply divisible_distance; auto.
    apply disjoint_consecutive_mapsto; auto. do 2 rewrite H; auto. exists w3, w2, w1, w23, w12. split; auto.
    assert (x - y >= length (f y)). rewrite (H x) in *. rewrite (H y) in *. apply divisible_distance; auto. rewrite sepcon_comm.
    apply disjoint_consecutive_mapsto; auto. do 2 rewrite H; auto. exists w1, w2, w3, w12, w23. split; auto.
  Qed.

  Lemma alignable_pregraph_cell: forall n (ng : NGraph adr nat n), alignable (pregraph_cell n_pg).
  Proof. intros. unfold pregraph_cell. apply (alignable_acmapsto (n + 1)). intros. simpl. rewrite n_neighbours. intuition. Qed.

  Lemma alignable_graph_cell: forall bg, alignable (graph_cell bg).
  Proof.
    intros. remember (bigraph_to_ngraph bg) as g3. assert (graph_cell bg = pregraph_cell b_pg). extensionality x.
    apply cells_are_the_same. rewrite H. assert ((@b_pg adr nat natEqDec bg) = n_pg). subst. simpl. auto. rewrite H0.
    apply alignable_pregraph_cell.
  Qed.

  Lemma precise_trinode: forall x d l r, precise (trinode x d l r).
  Proof.
    intros. unfold trinode. apply precise_andp_right. apply precise_sepcon. apply precise_mapsto. apply precise_sepcon.
    apply precise_mapsto. apply precise_mapsto.
  Qed.

  Lemma sepcon_unique_graph_cell: forall bi, sepcon_unique (graph_cell bi).
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

  Lemma joinable_emapsto: forall w, joinable emapsto w. Proof. intros. apply alignable_joinable, alignable_emapsto. Qed.

  Lemma emapsto_mapsto: forall x y, mapsto x y |-- emapsto x. Proof. repeat intro. exists y; auto. Qed.

  Ltac assert_emapsto x := match goal with | [H: mapsto x ?b ?w |- _] => generalize (emapsto_mapsto x b w H); intro end.

  Lemma joinable_graph_cell: forall bg w, joinable (graph_cell bg) w.
  Proof. intros. apply alignable_joinable, alignable_graph_cell. Qed.

  Definition graph (x : adr) (bimg : @BiMathGraph adr nat 0 natEqDec): pred world :=
    (!!(x = 0) && emp) || EX l : list adr, !!reachable_list b_pg x l && iter_sepcon l (graph_cell bm_bi).

  Lemma graph_unfold:
    forall x bimg,
      graph x bimg = (!!(x = 0) && emp) || EX d:nat, EX l:adr, EX r:adr, !!(gamma bm_bi x = (d, l, r) /\ valid x) &&
                                                                           (trinode x d l r ⊗ graph l bimg ⊗ graph r bimg).
  Proof.
    intros; apply pred_ext; intro w; intros. unfold graph in H. destruct H. left; auto. right. destruct H as [li [[? ?] ?]].
    destruct (gamma bm_bi x) as [[d l] r] eqn: ?. exists d, l, r. split. split; auto. assert (NoDup li) as Hn1.
    generalize (sepcon_unique_graph_cell bm_bi). intro. apply (iter_sepcon_unique_nodup H2 H1). unfold gamma in Heqp.
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
    apply sepcon_unique_graph_cell. assert (NoDup listL). apply (iter_sepcon_unique_nodup H13 H10). assert (NoDup listR).
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
    destruct H0 as [l2 [? ?]]. destruct H, H0. assert (sepcon_unique (graph_cell bm_bi)). apply sepcon_unique_graph_cell.
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

  Lemma graphs_list_well_defined: forall S bimg w, graphs S bimg w -> well_defined_list bm_ma S.
  Proof.
    induction S; intros; unfold well_defined_list; intros. inversion H0. apply in_inv in H0. simpl in H. destruct_ocon H w.
    destruct H0. subst. unfold graph in H3. destruct H3; [left | right]. hnf in H0; auto. destruct H0; hnf in H0; auto.
    destruct H0 as [l [[? ?] ?]]. rewrite pg_the_same. auto. apply IHS with w23; auto.
  Qed.

  Lemma graph_0_is_emp: forall bimg, graph 0 bimg = emp.
  Proof.
    intros; apply pred_ext; intro w; intros. destruct H as [[? ?] | [l [[? ?] ?]]]. auto.
    rewrite <- pg_the_same in H. apply valid_not_null in H. exfalso; auto. left; split; hnf; auto.
  Qed.

  Lemma graphs_unfold:
    forall S bimg, graphs S bimg =
                   !!(well_defined_list bm_ma S) &&
                     EX l: list adr, !!reachable_set_list b_pg S l &&
                                       iter_sepcon l (graph_cell bm_bi).
  Proof.
    intros; apply pred_ext; intro w; intros. split. repeat intro. rewrite pg_the_same.
    rewrite <- pg_the_same. apply (graphs_list_well_defined _ _ _ H x); auto. revert w H. induction S; intros. simpl in H.
    exists nil. split. intros; split; intro.  destruct H0 as [r [? ?]]. inversion H0. inversion H0. simpl. auto. simpl in H.
    destruct (t_eq_dec a 0). subst. rewrite graph_0_is_emp in H. rewrite ocon_comm, ocon_emp in H. specialize (IHS w H).
    destruct IHS as [l [? ?]]. exists l. split; auto. intro; split; intro. apply H0. destruct H2 as [s [? ?]]. exists s.
    split; auto. apply in_inv in H2. destruct H2. subst. destruct H3 as [ll [[? ?] [? ?]]]. destruct ll; inversion H2.
    subst. assert (valid 0). simpl in H4. destruct ll; auto. destruct H4 as [[? [? ?]] ?]. auto. rewrite <- pg_the_same in H6.
    apply valid_not_null in H6. exfalso; auto. auto. hnf in H0. rewrite <- H0 in H2. destruct H2 as [s [? ?]]. exists s.
    split. apply in_cons; auto. auto. destruct_ocon H w. destruct H2 as [[? ?] | [la [? ?]]]. hnf in H2. exfalso; auto.
    unfold prop in H2. specialize (IHS w23 H3). destruct IHS as [lb [? ?]]. unfold prop in H5.
    assert (sepcon_unique (graph_cell bm_bi)). apply sepcon_unique_graph_cell. assert (NoDup la).
    apply (iter_sepcon_unique_nodup H7 H4). assert (NoDup lb). apply (iter_sepcon_unique_nodup H7 H6).
    destruct (double_list_split t_eq_dec H8 H9) as [i1 [i2 [i3 [? [? ?]]]]]. exists (i1 ++ i2 ++ i3). split. intro.
    split; intros. destruct H13 as [s [? ?]]. apply in_inv in H13. destruct H13. subst. destruct H2. rewrite <- H13 in H14.
    rewrite app_assoc. apply in_or_app. left. apply (Permutation_in x H10 H14). apply in_or_app. right.
    assert (reachable_through_set b_pg S x). exists s; split; auto. rewrite (H5 x) in H15. apply (Permutation_in x H11 H15).
    apply in_app_or in H13. destruct H13. assert (In x (i1 ++ i2)). apply in_or_app; left; auto. apply Permutation_sym in H10.
    apply (Permutation_in x H10) in H14. destruct H2. specialize (H15 x). rewrite H15 in H14. exists a. split. apply in_eq.
    auto. apply Permutation_sym in H11. apply (Permutation_in x H11) in H13. rewrite <- (H5 x) in H13. destruct H13 as [s[? ?]].
    exists s; split; [apply in_cons |]; auto. rewrite (iter_sepcon_permutation _ _ _ H10) in H4. generalize H4; intro.
    rewrite (iter_sepcon_permutation _ _ _ H11) in H6. rewrite iter_sepcon_app_sepcon in H4, H6. destruct_sepcon H4 j.
    destruct_sepcon H6 j. rename j0 into j2'. assert (precise (iter_sepcon i2 (graph_cell bm_bi))). apply precise_iter_sepcon.
    apply precise_graph_cell. try_join w2 w3 w23'; equate_join w23 w23'. assertSub j2 w HS1. assertSub j2' w HS2.
    equate_precise_through (iter_sepcon i2 (graph_cell bm_bi)) j2 j2'.
    assert (((iter_sepcon (i1 ++ i2 ++ i3) (graph_cell bm_bi)) * TT)%pred w). rewrite app_assoc. apply iter_sepcon_app_joinable.
    apply joinable_graph_cell. apply precise_graph_cell. intros. rewrite app_assoc in H12. apply (NoDup_app_not_in _ _ _ H12 x).
    auto. rewrite app_assoc in H12. apply (NoDup_app_l _ _ _ H12). exists w12, w3. split; auto. assertSub j3 w HS.
    destruct HS as [jj ?]. exists j3, jj. split; auto. destruct_sepcon H16 k. rename k1 into k123. rename k2 into k4.
    rewrite app_assoc in H19. rewrite iter_sepcon_app_sepcon in H19. destruct_sepcon H19 k. rename k2 into k3.
    rename k1 into k12. rewrite iter_sepcon_app_sepcon in H22. destruct_sepcon H22 k.
    assert (precise (iter_sepcon i1 (graph_cell bm_bi))). apply precise_iter_sepcon, precise_graph_cell.
    assert (precise (iter_sepcon i3 (graph_cell bm_bi))). apply precise_iter_sepcon, precise_graph_cell. assertSub k1 k123 HS1.
    assertSub k123 w HS2. assertSub k1 w HS3. clear HS1 HS2. assertSub j1 w HS1.
    equate_precise_through (iter_sepcon i1 (graph_cell bm_bi)) j1 k1. assertSub j2 w HS1. assertSub k2 k123 HS2.
    assertSub k123 w HS3. assertSub k2 w HS4. clear HS2 HS3. equate_precise_through (iter_sepcon i2 (graph_cell bm_bi)) j2 k2.
    assertSub j3 w HS1. assertSub k3 w HS2. equate_precise_through (iter_sepcon i3 (graph_cell bm_bi)) j3 k3.
    equate_join w12 k12. assert (k123 = w). apply (overlapping_eq j1 j2 j3 w1 w2 w3 w12 w23); trivial. subst. rewrite app_assoc.
    rewrite iter_sepcon_app_sepcon. exists w12, j3. split; auto.

    (* <- direction *)
    revert w H. induction S; intros; destruct H as [? [l [? ?]]]. hnf in H0. destruct l. auto. specialize (H0 a).
    destruct H0. assert (In a (a :: l)). apply in_eq. specialize (H2 H3). destruct H2 as [s [? ?]]. inversion H2.
    unfold prop in H, H0. destruct (t_eq_dec a 0). subst. simpl. rewrite graph_0_is_emp. rewrite ocon_comm, ocon_emp.
    apply IHS. split. hnf. intros. apply (H x). apply in_cons; auto. exists l; split; auto. intro x. rewrite <- (H0 x).
    split; intros; destruct H2 as [s [? ?]]; exists s. split. apply in_cons; auto. auto. apply in_inv in H2. destruct H2.
    subst. destruct H3 as [ll [[? ?] [? ?]]]. destruct ll; inversion H2. subst. simpl in H4. destruct ll.
    rewrite <- pg_the_same in H4. apply valid_not_null in H4. exfalso; auto. destruct H4 as [[? [? ?]] ?].
    rewrite <- pg_the_same in H4. apply valid_not_null in H4. exfalso; auto. split; auto. simpl. assert (In a (a :: S)).
    apply in_eq. destruct (H a H2). exfalso; auto. rewrite <- pg_the_same in H0.
    destruct (reachable_through_single_reachable bm_ma (a :: S) l H0 a H2 H3) as [l1 [? ?]]. assert (Sublist S (a :: S)).
    apply Sublist_cons. assert (well_defined_list bm_ma S). repeat intro. apply H. apply in_cons; auto.
    destruct (reachable_through_sublist_reachable bm_ma (a :: S) l H0 S H6 H7) as [l2 [? ?]]. assert (NoDup l).
    assert (sepcon_unique (graph_cell bm_bi)). apply sepcon_unique_graph_cell. apply (iter_sepcon_unique_nodup H10 H1).
    assert (l ~= (l1 ++ l2)). split; intro y; intros. apply (H0 y) in H11. rewrite reachable_through_set_eq in H11.
    apply in_or_app. destruct H11; [left | right]. destruct H4. rewrite H12. auto. apply H8. auto. apply in_app_or in H11.
    destruct H11. destruct H4. rewrite H12 in H11. apply H0. exists a. split. apply in_eq. auto. apply H8 in H11.
    apply H0. destruct H11 as [s [? ?]]. exists s; split; auto.
    destruct (tri_list_split t_eq_dec H10 H5 H9 H11) as [i1 [i2 [i3 [? [? ?]]]]].
    rewrite (iter_sepcon_permutation _ _ _ H14) in H1. rewrite iter_sepcon_app_sepcon in H1. destruct_sepcon H1 w.
    rename w2 into w23. generalize H16; intro. rewrite iter_sepcon_app_sepcon in H16. destruct_sepcon H16 w. rename w2 into w3.
    rename w0 into w2. try_join w1 w2 w12. exists w1, w2, w3, w12, w23. do 3 (split; auto). split. unfold graph. right.
    exists l1. split. unfold prop. rewrite <- pg_the_same. auto. rewrite (iter_sepcon_permutation _ _ _ H12).
    assert ((iter_sepcon (i1 ++ i2) (graph_cell bm_bi) * TT)%pred w12). apply iter_sepcon_app_joinable.
    apply joinable_graph_cell. apply precise_graph_cell. apply (Permutation_NoDup H12) in H5. intro x.
    apply (NoDup_app_not_in _ _ _ H5 x). apply (Permutation_NoDup H12) in H5. apply NoDup_app_l in H5. auto.
    exists w1, w2. split; auto. exists w2, w1. split; auto. destruct_sepcon H22 h. rename h1 into h12; rename h2 into h3.
    rewrite iter_sepcon_app_sepcon in H23. destruct_sepcon H23 h. assert (precise (iter_sepcon i1 (graph_cell bm_bi))).
    apply precise_iter_sepcon, precise_graph_cell. assert (precise (iter_sepcon i2 (graph_cell bm_bi))).
    apply precise_iter_sepcon, precise_graph_cell. assertSub w1 w12 HS1. assertSub h1 w12 HS2.
    equate_precise_through (iter_sepcon i1 (graph_cell bm_bi)) w1 h1. assertSub w2 w12 HS1. assertSub h2 w12 HS2.
    equate_precise_through (iter_sepcon i2 (graph_cell bm_bi)) w2 h2. equate_join w12 h12. rewrite iter_sepcon_app_sepcon.
    exists w1, w2. split; auto. apply IHS. split; auto. exists l2. split. unfold prop. rewrite <- pg_the_same. auto.
    rewrite (iter_sepcon_permutation _ _ _ H13). auto.
  Qed.

  Lemma reachable_eq_graphs_eq:
    forall S S' bimg, set_eq (reachable_through_set b_pg S) (reachable_through_set b_pg S') ->
                      well_defined_list bm_ma S -> well_defined_list bm_ma S' ->  graphs S bimg = graphs S' bimg.
  Proof.
    intros. apply pred_ext; intros; intro w; intros; rewrite graphs_unfold in *; destruct H2 as [_ [l [? ?]]]; split. apply H1.
    exists l. split. unfold prop in *. destruct H. unfold subset in *. intro. specialize (H x). specialize (H4 x).
    specialize (H2 x). rewrite <- H2. split; auto. auto. apply H0. exists l. split. unfold prop in *. destruct H.
    unfold subset in *. intro. specialize (H x). specialize (H4 x). specialize (H2 x). rewrite <- H2. split; auto. auto.
  Qed.

  Lemma single_graph_growth_double: forall x d (H: x <> 0), trinode x d x x |-- graph x (single_graph_double 0 natEqDec x d H).
  Proof.
    intros; intro w; intros. unfold graph. right. exists (x :: nil). split. split. unfold valid. simpl. auto. intro.
    split; intro. apply in_inv in H1. destruct H1. subst. apply reachable_by_reflexive. split. unfold valid; simpl; auto.
    hnf; auto. inversion H1. apply reachable_foot_valid in H1. unfold valid in H1. simpl in H1. subst. apply in_eq.
    simpl. rewrite sepcon_emp. hnf. unfold node_label. simpl. apply H0.
  Qed.

  Lemma single_graph_growth_left: forall x d (H: x <> 0), trinode x d x 0 |-- graph x (single_graph_left 0 natEqDec x d H).
  Proof.
    intros; intro w; intros. unfold graph. right. exists (x :: nil). split. split. unfold valid. simpl. auto. intro.
    split; intro. apply in_inv in H1. destruct H1. subst. apply reachable_by_reflexive. split. unfold valid; simpl; auto.
    hnf; auto. inversion H1. apply reachable_foot_valid in H1. unfold valid in H1. simpl in H1. subst. apply in_eq.
    simpl. rewrite sepcon_emp. hnf. unfold node_label. simpl. apply H0.
  Qed.

  Lemma single_graph_growth_right: forall x d (H: x <> 0), trinode x d 0 x |-- graph x (single_graph_right 0 natEqDec x d H).
  Proof.
    intros; intro w; intros. unfold graph. right. exists (x :: nil). split. split. unfold valid. simpl. auto. intro.
    split; intro. apply in_inv in H1. destruct H1. subst. apply reachable_by_reflexive. split. unfold valid; simpl; auto.
    hnf; auto. inversion H1. apply reachable_foot_valid in H1. unfold valid in H1. simpl in H1. subst. apply in_eq.
    simpl. rewrite sepcon_emp. hnf. unfold node_label. simpl. apply H0.
  Qed.

  Lemma separate_not_in:
    forall {x d l r} {wx w1 w2 w12 w3 wlr w : world} {ll : list adr} {bg},
      join wx wlr w -> join w1 w2 w12 -> join w12 w3 wlr -> trinode x d l r wx -> iter_sepcon ll (graph_cell bg) w12 ->
      forall y, In y ll -> y <> x.
  Proof.
    intros. intro. subst. apply in_split in H4. destruct H4 as [l1 [l2 ?]]. subst. generalize (Permutation_middle l1 l2 x).
    intro. apply Permutation_sym in H4. rewrite (iter_sepcon_permutation _ _ _ H4) in H3. clear H4. simpl in H3.
    destruct_sepcon H3 w. destruct H2. destruct_sepcon H6 w. destruct_sepcon H7 w. try_join w8 w6 t1. try_join w7 wlr t2.
    try_join w7 w12 t3. try_join w7 w0 t4. hnf in H4. destruct (@gamma adr nat natEqDec bg x) as [[d0 l0] r0].
    unfold trinode in H4. destruct H4. destruct_sepcon H19 w. destruct_sepcon H20 w. try_join w7 w9 t5. try_join w7 w11 w711.
    assert ((mapsto x d * mapsto x d0)%pred w711). exists w7, w11. split; auto. apply mapsto_unique in H28. auto.
  Qed.

  Lemma graphs_growth: forall (x: adr) (d: nat) l r (Hn: x <> 0) (g: BiMathGraph adr nat 0) (Hi: in_math bm_ma x l r),
                         (trinode x d l r * graphs (l :: r :: nil) g) |-- graph x (update_graph g x d l r Hi Hn).
  Proof.
    intros. intro w; intros. rewrite graph_unfold. right. exists d, l, r. rewrite ocon_assoc. split. split. simpl.
    destruct (gamma (update_BiGraph bm_bi x d l r) x) as [[dd ll] rr] eqn:? . unfold gamma in Heqp. unfold biEdge in Heqp.
    destruct (@only_two_neighbours adr nat natEqDec (@update_BiGraph adr nat natEqDec bm_bi x d l r) x) as [v1 [v2 ?]].
    simpl in e, Heqp. unfold change_edge_func in e. unfold change_node_label in Heqp. simpl in e, Heqp.
    destruct (eq_nat_dec x x). inversion Heqp. subst. inversion e. subst. auto. exfalso; auto. simpl. unfold change_valid.
    right; auto. apply sepcon_ocon. destruct_sepcon H w. rename w1 into wx; rename w2 into wlr. exists wx, wlr.
    do 2 (split; auto). simpl in H1. rewrite ocon_emp in H1. destruct_ocon H1 w. exists w1, w2, w3, w12, w23.
    do 3 (split; auto). split.

    (* left part *)

    unfold graph in H4. destruct H4. left. auto. right. destruct H4 as [ll [? ?]]. exists ll. destruct H4.
    assert (forall y, In y ll -> y <> x). apply (separate_not_in H H1 H3 H0 H6). split. split. simpl. unfold change_valid.
    left; apply H4. simpl. intros. rewrite H7. split; intro. destruct H9 as [p [? ?]]. exists p.
    assert (forall z, In z p -> In z ll). intros. rewrite H7. apply (reachable_path_in b_pg p l y). split; auto. auto.
    split. auto. split. destruct H10. clear H9 H12. induction p. simpl; auto. simpl. simpl in H10. destruct p.
    unfold change_valid; left; auto. destruct H10. destruct H9 as [? [? ?]]. split. split.
    simpl; unfold change_valid; left; auto. split. simpl; unfold change_valid; left. auto. simpl. unfold change_edge_func.
    simpl. destruct (eq_nat_dec a x). assert (In a (a :: a0 :: p)). apply in_eq. specialize (H11 a H14). specialize (H8 a H11).
    exfalso; auto. auto. apply IHp. auto. intros. apply H11. apply in_cons; auto. repeat intro; hnf; auto.
    destruct H9 as [p ?]. assert (In x p -> reachable b_pg l x) as Hix. assert (l <> x). assert (reachable b_pg l l).
    apply reachable_by_reflexive. split. auto. hnf. auto. rewrite <- H7 in H10. specialize (H8 l H10). auto. intros.
    apply (update_reachable_path_in Hn H10 H9 H11). destruct H9 as [? [? ?]]. exists p. split. auto. split.
    assert (forall z, In z p -> z <> x). intros. intro. subst. specialize (Hix H12). rewrite <- H7 in Hix.
    specialize (H8 _ Hix). auto. clear Hix.

    clear H11 H9. induction p. simpl. auto. simpl in H10. simpl. destruct p.
    unfold change_valid in H10. destruct H10; auto. assert (In a (a :: nil)) by apply in_eq. specialize (H12 a H10).
    exfalso; auto. destruct H10 as [[? [? ?]] ?]. split. split. simpl in H9. unfold change_valid in H9. destruct H9; auto.
    subst. assert (x <> x). apply H12. apply in_eq. exfalso. auto. split. simpl in H10. unfold change_valid in H10.
    destruct H10; auto. subst. assert (x <> x). apply H12. apply in_cons. apply in_eq. exfalso; auto. simpl in H11.
    unfold change_edge_func in H11. simpl in H11. destruct (eq_nat_dec a x). subst. assert (x <> x). apply H12. apply in_eq.
    exfalso; auto. auto. apply IHp. auto. intros. apply H12. apply in_cons. auto. repeat intro; hnf; auto.

    clear H7 H1 H3. revert w12 H6 H8. induction ll; intros; simpl; simpl in H6. auto. destruct_sepcon H6 h. exists h1, h2.
    split; auto. split. destruct (only_two_neighbours a) as [a1 [a2 ?]]. apply (graph_cell_trinode _ _ _ _ e) in H3.
    unfold graph_cell, gamma. destruct (@biEdge adr nat natEqDec (@update_BiGraph adr nat natEqDec bm_bi x d l r) a) eqn:? .
    unfold biEdge in Heqp. destruct (only_two_neighbours a) as [v1 [v2 ?]] in Heqp. inversion Heqp. subst. simpl in e0.
    unfold change_edge_func in e0. simpl in e0. assert (In a (a :: ll)) by apply in_eq. specialize (H8 _ H7).
    destruct (eq_nat_dec a x). exfalso; auto. rewrite e in e0. inversion e0. subst. simpl. unfold change_node_label. simpl.
    destruct (eq_nat_dec a x). exfalso; auto. apply H3. simpl in IHll. apply IHll. auto. intros. apply H8. apply in_cons; auto.

    (* right part *)

    unfold graph in H5. destruct H5. left. auto. right. destruct H5 as [ll [? ?]]. exists ll. destruct H5.
    assert (forall y, In y ll -> y <> x). try_join w2 w3 w23'; equate_join w23 w23'. apply join_comm in H9.
    apply (separate_not_in H H2 H9 H0 H6). split. split. simpl. unfold change_valid. left; apply H5. simpl. intros. rewrite H7.
    split; intro. destruct H9 as [p [? ?]]. exists p. assert (forall z, In z p -> In z ll). intros. rewrite H7.
    apply (reachable_path_in b_pg p r y). split; auto. auto. split. auto. split. destruct H10. clear H9 H12. induction p.
    simpl; auto. simpl. simpl in H10. destruct p. unfold change_valid; left; auto. destruct H10. destruct H9 as [? [? ?]].
    split. split. simpl; unfold change_valid; left; auto. split. simpl; unfold change_valid; left. auto. simpl.
    unfold change_edge_func. simpl. destruct (eq_nat_dec a x). assert (In a (a :: a0 :: p)). apply in_eq.
    specialize (H11 a H14). specialize (H8 a H11). exfalso; auto. auto. apply IHp. auto. intros. apply H11. apply in_cons; auto.
    repeat intro; hnf; auto.

    destruct H9 as [p ?]. assert (In x p -> reachable b_pg r x) as Hix. assert (r <> x). assert (reachable b_pg r r).
    apply reachable_by_reflexive. split. auto. hnf. auto. rewrite <- H7 in H10. specialize (H8 r H10). auto. intros.
    apply (update_reachable_path_in Hn H10 H9 H11). destruct H9 as [? [? ?]]. exists p. split. auto. split.
    assert (forall z, In z p -> z <> x). intros. intro. subst. specialize (Hix H12). rewrite <- H7 in Hix.
    specialize (H8 _ Hix). auto. clear Hix.

    clear H11 H9. induction p. simpl. auto. simpl in H10. simpl. destruct p. unfold change_valid in H10. destruct H10; auto.
    assert (In a (a :: nil)) by apply in_eq. specialize (H12 a H10). exfalso; auto. destruct H10 as [[? [? ?]] ?]. split. split.
    simpl in H9. unfold change_valid in H9. destruct H9; auto. subst. assert (x <> x). apply H12. apply in_eq. exfalso. auto.
    split. simpl in H10. unfold change_valid in H10. destruct H10; auto. subst. assert (x <> x). apply H12. apply in_cons.
    apply in_eq. exfalso; auto. simpl in H11. unfold change_edge_func in H11. simpl in H11. destruct (eq_nat_dec a x).
    subst. assert (x <> x). apply H12. apply in_eq. exfalso; auto. auto. apply IHp. auto. intros. apply H12. apply in_cons.
    auto. repeat intro; hnf; auto.

    clear H7 H2. revert w23 H6 H8. induction ll; intros; simpl; simpl in H6. auto. destruct_sepcon H6 h. exists h1, h2.
    split; auto. split. destruct (only_two_neighbours a) as [a1 [a2 ?]]. apply (graph_cell_trinode _ _ _ _ e) in H6.
    unfold graph_cell, gamma. destruct (@biEdge adr nat natEqDec (@update_BiGraph adr nat natEqDec bm_bi x d l r) a) eqn:? .
    unfold biEdge in Heqp. destruct (only_two_neighbours a) as [v1 [v2 ?]] in Heqp. inversion Heqp. subst. simpl in e0.
    unfold change_edge_func in e0. simpl in e0. assert (In a (a :: ll)) by apply in_eq. specialize (H8 _ H9).
    destruct (eq_nat_dec a x). exfalso; auto. rewrite e in e0. inversion e0. subst. simpl. unfold change_node_label. simpl.
    destruct (eq_nat_dec a x). exfalso; auto. apply H6. simpl in IHll. apply IHll. auto. intros. apply H8. apply in_cons; auto.
  Qed.

  Lemma graph_growth_right: forall (x: adr) (d: nat) r (Hn: x <> 0) (g: BiMathGraph adr nat 0) (Hi: in_math bm_ma x x r),
                              trinode x d x r * graph r g |-- graph x (update_graph g x d x r Hi Hn).
  Proof.
    intros. intro w; intros. destruct_sepcon H w. unfold graph in *. right. destruct H1. destruct H1. hnf in H1. subst.
    exists (x :: nil). split. split. simpl. unfold change_valid. right. auto. intro. split; intro. apply in_inv in H1.
    destruct H1. subst. apply reachable_by_reflexive. split. simpl; unfold change_valid; right; auto. hnf; auto. inversion H1.
    apply reachable_acyclic in H1. destruct H1 as [p [? ?]]. destruct H3 as [[? ?] [? ?]]. destruct p. inversion H3. simpl in H3.
    inversion H3. subst. destruct p. simpl in H4. inversion H4. subst. apply in_eq. rewrite <- (app_nil_l p) in H5.
    do 2 rewrite app_comm_cons in H5. apply valid_path_split in H5. destruct H5. simpl in H5. destruct H5 as [[? [? ?]] _].
    simpl in H9. unfold change_edge_func in H9. simpl in H9. destruct (eq_nat_dec x x). apply in_inv in H9. destruct H9. subst.
    apply NoDup_cons_2 in H1. exfalso; apply H1, in_eq. apply in_inv in H9. destruct H9. subst. simpl in H8.
    unfold change_valid in H8. destruct H8. rewrite <- pg_the_same in H8. apply valid_not_null in H8. exfalso; auto. exfalso.
    auto. inversion H9. exfalso; auto. simpl. exists w1, w2. do 2 (split; auto). apply (trinode_graph_cell x 0). simpl.
    unfold change_edge_func. simpl. destruct (eq_nat_dec x x). auto. exfalso; auto. simpl. unfold change_node_label. simpl.
    destruct (eq_nat_dec x x). auto. exfalso; auto.

    destruct H1 as [ll [? ?]]. assert (unit_for (core w2) w2) as Ht. apply core_unit. unfold unit_for in Ht.
    apply join_comm in Ht. assert (forall y, In y ll -> y <> x). intros. apply (separate_not_in H Ht Ht H0 H2 y H3). clear Ht.
    exists (x :: ll). split. split. simpl; unfold change_valid; right; auto. intros. split; intro. apply in_inv in H4. simpl.
    destruct H4. apply eq_sym in H4; subst. apply reachable_by_reflexive. split. simpl; unfold change_valid; right; auto.
    hnf; auto. destruct H1. rewrite H5 in H4. destruct H4 as [p ?]. assert (forall z, In z p -> In z ll). intros. rewrite H5.
    apply (reachable_path_in b_pg p r y). auto. auto. destruct H4 as [[? ?] [? ?]]. exists (x :: p). split; split. simpl. auto.
    generalize (foot_in _ _ H7); intro. rewrite <- (app_nil_l p). rewrite app_comm_cons. rewrite foot_app. auto. intro. subst.
    inversion H10. simpl. destruct p. unfold change_valid. right; auto. simpl in H4. inversion H4. subst. split. split. simpl.
    unfold change_valid; right; auto. split. simpl; unfold change_valid; left; auto. simpl; unfold change_edge_func; simpl.
    destruct (eq_nat_dec x x). apply in_cons, in_eq. exfalso; auto. remember (@cons adr r p) as pa. clear Heqpa H7 H9.
    assert (forall z, In z pa -> valid z). intros. apply H6 in H7. rewrite H5 in H7. apply reachable_foot_valid in H7. auto.
    induction pa. simpl; auto. simpl. destruct pa. unfold change_valid. left. apply H7. apply in_eq. split. assert (a <> x).
    apply H3. apply H6. apply in_eq. rewrite <-(app_nil_l pa) in H8. do 2 rewrite app_comm_cons in H8.
    apply valid_path_split in H8. destruct H8. simpl in H8. destruct H8 as [[? [? ?]] _]. split. simpl; unfold change_valid.
    left; auto. split. simpl; unfold change_valid; left; auto. simpl. unfold change_edge_func. simpl. destruct (eq_nat_dec a x).
    exfalso; auto. auto. apply IHpa. rewrite <- (app_nil_l (a0 :: pa)) in H8. rewrite app_comm_cons in H8.
    apply valid_path_split in H8. destruct H8. auto. intros. apply H6. apply in_cons; auto. intros. apply H7. apply in_cons.
    auto. repeat intro; hnf; auto. simpl in H4. destruct (eq_nat_dec y x). subst. apply in_eq. apply reachable_acyclic in H4.
    destruct H4 as [p [? ?]]. destruct p. destruct H5 as [[? _] _]. inversion H5. assert (a = x). destruct H5 as [[? _] _].
    simpl in H5. inversion H5. auto. subst. destruct p. destruct H5 as [[_ ?] _]. simpl in H5. inversion H5. exfalso; auto.
    assert (a = r). destruct H5 as [_ [? _]]. rewrite <- (app_nil_l p) in H5. do 2 rewrite app_comm_cons in H5.
    apply valid_path_split in H5. destruct H5. simpl in H5. destruct H5 as [[_ [_ ?]] _]. simpl in H5.
    unfold change_edge_func in H5. simpl in H5. destruct (eq_nat_dec x x). simpl in H5. destruct H5. subst.
    apply NoDup_cons_2 in H4. exfalso; apply H4. apply in_eq. destruct H5. auto. exfalso; auto. exfalso; auto. subst.
    right. destruct H1. rewrite H6. apply (update_reachable_tail_reachable H4 H5).

    simpl. exists w1, w2. split; auto. split. apply (trinode_graph_cell x r). simpl. unfold change_edge_func. simpl.
    destruct (eq_nat_dec x x). auto. exfalso; auto. simpl. unfold change_node_label. simpl. destruct (eq_nat_dec x x). auto.
    exfalso; auto. clear H1 H. revert w2 H2 H3. induction ll; intros; simpl; simpl in H2. auto. destruct_sepcon H2 h.
    exists h1, h2. split; auto. split. destruct (only_two_neighbours a) as [a1 [a2 ?]].
    apply (graph_cell_trinode _ _ _ _ e) in H1. unfold graph_cell, gamma.
    destruct (@biEdge adr nat natEqDec (@update_BiGraph adr nat natEqDec bm_bi x d x r) a) eqn:? .
    unfold biEdge in Heqp. destruct (only_two_neighbours a) as [v1 [v2 ?]] in Heqp. inversion Heqp. subst. simpl in e0.
    unfold change_edge_func in e0. simpl in e0. assert (In a (a :: ll)) by apply in_eq. specialize (H3 _ H4).
    destruct (eq_nat_dec a x). exfalso; auto. rewrite e in e0. inversion e0. subst. simpl. unfold change_node_label. simpl.
    destruct (eq_nat_dec a x). exfalso; auto. apply H1. simpl in IHll. apply IHll. auto. intros. apply H3. apply in_cons; auto.
  Qed.

  Lemma graph_growth_left: forall (x: adr) (d: nat) l (Hn: x <> 0) (g: BiMathGraph adr nat 0) (Hi: in_math bm_ma x l x),
                              trinode x d l x * graph l g |-- graph x (update_graph g x d l x Hi Hn).
  Proof.
    intros. intro w; intros. destruct_sepcon H w. unfold graph in *. right. destruct H1. destruct H1. hnf in H1. subst.
    exists (x :: nil). split. split. simpl. unfold change_valid. right. auto. intro. split; intro. apply in_inv in H1.
    destruct H1. subst. apply reachable_by_reflexive. split. simpl; unfold change_valid; right; auto. hnf; auto. inversion H1.
    apply reachable_acyclic in H1. destruct H1 as [p [? ?]]. destruct H3 as [[? ?] [? ?]]. destruct p. inversion H3. simpl in H3.
    inversion H3. subst. destruct p. simpl in H4. inversion H4. subst. apply in_eq. rewrite <- (app_nil_l p) in H5.
    do 2 rewrite app_comm_cons in H5. apply valid_path_split in H5. destruct H5. simpl in H5. destruct H5 as [[? [? ?]] _].
    simpl in H9. unfold change_edge_func in H9. simpl in H9. destruct (eq_nat_dec x x). apply in_inv in H9. destruct H9. subst.
    simpl in H8. unfold change_valid in H8. destruct H8. rewrite <- pg_the_same in H8. apply valid_not_null in H8.
    exfalso; auto. exfalso. auto. apply in_inv in H9. destruct H9. subst. apply NoDup_cons_2 in H1. exfalso; apply H1, in_eq.
    inversion H9. exfalso; auto. simpl. exists w1, w2. do 2 (split; auto). apply (trinode_graph_cell 0 x). simpl.
    unfold change_edge_func. simpl. destruct (eq_nat_dec x x). auto. exfalso; auto. simpl. unfold change_node_label. simpl.
    destruct (eq_nat_dec x x). auto. exfalso; auto.

    destruct H1 as [ll [? ?]]. assert (unit_for (core w2) w2) as Ht. apply core_unit. unfold unit_for in Ht.
    apply join_comm in Ht. assert (forall y, In y ll -> y <> x). intros. apply (separate_not_in H Ht Ht H0 H2 y H3). clear Ht.
    exists (x :: ll). split. split. simpl; unfold change_valid; right; auto. intros. split; intro. apply in_inv in H4. simpl.
    destruct H4. apply eq_sym in H4; subst. apply reachable_by_reflexive. split. simpl; unfold change_valid; right; auto.
    hnf; auto. destruct H1. rewrite H5 in H4. destruct H4 as [p ?]. assert (forall z, In z p -> In z ll). intros. rewrite H5.
    apply (reachable_path_in b_pg p l y). auto. auto. destruct H4 as [[? ?] [? ?]]. exists (x :: p). split; split. simpl. auto.
    generalize (foot_in _ _ H7); intro. rewrite <- (app_nil_l p). rewrite app_comm_cons. rewrite foot_app. auto. intro. subst.
    inversion H10. simpl. destruct p. unfold change_valid. right; auto. simpl in H4. inversion H4. subst. split. split. simpl.
    unfold change_valid; right; auto. split. simpl; unfold change_valid; left; auto. simpl; unfold change_edge_func; simpl.
    destruct (eq_nat_dec x x). apply in_eq. exfalso; auto. remember (@cons adr l p) as pa. clear Heqpa H7 H9.
    assert (forall z, In z pa -> valid z). intros. apply H6 in H7. rewrite H5 in H7. apply reachable_foot_valid in H7. auto.
    induction pa. simpl; auto. simpl. destruct pa. unfold change_valid. left. apply H7. apply in_eq. split. assert (a <> x).
    apply H3. apply H6. apply in_eq. rewrite <-(app_nil_l pa) in H8. do 2 rewrite app_comm_cons in H8.
    apply valid_path_split in H8. destruct H8. simpl in H8. destruct H8 as [[? [? ?]] _]. split. simpl; unfold change_valid.
    left; auto. split. simpl; unfold change_valid; left; auto. simpl. unfold change_edge_func. simpl. destruct (eq_nat_dec a x).
    exfalso; auto. auto. apply IHpa. rewrite <- (app_nil_l (a0 :: pa)) in H8. rewrite app_comm_cons in H8.
    apply valid_path_split in H8. destruct H8. auto. intros. apply H6. apply in_cons; auto. intros. apply H7. apply in_cons.
    auto. repeat intro; hnf; auto. simpl in H4. destruct (eq_nat_dec y x). subst. apply in_eq. apply reachable_acyclic in H4.
    destruct H4 as [p [? ?]]. destruct p. destruct H5 as [[? _] _]. inversion H5. assert (a = x). destruct H5 as [[? _] _].
    simpl in H5. inversion H5. auto. subst. destruct p. destruct H5 as [[_ ?] _]. simpl in H5. inversion H5. exfalso; auto.
    assert (a = l). destruct H5 as [_ [? _]]. rewrite <- (app_nil_l p) in H5. do 2 rewrite app_comm_cons in H5.
    apply valid_path_split in H5. destruct H5. simpl in H5. destruct H5 as [[_ [_ ?]] _]. simpl in H5.
    unfold change_edge_func in H5. simpl in H5. destruct (eq_nat_dec x x). simpl in H5. destruct H5. auto. destruct H5.
    subst. apply NoDup_cons_2 in H4. exfalso; apply H4. apply in_eq. exfalso; auto. exfalso; auto. subst. right. destruct H1.
    rewrite H6. apply (update_reachable_tail_reachable H4 H5).

    simpl. exists w1, w2. split; auto. split. apply (trinode_graph_cell l x). simpl. unfold change_edge_func. simpl.
    destruct (eq_nat_dec x x). auto. exfalso; auto. simpl. unfold change_node_label. simpl. destruct (eq_nat_dec x x). auto.
    exfalso; auto. clear H1 H. revert w2 H2 H3. induction ll; intros; simpl; simpl in H2. auto. destruct_sepcon H2 h.
    exists h1, h2. split; auto. split. destruct (only_two_neighbours a) as [a1 [a2 ?]].
    apply (graph_cell_trinode _ _ _ _ e) in H1. unfold graph_cell, gamma.
    destruct (@biEdge adr nat natEqDec (@update_BiGraph adr nat natEqDec bm_bi x d l x) a) eqn:? .
    unfold biEdge in Heqp. destruct (only_two_neighbours a) as [v1 [v2 ?]] in Heqp. inversion Heqp. subst. simpl in e0.
    unfold change_edge_func in e0. simpl in e0. assert (In a (a :: ll)) by apply in_eq. specialize (H3 _ H4).
    destruct (eq_nat_dec a x). exfalso; auto. rewrite e in e0. inversion e0. subst. simpl. unfold change_node_label. simpl.
    destruct (eq_nat_dec a x). exfalso; auto. apply H1. simpl in IHll. apply IHll. auto. intros. apply H3. apply in_cons; auto.
  Qed.

  Lemma iter_sepcon_not_in_eq:
    forall {g : BiGraph adr nat} {x : adr} {li : list adr} {d: nat} {l r : adr},
      ~ In x li -> iter_sepcon li (graph_cell (update_BiGraph g x d l r)) = iter_sepcon li (graph_cell g).
  Proof.
    intros; apply pred_ext; intro w; intro; revert w H0; induction li; intros; simpl; simpl in H0; auto;
    assert (a <> x) by (intro; subst; apply H, in_eq); destruct_sepcon H0 w; exists w1, w2; split; auto; split.
    unfold graph_cell, gamma, biEdge in H2; unfold graph_cell, gamma, biEdge.
    destruct (@only_two_neighbours adr nat natEqDec g a) as [v1 [v2 ?]].
    destruct (@only_two_neighbours adr nat natEqDec (@update_BiGraph adr nat natEqDec g x d l r) a) as [u1 [u2 ?]].
    simpl in e0. unfold change_edge_func in e0. destruct (t_eq_dec a x). exfalso; auto. rewrite e in e0. inversion e0. subst.
    simpl in H2. unfold change_node_label in H2. destruct (t_eq_dec a x). exfalso; auto. auto. apply IHli. intro; apply H.
    apply in_cons; auto. auto.

    unfold graph_cell, gamma, biEdge in H2; unfold graph_cell, gamma, biEdge.
    destruct (@only_two_neighbours adr nat natEqDec g a) as [v1 [v2 ?]].
    destruct (@only_two_neighbours adr nat natEqDec (@update_BiGraph adr nat natEqDec g x d l r) a) as [u1 [u2 ?]].
    simpl in e0. unfold change_edge_func in e0. destruct (t_eq_dec a x). exfalso; auto. rewrite e in e0. inversion e0. subst.
    simpl. unfold change_node_label. destruct (t_eq_dec a x). exfalso; auto. auto. apply IHli. intro; apply H; apply in_cons.
    auto. auto.
  Qed.

  Lemma single_graph_node_update_1:
    forall (g: BiMathGraph adr nat 0) (x: adr) (d: nat) (l r: adr) (d': nat) (l' r': adr) (g': BiMathGraph adr nat 0)
           (Hn: x <> 0) (Hi: in_math bm_ma x l' r') S,
      @gamma adr nat natEqDec (@bm_bi adr nat O natEqDec g) x = (d, l, r) -> g' = update_graph g x d' l' r' Hi Hn ->
      graphs ((x :: l' :: r' ::nil) ++ S) g |-- trinode x d l r * (trinode x d' l' r' -* graphs ((x :: l :: r ::nil) ++ S) g').
  Proof.
    intros; intro w; intros. remember (l' :: r' :: S) as nx. simpl in H1. assert ((graph x g ⊗ graphs nx g) w). subst. simpl.
    auto. clear H1. remember (l :: r :: nx) as li. assert ((trinode x d l r ⊗ graphs li g) w). destruct_ocon H2 h.
    rewrite graph_unfold in H4. destruct H4 as [[? ?] | ?]. hnf in H4. exfalso; auto. destruct H4 as [dd [ll [rr [[? ?] ?]]]].
    rewrite H in H4. apply eq_sym in H4. inversion H4. subst. clear H4.
    assert (((trinode x d l r ⊗ graph l g ⊗ graph r g) ⊗ graphs (l' :: r' :: S) g) w). exists h1, h2, h3, h12, h23. split; auto.
    simpl in H0. do 2 rewrite ocon_assoc in H0. simpl. auto. rewrite Heqnx in Heqli. clear Heqnx. clear H2; generalize H1.
    intro. destruct_ocon H1 h. try_join h2 h3 h23'; equate_join h23 h23'. rewrite graphs_unfold in H6. destruct H6. hnf in H6.
    destruct H7 as [ll [? ?]]. assert (NoDup ll). assert (sepcon_unique (graph_cell (@bm_bi adr nat O natEqDec g))).
    apply sepcon_unique_graph_cell. apply (iter_sepcon_unique_nodup H10 H9). destruct (in_dec eq_nat_dec x ll).

    (* In x ll *)

    (* make heap clear *)
    apply in_split in i. destruct i as [l1 [l2 ?]]. rewrite H11 in *. clear H11 ll. generalize (Permutation_middle l1 l2 x).
    intro. apply Permutation_sym in H11. rewrite (iter_sepcon_permutation _ _ _ H11) in H9. clear H11. simpl in H9.
    destruct_sepcon H9 t. unfold graph_cell in H11. rewrite H in H11. assert (precise (trinode x d l r)). apply precise_trinode.
    assertSub h12 w HS1. assertSub t1 w HS2. equate_precise_through (trinode x d l r) h12 t1. assert (emp h1).
    assertSub h1 h23 HS. assert (joins h1 h23). exists w. auto. apply (join_sub_joins_identity HS H11).
    apply (join_unit1_e _ _ H11) in H1. rewrite <- H1 in *. clear H1 h12. apply (join_unit1_e _ _ H11) in H8. rewrite H8 in *.
    clear H8 h23 H11 h1. apply join_comm in H4. apply join_comm in H9. generalize (join_canc H9 H4); intro. rewrite H1 in *.
    clear H1 t2 H4 H9 H13. exists h2, h3. do 2 (split; auto). intros h2' w'; intros. rewrite graphs_unfold. split.

    (* well_defined_list part *)
    hnf. intro y; intros. simpl in H8. destruct H8. subst. right. simpl. unfold change_valid. right; auto. destruct H8. subst.
    simpl. unfold change_valid. assert (In y (y :: r :: l' :: r' :: S)). apply in_eq. specialize (H6 _ H0).
    destruct H6; [left | right; left]; auto. destruct H8. subst. simpl. unfold change_valid.
    assert (In y (l :: y :: l' :: r' :: S)). apply in_cons, in_eq. specialize (H6 _ H0). destruct H6; [left|right; left]; auto.
    subst; simpl; unfold change_valid. assert (In y (l :: r :: l' :: r' :: S)). do 4 apply in_cons. auto. specialize (H6 _ H0).
    destruct H6; [left | right; left]; auto.

    exists (x :: l1 ++ l2). subst. hnf in H7. split.

    (* reachable_set_list part *)
    hnf. intro y. assert (In y (x :: l1 ++ l2) <-> In y (l1 ++ x :: l2)). generalize (Permutation_middle l1 l2 x); intro.
    split; intros. apply (Permutation_in y H0 H8). apply Permutation_sym in H0. apply (Permutation_in y H0 H8). split; intros.

    (* -> direction *)
    destruct (eq_nat_dec y x). subst. apply in_eq. simpl in H8. rewrite H0. rewrite <- (H7 y). destruct H8 as [s [? ?]].
    unfold reachable_through_set. apply reachable_acyclic in H9. destruct H9 as [p [? ?]]. destruct (in_dec t_eq_dec x p).
    destruct (reachable_by_path_split_in _ _ _ _ _ _ _ _ _ H11 i) as [p1 [p2 [? [? ?]]]]. apply reachable_by_path_foot in H14.
    apply foot_explicit in H14. destruct H14 as [p1h ?]. rewrite H14 in *; clear H14 p1; rename p1h into p1.
    generalize H15; intro; apply reachable_by_path_head in H14. unfold path_glue in H13. destruct p2. inversion H14.
    inversion H14. rewrite H17 in *; clear H17 a H14. simpl in H13. rewrite <- app_cons_assoc in H13. subst.
    apply NoDup_app_r in H9. clear H11 i p1. destruct p2. apply reachable_by_path_foot in H15. inversion H15. exfalso; auto.
    assert (a = l' \/ a = r'). destruct H15 as [_ [? _]]. rewrite <- (app_nil_l p2) in H11. do 2 rewrite app_comm_cons in H11.
    apply valid_path_split in H11. destruct H11. simpl in H11. destruct H11 as [[_ [_ ?]] _].
    simpl in H11. unfold change_edge_func in H11. simpl in H11. destruct (eq_nat_dec x x). simpl in H11. destruct H11.
    left; auto. destruct H11. right; auto. exfalso; auto. exfalso; auto. destruct H11. subst. exists l'. split.
    do 2 apply in_cons. apply in_eq. apply (update_reachable_tail_reachable H9 H15). subst. exists r'. split.
    do 3 apply in_cons. apply in_eq. apply (update_reachable_tail_reachable H9 H15). apply in_inv in H8. destruct H8.
    apply eq_sym in H8. subst. destruct p. apply reachable_by_path_foot in H11. inversion H11.
    apply reachable_by_path_head in H11. simpl in H11. inversion H11. subst. exfalso; apply n0, in_eq. exists s. split.
    simpl in H8. destruct H8 as [? | [? | ?]]; subst. apply in_eq. apply in_cons, in_eq. do 4 apply in_cons. auto.
    exists p. rewrite (update_reachable_by_path_not_in n0) in H11. auto.

    (* <- direction *)
    destruct (eq_nat_dec y x). subst. exists x. split. simpl. left; auto. apply reachable_by_reflexive. split. simpl.
    unfold change_valid. right; auto. repeat intro; hnf; auto. simpl. rewrite H0 in H8. rewrite <- (H7 y) in H8.
    destruct H8 as [s [? ?]]. apply reachable_acyclic in H9. destruct H9 as [p [? ?]]. destruct (in_dec t_eq_dec x p).

    (* In x p *)
    destruct (reachable_by_path_split_in _ _ _ _ _ _ _ _ _ H11 i) as [p1 [p2 [? [? ?]]]]. apply reachable_by_path_foot in H14.
    apply foot_explicit in H14. destruct H14 as [p1h ?]. rewrite H14 in *; clear H14 p1; rename p1h into p1.
    generalize H15; intro; apply reachable_by_path_head in H14. unfold path_glue in H13. destruct p2. inversion H14.
    inversion H14. rewrite H17 in *; clear H17 a H14. simpl in H13. rewrite <- app_cons_assoc in H13. subst.
    apply NoDup_app_r in H9. clear H11 i p1. destruct p2. apply reachable_by_path_foot in H15. inversion H15. exfalso; auto.
    assert (a = l \/ a = r). destruct H15 as [_ [? _]]. rewrite <- (app_nil_l p2) in H11. do 2 rewrite app_comm_cons in H11.
    apply valid_path_split in H11. destruct H11. simpl in H11. destruct H11 as [[_ [_ ?]] _]. unfold gamma, biEdge in H.
    destruct (only_two_neighbours x) as [v1 [v2 ?]]. inversion H. subst. rewrite e in H11. simpl in H11. destruct H11.
    left; auto. destruct H11. right; auto. exfalso; auto. destruct H11. subst. exists l. split. apply in_cons, in_eq.
    assert (paths_meet_at _ (x :: l :: nil) (l :: p2) l). unfold paths_meet_at. split; simpl; auto.
    assert (x :: l :: p2 = path_glue _ (x :: l :: nil) (l :: p2)). unfold path_glue. simpl. auto. rewrite H13 in H15.
    destruct (reachable_by_path_split_glue _ _ _ _ _ _ _ _ _ _ H11 H15). exists (l :: p2). apply NoDup_cons_2 in H9.
    rewrite (update_reachable_by_path_not_in H9). auto. subst. exists r. split. do 2 apply in_cons. apply in_eq.
    assert (paths_meet_at _ (x :: r :: nil) (r :: p2) r). unfold paths_meet_at. split; simpl; auto.
    assert (x :: r :: p2 = path_glue _ (x :: r :: nil) (r :: p2)). unfold path_glue. simpl. auto. rewrite H13 in H15.
    destruct (reachable_by_path_split_glue _ _ _ _ _ _ _ _ _ _ H11 H15). exists (r :: p2). apply NoDup_cons_2 in H9.
    rewrite (update_reachable_by_path_not_in H9). auto.

    (* In l' p *)
    destruct (in_dec t_eq_dec l' p). destruct (reachable_by_path_split_in _ _ _ _ _ _ _ _ _ H11 i) as [p1 [p2 [? [? ?]]]].
    apply reachable_by_path_foot in H14. apply foot_explicit in H14. destruct H14 as [p1h ?]. rewrite H14 in *; clear H14 p1.
    rename p1h into p1. generalize H15; intro; apply reachable_by_path_head in H14. unfold path_glue in H13. destruct p2.
    inversion H14. inversion H14. rewrite H17 in *; clear H17 a H14. simpl in H13. rewrite <- app_cons_assoc in H13. subst.
    apply NoDup_app_r in H9. assert (~ In x (l' :: p2)). intro; apply n0; apply in_or_app; right; auto. clear H11 i n0 p1.
    exists x. split. apply in_eq. apply reachable_by_merge with l'. exists (x :: l' :: nil). split; split. simpl; auto.
    simpl; auto. simpl. assert (valid l'). destruct H15 as [_ [? _]]. simpl in H11. destruct p2. auto. destruct H11 as [[? _]_].
    auto. split. split. simpl; unfold change_valid; right; auto. split. simpl. unfold change_valid. left; auto. simpl.
    unfold change_edge_func. destruct (t_eq_dec x x). apply in_eq. exfalso; auto. unfold change_valid. left; auto. repeat intro.
    hnf; auto. exists (l' :: p2). rewrite (update_reachable_by_path_not_in H13). auto.

    (* In r' p *)
    destruct (in_dec t_eq_dec r' p). destruct (reachable_by_path_split_in _ _ _ _ _ _ _ _ _ H11 i) as [p1 [p2 [? [? ?]]]].
    apply reachable_by_path_foot in H14. apply foot_explicit in H14. destruct H14 as [p1h ?]. rewrite H14 in *; clear H14 p1.
    rename p1h into p1. generalize H15; intro; apply reachable_by_path_head in H14. unfold path_glue in H13. destruct p2.
    inversion H14. inversion H14. rewrite H17 in *; clear H17 a H14. simpl in H13. rewrite <- app_cons_assoc in H13. subst.
    apply NoDup_app_r in H9. assert (~ In x (r' :: p2)). intro; apply n0; apply in_or_app; right; auto. clear H11 i n0 n1 p1.
    exists x. split. apply in_eq. apply reachable_by_merge with r'. exists (x :: r' :: nil). split; split. simpl; auto.
    simpl; auto. simpl. assert (valid r'). destruct H15 as [_ [? _]]. simpl in H11. destruct p2. auto. destruct H11 as [[? _]_].
    auto. split. split. simpl; unfold change_valid; right; auto. split. simpl. unfold change_valid. left; auto. simpl.
    unfold change_edge_func. destruct (t_eq_dec x x). apply in_cons, in_eq. exfalso; auto. unfold change_valid. left; auto.
    repeat intro; hnf; auto. exists (r' :: p2). rewrite (update_reachable_by_path_not_in H13). auto.

    (* other cases *)
    assert (In s (l :: r :: S)). simpl in H8. simpl. destruct H8 as [? | [? | [? | [? | ?]]]]. left; auto. right; left; auto.
    rewrite <- H8 in *. destruct p; apply reachable_by_path_head in H11. inversion H11. simpl in H11. inversion H11. subst.
    exfalso; apply n1, in_eq. rewrite <- H8 in *. destruct p; apply reachable_by_path_head in H11. inversion H11. simpl in H11.
    inversion H11. subst. exfalso; apply n2, in_eq. right; right; auto. exists s. split. apply in_cons; auto. exists p.
    rewrite (update_reachable_by_path_not_in n0). auto.

    (* iter_sepcon_part *)
    simpl. exists h2', h3. split; auto. split. apply (trinode_graph_cell l' r'). simpl. unfold change_edge_func.
    destruct (t_eq_dec x x). auto. exfalso; auto. simpl. unfold change_node_label. destruct (t_eq_dec x x). auto. exfalso; auto.
    generalize (Permutation_middle l1 l2 x); intro. apply Permutation_sym in H0. apply (Permutation_NoDup H0) in H10.
    apply NoDup_cons_2 in H10. rewrite (iter_sepcon_not_in_eq H10). auto.

    (* ~ In x ll *)

    (* make heap clear *)
    assert (graph_cell (@bm_bi adr nat O natEqDec g) x h12). unfold gamma, biEdge in H.
    destruct (only_two_neighbours x) as [v1 [v2 ?]]. inversion H. subst.  apply (trinode_graph_cell l r). auto. auto.
    assert ((graph_cell(@bm_bi adr nat 0 natEqDec g) x * iter_sepcon ll (graph_cell(@bm_bi adr nat 0 natEqDec g)) * TT)%pred w).
    apply iter_sepcon_joinable. apply joinable_graph_cell. apply precise_graph_cell. auto. exists h12, h3. split; auto.
    exists h23, h1. split; auto. destruct_sepcon H12 t. destruct_sepcon H13 t. assertSub h12 w HS1. assertSub t0 w HS2.
    assert (precise (graph_cell (@bm_bi adr nat O natEqDec g) x)). apply precise_graph_cell.
    equate_precise_through (graph_cell (@bm_bi adr nat O natEqDec g) x) h12 t0. clear H17. assertSub h23 w HS1.
    assertSub t3 w HS2. assert (precise (iter_sepcon ll (graph_cell(@bm_bi adr nat 0 natEqDec g)))). apply precise_iter_sepcon.
    apply precise_graph_cell. equate_precise_through (iter_sepcon ll (graph_cell(@bm_bi adr nat 0 natEqDec g))) h23 t3.
    assert (emp h2). assertSub h2 h12 HS. assert (joins h2 h12). try_join h2 h12 ht. exists ht. auto.
    apply (join_sub_joins_identity HS H16). clear H12 H13 H14 H15 t1 t2. apply (join_unit2_e _ _ H16) in H1. rewrite <- H1 in *.
    clear H1 h12. apply (join_unit1_e _ _ H16) in H3. rewrite <- H3 in *. clear H3 h23 H16 h2 H8. exists h1, h3.
    do 2 (split; auto). intros h1' w'; intros. rewrite graphs_unfold. split.

    (* well_defined_list part *)
    hnf. intro y; intros. simpl in H8. destruct H8. subst. right. simpl. unfold change_valid. right; auto. destruct H8. subst.
    simpl. unfold change_valid. assert (In y (y :: r :: l' :: r' :: S)). apply in_eq. specialize (H6 _ H0).
    destruct H6; [left | right; left]; auto. destruct H8. subst. simpl. unfold change_valid.
    assert (In y (l :: y :: l' :: r' :: S)). apply in_cons, in_eq. specialize (H6 _ H0). destruct H6; [left|right; left]; auto.
    subst; simpl; unfold change_valid. assert (In y (l :: r :: l' :: r' :: S)). do 4 apply in_cons. auto. specialize (H6 _ H0).
    destruct H6; [left | right; left]; auto.

    exists (x :: ll). subst. hnf in H7. split.

    (* reachable_set_list part *)
    hnf. intro y. split; intros.

    (* -> direction *)
    destruct (eq_nat_dec y x). subst. apply in_eq. hnf in H0. right. rewrite <- (H7 y). destruct H0 as [s [? ?]].
    do 3 rewrite <- app_comm_cons in H0. rewrite app_nil_l in H0. simpl in H8. unfold reachable_through_set.
    apply reachable_acyclic in H8. destruct H8 as [p [? ?]]. destruct (in_dec t_eq_dec x p).
    destruct (reachable_by_path_split_in _ _ _ _ _ _ _ _ _ H12 i) as [p1 [p2 [? [? ?]]]]. apply reachable_by_path_foot in H14.
    apply foot_explicit in H14. destruct H14 as [p1h ?]. rewrite H14 in *; clear H14 p1; rename p1h into p1.
    generalize H15; intro; apply reachable_by_path_head in H14. unfold path_glue in H13. destruct p2. inversion H14.
    inversion H14. rewrite H17 in *; clear H17 a H14. simpl in H13. rewrite <- app_cons_assoc in H13. subst.
    apply NoDup_app_r in H8. clear H12 i p1. destruct p2. apply reachable_by_path_foot in H15. inversion H15. exfalso; auto.
    assert (a = l' \/ a = r'). destruct H15 as [_ [? _]]. rewrite <- (app_nil_l p2) in H12. do 2 rewrite app_comm_cons in H12.
    apply valid_path_split in H12. destruct H12. simpl in H12. destruct H12 as [[_ [_ ?]] _].
    simpl in H12. unfold change_edge_func in H12. simpl in H12. destruct (eq_nat_dec x x). simpl in H12. destruct H12.
    left; auto. destruct H12. right; auto. exfalso; auto. exfalso; auto. destruct H12. subst. exists l'. split.
    do 2 apply in_cons. apply in_eq. apply (update_reachable_tail_reachable H8 H15). subst. exists r'. split.
    do 3 apply in_cons. apply in_eq. apply (update_reachable_tail_reachable H8 H15). apply in_inv in H0. destruct H0.
    apply eq_sym in H0. subst. destruct p. apply reachable_by_path_foot in H12. inversion H12.
    apply reachable_by_path_head in H12. simpl in H12. inversion H12. subst. exfalso; apply n1, in_eq. exists s. split.
    simpl in H0. destruct H0 as [? | [? | ?]]; subst. apply in_eq. apply in_cons, in_eq. do 4 apply in_cons. auto.
    exists p. rewrite (update_reachable_by_path_not_in n1) in H12. auto.


    (* <- direction *)
    destruct (eq_nat_dec y x). subst. exists x. split. simpl. left; auto. apply reachable_by_reflexive. split. simpl.
    unfold change_valid. right; auto. repeat intro; hnf; auto. simpl. simpl in H0. destruct H0. exfalso; auto.
    rewrite <- (H7 y) in H0. destruct H0 as [s [? ?]]. apply reachable_acyclic in H8. destruct H8 as [p [? ?]].
    assert (~ In x p). intro. apply (reachable_path_in b_pg p s y H12 x) in H13. assert (In x ll). rewrite <- (H7 x). exists s.
    split; auto. auto.

    (* In l' p *)
    destruct (in_dec t_eq_dec l' p). destruct (reachable_by_path_split_in _ _ _ _ _ _ _ _ _ H12 i) as [p1 [p2 [? [? ?]]]].
    apply reachable_by_path_foot in H15. apply foot_explicit in H15. destruct H15 as [p1h ?]. rewrite H15 in *; clear H15 p1.
    rename p1h into p1. generalize H16; intro; apply reachable_by_path_head in H15. unfold path_glue in H14. destruct p2.
    inversion H15. inversion H15. rewrite H18 in *; clear H18 a H15. simpl in H14. rewrite <- app_cons_assoc in H14. subst.
    apply NoDup_app_r in H8. assert (~ In x (l' :: p2)). intro; apply H13; apply in_or_app; right; auto. clear H12 H13 i p1.
    exists x. split. apply in_eq. apply reachable_by_merge with l'. exists (x :: l' :: nil). split; split. simpl; auto.
    simpl; auto. simpl. assert (valid l'). destruct H16 as [_ [? _]]. simpl in H11. destruct p2. auto. destruct H12 as [[? _]_].
    auto. split. split. simpl; unfold change_valid; right; auto. split. simpl. unfold change_valid. left; auto. simpl.
    unfold change_edge_func. destruct (t_eq_dec x x). apply in_eq. exfalso; auto. unfold change_valid. left; auto. repeat intro.
    hnf; auto. exists (l' :: p2). rewrite (update_reachable_by_path_not_in H14). auto.

    (* In r' p *)
    destruct (in_dec t_eq_dec r' p). destruct (reachable_by_path_split_in _ _ _ _ _ _ _ _ _ H12 i) as [p1 [p2 [? [? ?]]]].
    apply reachable_by_path_foot in H15. apply foot_explicit in H15. destruct H15 as [p1h ?]. rewrite H15 in *; clear H15 p1.
    rename p1h into p1. generalize H16; intro; apply reachable_by_path_head in H15. unfold path_glue in H14. destruct p2.
    inversion H15. inversion H15. rewrite H18 in *; clear H18 a H15. simpl in H14. rewrite <- app_cons_assoc in H14. subst.
    apply NoDup_app_r in H8. assert (~ In x (r' :: p2)). intro; apply H13; apply in_or_app; right; auto. clear H12 H13 n1 i p1.
    exists x. split. apply in_eq. apply reachable_by_merge with r'. exists (x :: r' :: nil). split; split. simpl; auto.
    simpl; auto. simpl. assert (valid r'). destruct H16 as [_ [? _]]. simpl in H11. destruct p2. auto. destruct H12 as [[? _]_].
    auto. split. split. simpl; unfold change_valid; right; auto. split. simpl. unfold change_valid. left; auto. simpl.
    unfold change_edge_func. destruct (t_eq_dec x x). apply in_cons, in_eq. exfalso; auto. unfold change_valid. left; auto.
    repeat intro; hnf; auto. exists (r' :: p2). rewrite (update_reachable_by_path_not_in H14). auto.

    (* other cases *)
    assert (In s (l :: r :: S)). simpl in H0. simpl. destruct H0 as [? | [? | [? | [? | ?]]]]. left; auto. right; left; auto.
    rewrite <- H0 in *. destruct p; apply reachable_by_path_head in H12. inversion H12. simpl in H12. inversion H12. subst.
    exfalso; apply n1, in_eq. rewrite <- H0 in *. destruct p; apply reachable_by_path_head in H12. inversion H12. simpl in H12.
    inversion H12. subst. exfalso; apply n2, in_eq. right; right; auto. exists s. split. apply in_cons; auto. exists p.
    rewrite (update_reachable_by_path_not_in H13). auto.

    (* iter_sepcon part *)
    simpl. exists h1', h3. split; auto. split. apply (trinode_graph_cell l' r'). simpl. unfold change_edge_func.
    destruct (t_eq_dec x x). auto. exfalso; auto. simpl. unfold change_node_label. destruct (t_eq_dec x x). auto. exfalso; auto.
    rewrite (iter_sepcon_not_in_eq n). auto.
  Qed.

  Lemma graphs_eq_graph: forall (g: BiMathGraph adr nat 0) (x: adr) (d: nat) (l r: adr),
                           gamma bm_bi x = (d, l, r) -> x <> 0 -> graphs (x :: l :: r :: nil) g = graph x g.
  Proof.
    intros; apply pred_ext; intro w; intro. simpl in H1. destruct_ocon H1 h. rewrite ocon_emp in H5.
    rewrite graph_unfold in H4. destruct H4. destruct H4. hnf in H4. exfalso; auto. destruct H4 as [dd [ll [rr [[? ?] ?]]]].
    rewrite H4 in H. inversion H. subst. assert (((trinode x d l r ⊗ graph l g ⊗ graph r g) ⊗ (graph l g ⊗ graph r g)) w).
    exists h1, h2, h3, h12, h23. split; auto. rewrite <- ocon_assoc in H8.
    rewrite (ocon_assoc (trinode x d l r ⊗ graph l g) (graph r g) (graph l g)) in H8.
    rewrite (ocon_comm (graph r g) (graph l g)) in H8. rewrite <- ocon_assoc in H8.
    rewrite (ocon_assoc (trinode x d l r) (graph l g) (graph l g)) in H8. assert (precise (graph l g)). apply precise_graph.
    rewrite (ocon_precise_elim _ H9) in H8. rewrite (ocon_assoc (trinode x d l r ⊗ graph l g) (graph r g) (graph r g)) in H8.
    assert (precise (graph r g)). apply precise_graph. rewrite (ocon_precise_elim _ H10) in H8. clear H1 H2 H3 H5 H7 H9 H10.
    clear h1 h2 h3 h12 h23 H. rewrite graph_unfold. right. exists d, l, r. split. split; auto. auto. simpl. rewrite ocon_emp.
    generalize H1; intro. rewrite graph_unfold in H2. destruct H2 as [[? _] | ?]. hnf in H2. exfalso; auto.
    destruct H2 as [dd [ll [rr [[? ?] ?]]]]. rewrite H2 in H. inversion H. subst. rewrite ocon_assoc in H4.
    destruct_ocon H4 h. try_join h2 h3 h23'; equate_join h23 h23'. hnf. exists h1, h23, (core h23), w, h23. split; auto. split.
    apply join_comm, core_unit. split. apply join_comm in H10. rewrite (join_core H10). apply join_comm, core_unit. split; auto.
  Qed.

  Lemma single_graph_node_update_2:
    forall (g: BiMathGraph adr nat 0) (x: adr) (d: nat) (l r: adr) (d': nat) (g': BiMathGraph adr nat 0)
           (Hn: x <> 0) (Hi: in_math bm_ma x l r),
      @gamma adr nat natEqDec (@bm_bi adr nat O natEqDec g) x = (d, l, r) -> g' = update_graph g x d' l r Hi Hn ->
      graph x g |-- trinode x d l r * (trinode x d' l r -* graph x g').
  Proof.
    intros. generalize (single_graph_node_update_1 g x d l r d' l r g' Hn Hi nil H H0); intro. rewrite app_nil_r in H1.
    rewrite (graphs_eq_graph g x d l r H Hn) in H1.
    assert (@gamma adr nat natEqDec (@bm_bi adr nat O natEqDec g') x = (d', l, r)). unfold gamma, biEdge.
    destruct (@only_two_neighbours adr nat natEqDec (@bm_bi adr nat O natEqDec g') x) as [v1 [v2 ?]].
    rewrite H0 in e. simpl in e. unfold change_edge_func in e. rewrite H0. simpl. unfold change_node_label.
    destruct (t_eq_dec x x). inversion e. subst. auto. exfalso; auto. rewrite (graphs_eq_graph g' x d' l r H2 Hn) in H1. auto.
  Qed.

  Lemma single_graph_node_update_2_ewand:
    forall (g: BiMathGraph adr nat 0) (x: adr) (d: nat) (l r: adr) (d': nat) (g': BiMathGraph adr nat 0)
           (Hn: x <> 0) (Hi: in_math bm_ma x l r),
      @gamma adr nat natEqDec (@bm_bi adr nat O natEqDec g) x = (d, l, r) -> g' = update_graph g x d' l r Hi Hn ->
      trinode x d' l r * (trinode x d l r -⊛ graph x g) |-- graph x g'.
  Proof. intros. apply wand_ewand. apply precise_trinode. apply single_graph_node_update_2 with (Hn:= Hn) (Hi := Hi); auto. Qed.

  Lemma iter_sepcon_graph_cell_refine:
    forall (g: BiGraph adr nat) (l: list adr) w,
      iter_sepcon l (graph_cell g) w -> exists li, iter_sepcon li emapsto w /\
                                                   (forall x, In x l -> In x li /\ In (x + 1) li /\ In (x + 2) li) /\
                                                   (forall y, In y li -> In y l \/ In (y - 1) l \/ In (y - 2) l).
  Proof.
    intros. revert w H. induction l; intros; simpl in H. exists nil. split. simpl. auto. split; intros; inversion H0.
    destruct_sepcon H h. unfold graph_cell, gamma, biEdge in H0. destruct (only_two_neighbours a) as [v1 [v2 ?]].
    destruct H0. remember (a :: a + 1 :: a + 2 :: nil) as la. assert (iter_sepcon la emapsto h1). subst. simpl.
    rewrite sepcon_emp. rewrite <- sepcon_assoc. destruct_sepcon H2 i. exists i1, i2. split; auto. split. destruct_sepcon H3 j.
    exists j1, j2. split; auto. split. exists (node_label a); auto. exists v1; auto. exists v2; auto.
    assert (forall y, In y la -> y = a \/ (y - 1) = a \/ (y - 2) = a). subst. intros. simpl in H4. destruct H4 as [?|[?|[?|?]]].
    left; auto. right; left; intuition. right; right; intuition. exfalso; auto. assert (In a la /\ In (a+1) la /\ In (a+2) la).
    subst. split. apply in_eq. split; apply in_cons. apply in_eq. apply in_cons, in_eq. specialize (IHl h2 H1).
    destruct IHl as [lr [? [? ?]]]. exists (la ++ lr). split. rewrite iter_sepcon_app_sepcon. exists h1, h2. split; auto. split.
    intros. simpl in H9. destruct H9. rewrite H9 in *. clear H9 a. destruct H5 as [? [? ?]].
    repeat split; apply in_or_app; left; auto. specialize (H7 x H9). destruct H7 as [? [? ?]].
    repeat split; apply in_or_app; right; auto. intros. apply in_app_or in H9. destruct H9. specialize (H4 y H9).
    destruct H4 as [? | [? | ?]]; subst; [left | right; left | right; right]; apply in_eq. specialize (H8 y H9).
    destruct H8 as [? | [? | ?]]; [left | right; left | right; right]; apply in_cons; auto.
  Qed.

  Lemma points_to_preservation:
    forall (g g': BiMathGraph adr nat 0) (S S': list adr) (x: adr),
      subset (reachable_through_set (@b_pg adr nat natEqDec (@bm_bi adr nat O natEqDec g)) S)
             (reachable_through_set b_pg S') ->
      graphs S g ⊗ emapsto x |-- graphs S g * (graphs S' g' -* graphs S' g' ⊗ emapsto x).
  Proof.
    intros; intro w; intro. destruct_ocon H0 w. generalize H3; intro. rewrite graphs_unfold in H5. destruct H5 as [? [l [? ?]]].
    destruct (iter_sepcon_graph_cell_refine _ l w12 H7) as [li [? [? ?]]]. try_join w2 w3 w23'; equate_join w23 w23'.
    destruct (in_dec t_eq_dec x li).

    (* In x li *)

    (* make heap clear *)
    apply in_split in i. destruct i as [l1 [l2 ?]]. subst. generalize (Permutation_middle l1 l2 x); intro.
    apply Permutation_sym in H11. rewrite (iter_sepcon_permutation _ _ _ H11) in H8. clear H11. simpl in H8.
    destruct_sepcon H8 t. assert (precise (emapsto x)). apply precise_emapsto. assertSub w23 w HS1. assertSub t1 w HS2.
    equate_precise_through (emapsto x) w23 t1. assert (emp w3). assertSub w23 w12 HS2. assertSub w3 w12 HS. clear HS2.
    assert (joins w3 w12). exists w. auto. apply (join_sub_joins_identity HS H11). apply (join_unit2_e _ _ H11) in H1.
    rewrite <- H1 in *. clear H1 w23. apply (join_unit2_e _ _ H11) in H2. rewrite H2 in *. clear H2 w12 H11 w3 H14.
    apply join_comm in H8. generalize (join_canc H8 H12); intro. subst. clear H8 H12. exists w, (core w). split.
    apply join_comm, core_unit. split; auto. intros w' w''; intros. assert (emp (core w)). apply core_identity.
    apply (join_unit2_e _ _ H8) in H1. apply eq_sym in H1. subst. remember (l1 ++ x :: l2) as li. generalize H2; intro Hg'.
    rewrite graphs_unfold in H2. destruct H2 as [? [ll [? ?]]].

    assert (Sublist l ll). intro z; intros. rewrite <- (H6 z) in H12. specialize (H z H12). rewrite (H2 z) in H. auto.

    destruct (iter_sepcon_graph_cell_refine _ ll w' H11) as [lli [? [? ?]]]. assert (Sublist li lli). intro z; intros.
    specialize (H10 z H17). destruct H10 as [?|[?|?]]; specialize (H12 _ H10); specialize (H15 _ H12); destruct H15 as [?[? ?]].
    auto. destruct (eq_nat_dec z 0). assert (z - 1 = z). omega. rewrite H20 in H15. auto. assert (z - 1 + 1 = z) by omega.
    rewrite H20 in H18. auto. destruct (eq_nat_dec z 0). assert (z - 2 = z). omega. rewrite H20 in H15; auto.
    destruct (eq_nat_dec z 1). assert (z - 2 + 1 = z). omega. rewrite H20 in H18; auto. assert (z - 2 + 2 = z). omega.
    rewrite H20 in H19; auto.

    assert (In x lli). apply (H17 x). subst. apply in_or_app. right; apply in_eq. apply in_split in H18.
    destruct H18 as [ll1 [ll2 ?]]. subst. clear H15 H9 H10 H16 H17. generalize (Permutation_middle ll1 ll2 x); intro.
    apply Permutation_sym in H9. rewrite (iter_sepcon_permutation _ _ _ H9) in H14. clear H9. simpl in H14.
    destruct_sepcon H14 t. hnf. exists t2, t1, (core t1), w', t1. split; auto. split. apply join_comm, core_unit. split.
    assert (core t1 = core w'). apply (join_core H9). rewrite H15. apply join_comm, core_unit. split; auto.

    (* ~ In x li *)
    clear H9 H10. assert ((emapsto x * iter_sepcon li emapsto * TT)%pred w). apply iter_sepcon_joinable. apply joinable_emapsto.
    apply precise_emapsto. auto. exists w23, w1. split; auto. exists w12, w3. split; auto. destruct_sepcon H9 t.
    destruct_sepcon H10 t. assertSub w23 w HS1. assertSub t0 w HS2. assert (precise (emapsto x)). apply precise_emapsto.
    equate_precise_through (emapsto x) w23 t0. clear H15. assertSub w12 w HS1. assertSub t3 w HS2.
    assert (precise (iter_sepcon li emapsto)). apply precise_iter_sepcon. apply precise_emapsto.
    equate_precise_through (iter_sepcon li emapsto) w12 t3. assert (emp w2). assertSub w2 w12 HS. assert (joins w2 w12).
    try_join w2 w12 ht. exists ht. auto. apply (join_sub_joins_identity HS H14). clear H9 H10 H11 H13 t1 t2.
    apply (join_unit2_e _ _ H14) in H0. rewrite <- H0 in *. clear H0 w12. apply (join_unit1_e _ _ H14) in H1.
    rewrite <- H1 in *. clear H1 w23 H14 w2 H12. exists w1, w3. do 2 (split; auto). intros w1' w'; intros. apply sepcon_ocon.
    exists w1', w3. split; auto.
  Qed.

  Lemma subgraph_update:
    forall (g g': BiMathGraph adr nat 0) (S1 S1' S2: list adr),
      subset (reachable_through_set (b_pg_g g) S1) (reachable_through_set (b_pg_g g') S1') ->
      (unreachable_subgraph (b_pg_g g) S1) -=- (unreachable_subgraph (b_pg_g g') S1') ->
      graphs S1 g ⊗ graphs S2 g |-- graphs S1 g * (graphs S1' g' -* graphs S1' g' ⊗ graphs S2 g').
  Proof.
    intros; intro w; intro. destruct_ocon H1 w. try_join w2 w3 w23'; equate_join w23 w23'.
    exists w12, w3. do 2 (split; auto). intros w12' w'; intros. rewrite graphs_unfold in H4, H5.
    destruct H4 as [? [l1 [? ?]]]. destruct H5 as [? [l2 [? ?]]]. unfold prop in *.

    (* make heap clear *)
    assert (sepcon_unique (graph_cell (bm_bi_g g))). apply sepcon_unique_graph_cell.
    assert (NoDup l1). apply (iter_sepcon_unique_nodup H13 H10). assert (NoDup l2). apply (iter_sepcon_unique_nodup H13 H12).
    destruct (double_list_split t_eq_dec H14 H15) as [i1 [i2 [i3 [? [? ?]]]]].
    rewrite (iter_sepcon_permutation _ _ _ H16) in H10. generalize H10; intro.
    rewrite (iter_sepcon_permutation _ _ _ H17) in H12.
    rewrite iter_sepcon_app_sepcon in H10, H12. destruct_sepcon H10 h. destruct_sepcon H12 h. rename h0 into h2'.
    assert (precise (iter_sepcon i2 (graph_cell (bm_bi_g g)))). apply precise_iter_sepcon. apply precise_graph_cell.
    assertSub h2 w HS1. assertSub h2' w HS2. unfold bm_bi_g in *.
    equate_precise_through (iter_sepcon i2 (graph_cell (@bm_bi adr nat O natEqDec g))) h2 h2'.
    assert ((iter_sepcon ((i1 ++ i2) ++ i3) (graph_cell (bm_bi_g g)) * TT)%pred w). apply iter_sepcon_app_joinable.
    apply joinable_graph_cell. apply precise_graph_cell. rewrite app_assoc in H18. apply NoDup_app_not_in; auto.
    rewrite app_assoc in H18. apply NoDup_app_l in H18. auto. exists w12, w3. split; auto. assertSub h3 w HS. destruct HS.
    exists h3, x. split; auto. destruct_sepcon H22 t. rename t1 into t123. rename t2 into te.
    rewrite iter_sepcon_app_sepcon in H25. destruct_sepcon H25 t. rename t1 into t12. rename t2 into t3.
    assert (precise (iter_sepcon i3 (graph_cell (bm_bi_g g)))). apply precise_iter_sepcon. apply precise_graph_cell.
    assertSub h3 w HS1. assertSub t3 w HS2. unfold bm_bi_g in *.
    equate_precise_through (iter_sepcon i3 (graph_cell (@bm_bi adr nat O natEqDec g))) h3 t3.
    assert (precise (iter_sepcon (i1 ++ i2) (graph_cell (bm_bi_g g)))). apply precise_iter_sepcon. apply precise_graph_cell.
    assertSub w12 w HS1. assertSub t12 w HS2. unfold bm_bi_g in *.
    equate_precise_through (iter_sepcon (i1 ++ i2) (graph_cell (@bm_bi adr nat O natEqDec g))) w12 t12.
    generalize (overlapping_eq h1 h2 h3 w1 w2 w3 w12 w23 t123 w H10 H12 H25 H1 H2 H3). intro. subst. clear H26 H22 te.
    apply join_comm in H3. apply join_comm in H25. generalize (join_canc H25 H3); intro. subst. clear H25.
    generalize (join_canc H12 H2); intro. subst. clear H12. generalize (join_canc H10 H1); intro. subst. clear H10 H24 H28 H29.

    (* well_defined_list (bm_ma_g g') S2 *)
    generalize H8; intro HS1'. rewrite graphs_unfold in H8. destruct H8 as [? [l1' [? ?]]]. unfold prop in *.
    assert (well_defined_list (bm_ma_g g') S2). repeat intro. destruct (eq_nat_dec x 0). left; auto. right.
    destruct H0 as [? [? ?]]. specialize (H0 x). simpl in H0. unfold unreachable_valid in H1. destruct (in_dec t_eq_dec x l1').
    rewrite <- (H10 x) in i. destruct i as [s [? ?]]. apply reachable_foot_valid in H27. unfold bm_ma_g. rewrite pg_the_same.
    apply H27. specialize (H10 x). specialize (H x). assert (~ reachable_through_set (b_pg_g g') S1' x). intro. apply n0.
    rewrite <- H10. auto. unfold b_pg_g in H26. assert (~ reachable_through_set (b_pg_g g) S1 x). intro. apply H26. apply H.
    auto. unfold b_pg_g in H27. specialize (H5 x H22). destruct H5. exfalso; auto.
    assert ((@valid adr nat natEqDec (b_pg_g g) x) /\ ~ reachable_through_set (b_pg_g g) S1 x). split. unfold b_pg_g.
    rewrite <- pg_the_same. apply H5. apply H27. rewrite H0 in H28. destruct H28. unfold bm_ma_g. rewrite pg_the_same.
    apply H28. unfold bm_ma_g in H22.

    (* Get reachable list l2' for S2 in g' *)

    assert (forall x, ~ reachable_through_set (b_pg_g g') S1' x /\ reachable_through_set (b_pg_g g') S2 x <-> In x i3). intro.
    split; intro. rewrite <- (unreachable_sub_eq_unrch_rch_eq H0 x S2) in H24. destruct H24. rewrite (H11 x) in H25.
    apply (Permutation_in x H17) in H25. apply in_app_or in H25. destruct H25; auto. assert (In x l1).
    apply Permutation_sym in H16. apply (Permutation_in x H16). apply in_or_app; right; auto. rewrite <- (H9 x) in H26.
    exfalso; auto. rewrite <- (unreachable_sub_eq_unrch_rch_eq H0 x S2). split. rewrite app_assoc in H18.
    generalize (Permutation_app_comm (i1 ++ i2) i3); intro. apply (Permutation_NoDup H25) in H18.
    apply (NoDup_app_not_in _ _ _ H18 x) in H24. intro; apply H24. apply (Permutation_in x H16). rewrite <- (H9 x). apply H26.
    assert (In x (i2 ++ i3)). apply in_or_app; right; auto. apply Permutation_sym in H17. apply (Permutation_in x H17) in H25.
    unfold b_pg_g. rewrite (H11 x). auto.

    assert (forall x, reachable_through_set (b_pg_g g') S2 x -> In x (l1' ++ i3)). intros. apply in_or_app.
    destruct (in_dec t_eq_dec x l1'). left; auto. assert (~ reachable_through_set (b_pg_g g') S1' x). intro. apply n.
    apply (H10 x) in H26. auto. right. rewrite <- H24. split; auto. unfold b_pg_g in H25. rewrite <- pg_the_same in H25.

    assert (Sublist S2 S2). apply Sublist_refl.
    destruct (finite_reachable_set_sublist _ S2 (l1' ++ i3) H25 S2 H26 H22) as [l2' [? ?]].

    (* split l1'~union~l2' into j1 j2 j3 and prove that (Permutation j3 i3) *)
    assert (NoDup l1'). assert (sepcon_unique (graph_cell (bm_bi_g g'))). apply sepcon_unique_graph_cell.
    apply (iter_sepcon_unique_nodup H29 H12). destruct (double_list_split t_eq_dec H29 H28) as [j1 [j2 [j3 [? [? ?]]]]].
    assert (Permutation j3 i3). apply NoDup_Permutation. rewrite app_assoc in H32. apply NoDup_app_r in H32. auto.
    rewrite app_assoc in H18. apply NoDup_app_r in H18. auto. intro; split; intro. rewrite <- H24. split.
    rewrite app_assoc in H32. generalize (Permutation_app_comm (j1 ++ j2) j3); intro. apply (Permutation_NoDup H34) in H32.
    apply (NoDup_app_not_in _ _ _ H32 x) in H33. intro; apply H33. apply (Permutation_in x H30). rewrite <- (H10 x). apply H35.
    assert (In x (j2 ++ j3)). apply in_or_app; right; auto. apply Permutation_sym in H31. apply (Permutation_in x H31) in H34.
    unfold b_pg_g. rewrite <- pg_the_same. rewrite (H27 x). auto. rewrite <- H24 in H33. destruct H33. unfold b_pg_g in H34.
    rewrite <- pg_the_same in H34. rewrite (H27 x) in H34. apply (Permutation_in x H31) in H34. apply in_app_or in H34.
    destruct H34; auto. exfalso; apply H33. assert (In x (j1++j2)). apply in_or_app. right; auto. apply Permutation_sym in H30.
    apply (Permutation_in x H30) in H35. rewrite <- (H10 x) in H35. unfold b_pg_g. auto.

    (* iter_sepcon j3 (graph_cell (bm_bi_g g')) w3 *)

    assert (iter_sepcon j3 (graph_cell (bm_bi_g g')) w3). rewrite (iter_sepcon_permutation _ _ _ H33).
    assert (forall x, In x i3 -> valid_g g x /\ ~ reachable_through_set (b_pg_g g) S1 x). intros. rewrite <- H24 in H34.
    rewrite <- (unreachable_sub_eq_unrch_rch_eq H0 x S2) in H34. destruct H34. split; auto. destruct H35 as [? [? ?]].
    apply reachable_foot_valid in H36; apply H36. clear - H34 H23 H0. unfold b_pg_g in H0. destruct H0 as [? [? ?]].
    simpl in H, H0, H1. unfold unreachable_valid in * |- . revert w3 H23. induction i3; intros; simpl; simpl in H23.
    auto. destruct_sepcon H23 h. exists h1, h2. split; auto. split. assert (In a (a :: i3)). apply in_eq. specialize (H34 a H5).
    unfold valid_g in H34. specialize (H0 a H34). specialize (H1 a H34). unfold graph_cell, gamma, biEdge in H3.
    destruct (only_two_neighbours a) as [v1 [v2 ?]]. unfold bm_bi_g, graph_cell, gamma, biEdge.
    destruct (only_two_neighbours a) as [t1 [t2 ?]]. rewrite H1 in e. rewrite e in e0. inversion e0. subst.
    rewrite H0 in H3. apply H3. apply IHi3. intros. apply H34. apply in_cons; auto. auto.

    (* establish graphs S2 g' w23' *)
    rewrite (iter_sepcon_permutation _ _ _ H30) in H12. rewrite iter_sepcon_app_sepcon in H12. destruct_sepcon H12 h.
    rename h1 into w1'; rename h2 into w2'. try_join w2' w3 w23'. assert (iter_sepcon l2' (graph_cell (bm_bi_g g')) w23').
    rewrite (iter_sepcon_permutation _ _ _ H31). rewrite iter_sepcon_app_sepcon. exists w2', w3; split; auto.
    assert (graphs S2 g' w23'). rewrite graphs_unfold. split. unfold prop. apply H22. exists l2'. split. unfold prop.
    rewrite <- pg_the_same. apply H27. apply H39.

    (* reach the final goal *)
    exists w1', w2', w3, w12', w23'. split; auto.
  Qed.

  Lemma subgraph_update_ewand:
    forall (g g': BiMathGraph adr nat 0) (S1 S1' S2: list adr),
      subset (reachable_through_set (b_pg_g g) S1) (reachable_through_set (b_pg_g g') S1') ->
      (unreachable_subgraph (b_pg_g g) S1) -=- (unreachable_subgraph (b_pg_g g') S1') ->
      graphs S1' g' * (graphs S1 g -⊛ graphs S1 g ⊗ graphs S2 g) |-- graphs S1' g' ⊗ graphs S2 g'.
  Proof. intros. apply wand_ewand. apply precise_graphs. apply subgraph_update; auto. Qed.

End PointwiseGraph.
