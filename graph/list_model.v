Require Import Coq.Arith.Arith.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.MathGraph.
Require Import RamifyCoq.graph.FiniteGraph.
Require Import RamifyCoq.graph.reachable_computable.
Require Import Coq.Lists.List.

Section LIST_MODEL.
  
  Context {Vertex: Type}.
  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.

  Variable G : PreGraph Vertex Edge.

  Definition is_list (x: Vertex) : Prop :=
    exists p, valid_path G p /\ forall y, reachable G x y -> exists (py: path), unique (fun pa => G |= pa is x ~o~> y satisfying (fun _ => True)) py /\ Subpath G py p.

  Definition graph_list_isomorphism (l: list Vertex) (root: Vertex) : Prop :=
    (forall s d, reachable G root s /\ reachable G root d /\ G |= s ~> d <-> exists l1 l2, l = l1 ++ s :: d :: l2) /\ (forall v, reachable G root v <-> In v l) /\ NoDup l.

  Context {is_null: DecidablePred Vertex}.
  Context {MA: MathGraph G is_null}.
  Context {LF: LocalFiniteGraph G}.

  Lemma list_expand_nil_or_single: forall root l r,
      vvalid G root -> is_list root -> l = @new_working_list _ _ is_null nil (map (dst G) (edge_func G root)) (root :: r) -> l = nil \/ (exists v, l = v :: nil /\ G |= root ~> v).
  Proof.
    intros. destruct l. 1: left; auto. destruct l.
    + right. exists v; split; auto. assert (In v (v :: nil)) by apply in_eq. rewrite H1 in H2. rewrite in_new_working_list in H2. destruct H2 as [? [? ?]].
      rewrite app_nil_l in H2. rewrite <- edge_func_step in H2. split; [|split]; auto. rewrite step_spec in H2. destruct H2 as [e [? [? ?]]].
      destruct (valid_graph G e H2) as [_ ?]. hnf in H7. rewrite H6 in H7. destruct H7; [exfalso |]; auto.
    + exfalso. destruct LF in H1. unfold edge_func in H1. simpl in H1. destruct (local_enumerable root) as [l' [? ?]].
      simpl in H1. unfold Ensembles.In in i. destruct H0 as [lf [? ?]].
      assert (forall v', In v' (v :: v0 :: l) -> reachable G root v'). {
        intros. rewrite H1 in H3. rewrite in_new_working_list in H3. rewrite app_nil_l in H3. destruct H3 as [? [? ?]].
        rewrite in_map_iff in H3. destruct H3 as [e [? ?]]. exists (root, e :: nil). split; split; simpl; auto.
        + rewrite i in H6. destruct H6. unfold strong_evalid. rewrite H7. rewrite H3. do 3 (split; auto).
          destruct (valid_graph G e H6) as [_ ?]. hnf in H8. rewrite H3 in H8. destruct H8; [exfalso | ]; auto.
        + hnf. rewrite Forall_forall. intros; auto.
      } unfold new_working_list in H1. symmetry in H1. apply filter_2_cons in H1. destruct H1 as [l1 [l2 [l3 [? [? [? [? [? ?]]]]]]]]. simpl in H1. apply map_2_mid in H1.
      destruct H1 as [y1 [y2 [m1 [m2 [m3 [? [? [? [? [? ?]]]]]]]]]]. rewrite H1 in n. apply NoDup_app_r in n. apply NoDup_cons_2 in n.
      assert (reachable G root v) by apply H3, in_eq. assert (reachable G root v0) by apply H3, in_cons, in_eq. apply H2 in H14. apply H2 in H15.
      destruct H14 as [pv [[? ?] ?]]. destruct H15 as [pv0 [[? ?] ?]].
      assert (G |= (root, y1 :: nil) is root ~o~> v satisfying (fun _ => True)). {
        split; split; intros; auto. 2: hnf; rewrite Forall_forall; intros; auto. simpl. unfold strong_evalid. rewrite H12.
        assert (In y1 l') by (rewrite H1; rewrite in_app_iff; right; apply in_eq). rewrite i in H20. destruct H20. rewrite H21.
        apply reachable_by_path_is_reachable in H14. apply reachable_foot_valid in H14. split; auto.
      } pose proof (H16 _ H20). 
      assert (G |= (root, y2 :: nil) is root ~o~> v0 satisfying (fun _ => True)). {
        split; split; intros; auto. 2: hnf; rewrite Forall_forall; intros; auto. simpl. unfold strong_evalid. rewrite H13.
        assert (In y2 l') by (rewrite H1; rewrite in_app_iff; right; right; rewrite in_app_iff; right; apply in_eq). rewrite i in H22. destruct H22. rewrite H23.
        apply reachable_by_path_is_reachable in H15. apply reachable_foot_valid in H15. split; auto.
      } pose proof (H18 _ H22). apply n. rewrite in_app_iff. right.
      assert (In_path G v lf) by (apply (In_path_Subpath _ pv); auto; rewrite H21, <- H12; right; exists y1; simpl; tauto).
      assert (In_path G v0 lf) by (apply (In_path_Subpath _ pv0); auto; rewrite H23, <- H13; right; exists y2; simpl; tauto).
      pose proof (valid_path_reachable _ _ _ _ H0 H24 H25). destruct H26; destruct H26 as [[vl pl] ?].
      - assert (G |= (path_glue (root, y1 :: nil) (vl, pl)) is root ~o~> v0 satisfying (fun _ => True)) by (apply reachable_by_path_merge with v; auto).
        unfold path_glue, fst, snd in H27. rewrite <- app_comm_cons, app_nil_l in H27. apply H18 in H27. rewrite H23 in H27. inversion H27. apply in_eq.
      - assert (G |= (path_glue (root, y2 :: nil) (vl, pl)) is root ~o~> v satisfying (fun _ => True)) by (apply reachable_by_path_merge with v0; auto).
        unfold path_glue, fst, snd in H27. rewrite <- app_comm_cons, app_nil_l in H27. apply H16 in H27. rewrite H21 in H27. inversion H27. apply in_eq.
  Qed.

  (* Print Assumptions list_expand_nil_or_single. *)

  Definition list_composed_by_edges (l: list Vertex) : Prop := forall l1 l2 s d, l = l1 ++ s :: d :: l2 -> G |= s ~> d.

  Lemma list_composed_by_edges_nil: list_composed_by_edges nil.
  Proof. repeat intro. assert (@length Vertex nil = length (l1 ++ s :: d :: l2)) by (rewrite H; tauto). rewrite app_length in H0; simpl in H0. intuition. Qed.

  Lemma list_composed_by_edges_single: forall v, list_composed_by_edges (v :: nil).
  Proof.
    repeat intro. exfalso. assert (length (v :: nil) = length (l1 ++ s :: d :: l2)) by (rewrite H; tauto). rewrite app_length in H0. simpl in H0. intuition.
  Qed.

  Lemma lcbe_rev_cons: forall v l, list_composed_by_edges (rev (v :: l)) -> list_composed_by_edges (rev l).
  Proof.
    intros. rewrite <- (app_nil_l l), app_comm_cons, rev_app_distr in H. simpl in H. unfold list_composed_by_edges in *. intros.
    specialize (H l1 (l2 +:: v) s d). apply H. rewrite H0. rewrite <- app_assoc. simpl. auto.
  Qed.

  Lemma lcbe_rev_cons_inv: forall v root l, G |= root ~> v -> list_composed_by_edges (rev (root :: l)) -> list_composed_by_edges (rev (v :: root :: l)).
  Proof.
    intros. rewrite <- (app_nil_l (root :: l)), app_comm_cons, rev_app_distr. simpl rev at 2. unfold list_composed_by_edges in *. intros. destruct l2.
    + simpl in H1. rewrite <- (app_nil_l (d :: nil)), (app_comm_cons nil (d :: nil) s) in H1. rewrite app_assoc in H1.
      do 2 (apply app_inj_tail in H1; destruct H1). subst. auto.
    + assert (v0 :: l2 <> nil) by (intro; inversion H2). apply exists_last in H2. destruct H2 as [l' [a ?]]. rewrite e in H1.
      rewrite app_comm_cons, (app_comm_cons (d :: l') (a :: nil) s), app_assoc in H1. apply app_inj_tail in H1. destruct H1. apply (H0 l1 l'); auto.
  Qed.

  Lemma is_list_edge: forall root v, G |= root ~> v -> is_list root -> is_list v.
  Proof.
    intros. unfold is_list in *. destruct H0 as [p [? ?]]. exists p. split; auto. intros.
    destruct H2 as [[v' pv] ?]. assert (v' = v) by (destruct H2 as [[? _] _]; simpl in H2; auto). subst v'. destruct H as [? [? ?]]. rewrite step_spec in H4.
    destruct H4 as [e [? [? ?]]].
    assert (forall pp, G |= pp is v ~o~> y satisfying (fun _ => True) -> G |= (path_glue (root, e :: nil) pp) is root ~o~> y satisfying (fun _ => True)). {
      intros. apply reachable_by_path_merge with v; auto. split; split; simpl; auto.
      + unfold strong_evalid. rewrite H5, H6. split; auto.
      + hnf. rewrite Forall_forall. intros; auto.
    }
    pose proof (H7 _ H2). unfold path_glue, fst, snd in H8. rewrite <- app_comm_cons, app_nil_l in H8. pose proof (reachable_by_path_is_reachable _ _ _ _ _ H8).
    apply H1 in H9. clear H1. destruct H9 as [py [[? ?] ?]]. pose proof (H9 _ H8). exists (v, pv). split; split; auto.
    + intros. specialize (H7 _ H12). destruct x' as [x px]. assert (x = v) by (destruct H12 as [[? _] _]; simpl in H12; auto). subst x.
      unfold path_glue, fst, snd in H7. rewrite <- app_comm_cons, app_nil_l in H7. specialize (H9 _ H7). rewrite H9 in H11. inversion H11. auto.
    + simpl. destruct H10. subst py. simpl in *. clear -H10. unfold incl in *. intros. apply H10. right; auto.
    + simpl. destruct H10. subst py. simpl in *. unfold In_path. clear -H6 H10. right. exists e. split; intuition.
  Qed.

  Lemma construct_reachable_edge:
    forall lim root r, vvalid G root -> is_list root -> list_composed_by_edges (rev (root :: r)) -> list_composed_by_edges (rev (@construct_reachable _ _ _ _ G is_null _ (lim, root :: nil, r))).
  Proof.
    intros lim root r. remember (lengthInput (lim, root :: nil, r)) as n. assert (lengthInput (lim, root :: nil, r) <= n) by intuition. clear Heqn.
    revert n lim root r H. induction n; intros.
    + simpl in H. rewrite construct_reachable_unfold. destruct (le_dec lim (length r)); [apply (lcbe_rev_cons root) | exfalso]; intuition.
    + rewrite construct_reachable_unfold. unfold lengthInput in H, IHn. destruct (le_dec lim (length r)). 1: apply (lcbe_rev_cons root); auto.
      remember (@new_working_list _ _ is_null nil (map (dst G) (edge_func G root)) (root :: r)).
      assert (l = nil \/ exists v, l = (v :: nil) /\ G |= root ~> v) by (apply (list_expand_nil_or_single _ _ r); auto). destruct H3.
      - clear Heql. subst l. simpl. rewrite construct_reachable_unfold. auto.
      - destruct H3 as [v [? ?]]. rewrite H3. simpl. apply IHn.
        * simpl. clear - H n0. intuition.
        * hnf in H4. intuition.
        * apply (is_list_edge root); auto.
        * apply lcbe_rev_cons_inv; auto.
  Qed.

  Lemma is_list_no_self_loop: forall root s, vvalid G root -> is_list root -> reachable G root s -> G |= s ~> s -> False.
  Proof.
    intros. destruct H2 as [? [? ?]]. rewrite step_spec in H4. destruct H4 as [e [? [? ?]]].
    assert (G |= (s, e :: nil) is s ~o~> s satisfying (fun _ => True)). {
      split; split; simpl; auto.
      + unfold strong_evalid. rewrite H5, H6. split; auto.
      + hnf. rewrite Forall_forall; intros; auto.
    } destruct H0 as [pf [? ?]]. apply H8 in H1. clear H8. destruct H1 as [ps [[? ?] ?]]. destruct ps as [v ps].
    assert (v = root) by (destruct H1 as [[? _] _]; simpl in H1; auto). subst v. pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H1 H7). unfold path_glue, fst, snd in H10.
    apply H8 in H10. inversion H10. pose proof (f_equal (@length Edge) H12). rewrite app_length in H11. simpl in H11. intuition.
  Qed.

  Lemma is_list_edge_dst_the_same: forall root s d v, vvalid G root -> is_list root -> reachable G root s -> G |= s ~> d -> G |= s ~> v -> d = v.
  Proof.
    intros. assert (reachable G root d) by (apply reachable_edge with s; auto). assert (reachable G root v) by (apply reachable_edge with s; auto).
    destruct H0 as [pf [? ?]]. apply H6 in H4. destruct H4 as [pd [[? ?] ?]]. apply H6 in H5. destruct H5 as [pv [[? ?] ?]].
    assert (In_path G v pf) by (apply In_path_Subpath with pv; auto; destruct H5 as [[_ ?] _]; apply pfoot_in; auto).
    assert (In_path G d pf) by (apply In_path_Subpath with pd; auto; destruct H4 as [[_ ?] _]; apply pfoot_in; auto).
    pose proof (valid_path_reachable _ _ _ _ H0 H11 H12). clear H8 H10 H11 H12. destruct H2 as [? [? ?]]. rewrite step_spec in H10. destruct H10 as [ed [? [? ?]]].
    destruct H3 as [? [? ?]]. rewrite step_spec in H15. destruct H15 as [ev [? [? ?]]]. destruct H1 as [ps ?].
    assert (G |= (s, ed :: nil) is s ~o~> d satisfying (fun _ => True)). {
      split; split; simpl; auto.
      + unfold strong_evalid. rewrite H11, H12; split; auto.
      + hnf. rewrite Forall_forall; intros; auto.
    }
    assert (G |= (s, ev :: nil) is s ~o~> v satisfying (fun _ => True)). {
      split; split; simpl; auto.
      + unfold strong_evalid. rewrite H16, H17; split; auto.
      + hnf. rewrite Forall_forall; intros; auto.
    } destruct ps as [vs ps]. assert (vs = root) by (destruct H1 as [[? _] _]; simpl in H1; auto). subst vs.
    pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H1 H18). unfold path_glue, fst, snd in H20.
    pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H1 H19). unfold path_glue, fst, snd in H21. clear H4 H5. pose proof (H7 _ H20). pose proof (H9 _ H21). destruct H13.
    + destruct H13 as [[v' pv'] ?]. assert (v' = v) by (destruct H13 as [[? _] _]; simpl in H13; auto). subst v'. 
      pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H21 H13). unfold path_glue, fst, snd in H22. apply H7 in H22. rewrite H4 in H22. inversion H22.
      pose proof (f_equal (@length Edge) H24). rewrite !app_length in H23. simpl in H23. assert (length pv' = 0) by intuition. destruct pv'. 2: inversion H25.
      clear H23 H25. rewrite app_nil_r in H24. apply app_inj_tail in H24. destruct H24. subst ed. rewrite H12 in H17. auto.
    + destruct H13 as [[d' pd'] ?]. assert (d' = d) by (destruct H13 as [[? _] _]; simpl in H13; auto). subst d'. 
      pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H20 H13). unfold path_glue, fst, snd in H22. apply H9 in H22. rewrite H5 in H22. inversion H22.
      pose proof (f_equal (@length Edge) H24). rewrite !app_length in H23. simpl in H23. assert (length pd' = 0) by intuition. destruct pd'. 2: inversion H25.
      clear H23 H25. rewrite app_nil_r in H24. apply app_inj_tail in H24. destruct H24. subst ed. rewrite H12 in H17. auto.
  Qed.

  Lemma is_list_edge_src_the_same: forall root s d v, vvalid G root -> is_list root -> reachable G root s -> reachable G root v -> G |= s ~> d -> G |= v ~> d -> s = v.
  Proof.
    intros. destruct H3 as [? [? ?]]. rewrite step_spec in H6. destruct H6 as [es [? [? ?]]]. destruct H4 as [? [? ?]]. rewrite step_spec in H10. destruct H10 as [ev [? [? ?]]].
    assert (G |= (s, es :: nil) is s ~o~> d satisfying (fun _ => True)). {
      split; split; simpl; auto; [unfold strong_evalid; rewrite H7, H8; split; auto | hnf; rewrite Forall_forall; intros; auto].
    }
    assert (G |= (v, ev :: nil) is v ~o~> d satisfying (fun _ => True)). {
      split; split; simpl; auto; [unfold strong_evalid; rewrite H11, H12; split; auto | hnf; rewrite Forall_forall; intros; auto].
    } destruct H1 as [[vs ps] ?]. destruct H2 as [[vv pv] ?]. 
    pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H1 H13). unfold path_glue, fst, snd in H15.
    pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H2 H14). unfold path_glue, fst, snd in H16. destruct H0 as [pf [? ?]].
    pose proof (reachable_by_path_is_reachable _ _ _ _ _ H16). apply H17 in H18. destruct H18 as [pp [[? ?] ?]]. apply H19 in H15. apply H19 in H16. rewrite H15 in H16.
    inversion H16. apply app_inj_tail in H23. destruct H23. subst es. rewrite H7 in H11. auto.
  Qed.

  Lemma construct_reachable_tail_preserve: forall lim p r, exists l', @construct_reachable _ _ _ _ G is_null _ (lim, p, r) = l' ++ r.
  Proof.
    intros lim p r. remember (lengthInput (lim, p, r)) as n. assert (lengthInput (lim, p, r) <= n) by intuition. clear Heqn. revert lim p r H. induction n; intros.
    + simpl in H. rewrite construct_reachable_unfold. destruct p. exists nil; rewrite app_nil_l; auto. destruct (le_dec lim (length r)).
      exists nil; rewrite app_nil_l; auto. exfalso; intuition.
    + simpl in H. rewrite construct_reachable_unfold. destruct p. exists nil; rewrite app_nil_l; auto. destruct (le_dec lim (length r)). exists nil; rewrite app_nil_l; auto.
      remember (@new_working_list _ _ is_null p (map (dst G) (edge_func G v)) (v :: r)). simpl. simpl in IHn. specialize (IHn lim l (v :: r)).
      assert (lim - length (v :: r) <= n) by (simpl; intuition). apply IHn in H0. destruct H0 as [l1 ?]. rewrite app_cons_assoc in H0. exists (l1 +:: v). auto.
  Qed.

  Theorem is_list_is_list: forall root, vvalid G root -> EnumCovered Vertex (reachable G root) -> is_list root -> {l | graph_list_isomorphism l root}.
  Proof.
    intros. remember (@construct_reachable _ _ _ _ G is_null _ (length (proj1_sig X), root :: nil, nil)). destruct (finite_reachable_computable' _ _ X l H Heql).
    hnf in H1. exists (rev l). split; [|split].
    + intros. destruct X as [ss [? ?]]. simpl in Heql. unfold Ensembles.In in i.
      assert (list_composed_by_edges (rev (root :: nil))) by (simpl; apply list_composed_by_edges_single). apply (construct_reachable_edge (length ss) _ nil H H0) in H3.
      hnf in H3. rewrite <- Heql in H3. split; intros.
      - destruct H4 as [? [? ?]]. pose proof H4. rewrite <- H1, in_rev in H4. apply in_split in H4. destruct H4 as [l1 [l2 ?]]. exists l1. destruct l2.
        * exfalso. pose proof H5. rewrite <- H1, in_rev, H4 in H8. rewrite in_app_iff in H8. simpl in H8. destruct H8 as [? | [? | ?]]; auto.
          2: subst d; apply (is_list_no_self_loop root s); auto. destruct l1. 1: inversion H8.
          assert (v = root). {
            rewrite construct_reachable_unfold in Heql. destruct (le_dec (length ss) (length nil)). 1: rewrite Heql in H4; simpl in H4; inversion H4.
            remember (@new_working_list _ _ is_null nil (map (dst G) (edge_func G root)) (root :: nil)). simpl in Heql.
            destruct (construct_reachable_tail_preserve (length ss) l0 (root :: nil)) as [l' ?]. rewrite <- Heql in H9. rewrite H9 in H4.
            rewrite rev_unit in H4. simpl in H4. inversion H4. auto.
          } subst v. simpl in H8. destruct H8.
          1: {
            subst d. destruct H0 as [pf [? ?]]. apply H8 in H5. clear H8. destruct H5 as [pr [[? ?] ?]].
            assert (G |= (root, nil) is root ~o~> root satisfying (fun _ => True)) by
                (split; split; simpl; auto; red; simpl; auto).
            destruct H7 as [[vr ps] ?]. destruct H6 as [? [? ?]]. rewrite step_spec in H12. destruct H12 as [e [? [? ?]]].
            assert (G |= (s, e :: nil) is s ~o~> root satisfying (fun _ => True)). {
              split; split; simpl; auto.
              + unfold strong_evalid. rewrite H13, H14. split; auto.
              + hnf. rewrite Forall_forall; intros; auto.
            } pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H7 H15). unfold path_glue, fst, snd in H16. apply H8 in H10. apply H8 in H16. rewrite H10 in H16.
            inversion H16. destruct ps; simpl in H19; inversion H19.
          }
          1: {
            apply in_split in H8. destruct H8 as [l0 [l2 ?]]. subst l1. assert (root :: l0 <> nil) by (intro HS; inversion HS). apply exists_last in H8.
            destruct H8 as [l' [a ?]]. rewrite app_comm_cons, e in H4. rewrite <- app_cons_assoc, <- app_assoc in H4. simpl in H4. specialize (H3 _ _ _ _ H4).
            assert (a = s) by (apply (is_list_edge_src_the_same root _ d); auto; rewrite <- H1, in_rev, H4, in_app_iff; right; apply in_eq). subst a.
            assert (NoDup (rev l)) by (apply Permutation_NoDup with (l := l); auto; apply Permutation_rev). rewrite H4 in H8. apply NoDup_app_r in H8.
            apply NoDup_cons_2 in H8. apply H8. simpl. right. rewrite in_app_iff. right. apply in_eq.
          }
        * specialize (H3 _ _ _ _ H4). assert (d = v) by (apply (is_list_edge_dst_the_same root s); auto). subst v. exists l2; auto.
      - destruct H4 as [l1 [l2 ?]]. split; [|split]; [apply H1; rewrite in_rev; rewrite H4; rewrite in_app_iff; right ..|]; [apply in_eq | right; apply in_eq |].
        apply (H3 l1 l2); auto.
    + intros; rewrite <- in_rev, H1; tauto.
    + apply Permutation_NoDup with (l := l); auto. apply Permutation_rev.
  Qed.

  (* Print Assumptions is_list_is_list. *)
  
End LIST_MODEL.
