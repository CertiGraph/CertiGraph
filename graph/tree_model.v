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

Section TREE_DEF.

  Context {Vertex: Type}.

  Inductive Tree :=
  | EPT: Tree
  | T: Vertex -> list Tree -> Tree.

  Inductive find_tree : Vertex -> Tree -> Tree -> Prop :=
  | FT_base: forall v t, find_tree v (T v t) (T v t)
  | FT_succ: forall v v' tr' tr tl , In tr' tl -> find_tree v tr' tr -> find_tree v (T v' tl) tr.

  Definition subtrees (t: Tree): list Tree :=
    match t with
    | EPT => nil
    | T _ l => l
    end.

  Fixpoint forest_head (tl: list Tree) : list Vertex :=
    match tl with
    | nil => nil
    | EPT :: tl' => forest_head tl'
    | T v l :: tl' => v :: forest_head tl'
    end.

  Fixpoint leaves (t: Tree) : list Vertex :=
    match t with
    | EPT => nil
    | T v l => v :: (flat_map leaves l)
    end.

  Lemma find_tree_in_leaves: forall s t1 t2, find_tree s t1 t2 -> In s (leaves t1).
  Proof.
    intros. induction H.
    + simpl. left; auto.
    + simpl. right. rewrite in_flat_map. exists tr'. split; auto.
  Qed.

  Lemma find_tree_in_leaves': forall s t1 t2, find_tree s t1 t2 -> forall x, In x (leaves t2) -> In x (leaves t1).
  Proof.
    intros s t1 t2 ?. induction H. 1: intuition.
    intros. specialize (IHfind_tree _ H1). simpl. right. rewrite in_flat_map. exists tr'. split; auto.
  Qed.

  Lemma forest_head_in_leaves: forall d t, In d (forest_head (subtrees t)) -> In d (leaves t).
  Proof.
    intros. induction t. 1: simpl in H; exfalso; auto. simpl in H. simpl. right. induction l.
    + simpl in H. exfalso; auto.
    + simpl in *. destruct a.
      - specialize (IHl H). simpl. auto.
      - simpl in *. destruct H; [left | right]; auto. specialize (IHl H). apply in_or_app. right; auto.
  Qed.

  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.

  Definition graph_tree_isomorphism_v (g: PreGraph Vertex Edge) (t: Tree) (root: Vertex): Prop :=
    (forall s d, reachable g root s /\ reachable g root d /\ g |= s ~> d <-> exists t', find_tree s t t' /\ In d (forest_head (subtrees t'))) /\
    (forall v, reachable g root v <-> In v (leaves t)) /\ NoDup (leaves t).

  Definition graph_tree_isomorphism (g: PreGraph Vertex Edge) (t: Tree) : Prop :=
    (forall s d, g |= s ~> d <-> exists t', find_tree s t t' /\ In d (forest_head (subtrees t'))) /\
    (forall v, vvalid g v <-> In v (leaves t)) /\ NoDup (leaves t).

  Lemma graph_tree_isomorphism_eq:
    forall (g: PreGraph Vertex Edge) t root, (forall v, vvalid g v -> reachable g root v) -> (graph_tree_isomorphism_v g t root <-> graph_tree_isomorphism g t).
  Proof.
    intros. split; intro; destruct H0 as [? [? ?]]; split; [ |split| |split]; intros; auto.
    + split; intros.
      - pose proof H3. destruct H4 as [? [? _]]. apply H in H4. apply H in H5. specialize (H0 s d). intuition.
      - rewrite <- H0 in H3. intuition.
    + rewrite <- H1. intuition. apply reachable_foot_valid in H3. auto.
    + split; intros. 1: rewrite <- H0; intuition. rewrite <- H0 in H3. pose proof H3. destruct H4 as [? [? _]].
      apply H in H4. apply H in H5. intuition.
    + rewrite <- H1. intuition. apply reachable_foot_valid in H3; auto.
  Qed.

  Definition veq_dec := (@equiv_dec _ _ _ EV).

  Section CONVERSION.

    Variable G: PreGraph Vertex Edge.
    Context {is_null: DecidablePred Vertex}.
    Context {MA: MathGraph G is_null}.
    Context {LF: LocalFiniteGraph G}.

    Definition not_null_bool (v: Vertex) := if @is_null_dec _ is_null v then false else true.

    Fixpoint graph_to_tree (limit: nat) (root: Vertex): nat * Tree :=
      match limit with
      | O => (O, EPT)
      | S n => let vertices_list := nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G root))) in
               let (total, sub_trees) := to_tree_list n vertices_list (0, nil) in
               (1 + total, T root sub_trees)
      end with
    to_tree_list (limit: nat) (l: list Vertex) (result: nat * list Tree) : nat * list Tree :=
      match limit with
      | O => result
      | S n => match l with
               | nil => result
               | x :: tl => let (current, tr) := graph_to_tree n x in
                            if eq_nat_dec current O
                            then result
                            else to_tree_list (n - current) tl (fst result + current + 1, tr :: snd result)
               end
      end.

    Lemma in_step_list_edge: forall root x l, step_list G root l -> (In x (filter not_null_bool l) <-> G |= root ~> x).
    Proof.
      intros. rewrite filter_In. rewrite (H x). clear H. split; intros.
      + destruct H. unfold not_null_bool in H0. destruct (is_null_dec x). 1: inversion H0.
        pose proof H. rewrite step_spec in H1. destruct H1 as [e [? [? ?]]].
        destruct (valid_graph G e H1). rewrite H2 in H4. rewrite H3 in H5. destruct H5. 1: exfalso; auto. split; auto.
      + destruct H as [? [? ?]]. split; auto. unfold not_null_bool. destruct (is_null_dec x); auto. exfalso. apply (valid_not_null G x); auto.
    Qed.

    Lemma in_edge_func_edge: forall root x, In x (filter not_null_bool (map (dst G) (edge_func G root))) <-> G |= root ~> x.
    Proof. intros. apply in_step_list_edge. intro. rewrite edge_func_step. tauto. Qed.

    Lemma graph_to_tree_bound': forall lim, (forall root, fst (graph_to_tree lim root) <= lim) /\
                                            (forall l n trL, fst (to_tree_list lim l (n, trL)) <= lim + n).
    Proof.
      intro lim. remember lim as up.  rewrite Hequp. assert (lim <= up) by intuition. clear Hequp. revert lim H. induction up; intros; split; intros.
      + assert (lim = 0) by intuition. subst. simpl; auto.
      + assert (lim = 0) by intuition. subst. simpl; auto.
      + destruct lim; simpl; auto. remember (to_tree_list lim (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))) (0, nil)).
        destruct p as [total sub_trees]. simpl. assert (lim <= up) by intuition. destruct (IHup _ H0) as [_ ?].
        specialize (H1 (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))) 0 nil). rewrite <- Heqp in H1. simpl in H1. intuition.
      + destruct lim; simpl; auto. destruct l; simpl; intuition. remember (graph_to_tree lim v). destruct p as [current tr].
        destruct (eq_nat_dec current 0). 1: simpl; intuition.
        assert (lim <= up) by intuition. destruct (IHup _ H0) as [? _]. specialize (H1 v). rewrite <- Heqp in H1. simpl in H1.
        assert (lim - current <= up) by intuition. destruct (IHup _ H2) as [_ ?]. specialize (H3 l (n + current + 1) (tr :: trL)). intuition.
    Qed.

    Lemma graph_to_tree_bound: forall lim root, fst (graph_to_tree lim root) <= lim. Proof. intro. apply (proj1 (graph_to_tree_bound' lim)). Qed.

    Definition sum_of_leaves (trL : list Tree) := length (flat_map leaves trL).

    Lemma graph_to_tree_lower_bound': forall lim, (forall root, let (n, tree) := graph_to_tree lim root in n = 2 * length (leaves tree) - 1) /\
                                                  (forall l n trL, n = 2 * sum_of_leaves trL -> let (n', trL') := to_tree_list lim l (n, trL) in n' = 2 * sum_of_leaves trL').
    Proof.
      intro lim. remember lim as up.  rewrite Hequp. assert (lim <= up) by intuition. clear Hequp. revert lim H. induction up; intros; split; intros.
      + assert (lim = 0) by intuition. subst. simpl; auto.
      + assert (lim = 0) by intuition. subst. simpl; auto.
      + destruct lim; simpl; auto. assert (lim <= up) by intuition. destruct (IHup _ H0) as [_ ?].
        specialize (H1 (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))) 0 nil). assert (0 = 2 * sum_of_leaves nil) by intuition. specialize (H1 H2).
        remember (to_tree_list lim (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))) (0, nil)). destruct p as [total sub_trees]. simpl.
        unfold sum_of_leaves in H1. intuition.
      + destruct lim; simpl; auto. destruct l; simpl; auto. assert (lim <= up) by intuition. destruct (IHup _ H1) as [? _]. specialize (H2 v).
        remember (graph_to_tree lim v). destruct p as [current tr]. destruct (eq_nat_dec current 0). 1: intuition. assert (lim - current <= up) by intuition.
        destruct (IHup _ H3) as [_ ?]. specialize (H4 l (n + current + 1) (tr :: trL)).
        assert (n + current + 1 = 2 * sum_of_leaves (tr :: trL)). {
          unfold sum_of_leaves in *. simpl flat_map. rewrite app_length.
          clear -H0 H2 n0. intuition.
        } specialize (H4 H5). remember (to_tree_list (lim - current) l (n + current + 1, tr :: trL)). destruct p as [n' trL']. intuition.
    Qed.

    Lemma graph_to_tree_lower_bound: forall lim root, let (n, tree) := graph_to_tree lim root in n = 2 * length (leaves tree) - 1.
    Proof. intro. apply (proj1 (graph_to_tree_lower_bound' lim)). Qed.

    Lemma graph_to_tree_is_reachable': forall lim,
        (forall root x, vvalid G root -> In x (leaves (snd (graph_to_tree lim root))) -> reachable G root x) /\
        (forall root l n trL, Forall (reachable G root) l -> (forall x, In x (flat_map leaves trL) -> reachable G root x) ->
                              forall x, In x (flat_map leaves (snd (to_tree_list lim l (n, trL)))) -> reachable G root x).
    Proof.
      intro lim. remember lim as up. rewrite Hequp. assert (lim <= up) by intuition. clear Hequp. revert lim H. induction up; intros; split; intros.
      + assert (lim = 0) by intuition; subst; simpl in H1; exfalso; auto.
      + assert (lim = 0) by intuition; subst; simpl in H2; apply H1; auto.
      + destruct lim. 1: simpl in H1; exfalso; auto. simpl in H1. destruct lim; simpl in H1. 1: destruct H1; [subst | exfalso; auto]; apply reachable_refl; auto.
        remember (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))). destruct l.
        1: simpl in H1; destruct H1; [subst | exfalso; auto]; apply reachable_refl; auto.
        remember (graph_to_tree lim v). destruct p as [current tr]. destruct (eq_nat_dec current 0). 1: simpl in H1; destruct H1; [subst; apply reachable_refl | exfalso]; auto.
        remember (to_tree_list (lim - current) l (current + 1, tr :: nil)). destruct p as [total sub_trees].
        simpl in H1. destruct H1. 1: subst; apply reachable_refl; auto.
        assert (Forall (reachable G root) (v :: l)). {
          rewrite Forall_forall. intro y; intros. rewrite Heql in H2. rewrite nodup_In in H2. apply in_edge_func_edge in H2.
          apply reachable_edge with root; auto. apply reachable_refl; auto.
        } assert (lim - current <= up) by intuition. destruct (IHup _ H3) as [_ ?]. apply (H4 root l (current + 1) (tr :: nil)); clear H4.
        - apply Forall_tl in H2; auto.
        - simpl. intro y; intros. rewrite app_nil_r in H4. assert (lim <= up) by intuition. destruct (IHup _ H5) as [? _]. apply reachable_trans with v.
          * apply Forall_inv in H2; auto.
          * apply (H6 v). 1: apply Forall_inv in H2; apply reachable_foot_valid in H2; auto. rewrite <- Heqp. simpl. auto.
        - rewrite <- Heqp0. simpl. auto.
      + destruct lim; simpl in H2. 1: apply H1; auto. destruct l. 1: simpl in H2; apply H1; auto.
        remember (graph_to_tree lim v). destruct p as [current tr]. assert (lim - current <= up) by intuition.
        destruct (eq_nat_dec current 0). 1: simpl in H2; apply H1; auto.
        destruct (IHup _ H3) as [_ ?]. apply (H4 root l (n + current + 1) (tr :: trL)); auto; clear H4 H3.
        - apply Forall_tl in H0; auto.
        - intro y; intros. simpl in H3. apply in_app_or in H3. destruct H3. 2: apply H1; auto.
          assert (lim <= up) by intuition. destruct (IHup _ H4) as [? _]. apply reachable_trans with v.
          * apply Forall_inv in H0; auto.
          * apply (H5 v). 1: apply Forall_inv in H0; apply reachable_foot_valid in H0; auto. rewrite <- Heqp. simpl. auto.
    Qed.

    Lemma graph_to_tree_is_reachable: forall lim root x, vvalid G root -> In x (leaves (snd (graph_to_tree lim root))) -> reachable G root x.
    Proof. intro. apply (proj1 (graph_to_tree_is_reachable' lim)). Qed.

    Lemma to_tree_list_is_reachable: forall lim l n trL, Forall (vvalid G) l ->
                                                         (forall x, In x (flat_map leaves trL) -> exists v, In v (forest_head trL) /\ reachable G v x) ->
                                                         forall x, In x (flat_map leaves (snd (to_tree_list lim l (n, trL)))) ->
                                                                   exists v, In v (l ++ forest_head trL) /\ reachable G v x.
    Proof.
      intro lim. remember lim as up. rewrite Hequp. assert (lim <= up) by intuition. clear Hequp. revert lim H. induction up; intros.
      + assert (lim = 0) by intuition. subst. simpl in H2. specialize (H1 x H2). destruct H1 as [v [? ?]]. exists v. split; auto. apply in_or_app. right; auto.
      + destruct lim; simpl in H2. 1: specialize (H1 x H2); destruct H1 as [v [? ?]]; exists v; split; auto; apply in_or_app; right; auto.
        destruct l; simpl in H2. 1: specialize (H1 x H2); destruct H1 as [v [? ?]]; exists v; split; auto; apply in_or_app; right; auto.
        remember (graph_to_tree lim v). destruct p as [current tr]. destruct (eq_nat_dec current 0).
        1: simpl in H2; specialize (H1 x H2); destruct H1 as [v' [? ?]]; exists v'; split; auto; apply in_or_app; right; auto.
        assert (lim - current <= up) by intuition. assert (Forall (vvalid G) l) by (apply Forall_tl in H0; auto). specialize (IHup _ H3 l (n + current + 1) (tr :: trL) H4).
        clear H3 H4. assert (forall x : Vertex, In x (flat_map leaves (tr :: trL)) -> exists v : Vertex, In v (forest_head (tr :: trL)) /\ reachable G v x). {
          intro y; intros. simpl in H3. simpl. apply in_app_or in H3. destruct H3.
          + destruct tr. 1: simpl in H3; exfalso; auto.
            assert (v0 = v). {
              clear -Heqp. destruct lim; simpl in Heqp. 1: inversion Heqp.
              remember (to_tree_list lim (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G v)))) (0, nil)).
              destruct p as [total sub_trees]. inversion Heqp. auto.
            } subst. exists v. simpl. split. 1: left; auto. pose proof (graph_to_tree_is_reachable lim v y). apply H4.
            - apply Forall_inv in H0; auto.
            - rewrite <- Heqp. simpl; auto.
          + specialize (H1 y H3). destruct tr. 1: apply H1. destruct H1 as [v1 [? ?]]. exists v1. split; auto. simpl. right; auto.
        } specialize (IHup H3 _ H2). clear H2 H3 n0. destruct IHup as [v' [? ?]]. exists v'. split; auto. apply in_app_or in H2. apply in_or_app. destruct H2.
        - left. simpl. right. auto.
        - simpl in H2. destruct tr. 1: right; auto. simpl in H2. destruct H2. 2: right; auto. subst.
          assert (v' = v). {
            destruct lim; simpl in Heqp. 1: inversion Heqp. remember (to_tree_list lim (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G v)))) (0, nil)).
            destruct p as [p1 p2]. inversion Heqp. auto.
          } subst. left. simpl. left; auto.
    Qed.

    Lemma graph_to_tree_is_valid': forall lim,
        (forall root x, vvalid G root -> In x (leaves (snd (graph_to_tree lim root))) -> vvalid G x) /\
        (forall l n trL, Forall (vvalid G) l -> (forall x, In x (flat_map leaves trL) -> vvalid G x) ->
                                                 forall x, In x (flat_map leaves (snd (to_tree_list lim l (n, trL)))) -> vvalid G x).
    Proof.
      intro lim. remember lim as up.  rewrite Hequp. assert (lim <= up) by intuition. clear Hequp. revert lim H. induction up; intros; split; intros.
      + assert (lim = 0) by intuition; subst; simpl in H1; exfalso; auto.
      + assert (lim = 0) by intuition; subst; simpl in H2; apply H1; auto.
      + destruct lim. 1: simpl in H1; exfalso; auto. simpl in H1. destruct lim. 1: simpl in H1; destruct H1; [subst | exfalso]; auto. simpl in H1.
        remember (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))). destruct l. 1: simpl in H1; destruct H1; [subst | exfalso]; auto.
        remember (graph_to_tree lim v). destruct p as [current tr]. destruct (eq_nat_dec current 0). 1: simpl in H1; destruct H1; [subst | exfalso]; auto.
        remember (to_tree_list (lim - current) l (current + 1, tr :: nil)). destruct p as [total sub_trees].
        simpl in H1. destruct H1. 1: subst; auto.
        assert (Forall (vvalid G) (v :: l)). {
          rewrite Forall_forall. intro y; intros. rewrite Heql in H2. rewrite nodup_In in H2. apply in_edge_func_edge in H2. destruct H2 as [? [? ?]]; auto.
        } assert (lim - current <= up) by intuition. destruct (IHup _ H3) as [_ ?]. apply (H4 l (current + 1) (tr :: nil)); clear H4.
        - apply Forall_tl in H2; auto.
        - simpl. intro y; intros. rewrite app_nil_r in H4. assert (lim <= up) by intuition. destruct (IHup _ H5) as [? _]. apply (H6 v); auto.
          * apply Forall_inv in H2; auto.
          * rewrite <- Heqp. simpl. auto.
        - rewrite <- Heqp0. simpl. auto.
      + destruct lim; simpl in H2. 1: apply H1; auto. destruct l. 1: simpl in H2; apply H1; auto.
        remember (graph_to_tree lim v). destruct p as [current tr]. assert (lim - current <= up) by intuition.
        destruct (eq_nat_dec current 0). 1: simpl in H2; apply H1; auto.
        destruct (IHup _ H3) as [_ ?]. apply (H4 l (n + current + 1) (tr :: trL)); auto; clear H4 H3.
        - apply Forall_tl in H0; auto.
        - intro y; intros. simpl in H3. apply in_app_or in H3. destruct H3. 2: apply H1; auto.
          assert (lim <= up) by intuition. destruct (IHup _ H4) as [? _]. apply (H5 v).
          * apply Forall_inv in H0; auto.
          * rewrite <- Heqp. simpl. auto.
    Qed.

    Lemma graph_to_tree_is_valid: forall lim root x, vvalid G root -> In x (leaves (snd (graph_to_tree lim root))) -> vvalid G x.
    Proof. intro. apply (proj1 (graph_to_tree_is_valid' lim)). Qed.

    Definition tree_match_graph_edges (s d : Vertex) (t t': Tree) : Prop := find_tree s t t' -> In d (forest_head (subtrees t')) -> G |= s ~> d.

    Lemma graph_to_tree_edge': forall lim, (forall s d t root, tree_match_graph_edges s d (snd (graph_to_tree lim root)) t) /\
                                           (forall s d t root l n trL, (forall m, In m l -> G |= root ~> m) ->
                                                                       (forall m, In m (forest_head trL) -> G |= root ~> m) ->
                                                                       tree_match_graph_edges s d (T root trL) t ->
                                                                       tree_match_graph_edges s d (T root (snd (to_tree_list lim l (n, trL)))) t).
    Proof.
      intro lim. remember lim as up.  rewrite Hequp. assert (lim <= up) by intuition. clear Hequp. revert lim H. induction up; split; intros; hnf; intros.
      + assert (lim = 0) by intuition; subst; simpl in H0; inversion H0.
      + assert (lim = 0) by intuition; subst. simpl in H3. apply H2; auto.
      + destruct lim; simpl in H0. 1: inversion H0. destruct lim; simpl in H0.
        1: inversion H0; [| inversion H5]; clear v t0 H2 H5; subst s; subst t; simpl in H1; exfalso; auto.
        remember (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))). destruct l; simpl in H0.
        1: inversion H0; [| inversion H5]; clear v t0 H2 H5; subst s; subst t; simpl in H1; exfalso; auto.
        remember (graph_to_tree lim v). destruct p as [current tr]. destruct (eq_nat_dec current 0). 1: inversion H0; subst; [simpl in H1 | simpl in H5]; exfalso; auto.
        remember (to_tree_list (lim - current) l (current + 1, tr :: nil)). destruct p as [total sub_trees].
        simpl in H0. assert (lim - current <= up) by intuition. destruct (IHup _ H2) as [_ ?].
        specialize (H3 s d t root l (current + 1) (tr :: nil)).
        assert (forall m : Vertex, In m (v :: l) -> G |= root ~> m). { intros. rewrite Heql in H4. rewrite nodup_In in H4; apply in_edge_func_edge; auto. }
        assert (forall m : Vertex, In m (forest_head (tr :: nil)) -> G |= root ~> m). {
          intros. clear H1 H2 H3. destruct lim; simpl in Heqp. 1: inversion Heqp; subst; simpl in H5; exfalso; auto.
          remember (to_tree_list lim (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G v)))) (0, nil)). destruct p as [total1 sub_trees1].
          inversion Heqp. subst. simpl in H5. destruct H5. 2: exfalso; auto. subst. apply H4. simpl; left; auto.
        } apply H3; auto.
        - intros. apply H4. apply in_cons; auto.
        - repeat intro. assert (lim <= up) by intuition. destruct (IHup _ H8) as [? _]. specialize (H9 s d t v). rewrite <- Heqp in H9. simpl in H9. inversion H6.
          * subst. unfold subtrees in H1. apply H5; auto.
          * subst. destruct H13. 2: exfalso; auto. rewrite <- H10 in *. apply H9; auto.
        - rewrite <- Heqp0. simpl. auto.
      + destruct lim; simpl in H3. 1: apply H2; auto. destruct l. 1: simpl in H3; apply H2; auto. remember (graph_to_tree lim v). destruct p as [current tr].
        destruct (eq_nat_dec current 0). 1: simpl in H3; apply H2; auto.
        assert (lim - current <= up) by intuition. destruct (IHup _ H5) as [_ ?].
        assert (forall m : Vertex, In m (forest_head (tr :: trL)) -> G |= root ~> m). {
          intros. destruct lim; simpl in Heqp; inversion Heqp; subst. 1: simpl in H7; apply H1; auto.
          remember (to_tree_list lim (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G v)))) (0, nil)). destruct p as [total1 sub_trees1].
          inversion H9. subst. simpl in H7. destruct H7. 2: apply H1; auto. subst v. apply H0. simpl; left; auto.
        } specialize (H6 s d t root l (n + current + 1) (tr :: trL)). apply H6; auto. 1: intros; apply H0; simpl; right; auto.
        repeat intro. clear H3 H4 H5 H6. inversion H8.
        - subst. unfold subtrees in H9. apply H7; auto.
        - subst. simpl in H6. destruct H6.
          * rewrite <- H3 in *. assert (lim <= up) by intuition. destruct (IHup _ H4) as [? _]. specialize (H5 s d t v). apply H5; auto.
            rewrite <- Heqp. simpl; auto.
          * apply H2; auto. apply FT_succ with tr'; auto.
    Qed.

    Lemma graph_to_tree_edge: forall lim s d t root, tree_match_graph_edges s d (snd (graph_to_tree lim root)) t.
    Proof. intro. apply (proj1 (graph_to_tree_edge' lim)). Qed.

    Lemma is_tree_not_to_root: forall root v x, is_tree G root -> G |= root ~> v -> reachable G v x -> x <> root.
    Proof.
      intros. destruct H0 as [? [? ?]]. assert (reachable G root root) by
          (apply reachable_refl; auto). specialize (H _ H4). destruct H as [p [? ?]].
      assert (G |= (root, nil) is root ~o~> root satisfying (fun _ => True)) by
          (split; split; simpl; auto; red; simpl; split; intros; auto).
      pose proof (H5 _ H6).
      intro. subst x. destruct H1 as [path' ?]. rewrite step_spec in H3. destruct H3 as [e [? [? ?]]].
      assert (G |= (root, e :: nil) is root ~o~> v satisfying (fun _ => True)) by
          (split; split; simpl; intuition; hnf; [subst root v | rewrite Forall_forall; intros]; auto).
      pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H10 H1). specialize (H5 _ H11). rewrite H7 in H5. clear -H5.
      destruct path' as [v' p']. unfold path_glue in H5. simpl in H5. inversion H5.
    Qed.

    Lemma is_tree_step_eq: forall root v1 v2 x, vvalid G root -> is_tree G root -> step G root v1 -> step G root v2 -> reachable G v1 x -> reachable G v2 x -> v1 = v2.
    Proof.
      intros. assert (reachable G root x) by (apply step_reachable with v1; auto). specialize (H0 _ H5). destruct H0 as [p [? ?]].
      destruct H3 as [p1 ?]. destruct H4 as [p2 ?].
      assert (forall e pa a, strong_evalid G e -> src G e = root -> dst G e = a -> G |= pa is a ~o~> x satisfying (fun _ : Vertex => True) ->
                             G |= path_glue (root, e :: nil) pa is root ~o~> x satisfying (fun _ : Vertex => True)). {
        intros. apply reachable_by_path_merge with a; auto. split; split; simpl; auto.
        hnf. rewrite Forall_forall; intros. auto.
      } rewrite step_spec in H1. destruct H1 as [e1 [? [? ?]]]. rewrite step_spec in H2. destruct H2 as [e2 [? [? ?]]].
      assert (strong_evalid G e1). {
        rewrite <- H8 in H. do 2 (split; auto). rewrite H9.
        apply reachable_by_path_is_reachable in H3. apply reachable_by_head_valid in H3. auto.
      }
      assert (strong_evalid G e2). {
        rewrite <- H10 in H. do 2 (split; auto). rewrite H11.
        apply reachable_by_path_is_reachable in H4. apply reachable_by_head_valid in H4. auto.
      } pose proof (H7 _ _ _ H12 H8 H9 H3). specialize (H7 _ _ _ H13 H10 H11 H4). apply H6 in H7. apply H6 in H14. rewrite H7 in H14. inversion H14.
      subst e2. rewrite H9 in H11. auto.
    Qed.

    (* Lemma is_tree_step_eq': forall root v1 v2 x, vvalid G root -> is_tree G root -> reachable G root x ->  *)

    Lemma graph_to_tree_nodup': forall lim root, vvalid G root -> is_tree G root ->
                                                NoDup (leaves (snd (graph_to_tree lim root))) /\
                                                (forall l n trL, (forall x, In x l -> step G root x /\ vvalid G x) ->
                                                                 NoDup (flat_map leaves trL) ->
                                                                 (forall x v m, In x l -> In v (leaves (snd (graph_to_tree m x))) -> ~ In v (flat_map leaves trL)) ->
                                                                 NoDup l ->
                                                                 NoDup (flat_map leaves (snd (to_tree_list lim l (n, trL))))).
    Proof.
      intro lim. remember lim as up.  rewrite Hequp. assert (lim <= up) by intuition. clear Hequp. revert lim H. induction up; intros; simpl; split; intros.
      + assert (lim = 0) by intuition. subst. simpl. apply NoDup_nil.
      + assert (lim = 0) by intuition. subst. simpl. auto.
      + destruct lim; simpl. 1: apply NoDup_nil. pose proof (to_tree_list_is_reachable lim (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))) 0 nil).
        remember (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))). simpl in H2. rewrite app_nil_r in H2.
        assert (Forall (vvalid G) l). {
          clear H2; rewrite Forall_forall. intros. subst. rewrite nodup_In in H2.
          apply in_edge_func_edge in H2. destruct H2 as [? [? ?]]. apply H3.
        }
        assert (forall x : Vertex, False -> exists v : Vertex, False /\ reachable G v x) by (intros; exfalso; auto). specialize (H2 H3 H4). clear H4.
        remember (to_tree_list lim l (0, nil)). destruct p as [total sub_trees]. simpl in *. constructor.
        - intro. specialize (H2 _ H4). destruct H2 as [v [? ?]]. rewrite Heql in H2. rewrite nodup_In in H2. apply in_edge_func_edge in H2.
          apply (is_tree_not_to_root _ _ _ H1 H2 H5); auto.
        - assert (lim <= up) by intuition. destruct (IHup _ H4 _ H0 H1) as [_ ?]. clear IHup. specialize (H5 l 0 nil). rewrite <- Heqp in H5.
          simpl in H5. apply H5.
          * intros. subst l. rewrite nodup_In in H6. apply in_edge_func_edge in H6. destruct H6 as [? [? ?]]. split; auto.
          * apply NoDup_nil.
          * intros. intro; auto.
          * rewrite Heql. apply NoDup_nodup.
      + destruct lim; simpl; auto. destruct l; simpl; auto. remember (graph_to_tree lim v). destruct p as [current tr]. destruct (eq_nat_dec current 0).
        1: simpl; auto. assert (lim  <= up) by intuition. assert (In v (v :: l)) by (simpl; left; auto). destruct (H2 _ H7).
        assert (is_tree G v) by (apply is_tree_sub_is_tree with root; auto). destruct (IHup _ H6 _ H9 H10) as [? _]. rewrite <- Heqp in H11. simpl in H11.
        assert (lim - current <= up) by intuition. destruct (IHup _ H12 _ H0 H1) as [_ ?]. clear IHup.
        specialize (H13 l (n + current + 1) (tr :: trL)). simpl in H13. apply H13; clear H13.
        - intros. apply H2. simpl; right; auto.
        - apply NoDup_app_inv; auto. intros. specialize (H4 v x lim). rewrite <- Heqp in H4. simpl in H4. apply H4; auto.
        - intros x v' m; intros. intro. apply in_app_or in H15. assert (In x (v :: l)) by (simpl; right; auto). destruct H15. 2: specialize (H4 x v' m H16 H14); apply H4; auto.
          pose proof (graph_to_tree_is_reachable lim v v' H9). rewrite <- Heqp in H17. simpl in H17. specialize (H17 H15).
          specialize (H2 _ H16). destruct H2. apply (graph_to_tree_is_reachable m x v' H18) in H14.
          assert (x <> v) by (apply NoDup_cons_2 in H5; intro; subst x; exfalso; auto). clear -H0 H1 H2 H8 H14 H17 H19.
          assert (x = v) by (apply (is_tree_step_eq root x v v'); auto). auto.
        - apply NoDup_cons_1 with v; auto.
    Qed.

    Lemma graph_to_tree_nodup: forall lim root, vvalid G root -> is_tree G root -> NoDup (leaves (snd (graph_to_tree lim root))).
    Proof. intros. apply (proj1 (graph_to_tree_nodup' lim root H H0)). Qed.

    Lemma graph_to_tree_zero: forall lim root, fst (graph_to_tree lim root) = 0 -> lim = 0.
    Proof.
      intros. destruct lim. auto. simpl in H. remember (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))).
      remember (to_tree_list lim l (0, nil)). destruct p. simpl in H. exfalso; intuition.
    Qed.

    Lemma reachable_through_set_nonull_nodup: forall S x, reachable_through_set G S x <-> reachable_through_set G (nodup veq_dec (filter not_null_bool S)) x.
    Proof.
      intros. split; repeat intro; destruct H as [y [? ?]].
      + exists y. rewrite nodup_In. rewrite filter_In. do 2 (split; auto). unfold not_null_bool.
        destruct (is_null_dec y); auto. apply reachable_head_valid in H0. exfalso; apply (valid_not_null _ y); auto.
      + rewrite nodup_In in H. rewrite filter_In in H. destruct H. exists y. split; auto.
    Qed.

    Lemma Enumerable_step_list_enum: forall root l, vvalid G root -> is_tree G root -> Enumerable Vertex (reachable G root) -> step_list G root l ->
                                                    Enumerable Vertex (reachable_through_set G (nodup veq_dec (filter not_null_bool l))).
    Proof.
      intros. destruct X as [l' [? ?]]. exists (remove EV root l'). split. 1: apply nodup_remove_nodup; auto. unfold Ensembles.In in *. intros.
      pose proof (reachable_ind.reachable_ind' _ _ _ x H H1). rewrite remove_In_iff. rewrite H3, H4, reachable_through_set_nonull_nodup. clear -MA H0 H1.
      intuition. destruct H as [v [? ?]]. rewrite nodup_In in H. rewrite (in_step_list_edge _ _ _ H1) in H. subst. eapply is_tree_not_to_root; eauto.
    Qed.

    Lemma sizeOfEnum_step_list: forall root l (X: Enumerable Vertex (reachable_through_set G (nodup veq_dec (filter not_null_bool l)))) s lim,
        vvalid G root -> is_tree G root -> step_list G root l -> NoDup s -> (forall x, In x s <-> reachable G root x) -> 2 * (length s) - 1 <= S lim -> 2 * sizeOfEnum X <= lim.
    Proof.
      intros. destruct X as [l' [? ?]]. unfold sizeOfEnum. simpl in *. unfold Ensembles.In in i.
      assert (Permutation (root :: l') s). {
        apply NoDup_Permutation; auto.
        + constructor; auto. intro. rewrite i in H5. destruct H5 as [v [? ?]]. rewrite nodup_In in H5.
          apply (in_step_list_edge root) in H5; auto. eapply is_tree_not_to_root; eauto.
        + intros. simpl. rewrite i. rewrite H3. rewrite <- reachable_through_set_nonull_nodup. symmetry. apply reachable_ind.reachable_ind'; auto.
      } apply Permutation_length in H5. simpl in H5. clear -H5 H4. intuition.
    Qed.

    Lemma sizeOfEnum_cons: forall root l (X: Enumerable Vertex (reachable_through_set G l)) v s lim current tr,
        vvalid G root -> is_tree G root -> NoDup (v :: l) -> (forall y, In y (v :: l) -> step G root y /\ vvalid G y) -> vvalid G v -> is_tree G v -> NoDup s ->
        (forall x, In x s <-> reachable_through_set G (v :: l) x) -> 2 * length s <= S lim ->
        (current, tr) = graph_to_tree lim v -> current <> 0 -> (forall x, reachable G v x <-> In x (leaves tr)) -> 2 * sizeOfEnum X <= lim - current.
    Proof.
      intros. destruct X as [s' [? ?]]. unfold sizeOfEnum. simpl. unfold Ensembles.In in i.
      cut (length s' + length s' + current <= lim). 1: intuition. pose proof (graph_to_tree_nodup lim v H3 H4). rewrite <- H8 in H11. simpl in H11.
      assert (forall x, In x s <-> In x (leaves tr ++ s')) by (intros; rewrite H6, reachable_through_set_eq, in_app_iff, <- H10, i; tauto).
      assert (NoDup (leaves tr ++ s')). {
        apply NoDup_app_inv; auto. repeat intro. rewrite <- H10 in H13. rewrite i in H14. destruct H14 as [v' [? ?]].
        assert (v' = v) by (apply (is_tree_step_eq root v' v x); auto; [destruct (H2 v'); auto; right | destruct (H2 v); auto; left]; auto).
        subst. apply NoDup_cons_2 in H1. auto.
      } assert (Permutation s (leaves tr ++ s')) by (apply NoDup_Permutation; auto).
      apply Permutation_length in H14. rewrite app_length in H14.
      pose proof (graph_to_tree_lower_bound lim v). destruct (graph_to_tree lim v) as [current' tr']. inversion H8. subst current' tr'. rewrite H14 in H7.
      clear -H7 H17 H9. intuition.
    Qed.

    Lemma graph_to_tree_contains_reachable': forall lim root,
        vvalid G root -> is_tree G root ->
        forall x, reachable G root x ->
                  (forall (H: Enumerable Vertex (reachable G root)), 2 * sizeOfEnum H - 1 <= lim -> In x (leaves (snd (graph_to_tree lim root)))) /\
                  (forall n l trL (H: Enumerable Vertex (reachable_through_set G l)),
                      2 * sizeOfEnum H <= lim -> x <> root -> NoDup l ->
                      (forall y, In y l -> step G root y /\ vvalid G y) ->
                      ((exists i, In i l /\ reachable G i x) \/ In x (flat_map leaves trL)) ->
                      In x (flat_map leaves (snd (to_tree_list lim l (n, trL))))).
    Proof.
      intro lim. remember lim as up. rewrite Hequp. assert (lim <= up) by intuition. clear Hequp. revert lim H.
      induction up; intros; split; intros; pose proof H3 as XX; destruct H3 as [? [? ?]]; unfold sizeOfEnum in H4; simpl in H4; unfold Ensembles.In in i.
      + assert (lim = 0) by intuition. subst. rewrite <- i in H2. destruct x0. inversion H2. simpl in H4. exfalso; intuition.
      + assert (lim = 0) by intuition. subst. simpl. destruct H8; auto. assert (reachable_through_set G l x) by (apply H3).
        rewrite <- i in H8. destruct x0. inversion H8. simpl in H4. exfalso; intuition.
      + remember (graph_to_tree lim root). destruct p as [num t]. simpl. destruct lim. 1: rewrite <- i in H2; destruct x0; [inversion H2 | simpl in H4; exfalso; intuition].
        simpl in Heqp. remember (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))). assert (lim <= up) by intuition. clear H.
        assert (step_list G root (map (dst G) (edge_func G root))) by (subst l; clear; intro y; rewrite edge_func_step; intuition).
        assert (Enumerable Vertex (reachable_through_set G l)) by (subst l; apply (Enumerable_step_list_enum root); auto).
        rewrite Heql in X. assert (2 * sizeOfEnum X <= lim) by (apply (sizeOfEnum_step_list root _ _ x0); auto). destruct (IHup _ H3 _ H0 H1 _ H2) as [_ ?].
        specialize (H6 0 _ nil X H5). rewrite <- Heql in H6. remember (to_tree_list lim l (0, nil)). destruct p as [total sub_trees].
        inversion Heqp. subst num t. clear Heqp. clear IHup. simpl in *. destruct_eq_dec x root; [left | right]; auto. apply H6; auto.
        - rewrite Heql. apply NoDup_nodup.
        - intros. rewrite Heql in H8. rewrite nodup_In in H8. apply in_edge_func_edge in H8. destruct H8 as [? [? ?]]. split; auto.
        - left; clear -MA H2 Heql H7. apply reachable_by_ind in H2. destruct H2. 1: exfalso; auto. destruct H as [z [? ?]]. exists z. apply reachable_by_is_reachable in H0.
          split; auto. rewrite Heql. rewrite nodup_In, in_edge_func_edge; auto.
      + destruct lim.
        1: simpl; destruct H8; auto; unfold reachable_through_set in i; rewrite <- i in H3; assert (length x0 = 0) by intuition; destruct x0; [inversion H3 | inversion H8].
        destruct l. 1: simpl; destruct H8; auto; destruct H3 as [i' [? _]]; inversion H3.
        remember (to_tree_list (S lim) (v :: l) (n, trL)). destruct p as [num t]. simpl in Heqp. remember (graph_to_tree lim v). destruct p as [current tr].
        destruct (eq_nat_dec current 0).
        - inversion Heqp. subst. simpl. clear Heqp. destruct H8; auto. assert (lim = 0) by (apply (graph_to_tree_zero lim v); rewrite <- Heqp0; simpl; auto). subst.
          assert (length x0 = 0) by intuition. assert (x0 = nil) by (destruct x0; auto; inversion H8). subst.
          assert (reachable_through_set G (v :: l) x) by apply H3. rewrite <- i in H9. inversion H9.
        - assert (In v (v :: l)) by apply in_eq. pose proof (H7 _ H3); destruct H9. assert (is_tree G v) by (apply is_tree_sub_is_tree with root; auto).
          assert (Enumerable Vertex (reachable G v)) by
              (apply (@finite_reachable_enumcovered_enumerable _ _ _ _ _ is_null); auto; exists x0; split; auto; unfold Ensembles.In; intros; rewrite i; exists v; split; auto).
          assert (2 * sizeOfEnum X - 1 <= lim). {
            clear -n0 i H4 X H3. destruct X as [l' [? ?]]. unfold sizeOfEnum. simpl. unfold Ensembles.In in i0.
            assert (incl l' x0) by (intro; rewrite i, i0; intros; exists v; split; auto).
            assert (length l' <= length x0) by (apply NoDup_incl_length; auto). intuition.
          }
          assert (forall y, reachable G v y -> In y (leaves tr)). {
            intros. assert (lim <= up) by intuition. destruct (IHup _ H14 _ H10 H11 _ H13) as [? _]. specialize (H15 X H12).
            rewrite <- Heqp0 in H15. simpl in H15; auto.
          } clear X H12.
          assert (lim - current <= up) by intuition. destruct (IHup _ H12 _ H0 H1 _ H2) as [_ ?]. specialize (H14 (n + current + 1) l (tr :: trL)). clear H12 IHup.
          assert (Enumerable Vertex (reachable_through_set G l)). {
            apply (reachable_through_set_enum _ (v :: l)); [apply Enumerable_is_EnumCovered; exists x0; split; auto | apply incl_tl, incl_refl |].
            hnf. intros. assert (In x1 (v :: l)) by (right; auto). apply H7 in H15. destruct H15. hnf. right; auto.
          }
          assert (2 * sizeOfEnum X <= lim - current) by
              (apply (sizeOfEnum_cons root l X v x0 lim current tr); auto; intros; split; auto; intros; apply (graph_to_tree_is_reachable lim); auto; rewrite <- Heqp0; auto).
          specialize (H14 X H12). rewrite Heqp. apply H14; auto. 1: apply NoDup_cons_1 in H6; auto. 1: intros; apply H7; right; auto. clear H14.
          simpl. rewrite in_app_iff. destruct H8 as [[v' [? ?]]| ?].
          * simpl in H8. destruct H8. 1: subst v'; right; left; apply H13; auto. left. exists v'. split; auto.
          * right; right; auto.
    Qed.

    Lemma graph_to_tree_contains_reachable: forall lim root (H: Enumerable Vertex (reachable G root)) x,
        2 * sizeOfEnum H - 1 <= lim -> vvalid G root -> is_tree G root -> reachable G root x -> In x (leaves (snd (graph_to_tree lim root))).
    Proof. intros. apply ((proj1 (graph_to_tree_contains_reachable' lim _ H1 H2 _ H3)) H H0). Qed.

    Definition graph_match_tree_edges (s d : Vertex) (t: Tree) : Prop := exists t', find_tree s t t' /\ In d (forest_head (subtrees t')).

    Lemma graph_match_tree_edges_in: forall s d t t', graph_match_tree_edges s d t' -> In t' (subtrees t) -> graph_match_tree_edges s d t.
    Proof.
      intros. destruct t; simpl in H0. 1: exfalso; auto.
      destruct H as [t1 [? ?]]. exists t1. split; auto. apply FT_succ with t'; auto.
    Qed.

    Lemma graph_match_tree_edges_cons_1: forall s d root t tL, graph_match_tree_edges s d (T root (t :: nil)) -> graph_match_tree_edges s d (T root (t :: tL)).
    Proof.
      intros. destruct H as [t' [? ?]]. inversion H; subst.
      + exists (T root (t :: tL)). split. 1: apply FT_base. simpl in *. destruct t. 1: inversion H0. destruct H0. 2: exfalso; auto. subst. apply in_eq.
      + exists t'. split; auto. apply FT_succ with tr'; auto. simpl in *. destruct H4. 2: exfalso; auto. left; auto.
    Qed.

    Lemma graph_match_tree_edges_cons_2: forall s d root t tL, graph_match_tree_edges s d (T root tL) -> graph_match_tree_edges s d (T root (t :: tL)).
    Proof.
      intros. destruct H as [t' [? ?]]. inversion H; subst.
      + exists (T root (t :: tL)). split. 1: apply FT_base. simpl in *. destruct t; [|right]; auto.
      + exists t'. split; auto. apply FT_succ with tr'; auto. right; auto.
    Qed.

    Lemma graph_to_tree_contains_all_edges':
      forall lim root s d, vvalid G root -> is_tree G root -> reachable G root s -> reachable G root d -> G |= s ~> d ->
                           (forall H: Enumerable Vertex (reachable G root), 2 * sizeOfEnum H - 1 <= lim -> graph_match_tree_edges s d (snd (graph_to_tree lim root))) /\
                           (forall n l trL (H: Enumerable Vertex (reachable_through_set G l)),
                               2 * sizeOfEnum H <= lim -> (forall y, In y l -> step G root y /\ vvalid G y) ->
                               (reachable_through_set G l d  \/ graph_match_tree_edges s d (T root trL)) -> NoDup l ->
                               graph_match_tree_edges s d (T root (snd (to_tree_list lim l (n, trL))))).
    Proof.
      intro lim. remember lim as up. rewrite Hequp. assert (lim <= up) by intuition. clear Hequp. revert lim H.
      induction up; intros; split; intros; pose proof H5 as XX; destruct H5 as [? [? ?]]; unfold sizeOfEnum in H6; simpl in H6; unfold Ensembles.In in i.
      + assert (lim = 0) by intuition. subst. rewrite <- i in H2. destruct x. inversion H2. simpl in H6; exfalso; intuition.
      + assert (lim = 0) by intuition. subst. simpl. destruct H8; auto. rewrite <- i in H5. destruct x. inversion H5. simpl in H6. exfalso; intuition.
      + remember (graph_to_tree lim root). destruct p as [num t]. simpl. destruct lim. 1: rewrite <- i in H2; destruct x; [inversion H2 | simpl in H6; exfalso; intuition].
        simpl in Heqp. remember (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))). assert (lim <= up) by intuition. clear H.
        assert (step_list G root (map (dst G) (edge_func G root))) by (subst l; clear; intro y; rewrite edge_func_step; intuition).
        assert (Enumerable Vertex (reachable_through_set G l)) by (subst l; apply (Enumerable_step_list_enum root); auto).
        rewrite Heql in X. assert (2 * sizeOfEnum X <= lim) by (apply (sizeOfEnum_step_list root _ _ x); auto).
        destruct (IHup _ H5 _ _ _ H0 H1 H2 H3 H4) as [_ ?]. specialize (H8 0 _ nil X H7). rewrite <- Heql in H8. remember (to_tree_list lim l (0, nil)).
        destruct p as [total sub_trees]. inversion Heqp. subst num t. clear Heqp. clear IHup. simpl in *. apply H8.
        - intros. rewrite Heql in H9. rewrite nodup_In in H9. apply in_edge_func_edge in H9. destruct H9 as [? [? ?]]. split; auto.
        - left. rewrite Heql. rewrite <- reachable_through_set_nonull_nodup. apply (reachable_ind.step_list_step_reachable _ root s); auto.
        - rewrite Heql. apply NoDup_nodup.
      + destruct lim. 1: simpl; destruct H8; auto; rewrite <- i in H5; destruct x; [inversion H5 | simpl in H6; exfalso; intuition].
        destruct l. 1: simpl; destruct H8; auto; destruct H5 as [? [? ?]]; inversion H5.
        remember (to_tree_list (S lim) (v :: l) (n, trL)). destruct p as [num t]. simpl in Heqp. remember (graph_to_tree lim v). destruct p as [current tr].
        destruct (eq_nat_dec current 0).
        - inversion Heqp. subst. simpl. clear Heqp. destruct H8; auto. assert (lim = 0) by (apply (graph_to_tree_zero lim v); rewrite <- Heqp0; simpl; auto). subst.
          assert (length x = 0) by intuition. assert (x = nil) by (destruct x; auto; inversion H8). subst.
          assert (reachable_through_set G (v :: l) v) by
              (assert (In v (v :: l)) by apply in_eq; exists v; split; auto; apply reachable_by_refl; auto; destruct (H7 _ H10); auto).
          rewrite <- i in H10. inversion H10.
        - assert (In v (v :: l)) by apply in_eq. pose proof (H7 _ H5); destruct H10. assert (is_tree G v) by (apply is_tree_sub_is_tree with root; auto).
          assert (Enumerable Vertex (reachable G v)) by
              (apply (@finite_reachable_enumcovered_enumerable _ _ _ _ _ is_null); auto; exists x; split; auto; unfold Ensembles.In; intros; rewrite i; exists v; split; auto).
          assert (2 * sizeOfEnum X - 1 <= lim). {
            clear -n0 i H6 X H5. destruct X as [l' [? ?]]. unfold sizeOfEnum. simpl. unfold Ensembles.In in i0.
            assert (incl l' x) by (intro; rewrite i, i0; intros; exists v; split; auto).
            assert (length l' <= length x) by (apply NoDup_incl_length; auto). intuition.
          }
          assert (reachable G v d -> graph_match_tree_edges s d (T root ((snd (graph_to_tree lim v)) :: nil))). {
            assert (EnumCovered Vertex (reachable G v)) by (apply Enumerable_is_EnumCovered; auto). intros. destruct (reachable_decidable_prime G v H11 X0 s).
            + assert (lim <= up) by intuition. destruct (IHup _ H15 v s d H11 H12 r H14 H4) as [? _]. clear IHup. specialize (H16 X H13).
              apply (graph_match_tree_edges_in _ _ _ _ H16). apply in_eq.
            + clear IHup. apply reachable_ind.reachable_ind in H2. destruct H2.
              - subst s. assert (d = v) by (destruct H4 as [? [? ?]]; apply (is_tree_step_eq root d v d); auto; apply reachable_refl; auto). subst d.
                exists (T root (snd (graph_to_tree lim v) :: nil)). split. 1: apply FT_base. rewrite <- Heqp0. unfold snd. clear -Heqp0 n1.
                destruct lim; simpl in Heqp0. inversion Heqp0. 1: exfalso; auto. remember (nodup veq_dec (filter not_null_bool (map (dst G) (edge_func G v)))).
                destruct (to_tree_list lim l (0, nil)). inversion Heqp0. simpl. left; auto.
              - exfalso. apply n2. destruct H2 as [z [? [? ?]]].
                assert (z = v) by (apply (is_tree_step_eq root z v d); auto; [destruct H2 as [? [? ?]] | apply reachable_edge with s]; auto). subst z; auto.
          }
          assert (Hs: forall y : Vertex, reachable G v y <-> In y (leaves tr)). {
            intro. split; intros.
            + apply (graph_to_tree_contains_reachable lim _ X) in H15; auto. rewrite <- Heqp0 in H15. simpl in H15; auto.
            + apply (graph_to_tree_is_reachable lim); auto. rewrite <- Heqp0. simpl; auto.
          } clear X H13.
          assert (lim - current <= up) by intuition. destruct (IHup _ H13 _ _ _ H0 H1 H2 H3 H4) as [_ ?]. specialize (H15 (n + current + 1) l (tr :: trL)). clear H13 IHup.
          assert (Enumerable Vertex (reachable_through_set G l)). {
            apply (reachable_through_set_enum _ (v :: l)); [apply Enumerable_is_EnumCovered; exists x; split; auto | apply incl_tl, incl_refl |].
            hnf. intros. assert (In x0 (v :: l)) by (right; auto). apply H7 in H16. destruct H16. hnf. right; auto.
          } assert (2 * sizeOfEnum X <= lim - current) by (apply (sizeOfEnum_cons root l X v x lim current tr); auto).
          specialize (H15 X H13). rewrite Heqp. apply H15; [intros; apply H7; right | | apply NoDup_cons_1 in H9]; auto. clear H15 X H13.
          rewrite reachable_through_set_eq in H8. destruct H8 as [[? | ?] | ?]. 2: left; auto.
          * specialize (H14 H8). right. rewrite <- Heqp0 in H14. simpl in H14. apply graph_match_tree_edges_cons_1; auto.
          * right. apply graph_match_tree_edges_cons_2; auto.
    Qed.

    Lemma graph_to_tree_contains_all_edges:
      forall lim root s d (H: Enumerable Vertex (reachable G root)), vvalid G root -> is_tree G root -> reachable G root s -> reachable G root d -> G |= s ~> d ->
                                                                     2 * sizeOfEnum H - 1 <= lim -> graph_match_tree_edges s d (snd (graph_to_tree lim root)).
    Proof. intros. apply ((proj1 (graph_to_tree_contains_all_edges' lim _ _ _ H0 H1 H2 H3 H4)) H H5). Qed.

    Theorem is_tree_is_tree: forall root, vvalid G root -> EnumCovered Vertex (reachable G root) -> is_tree G root -> {tree | graph_tree_isomorphism_v G tree root}.
    Proof.
      intros. pose proof X as XX. destruct X as [ul [? ?]]. unfold Ensembles.In in H2. remember (graph_to_tree (2 * (length ul)) root) as nT.
      destruct nT as [n tree]. exists tree. split; [|split]; intros.
      + split; intro.
        - pose proof (finite_reachable_enumcovered_enumerable _ _ H XX). destruct H3 as [? [? ?]].
          pose proof (graph_to_tree_contains_all_edges (2 * length ul) _ _ _ X H H0 H3 H4 H5). rewrite <- HeqnT in H6. apply H6. clear H6.
          destruct X as [l [? ?]]. unfold sizeOfEnum. simpl. unfold Ensembles.In in i. cut (length l <= length ul). 1: intuition.
          apply NoDup_incl_length; auto. repeat intro. apply H2. rewrite <- i. auto.
        - destruct H3 as [t' [? ?]]. assert (G |= s ~> d) by (apply (graph_to_tree_edge (2 * length ul) s d t' root); auto; rewrite <- HeqnT; simpl; auto).
          split; [|split]; auto.
          * apply find_tree_in_leaves in H3. apply (graph_to_tree_is_reachable (2 * length ul) root s); auto. rewrite <- HeqnT; simpl; auto.
          * apply forest_head_in_leaves in H4. pose proof (find_tree_in_leaves' _ _ _ H3 d H4).
            apply (graph_to_tree_is_reachable (2 * length ul) root d); auto. rewrite <- HeqnT; simpl; auto.
      + split; intros.
        - pose proof (finite_reachable_enumcovered_enumerable _ _ H XX). change (leaves tree) with (leaves (snd (n, tree))). rewrite HeqnT.
          apply (graph_to_tree_contains_reachable _ _ X); auto. destruct X as [l [? ?]]. unfold sizeOfEnum. simpl. unfold Ensembles.In in i.
          cut (length l <= length ul). 1: intuition. apply NoDup_incl_length; auto. repeat intro. apply H2. rewrite <- i. auto.
        - apply (graph_to_tree_is_reachable (2 * length ul)); auto. rewrite <- HeqnT; simpl; auto.
      + pose proof (graph_to_tree_nodup (2 * length ul) root H H0). rewrite <- HeqnT in H3. simpl in H3. auto.
    Qed.

  End CONVERSION.

End TREE_DEF.
