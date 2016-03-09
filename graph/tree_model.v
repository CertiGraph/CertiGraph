Require Import Coq.Arith.Arith.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
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
    Context {MA: MathGraph G}.
    Context {LF: LocalFiniteGraph G}.

    Definition not_null_bool (v: Vertex) := if is_null_dec G v then false else true.

    Fixpoint graph_to_tree (limit: nat) (root: Vertex): nat * Tree :=
      match limit with
      | O => (O, EPT)
      | S n => let vertices_list := remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G root))) in
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

    Lemma in_edge_func_edge: forall root, forall x, In x (filter not_null_bool (map (dst G) (edge_func G root))) -> edge G root x.
    Proof.
      intros. rewrite filter_In in H. destruct H. unfold not_null_bool in H0. destruct (is_null_dec G x). 1: inversion H0.
      rewrite <- edge_func_step in H. pose proof H. rewrite step_spec in H1. destruct H1 as [e [? [? ?]]].
      destruct (valid_graph G e H1). rewrite H2 in H4. rewrite H3 in H5. destruct H5. 1: exfalso; auto. split; auto.
    Qed.

    Lemma graph_to_tree_bound': forall lim, (forall root, fst (graph_to_tree lim root) <= lim) /\
                                            (forall l n trL, fst (to_tree_list lim l (n, trL)) <= lim + n).
    Proof.
      intro lim. remember lim as up.  rewrite Hequp. assert (lim <= up) by intuition. clear Hequp. revert lim H. induction up; intros; split; intros.
      + assert (lim = 0) by intuition. subst. simpl; auto.
      + assert (lim = 0) by intuition. subst. simpl; auto.
      + destruct lim; simpl; auto. remember (to_tree_list lim (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))) (0, nil)).
        destruct p as [total sub_trees]. simpl. assert (lim <= up) by intuition. destruct (IHup _ H0) as [_ ?]. 
        specialize (H1 (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))) 0 nil). rewrite <- Heqp in H1. simpl in H1. intuition.
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
        specialize (H1 (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))) 0 nil). assert (0 = 2 * sum_of_leaves nil) by intuition. specialize (H1 H2).
        remember (to_tree_list lim (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))) (0, nil)). destruct p as [total sub_trees]. simpl.
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
        remember (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))). destruct l.
        1: simpl in H1; destruct H1; [subst | exfalso; auto]; apply reachable_refl; auto.
        remember (graph_to_tree lim v). destruct p as [current tr]. destruct (eq_nat_dec current 0). 1: simpl in H1; destruct H1; [subst; apply reachable_refl | exfalso]; auto.
        remember (to_tree_list (lim - current) l (current + 1, tr :: nil)). destruct p as [total sub_trees].
        simpl in H1. destruct H1. 1: subst; apply reachable_refl; auto.
        assert (Forall (reachable G root) (v :: l)). {
          rewrite Forall_forall. intro y; intros. rewrite Heql in H2. rewrite <- remove_dup_in_inv in H2. apply in_edge_func_edge in H2.
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
              remember (to_tree_list lim (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G v)))) (0, nil)).
              destruct p as [total sub_trees]. inversion Heqp. auto.
            } subst. exists v. simpl. split. 1: left; auto. pose proof (graph_to_tree_is_reachable lim v y). apply H4.
            - apply Forall_inv in H0; auto.
            - rewrite <- Heqp. simpl; auto.
          + specialize (H1 y H3). destruct tr. 1: apply H1. destruct H1 as [v1 [? ?]]. exists v1. split; auto. simpl. right; auto.
        } specialize (IHup H3 _ H2). clear H2 H3 n0. destruct IHup as [v' [? ?]]. exists v'. split; auto. apply in_app_or in H2. apply in_or_app. destruct H2.
        - left. simpl. right. auto.
        - simpl in H2. destruct tr. 1: right; auto. simpl in H2. destruct H2. 2: right; auto. subst.
          assert (v' = v). {
            destruct lim; simpl in Heqp. 1: inversion Heqp. remember (to_tree_list lim (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G v)))) (0, nil)).
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
        remember (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))). destruct l. 1: simpl in H1; destruct H1; [subst | exfalso]; auto.
        remember (graph_to_tree lim v). destruct p as [current tr]. destruct (eq_nat_dec current 0). 1: simpl in H1; destruct H1; [subst | exfalso]; auto.
        remember (to_tree_list (lim - current) l (current + 1, tr :: nil)). destruct p as [total sub_trees].
        simpl in H1. destruct H1. 1: subst; auto.
        assert (Forall (vvalid G) (v :: l)). {
          rewrite Forall_forall. intro y; intros. rewrite Heql in H2. rewrite <- remove_dup_in_inv in H2. apply in_edge_func_edge in H2. destruct H2 as [? [? ?]]; auto.
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
        remember (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))). destruct l; simpl in H0. 
        1: inversion H0; [| inversion H5]; clear v t0 H2 H5; subst s; subst t; simpl in H1; exfalso; auto.
        remember (graph_to_tree lim v). destruct p as [current tr]. destruct (eq_nat_dec current 0). 1: inversion H0; subst; [simpl in H1 | simpl in H5]; exfalso; auto. 
        remember (to_tree_list (lim - current) l (current + 1, tr :: nil)). destruct p as [total sub_trees].
        simpl in H0. assert (lim - current <= up) by intuition. destruct (IHup _ H2) as [_ ?].
        specialize (H3 s d t root l (current + 1) (tr :: nil)).
        assert (forall m : Vertex, In m (v :: l) -> G |= root ~> m). { intros. rewrite Heql in H4. rewrite <- remove_dup_in_inv in H4; apply in_edge_func_edge; auto. }
        assert (forall m : Vertex, In m (forest_head (tr :: nil)) -> G |= root ~> m). {
          intros. clear H1 H2 H3. destruct lim; simpl in Heqp. 1: inversion Heqp; subst; simpl in H5; exfalso; auto.
          remember (to_tree_list lim (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G v)))) (0, nil)). destruct p as [total1 sub_trees1].
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
          remember (to_tree_list lim (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G v)))) (0, nil)). destruct p as [total1 sub_trees1].
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
      + destruct lim; simpl. 1: apply NoDup_nil. pose proof (to_tree_list_is_reachable lim (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))) 0 nil).
        remember (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))). simpl in H2. rewrite app_nil_r in H2.
        assert (Forall (vvalid G) l). {
          clear H2; rewrite Forall_forall. intros. subst. rewrite <- remove_dup_in_inv in H2.
          apply in_edge_func_edge in H2. destruct H2 as [? [? ?]]. apply H3.
        }
        assert (forall x : Vertex, False -> exists v : Vertex, False /\ reachable G v x) by (intros; exfalso; auto). specialize (H2 H3 H4). clear H4.
        remember (to_tree_list lim l (0, nil)). destruct p as [total sub_trees]. simpl in *. constructor.
        - intro. specialize (H2 _ H4). destruct H2 as [v [? ?]]. assert (reachable G root root) by (apply reachable_refl; auto). specialize (H1 _ H6).
          destruct H1 as [p [? ?]]. assert (G |= (root :: nil) is root ~o~> root satisfying (fun _ => True)) by (split; split; simpl; hnf; auto). pose proof (H7 _ H8).
          destruct H5 as [path ?]. assert (G |= (root :: path) is root ~o~> root satisfying (fun _ => True)). {
            destruct H5 as [[? ?] [? _]]. split; split. 1: simpl; auto.
            + simpl. destruct path; auto.
            + simpl. destruct path; auto. split; auto. assert (v0 = v) by (simpl in H5; inversion H5; auto). subst v0.
              rewrite Heql in H2. rewrite <- remove_dup_in_inv in H2. rewrite filter_In in H2.
              destruct H2. unfold not_null_bool in H12. destruct (is_null_dec G v). 1: inversion H12.
              rewrite <- edge_func_step in H2. pose proof H2. rewrite step_spec in H2. destruct H2 as [e [? [? ?]]]. destruct (valid_graph G e H2).
              rewrite H14 in H16. rewrite H15 in H17. destruct H17. 1: exfalso; auto. split; auto.
            + hnf. rewrite Forall_forall. intros; auto.
          } specialize (H7 _ H10). rewrite H7 in H9. inversion H9. subst. clear -H5. destruct H5 as [[? _] _]. simpl in H. inversion H.
        - assert (lim <= up) by intuition. destruct (IHup _ H4 _ H0 H1) as [_ ?]. clear IHup. specialize (H5 l 0 nil). rewrite <- Heqp in H5.
          simpl in H5. apply H5.
          * intros. subst l. rewrite <- remove_dup_in_inv in H6. apply in_edge_func_edge in H6. destruct H6 as [? [? ?]]. split; auto.
          * apply NoDup_nil.
          * intros. intro; auto.
          * rewrite Heql. apply remove_dup_nodup.
      + destruct lim; simpl; auto. destruct l; simpl; auto. remember (graph_to_tree lim v). destruct p as [current tr]. destruct (eq_nat_dec current 0).
        1: simpl; auto. assert (lim  <= up) by intuition. assert (In v (v :: l)) by (simpl; left; auto). destruct (H2 _ H7).
        assert (is_tree G v) by (apply is_tree_sub_is_tree with root; auto). destruct (IHup _ H6 _ H9 H10) as [? _]. rewrite <- Heqp in H11. simpl in H10.
        assert (lim - current <= up) by intuition. destruct (IHup _ H12 _ H0 H1) as [_ ?]. clear IHup.
        specialize (H13 l (n + current + 1) (tr :: trL)). simpl in H13. apply H13; clear H13.
        - intros. apply H2. simpl; right; auto.
        - apply NoDup_app_inv; auto. intros. specialize (H4 v x lim). rewrite <- Heqp in H4. simpl in H4. apply H4; auto.
        - intros x v' m; intros. intro. apply in_app_or in H15. assert (In x (v :: l)) by (simpl; right; auto). destruct H15. 2: specialize (H4 x v' m H16 H14); apply H4; auto.
          pose proof (graph_to_tree_is_reachable lim v v' H9). rewrite <- Heqp in H17. simpl in H17. specialize (H17 H15).
          specialize (H2 _ H16). destruct H2. apply (graph_to_tree_is_reachable m x v' H18) in H14.
          assert (x <> v) by (apply NoDup_cons_2 in H5; intro; subst x; exfalso; auto). clear -H0 H1 H2 H8 H14 H17 H19.
          assert (reachable G root v') by (apply step_reachable with x; auto). specialize (H1 _ H). destruct H1 as [p [? ?]]. destruct H14 as [px ?]. destruct H17 as [pv ?].
          assert (forall pa a, step G root a -> G |= pa is a ~o~> v' satisfying (fun _ : Vertex => True) ->
                               G |= (root :: pa) is root ~o~> v' satisfying (fun _ : Vertex => True)). {
            intros. clear -H0 H6 H7. destruct pa. 1: destruct H7 as [[? _] _]; simpl in H; inversion H.
            assert (v = a) by (destruct H7 as [[? _] _]; simpl in H; inversion H; auto). subst v.
            assert (root :: a :: pa = path_glue (root :: a :: nil) (a :: pa)) by intuition. rewrite H; clear H. apply reachable_by_path_merge with a; auto.
            split; split; simpl; auto. 2: hnf; rewrite Forall_forall; intros; auto.
            apply reachable_by_path_is_reachable in H7. apply reachable_by_head_valid in H7. split; [split|]; auto.
          } pose proof (H6 _ _ H2 H4). specialize (H6 _ _ H8 H5). apply H3 in H6. apply H3 in H7. rewrite H6 in H7. inversion H7.
          destruct px. 1: destruct H4 as [[? _] _]; simpl in H4; inversion H4. assert (v0 = x) by (destruct H4 as [[? _] _]; simpl in H4; inversion H4; auto). subst v0.
          destruct pv. 1: destruct H5 as [[? _] _]; simpl in H5; inversion H5. assert (v0 = v) by (destruct H5 as [[? _] _]; simpl in H5; inversion H5; auto). subst v0.
          inversion H10. exfalso; auto.
        - apply NoDup_cons_1 with v; auto.
    Qed.

    Lemma graph_to_tree_nodup: forall lim root, vvalid G root -> is_tree G root -> NoDup (leaves (snd (graph_to_tree lim root))).
    Proof. intros. apply (proj1 (graph_to_tree_nodup' lim root H H0)). Qed.

    Lemma graph_to_tree_zero: forall lim root, fst (graph_to_tree lim root) = 0 -> lim = 0.
    Proof.
      intros. destruct lim. auto. simpl in H. remember (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))).
      remember (to_tree_list lim l (0, nil)). destruct p. simpl in H. exfalso; intuition.
    Qed.

    Lemma graph_to_tree_contains_reachable:
      forall lim root, vvalid G root -> is_tree G root -> forall x, reachable G root x ->
                       (fst (graph_to_tree lim root) < lim -> In x (leaves (snd (graph_to_tree lim root)))) /\
                       (forall n l trL, x <> root -> ((exists i, In i l /\ reachable G i x) \/ In x (flat_map leaves trL)) -> fst (to_tree_list lim l (n, trL)) < lim ->
                                        In x (flat_map leaves (snd (to_tree_list lim l (n, trL))))).
    Proof.
      intro lim. remember lim as up.  rewrite Hequp. assert (lim <= up) by intuition. clear Hequp. revert lim H. induction up; intros; split; intros. 
      + assert (lim = 0) by intuition. subst. exfalso; intuition.
      + assert (lim = 0) by intuition. subst. exfalso; intuition.
      + remember (graph_to_tree lim root). destruct p as [n t]. simpl in *. destruct lim. 1: exfalso; intuition.
        simpl in Heqp. remember (remove_dup veq_dec (filter not_null_bool (map (dst G) (edge_func G root)))).
        assert (lim <= up) by intuition. destruct (IHup _ H4 _ H0 H1 _ H2) as [_ ?]. specialize (H5 0 l nil). 
        remember (to_tree_list lim l (0, nil)). destruct p as [total sub_trees]. inversion Heqp. subst n t. clear Heqp. simpl in *.
        destruct_eq_dec x root; [left | right]; auto. apply H5; [auto | | intuition]. left. destruct (root_reachable_by_derive _ _ _ _ H2). 1: exfalso; auto.
        destruct H7 as [e [? ?]]. apply reachable_by_is_reachable in H8. exists (dst G e). split; auto. rewrite Heql. rewrite <- remove_dup_in_inv. rewrite filter_In. split.
        - rewrite <- edge_func_step. rewrite step_spec. exists e. destruct H7. split; auto.
        - unfold not_null_bool. destruct (is_null_dec G (dst G e)); [|auto]. apply reachable_head_valid in H8. exfalso. apply (valid_not_null G (dst G e)); auto.
      + destruct lim. 1: simpl in H5; exfalso; intuition. destruct l. 1: simpl; destruct H4; auto; destruct H4 as [i [? _]]; exfalso; intuition.
        remember (to_tree_list (S lim) (v :: l) (n, trL)). destruct p as [num t]. simpl in Heqp. remember (graph_to_tree lim v). destruct p as [current tr].
        destruct (eq_nat_dec current 0).
        - inversion Heqp. subst. simpl. clear Heqp. destruct H4; auto. assert (lim  = 0) by (apply (graph_to_tree_zero lim v); rewrite <- Heqp0; simpl; auto). subst.
          simpl in H5.
    Abort.

    Lemma is_tree_is_tree: forall root, vvalid G root -> EnumCovered Vertex (reachable G root) -> is_tree G root ->  {tree | graph_tree_isomorphism_v G tree root}.
    Proof.
      intros. destruct X as [ul [? ?]]. unfold Ensembles.In in H2. remember (graph_to_tree (2 * (length ul)) root) as nT.
      destruct nT as [n tree]. exists tree. split; [|split]; intros.
      + split; intro.
        - admit.
        - destruct H3 as [t' [? ?]]. assert (G |= s ~> d) by (apply (graph_to_tree_edge (2 * length ul) s d t' root); auto; rewrite <- HeqnT; simpl; auto).
          split; [|split]; auto.
          * apply find_tree_in_leaves in H3. apply (graph_to_tree_is_reachable (2 * length ul) root s); auto. rewrite <- HeqnT; simpl; auto.
          * apply forest_head_in_leaves in H4. pose proof (find_tree_in_leaves' _ _ _ H3 d H4).
            apply (graph_to_tree_is_reachable (2 * length ul) root d); auto. rewrite <- HeqnT; simpl; auto.
      + split; intros.
        - destruct (H0 _ H3) as [p [? ?]]. admit.
        - apply (graph_to_tree_is_reachable (2 * length ul)); auto. rewrite <- HeqnT; simpl; auto.
      + pose proof (graph_to_tree_nodup (2 * length ul) root H H0). rewrite <- HeqnT in H3. simpl in H3. auto.
    Qed.
    
  End CONVERSION.

End TREE_DEF.

Eval compute in (forest_head (subtrees (T 1 (T 2 nil :: T 3 nil :: T 4 (T 5 nil :: T 6 nil :: nil) :: nil)))).
