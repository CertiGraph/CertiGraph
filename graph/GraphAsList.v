Require Import Coq.Classes.Morphisms.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.FiniteGraph.

Section LIST_DEF.

  Variable V E: Type.

  Definition GList := (V * list (E * V))%type.

  Fixpoint shiftLeft (v: V) (l: list (E * V)) : list (V * E) :=
    match l with
    | nil => nil
    | (e, v') :: l' => (v, e) :: (shiftLeft v' l')
    end.

  Fixpoint tailVertex (v: V) (l: list (E * V)) : V :=
    match l with
    | nil => v
    | (e, v') :: l' => tailVertex v' l'
    end.

  Lemma tailVertex_foot: forall v l e' v', tailVertex v (l +:: (e', v')) = v'.
  Proof. intros. revert v. induction l; simpl; auto. destruct a; auto. Qed.

  Lemma shiftLeft_app: forall v e x l1 l2, In (v, e) (shiftLeft x (l1 ++ l2)) <-> In (v, e) (shiftLeft x l1) \/ In (v, e) (shiftLeft (tailVertex x l1) l2).
  Proof.
    intros v e x. apply (rev_ind (fun l1 => forall l2, In (v, e) (shiftLeft x (l1 ++ l2)) <-> In (v, e) (shiftLeft x l1) \/ In (v, e) (shiftLeft (tailVertex x l1) l2))).
    - intros. simpl. intuition.
    - intros. rewrite <- app_assoc, <- app_comm_cons, app_nil_l. rewrite H. destruct x0 as [e' v']. simpl. rewrite H. simpl. rewrite tailVertex_foot. intuition.
  Qed.  

  Fixpoint listVertices' (l: list (E * V)) : list V :=
    match l with
    | nil => nil
    | (e, v) :: l' => v :: (listVertices' l')
    end.

  Lemma listVertices'_length: forall l, length (listVertices' l) = length l.
  Proof. induction l; intros; simpl; auto. destruct a. simpl. rewrite IHl; auto. Qed.

  Lemma listVertices'_In_app: forall l1 l2 v,
      In v (listVertices' (l1 ++ l2)) <->
      In v (listVertices' l1) \/ In v (listVertices' l2).
  Proof. intros l1; induction l1; intros; simpl. 1: tauto. destruct a. simpl. rewrite IHl1. tauto. Qed.

  Lemma listVertices'_In_rev: forall l v,
      In v (listVertices' l) <-> In v (listVertices' (rev l)).
  Proof. induction l; intros; simpl. 1: tauto. destruct a. simpl. rewrite listVertices'_In_app. simpl. rewrite IHl. tauto. Qed.

  Lemma listVertices'_In_length_reachable {EV: EqDec V eq} {EE: EqDec E eq}:
    forall (g: PreGraph V E) root len r (X: EnumCovered V (reachable g root)),
      length (proj1_sig X) <= len -> NoDup (listVertices' r) -> len <= length r ->
      (forall v, In v (listVertices' r) -> reachable g root v) ->
      forall v, reachable g root v -> In v (listVertices' r).
  Proof.
    intros. destruct X as [pl [? ?]]. simpl in H. unfold Ensembles.In in i.
    assert (incl (listVertices' r) pl) by (hnf; intros; apply H2 in H4; apply i in H4; auto). apply NoDup_Permutation_bis in H4; auto.
    1: specialize (i _ H3); apply Permutation_sym in H4; apply Permutation_in with pl; auto.
    apply NoDup_incl_length in H4; auto. rewrite <- listVertices'_length in H1. intuition.
  Qed.

  Definition listVertices (l: GList) :=
    match l with (v, l') => v :: listVertices' l' end.

  Fixpoint listEdges' (l: list (E * V)): list E :=
    match l with
    | nil => nil
    | (e, v) :: l' => e :: (listEdges' l')
    end.

  Lemma listEdges'_length: forall l, length (listEdges' l) = length l. Proof. induction l; intros; simpl; auto. destruct a. simpl. rewrite IHl; auto. Qed.

  Lemma listEdges'_app: forall l1 l2, listEdges' (l1 ++ l2) = listEdges' l1 ++ listEdges' l2.
  Proof. intro l1; induction l1; intros; simpl; auto. destruct a. simpl. rewrite IHl1. auto. Qed.

  Lemma listEdges'_In_app: forall l1 l2 e, In e (listEdges' (l1 ++ l2)) <-> In e (listEdges' l1) \/ In e (listEdges' l2).
  Proof. intros. rewrite listEdges'_app. rewrite in_app_iff. intuition. Qed.

  Lemma listEdges'_Permutation_rev: forall l, Permutation (listEdges' l) (listEdges' (rev l)).
  Proof.
    induction l; simpl.
    - apply perm_nil.
    - destruct a. simpl. rewrite listEdges'_app. simpl. rewrite IHl. apply Permutation_cons_append.
  Qed.

  Lemma listEdges'_In_rev: forall l e, In e (listEdges' l) <-> In e (listEdges' (rev l)).
  Proof. intros. pose proof (listEdges'_Permutation_rev l). rewrite H. intuition. Qed.

  Lemma listEdges'_NoDup_rev: forall l, NoDup (listEdges' l) <-> NoDup (listEdges' (rev l)).
  Proof. intros. pose proof (listEdges'_Permutation_rev l). rewrite H. tauto. Qed.

  Lemma listEdges'_In_length_reachable {EV: EqDec V eq} {EE: EqDec E eq}:
    forall (g: PreGraph V E) root len r (X: EnumCovered V (reachable g root)),
      length (proj1_sig X) <= len -> NoDup (listEdges' r) -> len <= length r ->
      (forall e, In e (listEdges' r) -> evalid g e /\ reachable g root (src g e) /\ vvalid g (dst g e)) ->
      (forall s e1 e2, reachable g root s -> src g e1 = s -> src g e2 = s -> evalid g e1 -> evalid g e2 -> vvalid g (dst g e1) -> vvalid g (dst g e2) -> e1 = e2) ->
      forall e, evalid g e -> reachable g root (src g e) -> vvalid g (dst g e) -> In e (listEdges' r).
  Proof.
    intros. destruct X as [pl [? ?]]. simpl in H. unfold Ensembles.In in i. remember (map (src g) (listEdges' r)).
    assert (incl l pl). {
      hnf; intros; subst l; rewrite in_map_iff in H7; destruct H7 as [e' [? ?]].
      apply H2 in H8. destruct H8 as [? [? ?]]; rewrite H7 in H9; apply i; auto.
    } apply NoDup_Permutation_bis in H7; auto.
    - specialize (i _ H5). apply Permutation_sym in H7. apply (Permutation_in (src g e)) in H7; auto. subst l.
      rewrite in_map_iff in H7. destruct H7 as [e' [? ?]]. pose proof H8. apply H2 in H8. destruct H8 as [? [? ?]].
      assert (e = e') by (apply (H3 (src g e)); auto). subst e; auto.
    - subst l. remember (listEdges' r) as l. clear Heql H7. induction l; simpl. 1: apply NoDup_nil. apply NoDup_cons.
      + clear IHl. intro. rewrite in_map_iff in H7. destruct H7 as [a' [? ?]]. assert (In a (a :: l)) by apply in_eq. assert (In a' (a :: l)) by (apply in_cons; auto).
        apply H2 in H9. apply H2 in H10. destruct H9 as [? [? ?]]. destruct H10 as [? [? ?]]. assert (a = a') by (apply (H3 (src g a)); auto). subst a'.
        rewrite NoDup_cons_iff in H0. destruct H0. clear -H0 H8. auto.        
      + apply IHl.
        * rewrite NoDup_cons_iff in H0. destruct H0; auto.
        * intros. apply H2. simpl; right; auto.
    - clear -H H1 Heql. pose proof (map_length (src g) (listEdges' r)). rewrite <- Heql in *. rewrite listEdges'_length in H0. rewrite H0. intuition.
  Qed.
  
  Definition listEdges (l: GList) := listEdges' (snd l).

End LIST_DEF.

Arguments listVertices {_} {_} _.
Arguments listEdges {_} {_} _.

Section IS_LIST.

  Context {Vertex: Type}.
  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.

  Variable g : PreGraph Vertex Edge.

  Definition is_list (x: Vertex) : Prop :=
    exists p, valid_path g p /\ forall y, reachable g x y -> exists (py: path), unique (fun pa => g |= pa is x ~o~> y satisfying (fun _ => True)) py /\ Subpath g py p.

    Lemma is_list_no_loop: forall root s p, is_list root -> reachable g root s -> snd p <> nil -> ~ g |= p is s ~o~> s satisfying (fun _ => True).
  Proof.
    repeat intro. destruct H as [pf [? ?]]. apply H3 in H0. clear H3. destruct H0 as [ps [[? ?] ?]]. pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H0 H2).
    apply H3 in H5. destruct ps as [v ps]. unfold path_glue in H5. simpl in H5. inversion H5. destruct p; simpl in *. rewrite app_nil_end in H7 at 1.
    apply app_inv_head in H7. auto.
  Qed.

  Lemma is_list_no_edge_loop: forall root s t, is_list root -> reachable g root s -> g |= s ~> t -> reachable g t s -> False.
  Proof.
    intros. destruct H1 as [? [? ?]]. rewrite step_spec in H4. destruct H4 as [e [? [? ?]]]. destruct H2 as [p ?].
    assert (g |= (s, e :: nil) is s ~o~> t satisfying (fun _ => True)). {
      split; split; simpl; auto.
      + unfold strong_evalid. rewrite H5, H6. split; auto.
      + hnf. rewrite Forall_forall; intros; auto.
    } pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H7 H2). apply (is_list_no_loop root) in H8; auto. simpl. intro. inversion H9.
  Qed.

  Lemma is_list_no_self_edge: forall root s, is_list root -> reachable g root s -> g |= s ~> s -> False.
  Proof. intros. apply (is_list_no_edge_loop root s s); auto. apply reachable_foot_valid in H0. apply reachable_refl; auto. Qed.

  Lemma is_list_same_src_same_edge: forall root s e1 e2, is_list root -> reachable g root s -> src g e1 = s -> src g e2 = s -> evalid g e1 -> evalid g e2 ->
                                                         vvalid g (dst g e1) -> vvalid g (dst g e2) -> e1 = e2.
  Proof.
    intros. assert (vvalid g s) by (apply reachable_foot_valid in H0; auto). 
    assert (g |= (s, e1 :: nil) is s ~o~> dst g e1 satisfying (fun _ => True)) by
        (split; split; simpl; auto; [split; [|unfold strong_evalid; rewrite H1] | hnf; rewrite Forall_forall; intros]; auto).
    assert (g |= (s, e2 :: nil) is s ~o~> dst g e2 satisfying (fun _ => True)) by
        (split; split; simpl; auto; [split; [|unfold strong_evalid; rewrite H2] | hnf; rewrite Forall_forall; intros]; auto).
    destruct H0 as [ps ?]. destruct ps as [vs ps]. assert (vs = root) by (destruct H0 as [[? _] _]; simpl in H0; auto). subst vs.
    pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H0 H8). unfold path_glue, fst, snd in H10. pose proof (reachable_by_path_is_reachable _ _ _ _ _ H10).
    pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H0 H9). unfold path_glue, fst, snd in H12. pose proof (reachable_by_path_is_reachable _ _ _ _ _ H12).
    destruct H as [pf [? ?]]. apply H14 in H11. destruct H11 as [p1 [[? ?] ?]]. apply H14 in H13. destruct H13 as [p2 [[? ?] ?]]. clear H14.
    assert (In_path g (dst g e1) pf) by (apply In_path_Subpath with p1; auto; destruct H11 as [[_ ?] _]; apply pfoot_in; auto).
    assert (In_path g (dst g e2) pf) by (apply In_path_Subpath with p2; auto; destruct H13 as [[_ ?] _]; apply pfoot_in; auto).
    pose proof (valid_path_reachable _ _ _ _ H H14 H19). clear H11 H13 H16 H18 H14 H19. pose proof (H15 _ H10). pose proof (H17 _ H12). destruct H20.
    + destruct H14 as [[vx px] ?]. assert (vx = dst g e1) by (destruct H14 as [[? _] _]; simpl in H14; auto). subst vx.
      pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H10 H14). unfold path_glue, fst, snd in H16. apply H17 in H16. rewrite H13 in H16. inversion H16.
      pose proof (f_equal (@length Edge) H19). rewrite !app_length in H18. simpl in H18. assert (length px = 0) by intuition. destruct px. 2: inversion H20.
      clear H18 H20. rewrite app_nil_r in H19. apply app_inj_tail in H19. destruct H19. auto.
    + destruct H14 as [[vx px] ?]. assert (vx = dst g e2) by (destruct H14 as [[? _] _]; simpl in H14; auto). subst vx.
      pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H12 H14). unfold path_glue, fst, snd in H16. apply H15 in H16. rewrite H11 in H16. inversion H16.
      pose proof (f_equal (@length Edge) H19). rewrite !app_length in H18. simpl in H18. assert (length px = 0) by intuition. destruct px. 2: inversion H20.
      clear H18 H20. rewrite app_nil_r in H19. apply app_inj_tail in H19. destruct H19. auto.
  Qed.

  Lemma is_list_edge_dst_the_same: forall root s d v, is_list root -> reachable g root s -> g |= s ~> d -> g |= s ~> v -> d = v.
  Proof.
    intros. destruct H1 as [? [? ?]]. destruct H2 as [? [? ?]]. rewrite step_spec in H4, H6. destruct H4 as [e1 [? [? ?]]]. destruct H6 as [e2 [? [? ?]]].
    subst v d. assert (e1 = e2) by (apply (is_list_same_src_same_edge root s e1 e2); auto). subst e1. auto.
  Qed.

  Lemma is_list_edge_src_the_same: forall root s d v, vvalid g root -> is_list root -> reachable g root s -> reachable g root v -> g |= s ~> d -> g |= v ~> d -> s = v.
  Proof.
    intros. destruct H3 as [? [? ?]]. rewrite step_spec in H6. destruct H6 as [es [? [? ?]]]. destruct H4 as [? [? ?]]. rewrite step_spec in H10. destruct H10 as [ev [? [? ?]]].
    assert (g |= (s, es :: nil) is s ~o~> d satisfying (fun _ => True)). {
      split; split; simpl; auto; [unfold strong_evalid; rewrite H7, H8; split; auto | hnf; rewrite Forall_forall; intros; auto].
    }
    assert (g |= (v, ev :: nil) is v ~o~> d satisfying (fun _ => True)). {
      split; split; simpl; auto; [unfold strong_evalid; rewrite H11, H12; split; auto | hnf; rewrite Forall_forall; intros; auto].
    } destruct H1 as [[vs ps] ?]. destruct H2 as [[vv pv] ?]. 
    pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H1 H13). unfold path_glue, fst, snd in H15.
    pose proof (reachable_by_path_merge _ _ _ _ _ _ _ H2 H14). unfold path_glue, fst, snd in H16. destruct H0 as [pf [? ?]].
    pose proof (reachable_by_path_is_reachable _ _ _ _ _ H16). apply H17 in H18. destruct H18 as [pp [[? ?] ?]]. apply H19 in H15. apply H19 in H16. rewrite H15 in H16.
    inversion H16. apply app_inj_tail in H23. destruct H23. subst es. rewrite H7 in H11. auto.
  Qed.

End IS_LIST.

Section LIST_TO_GRAPH.

  Context {Vertex: Type}.
  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.

  Fixpoint listToGraph' (g: PreGraph Vertex Edge) (v: Vertex) (l: list (Edge * Vertex)) : PreGraph Vertex Edge :=
    match l with
    | nil => g
    | (e, v') :: l' => listToGraph' (pregraph_add_whole_edge g e v v') v' l'
    end.

  Lemma listToGraph'_preserve_vvalid: forall g v v' l, vvalid g v -> vvalid (listToGraph' g v' l) v.
  Proof.
    intros. revert g v v' H. induction l; intros; simpl; auto.
    destruct a as [e vv]. apply IHl. apply addEdge_preserve_vvalid. auto.
  Qed.

  Definition listToGraph (gl: GList Vertex Edge) : PreGraph Vertex Edge :=
    match gl with (v, l) => listToGraph' (single_vertex_pregraph v) v l end.

  Lemma list_vertices_vvalid: forall g v l x, vvalid g v -> In x (listVertices (v, l)) -> vvalid (listToGraph' g v l) x.
  Proof.
    intros. destruct (equiv_dec v x).
    + hnf in e. subst v. clear H0. apply listToGraph'_preserve_vvalid; auto.
    + compute in c. revert g v H H0 c. induction l; intros. 1: simpl in *; destruct H0; exfalso; auto.
      destruct a; simpl in *. destruct H0. 1: exfalso; auto. destruct (equiv_dec v0 x).
      - hnf in e0. subst. apply listToGraph'_preserve_vvalid, addEdge_add_vvalid.
      - compute in c0. destruct H0. 1: exfalso; auto. apply IHl; auto. apply addEdge_add_vvalid.
  Qed.

  Lemma v_in_list_are_valid:
    forall gl x, In x (listVertices gl) -> vvalid (listToGraph gl) x.
  Proof. intro gl. destruct gl as [v l]. simpl. intros. apply list_vertices_vvalid; simpl; auto. Qed.

  Lemma valid_v_are_in_list: forall g v l x, vvalid (listToGraph' g v l) x -> vvalid g x \/ In x (listVertices (v, l)).
  Proof.
    intros g v l. revert g v. induction l; intros; simpl in *. 1: left; auto. destruct a.
    specialize (IHl (pregraph_add_whole_edge g e v v0) v0 x H). simpl. clear H. simpl in IHl. unfold addValidFunc in IHl. intuition.
  Qed.

  Lemma list_vertices_vvalid_iff: forall g v l x, vvalid g v -> (vvalid g x \/ In x (listVertices (v, l)) <-> vvalid (listToGraph' g v l) x).
  Proof.
    intros. split; intros.
    + destruct H0; [apply listToGraph'_preserve_vvalid | apply list_vertices_vvalid]; auto.
    + apply valid_v_are_in_list; auto.
  Qed.

  Lemma valid_v_eq_in_list: forall gl x, vvalid (listToGraph gl) x <-> In x (listVertices gl).
  Proof. intros. destruct gl as [v l]. simpl. rewrite <- list_vertices_vvalid_iff; simpl; tauto. Qed.

  Lemma listToGraph'_preserve_evalid: forall g v e l, evalid g e -> evalid (listToGraph' g v l) e.
  Proof.
    intros. revert g v e H. induction l; intros; simpl; auto.
    destruct a. apply IHl. apply addEdge_preserve_evalid. auto.
  Qed.

  Lemma list_edges_evalid: forall g v l e, In e (listEdges' Vertex Edge l) -> evalid (listToGraph' g v l) e.
  Proof.
    intros. revert g v H. induction l; simpl; intros. 1: exfalso; auto. destruct a. simpl in H. destruct H.
    + subst. apply listToGraph'_preserve_evalid, addEdge_add_evalid.
    + apply IHl. auto.
  Qed.

  Lemma e_in_list_are_valid:
    forall gl e, In e (listEdges gl) -> evalid (listToGraph gl) e.
  Proof. intros gl e. destruct gl as [v l]. apply list_edges_evalid. Qed.

  Lemma valid_e_are_in_list: forall g v l e, evalid (listToGraph' g v l) e -> evalid g e \/ In e (listEdges' Vertex Edge l).
  Proof.
    intros g v l. revert g v. induction l; simpl; intros; auto.
    destruct a. apply IHl in H. simpl in *. unfold addValidFunc in H. intuition.
  Qed.

  Lemma list_edges_evalid_iff: forall g v l e, evalid g e \/ In e (listEdges' Vertex Edge l) <-> evalid (listToGraph' g v l) e.
  Proof.
    intros; split; intros.
    + destruct H; [apply listToGraph'_preserve_evalid | apply list_edges_evalid]; auto.
    + apply (valid_e_are_in_list _ v); auto.
  Qed.

  Lemma valid_e_eq_in_list: forall gl e, evalid (listToGraph gl) e <-> In e (listEdges gl).
  Proof.
    intros. destruct gl as [v l]. unfold listEdges. simpl. rewrite <- list_edges_evalid_iff. simpl. tauto.
  Qed.

  Lemma listToGraph'_FiniteGraph: forall g v l, vvalid g v -> FiniteGraph g -> FiniteGraph (listToGraph' g v l).
  Proof.
    intros. destruct X as [[vl [_ ?]] [el [_ ?]]]. unfold Ensembles.In in *.
    apply Build_FiniteGraph; [exists (nodup equiv_dec (listVertices (v, l) ++ vl)) | exists (nodup equiv_dec (listEdges (v, l) ++ el))]; split; intros.
    + apply NoDup_nodup.
    + rewrite nodup_In. unfold Ensembles.In . rewrite in_app_iff, H0, <- list_vertices_vvalid_iff; tauto.
    + apply NoDup_nodup.
    + rewrite nodup_In. unfold Ensembles.In . rewrite in_app_iff, H1, <- list_edges_evalid_iff; tauto.
  Qed.

  Instance listToGraphFinite (gl: GList Vertex Edge) : FiniteGraph (listToGraph gl).
  Proof.
    destruct gl as [v l]. simpl. apply listToGraph'_FiniteGraph; simpl; auto.
    apply Build_FiniteGraph; [exists (v :: nil) | exists nil]; split; intros.
    + apply NoDup_cons; [intro S; simpl in S; auto | apply NoDup_nil].
    + unfold Ensembles.In . simpl. tauto.
    + apply NoDup_nil.
    + unfold Ensembles.In . simpl. tauto.
  Defined.

  Definition collectEdges (g: PreGraph Vertex Edge) (x: Vertex) (l: list Edge) := filter (fun e => if equiv_dec (src g e) x then true else false) l.

  Lemma collectEdges_In: forall g v l e, In e (collectEdges g v l) <-> In e l /\ src g e = v.
  Proof. intros. unfold collectEdges. rewrite filter_In. destruct (equiv_dec (src g e) v); hnf in * |- ; intuition. Qed.

  Lemma listToGraph'_src: forall g v l e x, src (listToGraph' g v l) e = x -> src g e = x \/ In e (listEdges (v, l)) /\ In x (listVertices (v, l)).
  Proof.
    intros. revert g v e x H. induction l; intros; simpl in *. 1: left; auto. destruct a. apply IHl in H. clear IHl.
    simpl. unfold listEdges, snd in H. destruct H.
    + rewrite addEdge_src_iff in H. intuition.
    + right. destruct H. split; intuition.
  Qed.

  Lemma listToGraph'_dst: forall g v l e x, dst (listToGraph' g v l) e = x -> dst g e = x \/ (In e (listEdges (v, l)) /\ In x (listVertices (v, l))).
  Proof.
    intros. revert g v e x H. induction l; intros; simpl in *. 1: left; auto. destruct a. apply IHl in H. clear IHl.
    simpl. unfold listEdges, snd in H. destruct H.
    + rewrite addEdge_dst_iff in H. intuition.
    + right. destruct H. split; intuition.
  Qed.

  Lemma listToGraph'_In: forall g v l e, In e (listEdges (v, l)) ->
                                         In (src (listToGraph' g v l) e) (listVertices (v, l)) /\ In (dst (listToGraph' g v l) e) (listVertices (v, l)).
  Proof.
    intros. revert g v e H. induction  l; intros; simpl in *. 1: intuition. destruct a. simpl in H. destruct H.
    2: apply (IHl (pregraph_add_whole_edge g e0 v v0) v0) in H; simpl; intuition.
    subst. remember (src (listToGraph' (pregraph_add_whole_edge g e v v0) v0 l) e) as x1. remember (dst (listToGraph' (pregraph_add_whole_edge g e v v0) v0 l) e) as x2.
    symmetry in Heqx1, Heqx2. pose proof Heqx1. pose proof Heqx2. apply listToGraph'_src in Heqx1. apply listToGraph'_dst in Heqx2. destruct Heqx1.
    + rewrite addEdge_src_iff in H1. destruct H1 as [[? ?] | [? ?]]. 1: exfalso; tauto. subst v. destruct Heqx2.
      * rewrite addEdge_dst_iff in H2. destruct H2 as [[? ?] | [? ?]]. 1: exfalso; tauto. subst v0. intuition.
      * destruct H2. apply (IHl (pregraph_add_whole_edge g e x1 v0)) in H2. destruct H2. rewrite H0 in H4. simpl. intuition.
    + destruct H1. apply (IHl (pregraph_add_whole_edge g e v v0)) in H1. rewrite H, H0 in H1. simpl. intuition.
  Qed.

  Lemma listToGraph'_In_dst: forall g v l e, In e (listEdges (v, l)) -> In (dst (listToGraph' g v l) e) (listVertices (v, l)).
  Proof. intros. apply (listToGraph'_In g) in H. intuition. Qed.

  Lemma listToGraph'_In_src: forall g v l e, In e (listEdges (v, l)) -> In (src (listToGraph' g v l) e) (listVertices (v, l)).
  Proof. intros. apply (listToGraph'_In g) in H. intuition. Qed.

  Lemma listToGraph'_not_In: forall g v l e, ~ In e (listEdges (v, l)) -> src (listToGraph' g v l) e = src g e /\ dst (listToGraph' g v l) e = dst g e.
  Proof.
    intros g v l. revert g v. induction l; intros; simpl in *; auto. destruct a. simpl in H.
    assert (~ In e (listEdges (v0, l))) by (unfold listEdges, snd; intro; apply H; right; auto). apply (IHl (pregraph_add_whole_edge g e0 v v0)) in H0. destruct H0.
    rewrite H0, H1. simpl. unfold updateEdgeFunc. destruct (equiv_dec e0 e); auto. hnf in e1. exfalso; apply H. left; auto.
  Qed.

  Lemma listToGraph'_not_In_dst: forall g v l e, ~ In e (listEdges (v, l)) -> dst (listToGraph' g v l) e = dst g e.
  Proof. intros. apply (listToGraph'_not_In g) in H. tauto. Qed.

  Lemma listToGraph'_not_In_src: forall g v l e, ~ In e (listEdges (v, l)) -> src (listToGraph' g v l) e = src g e.
  Proof. intros. apply (listToGraph'_not_In g) in H. tauto. Qed.

  Lemma listToGraph'_NoDup_In_dst:
    forall g v l e, NoDup (listEdges' Vertex Edge l) -> In e (listEdges' Vertex Edge l) -> exists v', In (e, v') l /\ dst (listToGraph' g v l) e = v'.
  Proof.
    intros. revert g v e H H0. induction l; simpl; intros. 1: exfalso; auto. destruct a. simpl in H0. destruct H0.
    - subst e0. exists v0. split.
      + left; auto.
      + apply NoDup_cons_iff in H. destruct H. apply (listToGraph'_not_In_dst (pregraph_add_whole_edge g e v v0) v0) in H. rewrite H. rewrite addEdge_dst_iff. right; split; auto.
    - specialize (IHl (pregraph_add_whole_edge g e0 v v0) v0 e). rewrite NoDup_cons_iff in H. destruct H. specialize (IHl H1 H0). destruct IHl as [v1 [? ?]]. exists v1. split; auto.
  Qed.

  Lemma listToGraph'_NoDup_In_src: forall g v l e, NoDup (listEdges' Vertex Edge l) -> In e (listEdges' Vertex Edge l) ->
                                                   exists v', In (v', e) (shiftLeft Vertex Edge v l) /\ src (listToGraph' g v l) e = v'.
  Proof.
    intros. revert g v e H H0. induction l; simpl; intros. 1: exfalso; auto. destruct a. simpl in H0. destruct H0.
    - subst e0. exists v. simpl. split.
      + left; auto.
      + apply NoDup_cons_iff in H. destruct H. apply (listToGraph'_not_In_src (pregraph_add_whole_edge g e v v0) v0) in H. rewrite H. rewrite addEdge_src_iff. right; split; auto.
    - specialize (IHl (pregraph_add_whole_edge g e0 v v0) v0 e). rewrite NoDup_cons_iff in H. destruct H. specialize (IHl H1 H0). destruct IHl as [v1 [? ?]]. exists v1.
      split; auto. simpl. right; auto.
  Qed.

  Lemma listToGraph'_LF: forall g v l, vvalid g v -> LocalFiniteGraph g -> LocalFiniteGraph (listToGraph' g v l).
  Proof.
    intros. destruct X. apply Build_LocalFiniteGraph. intros. unfold Enumerable, Ensembles.In in *. destruct (local_enumerable x) as [l' [? ?]].
    exists (nodup equiv_dec (collectEdges (listToGraph' g v l) x (l' ++ listEdges (v, l)))). split. 1: apply NoDup_nodup.
    intro e. rewrite nodup_In, collectEdges_In, in_app_iff. rewrite H1. unfold out_edges. rewrite <- list_edges_evalid_iff. intuition.
    apply listToGraph'_src in H4. intuition.
  Qed.

  Instance listToGraphLF (gl: GList Vertex Edge) : LocalFiniteGraph (listToGraph gl).
  Proof. apply LocalFiniteGraph_FiniteGraph, listToGraphFinite. Defined.

  Lemma listToGraph_vvalid_dec: forall gl v, Decidable (vvalid (listToGraph gl) v).
  Proof.
    intros. destruct (in_dec equiv_dec v (listVertices gl)); [left | right].
    + rewrite valid_v_eq_in_list; auto.
    + intro; apply n. rewrite <- valid_v_eq_in_list. auto.
  Qed.

  Lemma listToGraph_evalid_dec: forall gl e, Decidable (evalid (listToGraph gl) e).
  Proof.
    intros. destruct (in_dec equiv_dec e (listEdges gl)); [left | right].
    + rewrite valid_e_eq_in_list; auto.
    + intro; apply n. rewrite <- valid_e_eq_in_list. auto.
  Qed.

End LIST_TO_GRAPH.

Section GRAPH_TO_LIST.

  Context {Vertex: Type}.
  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.

  Class ValidVertexAccessible (g: PreGraph Vertex Edge) :=
    {
      filterE: list Edge -> list Edge;
      filter_valid: forall l e, Forall (evalid g) l -> In e (filterE l) <-> vvalid g (dst g e) /\ In e l
    }.

  Variable g : PreGraph Vertex Edge.
  Variable vva : ValidVertexAccessible g.

  Definition ToListInput := (nat * Vertex * list (Edge * Vertex))%type.

  Definition lengthInput (i : ToListInput) := match i with (len, _, l) => len - length l end.

  Definition inputOrder (i1 i2 : ToListInput) := lengthInput i1 < lengthInput i2.

  Lemma inputOrder_wf': forall len i, lengthInput i <= len -> Acc inputOrder i.
  Proof.
    induction len; intros; constructor; intros; unfold inputOrder in * |-.
    + exfalso. intuition.
    + apply IHlen. intuition.
  Qed.

  Lemma inputOrder_wf : well_founded inputOrder. Proof. red; intro; eapply inputOrder_wf'; eauto. Qed.

  Variable LF: LocalFiniteGraph g.

  Lemma construct_omega: forall len (r : list (Edge * Vertex)), (~ len <= length r) -> len - S (length r) < len - length r.
  Proof. intros; omega. Qed.

  Definition toEdgeList : ToListInput -> list (Edge * Vertex).
  Proof.
    refine (
        Fix inputOrder_wf (fun _ => list (Edge * Vertex))
            (fun (inp : ToListInput) =>
               match inp return
                     ((forall inp2, inputOrder inp2 inp -> list (Edge * Vertex))
                      -> list (Edge * Vertex)) with
                 (len, x, r) =>
                 fun f =>
                   if le_dec len (length r)
                   then r
                   else let eList := filterE (edge_func g x) in
                        match eList with
                        | nil => r
                        | e :: _ => f (len, dst g e, (e, dst g e) :: r) _
                        end
               end)).
    unfold inputOrder, lengthInput. simpl. apply construct_omega; auto.
  Defined.

  Lemma toEdgeList_unfold:
    forall i,
      toEdgeList i =
      match i with (len, x, r) =>
                   if le_dec len (length r)
                   then r
                   else let eList := filterE (edge_func g x) in
                        match eList with
                        | nil => r
                        | e :: _ => toEdgeList (len, dst g e, (e, dst g e) :: r)
                        end
      end.
  Proof.
    intros. destruct i as [[len x] r]. unfold toEdgeList at 1. rewrite Fix_eq.
    + destruct (le_dec len (length r)); auto.
    + intros. assert (f = g0) by (extensionality y; extensionality p; auto).
      subst; auto.
  Qed.

  Lemma toEdgeList_In: forall len x r, (forall e v, In (e, v) r -> v = dst g e) -> forall e v, In (e, v) (toEdgeList (len, x, r)) -> v = dst g e.
  Proof.
    intros len x r. remember (lengthInput (len, x, r)) as n. assert (lengthInput (len, x, r) <= n) by omega. clear Heqn. revert len x r H.
    induction n; intros; simpl; unfold lengthInput in H; rewrite toEdgeList_unfold in H1; destruct (le_dec len (length r)).
    - apply H0; auto.
    - exfalso; intuition.
    - apply H0; auto.
    - simpl in H1. destruct (filterE (edge_func g x)) eqn:? .
      + apply H0; auto.
      + specialize (IHn len (dst g e0) ((e0, dst g e0) :: r)). apply IHn; auto.
        * simpl. clear -H. intuition.
        * intros. simpl in H2. destruct H2.
          -- inversion H2. auto.
          -- apply H0; auto.
  Qed.

  Lemma shiftLeft_toEdgeList_In: forall root len x r, (forall v e, In (v, e) (shiftLeft Vertex Edge root (rev r)) -> v = src g e) ->
                                                      (r = nil -> x = root) ->
                                                      (forall e v l, r = (e, v) :: l -> x = v) ->
                                                      forall e v, In (v, e) (shiftLeft Vertex Edge root (rev (toEdgeList (len, x, r)))) -> v = src g e.
  Proof.
    intros root len x r. remember (lengthInput (len, x, r)) as n. assert (lengthInput (len, x, r) <= n) by omega. clear Heqn. revert len x r H.
    induction n; intros; simpl; unfold lengthInput in H; rewrite toEdgeList_unfold in H3; destruct (le_dec len (length r)).
    - apply H0; auto.
    - exfalso; intuition.
    - apply H0; auto.
    - simpl in H3. destruct (filterE (edge_func g x)) eqn:? .
      + apply H0; auto.
      + specialize (IHn len (dst g e0) ((e0, dst g e0) :: r)). assert (In e0 (e0 :: l)) by (simpl; left; auto). rewrite <- Heql in H4. rewrite filter_valid in H4.
        2: rewrite Forall_forall; intros; rewrite edge_func_spec in H5; destruct H5; auto.
        destruct H4. rewrite edge_func_spec in H5. destruct H5. apply IHn; auto; clear IHn H4 H5.
        * simpl. clear -H. intuition.
        * intros. simpl in H4. destruct r.
          -- simpl in H4. assert (x = root) by (apply H1; auto). subst x. destruct H4. 2: exfalso; auto. inversion H4. subst e1. subst v0. auto.
          -- destruct p as [e' v']. simpl in H4. assert (x = v') by (apply (H2 e' v' r); auto). subst v'.
             rewrite shiftLeft_app in H4. rewrite tailVertex_foot in H4. destruct H4.
             ++ simpl in H0. apply H0 in H4; auto.
             ++ simpl in H4. destruct H4. 2: exfalso; auto. inversion H4. subst v0. subst e1. auto.             
        * intros. inversion H4.
        * intros. inversion H4. auto.
  Qed.

  Lemma toEdgeList_edge_NoDup:
    forall root len x r, is_list g root -> reachable g root x -> NoDup (listEdges' Vertex Edge r) ->
                         (forall e, In e (listEdges' Vertex Edge r) -> ~ reachable g x (src g e)) -> NoDup (listEdges' Vertex Edge (toEdgeList (len, x, r))).
  Proof.
    intros root len x r ?. remember (lengthInput (len, x, r)) as n. assert (lengthInput (len, x, r) <= n) by omega. clear Heqn. revert len x r H0.
    induction n; intros; simpl; unfold lengthInput in H0; rewrite toEdgeList_unfold; destruct (le_dec len (length r)); auto.
    - exfalso; intuition.
    - simpl. destruct (filterE (edge_func g x)) eqn:?; auto. specialize (IHn len (dst g e) ((e, dst g e) :: r)).
      assert (In e (e :: l)) by (simpl; left; auto). rewrite <- Heql in H4. rewrite filter_valid in H4.
      2: rewrite Forall_forall; intros; rewrite edge_func_spec in H5; destruct H5; auto. destruct H4. rewrite edge_func_spec in H5. destruct H5.
      assert (g |= x ~> (dst g e)) by (hnf; rewrite step_spec; apply reachable_foot_valid in H1; intuition; exists e; intuition). apply IHn; clear IHn; auto; simpl.
      + intuition.
      + apply reachable_edge with x; auto.
      + apply NoDup_cons; auto. intro. apply H3 in H8. apply H8. rewrite H6. apply reachable_refl. apply reachable_foot_valid in H1. auto.
      + simpl. intros. destruct H8.
        * subst e0. rewrite H6. intro. apply (is_list_no_edge_loop _ root) in H8; auto.
        * intro. apply H3 in H8. apply H8. apply edge_reachable with (dst g e); auto.
  Qed.

  Lemma toEdgeList_reachable: forall root len x r,
      reachable g root x -> (forall v, In v (listVertices' Vertex Edge r) -> reachable g root v) ->
      forall v, In v (listVertices' Vertex Edge (toEdgeList (len, x, r))) -> reachable g root v.
  Proof.
    intros root len x r. remember (lengthInput (len, x, r)) as n. assert (lengthInput (len, x, r) <= n) by omega. clear Heqn. revert len x r H.
    induction n; intros; simpl; unfold lengthInput in H; rewrite toEdgeList_unfold in H2;
      destruct (le_dec len (length r)); [apply H1; auto | exfalso; intuition | apply H1; auto |].
    simpl in H2. destruct (filterE (edge_func g x)) eqn:? . 1: apply H1; auto. specialize (IHn len (dst g e) ((e, dst g e) :: r)).
    assert (reachable g root (dst g e)). {
      assert (In e (e :: l)) by (simpl; left; auto). rewrite <- Heql in H3. rewrite filter_valid in H3.
      2: rewrite Forall_forall; intros; rewrite edge_func_spec in H4; destruct H4; auto. apply reachable_edge with x; auto.
      destruct H3. rewrite edge_func_spec in H4. hnf. rewrite step_spec. apply reachable_foot_valid in H0. intuition. exists e. intuition.
    } apply IHn; auto. 1: simpl; intuition. simpl; intros. destruct H4. 2: apply H1; auto. subst v0. auto.
  Qed.

  Lemma toEdgeList_edge_reachable: forall root len x r,
      (forall e, In e (listEdges' Vertex Edge r) -> evalid g e /\ reachable g root (src g e) /\ reachable g root (dst g e)) -> reachable g root x ->
      forall e, In e (listEdges' Vertex Edge (toEdgeList (len, x, r))) -> evalid g e /\ reachable g root (src g e) /\ reachable g root (dst g e).
  Proof.
    intros root len x r. remember (lengthInput (len, x, r)) as n. assert (lengthInput (len, x, r) <= n) by omega. clear Heqn. revert len x r H.
    induction n; intros; simpl; unfold lengthInput in H; rewrite toEdgeList_unfold in H2; destruct (le_dec len (length r));
      [apply H0; auto | exfalso; intuition | apply H0; auto |]. simpl in H2.
    destruct (filterE (edge_func g x)) eqn:? . 1: apply H0; auto. specialize (IHn len (dst g e0) ((e0, dst g e0) :: r)). assert (In e0 (e0 :: l)) by (simpl; left; auto).
    rewrite <- Heql, filter_valid in H3. 2: rewrite Forall_forall; intros; rewrite edge_func_spec in H4; destruct H4; auto.
    destruct H3. rewrite edge_func_spec in H4. destruct H4.
    assert (reachable g root (dst g e0)). {
      apply reachable_edge with x; auto. hnf. rewrite step_spec. split; [|split]; [apply reachable_foot_valid in H1 | | exists e0; split]; auto.
    } apply IHn; auto; clear IHn.
    + unfold lengthInput. simpl. intuition.
    + intros. simpl in H7. destruct H7. 2: apply H0; auto. subst e1. rewrite H5; split; [|split]; auto.
  Qed.

  Lemma toEdgeList_tail: forall len x r, exists l, toEdgeList (len, x, r) = l ++ r.
  Proof.
    intros. remember (lengthInput (len, x, r)). assert (lengthInput (len, x, r) <= n) by omega. clear Heqn. revert len x r H. induction n; intros; simpl.
    + unfold lengthInput in H. rewrite toEdgeList_unfold. destruct (le_dec len (length r)). exists nil; simpl; auto. exfalso; omega.
    + unfold lengthInput in H. rewrite toEdgeList_unfold. destruct (le_dec len (length r)). exists nil; simpl; auto. simpl. destruct (filterE (edge_func g x)).
      exists nil; simpl; auto. assert (lengthInput (len, dst g e, (e, dst g e) :: r) <= n) by (simpl; omega). apply IHn in H0.
      destruct H0 as [l' ?]. exists (l' ++ (e, dst g e) :: nil). rewrite <- app_assoc, <- app_comm_cons. simpl. auto.
  Qed.

  Lemma reachable_toEdgeList:
    forall root len x r (X: EnumCovered Vertex (reachable g root)),
      is_list g root -> length (proj1_sig X) <= len -> reachable g root x -> NoDup (listVertices' Vertex Edge r) ->
      (forall v, reachable g root v -> v <> root -> reachable g x v \/ In v (listVertices' Vertex Edge r)) ->
      (forall v, In v (listVertices' Vertex Edge r) -> reachable g root v) -> (forall v, reachable g x v -> x <> v -> ~ In v (listVertices' Vertex Edge r)) ->
      (x <> root -> In x (listVertices' Vertex Edge r)) -> forall v, reachable g root v -> v <> root -> In v (listVertices' Vertex Edge (toEdgeList (len, x, r))).
  Proof.
    intros root len x r ? ?. remember (lengthInput (len, x, r)) as n. assert (lengthInput (len, x, r) <= n) by omega. clear Heqn. revert len x r H0.
    induction n; intros; simpl; unfold lengthInput in H0; rewrite toEdgeList_unfold; destruct (le_dec len (length r));
      [apply (listVertices'_In_length_reachable _ _ _ _ len _ X) | simpl; exfalso; intuition | apply (listVertices'_In_length_reachable _ _ _ _ len _ X)| ]; auto.
    assert (HS: Forall (evalid g) (edge_func g x)) by (rewrite Forall_forall; intros; rewrite edge_func_spec in H10; destruct H10; auto).
    simpl. destruct (filterE (edge_func g x)) eqn:? .
    + specialize (H4 _ H8 H9). destruct H4; auto. clear IHn. apply reachable_by_ind in H4. destruct H4. 1: subst x; apply H7; auto.
      exfalso. destruct H4 as [z [[? [? ?]] ?]]. rewrite step_spec in H11. destruct H11 as [e [? [? ?]]].
      assert (vvalid g (dst g e) /\ In e (edge_func g x)) by (split; [rewrite H14 | rewrite edge_func_spec; split]; auto).
      rewrite <- filter_valid in H15; auto. rewrite Heql in H15. simpl in H15; auto.
    + specialize (IHn len (dst g e) ((e, dst g e) :: r)). assert (S: len - length ((e, dst g e) :: r) <= n) by (simpl; clear -H0; intuition). specialize (IHn S H1); clear S.
      assert (g |= x ~> (dst g e)). {
        assert (In e (e :: l)) by (simpl; left; auto). rewrite <- Heql in H10. rewrite filter_valid in H10; auto.
        rewrite edge_func_spec in H10. hnf. rewrite step_spec. destruct H10 as [? [? ?]]. apply reachable_foot_valid in H2. split; [|split; [|exists e]]; auto.
      } assert (vvalid g root) by (apply reachable_head_valid in H2; auto). apply IHn; auto; clear IHn.
      * apply reachable_edge with x; auto.
      * simpl. apply NoDup_cons; auto. apply H6. 1: apply reachable_edge with x; auto; apply reachable_refl; apply reachable_foot_valid in H2; auto.
        intro. subst x. apply (is_list_no_self_edge g root) in H10; auto.
      * intros. specialize (H4 _ H12 H13). simpl. destruct H4. 2: right; right; auto. apply reachable_by_ind in H4. destruct H4. 1: right; right; subst x; apply H7; auto.
        destruct H4 as [z [? ?]]. pose proof (is_list_edge_dst_the_same _ _ _ _ _ H H2 H4 H10). subst z. apply reachable_by_is_reachable in H14. left; auto.
      * simpl; intros. destruct H12. 2: apply H5; auto. subst v0. apply reachable_edge with x; auto.
      * intros. simpl. intro. destruct H14; auto. revert H14. apply H6. 1: apply edge_reachable with (dst g e); auto. intro. subst v0.
        apply (is_list_no_edge_loop g root x (dst g e)); auto.
      * simpl; intros; left; auto.
  Qed.

  Lemma reachable_edge_toEdgeList:
    forall root len x r (X: EnumCovered Vertex (reachable g root)), is_list g root -> length (proj1_sig X) <= len -> reachable g root x -> NoDup (listEdges' Vertex Edge r) ->
      (forall e, evalid g e -> reachable g root (src g e) -> vvalid g (dst g e) -> reachable g x (src g e) \/ In e (listEdges' Vertex Edge r)) ->
      (forall e, In e (listEdges' Vertex Edge r) -> evalid g e /\ reachable g root (src g e) /\ vvalid g (dst g e)) ->
      (forall e, evalid g e -> reachable g x (src g e) -> vvalid g (dst g e) -> ~ In e (listEdges' Vertex Edge r)) ->
      forall e, evalid g e -> reachable g root (src g e) -> vvalid g (dst g e) -> In e (listEdges' Vertex Edge (toEdgeList (len, x, r))).
  Proof.
    intros root len x r ? ?. remember (lengthInput (len, x, r)) as n. assert (lengthInput (len, x, r) <= n) by omega. clear Heqn. revert len x r H0.
    assert (forall s e1 e2, reachable g root s -> src g e1 = s -> src g e2 = s -> evalid g e1 -> evalid g e2 -> vvalid g (dst g e1) -> vvalid g (dst g e2) -> e1 = e2)
      by (intros s e1 e2; apply (is_list_same_src_same_edge g root); auto).
    induction n; intros; simpl; unfold lengthInput in H1; rewrite toEdgeList_unfold; destruct (le_dec len (length r)).
    - apply (listEdges'_In_length_reachable _ _ g root len _ X); auto.
    - exfalso; intuition.
    - apply (listEdges'_In_length_reachable _ _ g root len _ X); auto.
    - assert (HS: Forall (evalid g) (edge_func g x)) by (rewrite Forall_forall; intros; rewrite edge_func_spec in H11; destruct H11; auto).
      simpl. destruct (filterE (edge_func g x)) eqn:? .
      + specialize (H5 _ H8 H9 H10). destruct H5; auto. clear IHn. apply reachable_by_ind in H5. destruct H5.
        * subst x. assert (vvalid g (dst g e) /\ In e (edge_func g (src g e))) by (split; auto; rewrite edge_func_spec; split; auto).
          rewrite <- filter_valid in H5; auto. rewrite Heql in H5. inversion H5.
        * destruct H5 as [z [[? [? ?]] ?]]. rewrite step_spec in H12. destruct H12 as [e' [? [? ?]]].
          assert (vvalid g (dst g e') /\ In e' (edge_func g x)) by (split; [rewrite H15 | rewrite edge_func_spec; split]; auto).
          rewrite <- filter_valid in H16; auto. rewrite Heql in H16. inversion H16.
      + specialize (IHn len (dst g e0) ((e0, dst g e0) :: r)). assert (In e0 (e0 :: l)) by (simpl; left; auto). rewrite <- Heql in H11.
        rewrite filter_valid in H11; auto. destruct H11. rewrite edge_func_spec in H12. destruct H12.
        assert (g |= x ~> (dst g e0)) by (apply reachable_foot_valid in H3; split; [|split; [|exists e0]]; auto). apply IHn; clear IHn; auto.
        * simpl. clear -H1. intuition.
        * apply reachable_edge with x; auto.
        * simpl. apply NoDup_cons; auto. apply H7; auto. rewrite H13. apply reachable_refl. apply reachable_foot_valid in H3; auto.
        * intros. specialize (H5 _ H15 H16 H17). destruct H5.
          -- apply reachable_by_ind in H5. destruct H5.
             ++ assert (e1 = e0) by (apply (H0 x); auto). subst e1. simpl. right; left; auto.
             ++ destruct H5 as [z [? ?]]. pose proof (is_list_edge_dst_the_same _ _ _ _ _ H H3 H5 H14). subst z. apply reachable_by_is_reachable in H18; left; auto.
          -- right. simpl. right. auto.
        * simpl. intros. destruct H15.
          -- subst e1. rewrite H13. split; [|split]; auto.
          -- apply H6; auto.
        * intros. simpl. intro. destruct H18.
          -- subst e1. rewrite H13 in H16. apply (is_list_no_edge_loop g root x (dst g e0)); auto.
          -- revert H18. apply H7; auto. apply edge_reachable with (dst g e0); auto.
  Qed.
    
  Definition graphToList (bound: nat) (x: Vertex) : GList Vertex Edge := (x, rev (toEdgeList (bound, x, nil))).

End GRAPH_TO_LIST.

Section GtoL_LtoG_EQ.

  Context {Vertex: Type}.
  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.

  (* Lemma listToGraph'_vva: forall (g: PreGraph Vertex Edge) v l, vvalid g v -> ValidVertexAccessible g -> ValidVertexAccessible (listToGraph' g v l). *)
  (* Proof. *)
  (*   intros. destruct X as [filterG ?]. *)
  (*   remember (fun l' => filterG l' ++ filter (fun e => if in_dec equiv_dec (dst (listToGraph' g v l) e) (listVertices (v, l)) then true else false) l') as f. *)
  (*   apply (Build_ValidVertexAccessible _ f). intros l' e ?. subst f. rewrite in_app_iff. rewrite filter_valid0. rewrite filter_In, <- list_vertices_vvalid_iff; auto. *)
  (*   intuition; remember (dst (listToGraph' g v l) e) as x; symmetry in Heqx. *)
  (*   + apply listToGraph'_dst in Heqx. destruct Heqx. 1: rewrite H1 in H0; auto. intuition. *)
  (*   + destruct (in_dec equiv_dec x (listVertices (v, l))). 2: inversion H2. right; auto. *)
  (*   + apply listToGraph'_dst in Heqx. destruct Heqx. 1: left; rewrite <- H1 in H0; intuition. destruct H1. right. split; auto. *)
  (*     destruct (in_dec equiv_dec x (listVertices (v, l))); auto. *)
  (*   + destruct (in_dec equiv_dec x (listVertices (v, l))). right; auto. exfalso; auto. *)
  (* Qed. *)

  Instance listToGraph_vva (gl: GList Vertex Edge) : ValidVertexAccessible (listToGraph gl).
  Proof.
    apply (Build_ValidVertexAccessible _ (fun (l: list Edge) => filter (fun e => if (listToGraph_vvalid_dec gl (dst (listToGraph gl) e)) then true else false) l)).
    intros. rewrite filter_In. destruct (listToGraph_vvalid_dec gl (dst (listToGraph gl) e)); intuition.
  Defined.

  Lemma gToLst_lstToG_eq': forall (g: PreGraph Vertex Edge) v l r len
                                  (H: vvalid g v) (LF: LocalFiniteGraph (listToGraph' g v l)) (VVA: ValidVertexAccessible (listToGraph' g v l)),
      length l + length r <= len -> NoDup (listVertices (v, l)) -> NoDup (listEdges (v, l)) -> (forall x e, In x (listVertices (v, l)) -> ~ out_edges g x e) ->
      toEdgeList (listToGraph' g v l) VVA LF (len, v, r) = rev l ++ r.
  Proof.
    intros g v l r len. remember (lengthInput (len, v, r)) as n. simpl in Heqn. assert (len - length r <= n) by omega. clear Heqn. revert  g v l r len H.
    induction n; intros; simpl.
    + rewrite toEdgeList_unfold. destruct (le_dec len (length r)). 2: exfalso; intuition. destruct l; simpl; auto. simpl in H1; exfalso; intuition.
    + rewrite toEdgeList_unfold. destruct (le_dec len (length r)). destruct l; simpl; auto. simpl in H1; exfalso; intuition. simpl. destruct l; simpl.
      * destruct (filterE (edge_func g v)) eqn:?; auto. assert (In e (e :: l)) by (simpl; auto). rewrite <- Heql in H5. rewrite filter_valid, edge_func_spec in H5.
        exfalso. apply (H4 v e); simpl. 1: left; auto. hnf. destruct H5; auto. rewrite Forall_forall. intros. rewrite edge_func_spec in H6. destruct H6; auto.
      * destruct p as [e0 v0].
        assert (In e0 (@filterE _ _ _ _ (listToGraph' (pregraph_add_whole_edge g e0 v v0) v0 l) VVA (@edge_func _ _ _ _ (listToGraph' (pregraph_add_whole_edge g e0 v v0) v0 l) LF v))). {
          rewrite filter_valid. 2: rewrite Forall_forall; intros; rewrite edge_func_spec in H5; destruct H5; auto. split.
          + apply listToGraph'_preserve_vvalid. rewrite listToGraph'_not_In_dst.
            * replace (dst (pregraph_add_whole_edge g e0 v v0) e0) with v0. apply addEdge_add_vvalid. symmetry. rewrite addEdge_dst_iff. right. auto.
            * unfold listEdges in H3 |-* ; simpl in H3 |-* ; rewrite NoDup_cons_iff in H3; destruct H3; auto.
          + rewrite edge_func_spec. split. 1: apply listToGraph'_preserve_evalid, addEdge_add_evalid. rewrite listToGraph'_not_In_src.
            * rewrite addEdge_src_iff. right; auto.
            * clear -H3. unfold listEdges in *. simpl in *. apply NoDup_cons_iff in H3. destruct H3; auto.
        } destruct (filterE (edge_func (listToGraph' (pregraph_add_whole_edge g e0 v v0) v0 l) v)) eqn: ?. 1: simpl in H5; intuition.
        assert (e = e0). {
          assert (In e (e :: l0)) by (simpl; auto). rewrite <- Heql0 in H6. rewrite filter_valid in H6.
          2: rewrite Forall_forall; intros; rewrite edge_func_spec in H7; destruct H7; auto.
          destruct H6. rewrite edge_func_spec in H7. destruct H7. destruct (in_dec equiv_dec e (listEdges (v0, l))).
          + apply (listToGraph'_In_src (pregraph_add_whole_edge g e0 v v0)) in i.
            rewrite H8 in i. simpl in H2, i; rewrite NoDup_cons_iff in H2; destruct H2; exfalso; apply H2; simpl; auto.
          + apply listToGraph'_src in H8. rewrite addEdge_src_iff in H8. destruct H8 as [[[? ?] | [? ?]] | [? ?]]; [ | | exfalso]; auto.
            apply valid_e_are_in_list in H7. unfold listEdges in n. simpl in n. destruct H7. 2: exfalso; auto. simpl in H7. unfold addValidFunc in H7.
            destruct H7; auto. unfold out_edges in H4. specialize (H4 v e). exfalso. apply H4; [left|]; auto.
        } subst e. clear l0 Heql0 H5. remember (dst (listToGraph' (pregraph_add_whole_edge g e0 v v0) v0 l) e0) as x. symmetry in Heqx. apply listToGraph'_dst in Heqx.
        destruct Heqx as [? | [? ?]]. 2: unfold listEdges in H5, H3; simpl in H5, H3; rewrite NoDup_cons_iff in H3; exfalso; intuition.
        rewrite addEdge_dst_iff in H5. destruct H5 as [[? ?] | [_ ?]]. 1: exfalso; tauto. subst x. rewrite <- app_assoc, <- app_comm_cons. simpl. rewrite IHn; auto.
        - simpl; intuition.
        - apply addEdge_add_vvalid.
        - simpl in H1 |-* ; intuition.
        - simpl in H2 |-* . rewrite NoDup_cons_iff in H2. destruct H2; auto.
        - clear -H3. unfold listEdges in *. simpl in *. rewrite NoDup_cons_iff in H3. destruct H3; auto.
        - intros xo eo ? ?. unfold out_edges in H4, H6. simpl in H6. unfold addValidFunc, updateEdgeFunc in H6. destruct H6.
          destruct (equiv_dec e0 eo).
          -- subst xo. simpl in H2. unfold listVertices in H5. rewrite NoDup_cons_iff in H2. destruct H2; intuition.
          -- compute in c. destruct H6; auto. specialize (H4 xo eo). apply H4; auto. simpl in H5 |-* . right; auto.
  Qed.

  Lemma gToLst_lstToG_eq: forall v l, NoDup (listVertices (v, l)) -> NoDup (listEdges (v, l)) ->
      graphToList (listToGraph (v, l)) (listToGraph_vva (v, l)) (listToGraphLF (v, l)) (length l) v = (v, l).
  Proof.
    intros. unfold graphToList. f_equal. remember (listToGraph_vva (v, l)) as VVA. clear HeqVVA.
    remember (listToGraphLF (v, l)) as LF. clear HeqLF. unfold listToGraph in *. rewrite gToLst_lstToG_eq'; auto.
    + rewrite app_nil_r. apply rev_involutive.
    + simpl; auto.
    + simpl; intuition.
    + intros. unfold out_edges. simpl. intro. destruct H2; auto.
  Qed.

End GtoL_LtoG_EQ.

Section LtoG_GtoL_EQ.

  Context {Vertex: Type}.
  Context {Edge: Type}.
  Context {EV: EqDec Vertex eq}.
  Context {EE: EqDec Edge eq}.

  Lemma lstToG_gToLst_eq: forall (g: PreGraph Vertex Edge) (LF: LocalFiniteGraph g) (VVA: ValidVertexAccessible g) root (X: EnumCovered Vertex (reachable g root)),
      vvalid g root -> is_list g root -> (listToGraph (graphToList g VVA LF (length (proj1_sig X)) root)) ~=~ (predicate_subgraph g (reachable g root)).
  Proof.
    intros. hnf. split; [|split; [|split]]; intros; simpl.
    - unfold predicate_vvalid. rewrite <- list_vertices_vvalid_iff; simpl; auto.
      rewrite <- listVertices'_In_rev. split; intros.
      + destruct H1 as [? | [? | ?]];
          [subst v; split; [| apply reachable_refl]; auto ..| ].
        apply (toEdgeList_reachable g VVA LF root) in H1.
        * split; auto. apply reachable_foot_valid in H1; auto.
        * apply reachable_refl; auto.
        * intros. simpl in H2. exfalso; auto.
      + destruct (equiv_dec root v). 1: hnf in e; left; auto. compute in c.
        right; right. apply (reachable_toEdgeList _ _ _ root _ _ _ X); auto.
        * apply reachable_refl; auto.
        * simpl. apply NoDup_nil.
        * simpl. intros. exfalso; auto.
        * intros. exfalso; auto.
        * destruct H1; auto.
    - unfold predicate_evalid. rewrite <- list_edges_evalid_iff. simpl.
      cut (In e (listEdges' Vertex Edge (rev (toEdgeList g VVA LF (length (proj1_sig X), root, nil)))) <->
           evalid g e /\ reachable g root (src g e) /\ reachable g root (dst g e)). 1: intros; intuition. rewrite <- listEdges'_In_rev. split; intros.
      + apply (toEdgeList_edge_reachable g VVA LF root) in H1; auto.
        * intros. simpl in H2; exfalso; auto.
        * apply reachable_refl; auto.
      + destruct H1 as [? [? ?]]. apply reachable_foot_valid in H3. apply (reachable_edge_toEdgeList _ _ _ root _ _ _ X); auto.
        * apply reachable_refl; auto.
        * simpl; apply NoDup_nil.
        * simpl; intros. exfalso; auto.
    - simpl in *. unfold predicate_evalid in H2. rewrite <- list_edges_evalid_iff in H1. simpl in H1. destruct H1. 1: exfalso; auto.
      apply (listToGraph'_NoDup_In_src (single_vertex_pregraph root) root) in H1.
      + destruct H1 as [v' [? ?]]. rewrite H3. apply shiftLeft_toEdgeList_In in H1; auto; intros.
        * simpl in H4. exfalso; auto.
        * inversion H4.
      + rewrite <- listEdges'_NoDup_rev. apply toEdgeList_edge_NoDup with root; auto.
        * apply reachable_refl; auto.
        * simpl. apply NoDup_nil.
    - simpl in *. unfold predicate_evalid in H2. rewrite <- list_edges_evalid_iff in H1. simpl in H1. destruct H1. 1: exfalso; auto.
      apply (listToGraph'_NoDup_In_dst (single_vertex_pregraph root) root) in H1.
      + destruct H1 as [v' [? ?]]. rewrite H3. rewrite <- in_rev in H1. apply toEdgeList_In in H1; auto. intros. simpl in H4. exfalso; auto.
      + rewrite <- listEdges'_NoDup_rev. apply toEdgeList_edge_NoDup with root; auto.
        * apply reachable_refl; auto.
        * simpl. apply NoDup_nil.
  Qed.

End LtoG_GtoL_EQ.
