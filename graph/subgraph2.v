Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Arith.Arith.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import Coq.Lists.List.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Equivalence.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.List_ext.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_ind.

Section SubGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context (g: PreGraph V E).
Context {MA: MathGraph g}.
Context {LF: LocalFiniteGraph g}.

Definition predicate_vvalid (p: V -> Prop): Ensemble V :=
  fun n => vvalid g n /\ p n.

Definition predicate_evalid (p: V -> Prop): Ensemble E :=
  fun e => evalid g e /\ p (src g e) /\ p (dst g e).

Definition predicate_weak_evalid (p: V -> Prop): Ensemble E :=
  fun e => evalid g e /\ p (src g e).

Definition predicate_subgraph (p: V -> Prop): PreGraph V E :=
  Build_PreGraph EV EE (predicate_vvalid p) (predicate_evalid p) (src g) (dst g).

Definition predicate_partialgraph (p: V -> Prop): PreGraph V E :=
  Build_PreGraph EV EE (predicate_vvalid p) (predicate_weak_evalid p) (src g) (dst g).

Definition reachable_subgraph (S : list V): PreGraph V E :=
  predicate_subgraph (reachable_through_set g S).

Definition unreachable_partialgraph (S : list V): PreGraph V E :=
  predicate_partialgraph (fun n => ~ reachable_through_set g S n).

Definition predicate_sub_mathgraph (p: V -> Prop): MathGraph (predicate_subgraph p).
Proof.
  refine (Build_MathGraph _ (is_null g) (is_null_dec g) _ _).
  + unfold predicate_subgraph, predicate_vvalid, predicate_evalid; simpl; intros.
    pose proof valid_graph g e.
    unfold weak_valid in H0.
    tauto.
  + unfold predicate_subgraph, predicate_vvalid, predicate_evalid; simpl; intros.
    pose proof valid_not_null g x.
    tauto.
Defined.

Definition predicate_sub_localfinitegraph (p: NodePred V) : LocalFiniteGraph (predicate_subgraph p).
Proof.
  refine (Build_LocalFiniteGraph _ _).
  intros.
  exists (filter (fun e => if (sumbool_dec_and (node_pred_dec p (src g e)) (node_pred_dec p (dst g e))) then true else false) (edge_func g x)).
  split.
  + apply NoDup_filter.
    unfold edge_func.
    destruct (local_enumerable x); simpl.
    tauto.
  + intros.
    unfold predicate_subgraph, predicate_vvalid, predicate_evalid; simpl; intros.
    rewrite filter_In.
    rewrite edge_func_spec.
    destruct (sumbool_dec_and (node_pred_dec p (src g x0)) (node_pred_dec p (dst g x0))).
    - unfold out_edges, Ensembles.In in *; simpl.
      assert (true = true) by auto; tauto.
    - unfold out_edges, Ensembles.In in *; simpl.
      assert (~ false = true) by congruence; tauto.
Defined.

Definition predicate_partial_localfinitegraph (p: NodePred V) : LocalFiniteGraph (predicate_partialgraph p).
Proof.
  refine (Build_LocalFiniteGraph _ _).
  intros.
  exists (filter (fun e => if (node_pred_dec p (src g e)) then true else false) (edge_func g x)).
  split.
  + apply NoDup_filter.
    unfold edge_func.
    destruct (local_enumerable x); simpl.
    tauto.
  + intros.
    unfold predicate_partialgraph, predicate_vvalid, predicate_weak_evalid; simpl; intros.
    rewrite filter_In.
    rewrite edge_func_spec.
    destruct (node_pred_dec p (src g x0)).
    - unfold out_edges, Ensembles.In in *; simpl.
      assert (true = true) by auto; tauto.
    - unfold out_edges, Ensembles.In in *; simpl.
      assert (~ false = true) by congruence; tauto.
Defined.

Lemma reachable_subgraph_partialgraph (p: V -> Prop):
  forall (n1 n2: V),
    reachable (predicate_subgraph p) n1 n2 <-> reachable (predicate_partialgraph p) n1 n2.
Proof.
  intros.
  unfold reachable, reachable_by, reachable_by_path, good_path.
  apply ex_iff.
  intro l.
  apply and_iff_compat_l.
  apply and_iff_compat_r.
  destruct l; [simpl; tauto |].
  revert v; induction l; intros.
  + simpl.
    tauto.
  + change (valid_path (predicate_subgraph p) (v :: a :: l)) with (edge (predicate_subgraph p) v a /\ valid_path (predicate_subgraph p) (a :: l)).
    change (valid_path (predicate_partialgraph p) (v :: a :: l)) with (edge (predicate_partialgraph p) v a /\ valid_path (predicate_partialgraph p) (a :: l)).
    rewrite IHl.
    apply and_iff_compat_r_weak; intro.
    assert (vvalid (predicate_partialgraph p) a).
    Focus 1. {
      apply valid_path_valid in H.
      inversion H; subst; auto.
    } Unfocus.
    unfold edge; simpl.
    rewrite !step_spec. simpl.
    apply and_iff_compat_l.
    apply and_iff_compat_l.
    apply ex_iff.
    intro.
    apply and_iff_compat_r_weak; intros [? ?].
    simpl in H0.
    unfold predicate_evalid, predicate_weak_evalid.
    unfold predicate_vvalid in H0.
    subst.
    tauto.
Qed.

Lemma reachable_by_eq_subgraph_reachable (p: V -> Prop):
  forall (n1 n2: V),
    g |= n1 ~o~> n2 satisfying p <-> reachable (predicate_subgraph p) n1 n2.
Proof.
  intros; split; intros; destruct H as [path [? [? ?]]]; exists path.
  + split; auto. split. 2: repeat intro; hnf; auto.
    (* destruct path. simpl; auto. *)
    clear H.
    destruct path. simpl; auto.
    revert v H0 H1. induction path; intros.
    - simpl in *. unfold predicate_vvalid. split; auto.
      hnf in H1. inversion H1; auto.
    - specialize (IHpath a). simpl in *. destruct H0. split.
      * hnf in H. destruct H as [? [? ?]]. hnf.
        unfold vvalid. unfold edge_func.
        unfold predicate_subgraph.
        unfold predicate_vvalid, predicate_evalid.
        hnf in H1. inversion H1; subst. inversion H7; subst.
        split; auto.
        split; auto.
        rewrite step_spec in H3 |- *; simpl in H3 |- *.
        destruct H3 as [e [? [? ?]]]; exists e; subst; tauto.
      * apply IHpath. apply H0. hnf in H1. hnf; intros. inversion H1; subst; auto.
    - rewrite Forall_forall; intros; auto.
  + split; auto. split.
    - clear H H1. destruct path. simpl; auto.
      revert v H0. induction path; intros; simpl in *.
      * destruct H0; auto.
      * destruct H0. split. hnf in H.
        destruct H as [[? ?] [[? ?] ?]].
        split; auto. split; auto. unfold edge_func in H4.
        unfold predicate_subgraph in H4.
        unfold predicate_vvalid, predicate_evalid in H4.
        rewrite step_spec in H4 |- *; simpl in H4 |- *.
        destruct H4 as [e [? [? ?]]]; exists e; subst; tauto.
        apply IHpath. apply H0.
    - clear H H1. destruct path. hnf; intros. constructor.
      revert v H0. induction path; intros.
      * unfold predicate_subgraph in *.
        hnf. intros. simpl in H0. destruct H0. repeat constructor; auto.
      * unfold path_prop in *. 
        specialize (IHpath a).
        inversion H0.
        unfold edge, predicate_subgraph, predicate_vvalid in H; simpl in H.
        constructor; [tauto | auto].
Qed.

Lemma reachable_by_eq_partialgraph_reachable (p: V -> Prop):
  forall (n1 n2: V),
    g |= n1 ~o~> n2 satisfying p <-> reachable (predicate_partialgraph p) n1 n2.
Proof.
  intros.
  rewrite reachable_by_eq_subgraph_reachable.
  apply reachable_subgraph_partialgraph.
Qed.

Lemma reachable_by_head_valid (p: V -> Prop):
  forall (n1 n2: V),
    g |= n1 ~o~> n2 satisfying p -> vvalid g n1.
Proof.
  intros.
  rewrite reachable_by_eq_partialgraph_reachable in H.
  apply reachable_head_valid in H.
  destruct H.
  auto.
Qed.

Lemma reachable_by_foot_valid (p: V -> Prop):
  forall (n1 n2: V),
    g |= n1 ~o~> n2 satisfying p -> vvalid g n2.
Proof.
  intros.
  rewrite reachable_by_eq_partialgraph_reachable in H.
  apply reachable_foot_valid in H.
  destruct H.
  auto.
Qed.

Lemma predicate_subgraph_reachable_included (p: V -> Prop): 
  forall (n: V), Included (reachable (predicate_subgraph p) n) (reachable g n).
Proof.
  intros.
  intro; intros.
  unfold Ensembles.In in *.
  rewrite reachable_ind_reachable.
  rewrite reachable_ind_reachable in H.
  induction H.
  + constructor. destruct H; auto.
  + apply ind.reachable_cons with y; auto.
    destruct H as [[? ?] [[? ?] ?]].
    rewrite step_spec in H4.
    destruct H4 as [e [[? ?] [? ?]]].
    split; [| split]; auto.
    rewrite step_spec.
    exists e; auto.
Qed.

Lemma predicate_partialgraph_reachable_included (p: V -> Prop): 
  forall (n: V), Included (reachable (predicate_partialgraph p) n) (reachable g n).
Proof.
  intros.
  intro; intros.
  unfold Ensembles.In in *.
  rewrite reachable_ind_reachable.
  rewrite reachable_ind_reachable in H.
  induction H.
  + constructor. destruct H; auto.
  + apply ind.reachable_cons with y; auto.
    destruct H as [[? ?] [[? ?] ?]].
    rewrite step_spec in H4.
    destruct H4 as [e [[? ?] [? ?]]].
    split; [| split]; auto.
    rewrite step_spec.
    exists e; auto.
Qed.

Lemma subgraph_step: forall (p: V -> Prop) x y,
  step g x y -> p x -> p y -> step (predicate_subgraph p) x y.
Proof.
  intros.
  rewrite step_spec in H |- *.
  destruct H as [e [? [? ?]]].
  exists e.
  split; [| split; simpl; auto].
  simpl.
  unfold predicate_evalid.
  rewrite H2, H3.
  auto.
Qed.

Lemma subgraph_edge: forall (p: V -> Prop) x y,
    edge g x y -> p x -> p y -> edge (predicate_subgraph p) x y.
Proof.
  intros.
  destruct H as [? [? ?]].
  unfold edge.
  simpl.
  unfold predicate_vvalid.
  do 2 (split; [tauto |]).
  apply subgraph_step; auto.
Qed.

Lemma partialgraph_step: forall (p: V -> Prop) x y,
  step g x y -> p x -> step (predicate_partialgraph p) x y.
Proof.
  intros.
  rewrite step_spec in H |- *.
  destruct H as [e [? [? ?]]].
  exists e.
  split; [| split; simpl; auto].
  simpl.
  unfold predicate_weak_evalid.
  rewrite H1.
  auto.
Qed.

Lemma partialgraph_edge: forall (p: V -> Prop) x y,
    edge g x y -> p x -> p y -> edge (predicate_partialgraph p) x y.
Proof.
  intros.
  destruct H as [? [? ?]].
  unfold edge.
  simpl.
  unfold predicate_vvalid.
  do 2 (split; [tauto |]).
  apply partialgraph_step; auto.
Qed.

End SubGraph.

Section IS_PARTIAL_GRAPH.

  Context {V E: Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.

  Definition is_partial_graph (g1 g2: PreGraph V E) :=
    (forall v : V, vvalid g1 v -> vvalid g2 v) /\
    (forall e: E, evalid g1 e -> evalid g2 e) /\
    (forall e: E, evalid g1 e -> vvalid g1 (src g1 e) -> src g1 e = src g2 e) /\
    (forall e: E, evalid g1 e -> vvalid g1 (dst g1 e) -> dst g1 e = dst g2 e).

  Lemma is_partial_graph_reachable_by_path: forall (g1 g2: PreGraph V E) (p: path) (n: V) (P: Ensemble V) (n': V),
      is_partial_graph g1 g2 -> g1 |= p is n ~o~> n' satisfying P -> g2 |= p is n ~o~> n' satisfying P.
  Proof.
    intros. destruct H0 as [[? ?] [? ?]]. split; split; auto. clear H0 H1 H3. induction p; simpl; auto.
    simpl in H2. destruct H as [? [? [? ?]]]. destruct p.
    + apply H; auto.
    + destruct H2. specialize (IHp H4). split; auto.
      destruct H2 as [? [? ?]]. pose proof (H _ H2). pose proof (H _ H5). do 2 (split; auto).
      rewrite step_spec in H6 |-* . destruct H6 as [e [? [? ?]]]. exists e. split; [|split].
      - apply H0; auto.
      - rewrite <- H9 in *. specialize (H1 _ H6 H2). auto.
      - rewrite <- H10 in *. specialize (H3 _ H6 H5). auto.
  Qed.

  Lemma is_partial_graph_reachable_by: forall (g1 g2: PreGraph V E) (n: V) (P: Ensemble V) (n': V),
      is_partial_graph g1 g2 -> g1 |= n ~o~> n' satisfying P -> g2 |= n ~o~> n' satisfying P.
  Proof. intros. destruct H0 as [p ?]. exists p. apply is_partial_graph_reachable_by_path with g1; auto. Qed.

  Lemma is_partial_graph_reachable: forall (g1 g2: PreGraph V E) (n: V) (n': V),
      is_partial_graph g1 g2 -> reachable g1 n n' -> reachable g2 n n'.
  Proof. intros. apply is_partial_graph_reachable_by with g1; auto. Qed.

End IS_PARTIAL_GRAPH.

Section SI_EQUIV.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Lemma partial_partialgraph: forall p1 p2 (g: PreGraph V E),
  (predicate_partialgraph (predicate_partialgraph g p1) p2) ~=~ 
  (predicate_partialgraph g (Intersection _ p1 p2)).
Proof.
  intros.
  split; [| split; [| split]]; simpl; intros.
  + unfold predicate_vvalid; simpl; unfold predicate_vvalid.
    rewrite Intersection_spec.
    tauto.
  + unfold predicate_weak_evalid; simpl.
    unfold predicate_weak_evalid.
    rewrite Intersection_spec.
    tauto.
  + reflexivity.
  + reflexivity.
Qed.

Lemma sub_subgraph: forall p1 p2 (g: PreGraph V E),
  (predicate_subgraph (predicate_subgraph g p1) p2) ~=~ 
  (predicate_subgraph g (Intersection _ p1 p2)).
Proof.
  intros.
  split; [| split; [| split]]; simpl; intros.
  + unfold predicate_vvalid; simpl; unfold predicate_vvalid.
    rewrite Intersection_spec.
    tauto.
  + unfold predicate_evalid; simpl; unfold predicate_evalid; simpl.
    rewrite !Intersection_spec.
    tauto.
  + reflexivity.
  + reflexivity.
Qed.

Lemma partialgraph_si_node_prop: forall n (g1 g2: PreGraph V E) p1 p2,
  (predicate_partialgraph g1 p1) ~=~ (predicate_partialgraph g2 p2) ->
  Included p1 (vvalid g1) ->
  Included p2 (vvalid g2) ->
  (p1 n <-> p2 n).
Proof.
  intros.
  destruct H as [? _].
  specialize (H n).
  specialize (H0 n).
  specialize (H1 n).
  simpl in *.
  unfold predicate_vvalid in H.
  tauto.
Qed.

Lemma subgraph_node_prop: forall n (g1 g2: PreGraph V E) p1 p2,
  (predicate_subgraph g1 p1) ~=~ (predicate_subgraph g2 p2) ->
  Included p1 (vvalid g1) ->
  Included p2 (vvalid g2) ->
  (p1 n <-> p2 n).
Proof.
  intros.
  destruct H as [? _].
  specialize (H n).
  specialize (H0 n).
  specialize (H1 n).
  simpl in *.
  unfold Ensembles.In in *.
  unfold predicate_vvalid in H.
  tauto.
Qed.

Lemma si_stronger_partialgraph: forall (g1 g2: PreGraph V E) (p1 p2 p1' p2' p: V -> Prop),
  (forall v, p1' v <-> p1 v /\ p v) ->
  (forall v, p2' v <-> p2 v /\ p v) ->
  (predicate_partialgraph g1 p1) ~=~ (predicate_partialgraph g2 p2) ->
  (predicate_partialgraph g1 p1') ~=~ (predicate_partialgraph g2 p2').
Proof.
  intros.
  destruct H1 as [? [? [? ?]]].
  split; [| split; [| split]].
  + intro v; specialize (H1 v); specialize (H0 v); specialize (H v);
    simpl in H1 |- *.
    unfold predicate_vvalid in H1 |- *.
    tauto.
  + intro e; specialize (H2 e); specialize (H3 e); specialize (H (src g1 e)); specialize (H0 (src g2 e));
    simpl in H2, H3 |- *.
    unfold predicate_weak_evalid in H2, H3 |- *. clear H4. split; intros; destruct H4.
    - rewrite H in H5. destruct H5. assert (evalid g1 e /\ p1 (src g1 e)) by auto.
      specialize (H3 H7). rewrite H2 in H7. specialize (H3 H7). rewrite <- H3 in *. tauto.
    - rewrite H0 in H5. destruct H5. assert (evalid g2 e /\ p2 (src g2 e)) by auto.
      assert (evalid g1 e /\ p1 (src g1 e)) by tauto. specialize (H3 H8 H7).
      rewrite H3 in *. rewrite H. tauto.
  + simpl in *. unfold predicate_weak_evalid in *. intros.
    rewrite H in H5. rewrite H0 in H6. apply H3; tauto.
  + simpl in *. unfold predicate_weak_evalid in *. intros.
    rewrite H in H5. rewrite H0 in H6. apply H4; tauto.
Qed.

Lemma si_stronger_partialgraph_simple: forall (g1 g2: PreGraph V E) (p p': V -> Prop),
  Included p' p ->
  (predicate_partialgraph g1 p) ~=~ (predicate_partialgraph g2 p) ->
  (predicate_partialgraph g1 p') ~=~ (predicate_partialgraph g2 p').
Proof.
  intros.
  eapply si_stronger_partialgraph with (p := p'); [| | exact H0].
  + intro v; specialize (H v); simpl in H; tauto.
  + intro v; specialize (H v); simpl in H; tauto.
Qed.

Instance subgraph_proper: Proper (structurally_identical ==> (pointwise_relation V iff) ==> structurally_identical) predicate_subgraph.
Proof.
  do 2 (hnf; intros).
  destruct H as [? [? [? ?]]].
  split; [| split; [| split]]; intros; simpl.
  + unfold predicate_vvalid.
    rewrite H0, H.
    reflexivity.
  + unfold predicate_evalid. rewrite H0, H1. specialize (H1 e).
    split; intros; destruct H4 as [? [? ?]]; [rewrite <- H2, <- H3 | rewrite H2, H3]; tauto.
  + simpl in * |- . unfold predicate_evalid in * |- . apply H2; tauto.
  + simpl in * |- . unfold predicate_evalid in * |- . apply H3; tauto.
Defined.

Global Existing Instance subgraph_proper.

Instance partialgraph_proper: Proper (structurally_identical ==> (pointwise_relation V iff) ==> structurally_identical) predicate_partialgraph.
Proof.
  do 2 (hnf; intros).
  destruct H as [? [? [? ?]]].
  split; [| split; [| split]]; intros; simpl.
  + unfold predicate_vvalid.
    rewrite H0, H.
    reflexivity.
  + unfold predicate_weak_evalid. rewrite H0, H1. specialize (H1 e).
    split; intro; intuition; [rewrite <- H2 | rewrite H2]; auto.
  + simpl in * |- . unfold predicate_weak_evalid in * |- . apply H2; tauto.
  + simpl in * |- . unfold predicate_weak_evalid in * |- . apply H3; tauto.
Defined.

Global Existing Instance partialgraph_proper.

Instance reachable_by_proper: Proper ((@structurally_identical V E _ _) ==> (@eq V) ==> (pointwise_relation V iff) ==> (@eq V) ==> iff) (@reachable_by V E _ _).
Proof.
  intros.
  do 4 (hnf; intros); subst.
  rewrite !reachable_by_eq_partialgraph_reachable.
  rewrite H, H1.
  reflexivity.
Defined.

Global Existing Instance reachable_by_proper.

Instance reachable_by_proper': Proper ((@structurally_identical V E _ _) ==> (@eq V) ==> (pointwise_relation V iff) ==> (pointwise_relation V iff)) (@reachable_by V E _ _).
Proof.
  intros.
  do 4 (hnf; intros); subst.
  rewrite !reachable_by_eq_partialgraph_reachable.
  rewrite H, H1.
  reflexivity.
Defined.

Global Existing Instance reachable_by_proper'.

Lemma predicate_partialgraph_reachable_by_included (g: PreGraph V E) (p p0: V -> Prop): 
  forall (n: V), Included (reachable_by (predicate_partialgraph g p) n p0) (reachable_by g n p0).
Proof.
  intros.
  intro; intros.
  unfold Ensembles.In in *.
  rewrite reachable_by_eq_partialgraph_reachable in H |- *.
  rewrite partial_partialgraph in H.
  rewrite Intersection_comm in H.
  rewrite <- partial_partialgraph in H.
  apply predicate_partialgraph_reachable_included in H.
  auto.
Qed.

Lemma reachable_partialgraph_reachable (g: PreGraph V E): 
  forall (n: V), Included (reachable g n) (reachable (predicate_partialgraph g (reachable g n)) n).
Proof.
  intros.
  intro; intros.
  unfold Ensembles.In in *.
  rewrite reachable_ind2_reachable in H.
  induction H.
  + apply reachable_refl.
    simpl; unfold predicate_vvalid.
    split; auto.
    apply reachable_refl; auto.
  + apply reachable_edge with y; auto.
    apply partialgraph_edge; auto.
    rewrite reachable_ind2_reachable; auto.
    apply reachable_edge with y; auto.
    rewrite reachable_ind2_reachable; auto.
Qed.

Lemma reachable_partialgraph_reachable_equiv (g: PreGraph V E) (P: V -> Prop) (n: V):
  Included (reachable g n) P ->
  (pointwise_relation V iff) (reachable g n) (reachable (predicate_partialgraph g P) n).
Proof.
  intros.
  intro.
  split.
  + intros.
    apply reachable_partialgraph_reachable in H0.
    unfold Ensembles.In in H0.
    rewrite <- reachable_by_eq_partialgraph_reachable in H0 |- *.
    eapply reachable_by_weaken; [| eauto].
    auto.
  + apply predicate_partialgraph_reachable_included.
Qed.

Lemma reachable_by_partialgraph_reachable_by_equiv (g: PreGraph V E) (P p0: V -> Prop) (n: V):
  Included (reachable_by g n p0) P ->
  (pointwise_relation V iff) (reachable_by g n p0) (reachable_by (predicate_partialgraph g P) n p0).
Proof.
  intros.
  assert (pointwise_relation _ iff (reachable_by g n p0) (reachable (predicate_partialgraph g p0) n)).
  Focus 1. {
    hnf; intros.
    apply reachable_by_eq_partialgraph_reachable; auto.
  } Unfocus.
  rewrite H0 in H |- *.
  apply reachable_partialgraph_reachable_equiv in H.
  rewrite H.
  rewrite partial_partialgraph, Intersection_comm, <- partial_partialgraph.
  intro.
  rewrite reachable_by_eq_partialgraph_reachable.
  reflexivity.
Qed.

Lemma si_subgraph_edge: forall (g1 g2: PreGraph V E) (p1 p2: V -> Prop),
  g1 ~=~ g2 ->
  (forall x, vvalid g1 x -> vvalid g2 x -> (p1 x <-> p2 x)) ->
  (forall x y, edge (predicate_subgraph g1 p1) x y <-> edge (predicate_subgraph g2 p2) x y).
Proof.
  cut (forall (g1 g2: PreGraph V E) (p1 p2: V -> Prop),
    g1 ~=~ g2 ->
    (forall x, vvalid g1 x -> vvalid g2 x -> (p1 x <-> p2 x)) ->
    (forall x y, edge (predicate_subgraph g1 p1) x y -> edge (predicate_subgraph g2 p2) x y)).
  1: intros; split; apply H; auto; symmetry; auto.
  intros.
  unfold edge in *; rewrite !@step_spec in *.
  destruct H1 as [? [? [e [? [? ?]]]]].
  simpl in *.
  unfold predicate_vvalid, predicate_evalid in *.
  destruct H as [? [? [? ?]]].
  pose proof H0 x.
  pose proof H0 y.
  pose proof H x.
  pose proof H y.
  destruct H3 as [? [? ?]].
  specialize (H7 e H3). specialize (H8 e H3).
  assert (evalid g2 e) by (rewrite <- H6; auto).
  specialize (H7 H15). specialize (H8 H15).
  split; [tauto |].
  split; [tauto |].
  exists e.
  rewrite <- !H6.
  rewrite <- !H7.
  rewrite <- !H8.
  subst.
  repeat split; auto; try tauto.
Qed.

Lemma si_reachable_subgraph: forall (g1 g2: PreGraph V E) S, g1 ~=~ g2 -> (reachable_subgraph g1 S) ~=~ (reachable_subgraph g2 S).
Proof.
  intros.
  pose proof (fun x => si_reachable_through_set g1 g2 S x H).
  destruct H as [? [? [? ?]]].
  split; [| split; [| split]]; simpl; unfold predicate_evalid, predicate_vvalid; simpl; intros; auto.
  + rewrite (H0 v), H. tauto.
  + rewrite (H0 (src g1 e)), (H0 (dst g1 e)), H1. specialize (H1 e).
    split; intros; [rewrite <- H2, <- H3 | rewrite H2, H3]; intuition.
  + apply H2; tauto.
  + apply H3; tauto.
Qed.

Lemma si_reachable_by: forall (g1 g2: PreGraph V E) (p1 p2: V -> Prop) x y,
  g1 ~=~ g2 ->
  vertex_prop_coincide g1 g2 p1 p2 ->
  (g1 |= x ~o~> y satisfying p1 <-> g2 |= x ~o~> y satisfying p2).
Proof.
  cut (forall (g1 g2: PreGraph V E) p1 p2 (x y : V),
         g1 ~=~ g2 ->
         vertex_prop_coincide g1 g2 p1 p2 ->
         g1 |= x ~o~> y satisfying p1 ->
         g2 |= x ~o~> y satisfying p2).
  1: intros; split; apply H; [| | symmetry | apply vertex_prop_coincide_sym]; auto.
  intros.
  rewrite reachable_by_eq_subgraph_reachable in H1 |- *.
  assert (forall x, vvalid (predicate_subgraph g1 p1) x <-> vvalid (predicate_subgraph g2 p2) x).
  Focus 1. {
    intros; simpl; unfold predicate_vvalid.
    destruct H as [? _].
    specialize (H x0).
    specialize (H0 x0).
    hnf in H0.
    tauto.
  } Unfocus.
  assert (forall x y, edge (predicate_subgraph g1 p1) x y <-> edge (predicate_subgraph g2 p2) x y).
  Focus 1. {
    apply si_subgraph_edge.
    + auto.
    + intros.
      specialize (H0 x0).
      tauto.
  } Unfocus.
  pose proof (edge_equiv_reachable_equiv (predicate_subgraph g1 p1) (predicate_subgraph g2 p2) H2 H3).
  destruct (H4 x) as [? _].
  apply H5.
  auto.
Qed.

Lemma ReachDecidable_si: forall (g1 g2: PreGraph V E) (p1 p2: V -> Prop) x,
  g1 ~=~ g2 ->
  vertex_prop_coincide g1 g2 p1 p2 ->
  ReachDecidable g1 x p1 -> ReachDecidable g2 x p2.
Proof.
  intros.
  intro y; specialize (X y).
  destruct X; [left | right].
  + rewrite (si_reachable_by g1 g2 p1 p2) in r by auto; auto.
  + rewrite (si_reachable_by g1 g2 p1 p2) in n by auto; auto.
Qed.

Lemma si_reachable_by_through_set: forall (g1 g2: PreGraph V E) S p1 p2 n,
    g1 ~=~ g2 -> vertex_prop_coincide g1 g2 p1 p2 ->
    (reachable_by_through_set g1 S p1 n <-> reachable_by_through_set g2 S p2 n).
Proof.
  cut (forall (g1 g2: PreGraph V E) S p1 p2 n,
          g1 ~=~ g2 -> vertex_prop_coincide g1 g2 p1 p2 ->
          reachable_by_through_set g1 S p1 n -> reachable_by_through_set g2 S p2 n); intros.
  + split; intro; [apply (H g1 g2 S p1 p2) | apply (H g2 g1 S p2 p1)]; auto.
    - symmetry; auto.
    - unfold vertex_prop_coincide in H1 |-* . intros. symmetry. apply H1; auto.
  + destruct H1 as [s [? ?]]. exists s; split; auto. rewrite <- (si_reachable_by g1 g2 p1 p2); auto.
Qed.

End SI_EQUIV.

