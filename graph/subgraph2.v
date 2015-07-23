Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import RamifyCoq.Coqlib.
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
  fun e => evalid g e /\ p (src g e) /\ p (dst g e).

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
  exists (filter (fun e => if (sumbool_dec_and (node_pred_dec p (src g e)) (node_pred_dec p (dst g e))) then true else false) (edge_func g x)).
  split.
  + apply NoDup_filter.
    unfold edge_func.
    destruct (local_enumerable x); simpl.
    tauto.
  + intros.
    unfold predicate_partialgraph, predicate_vvalid, predicate_weak_evalid; simpl; intros.
    rewrite filter_In.
    rewrite edge_func_spec.
    destruct (sumbool_dec_and (node_pred_dec p (src g x0)) (node_pred_dec p (dst g x0))).
    - unfold out_edges, Ensembles.In in *; simpl.
      assert (true = true) by auto; tauto.
    - unfold out_edges, Ensembles.In in *; simpl.
      assert (~ false = true) by congruence; tauto.
Defined.

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

Lemma subgraph_edge: forall (p: V -> Prop) x y,
    edge g x y -> p x -> p y -> edge (predicate_subgraph p) x y.
Proof.
  intros.
  destruct H as [? [? ?]].
  unfold edge.
  simpl.
  unfold predicate_vvalid.
  do 2 (split; [tauto |]).
  rewrite step_spec in H3 |- *.
  destruct H3 as [e [? [? ?]]].
  exists e.
  split; [| split; simpl; auto].
  simpl.
  unfold predicate_evalid.
  rewrite H4, H5.
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
  rewrite step_spec in H3 |- *.
  destruct H3 as [e [? [? ?]]].
  exists e.
  split; [| split; simpl; auto].
  simpl.
  unfold predicate_weak_evalid.
  rewrite H4, H5.
  auto.
Qed.

End SubGraph.

Section SI_EQUIV.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

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
  split; [tauto |].
  split; [tauto |].
  exists e.
  rewrite <- !H6.
  rewrite <- !H7.
  rewrite <- !H8.
  subst.
  repeat split; auto; tauto.
Qed.

Lemma si_reachable_subgraph: forall (g1 g2: PreGraph V E) S, g1 ~=~ g2 -> (reachable_subgraph g1 S) ~=~ (reachable_subgraph g2 S).
Proof.
  intros.
  pose proof (fun x => si_reachable_through_set g1 g2 S x H).
  destruct H as [? [? [? ?]]].
  split; [| split; [| split]]; simpl; auto.
  + intros.
    unfold predicate_vvalid.
    rewrite (H0 v), H.
    tauto.
  + intros.
    unfold predicate_evalid.
    rewrite (H0 (src g1 e)), (H0 (dst g1 e)), H1, H2, H3.
    tauto.
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

End SI_EQUIV.