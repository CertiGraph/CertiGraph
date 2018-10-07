Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Equivalence_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.path_lemmas.

Section FiniteGraph.

Context {V E: Type} {EV: EqDec V eq} {EE: EqDec E eq}.

Class FiniteGraph (pg: PreGraph V E) :=
{
  finiteV: Enumerable V (vvalid pg);
  finiteE: Enumerable E (evalid pg)
}.

Class LocalFiniteGraph (pg: PreGraph V E) :=
{
  local_enumerable: forall x, Enumerable E (out_edges pg x)
}.

Definition edge_func (pg: PreGraph V E) {lfg: LocalFiniteGraph pg} x := proj1_sig (local_enumerable x).

Lemma edge_func_spec: forall {pg : PreGraph V E} {lfg: LocalFiniteGraph pg} e x,
  In e (edge_func pg x) <-> evalid pg e /\ src pg e = x.
Proof.
  intros.
  unfold edge_func.
  destruct (local_enumerable x) as [? [?H ?H]]; simpl.
  specialize (H0 e).
  rewrite H0; unfold out_edges.
  clear - H0.
  unfold Ensembles.In; tauto.
Qed.

Lemma edge_func_step: forall {pg : PreGraph V E} {lfg: LocalFiniteGraph pg} x y,
  step pg x y <-> In y (map (dst pg) (edge_func pg x)).
Proof.
  intros.
  rewrite step_spec.
  rewrite in_map_iff.
  apply Morphisms_Prop.ex_iff_morphism.
  hnf; cbv beta; intro e.
  rewrite edge_func_spec.
  clear - e.
  tauto.
Qed.

Instance LocalFiniteGraph_FiniteGraph (g: PreGraph V E) (fg: FiniteGraph g): LocalFiniteGraph g.
Proof.
  intros.
  destruct fg as [[vs [?H ?H]] [es [?H ?H]]].
  constructor.
  intros.
  exists (filter (fun e => if equiv_dec (src g e) x then true else false) es).
  split.
  + apply NoDup_filter; auto.
  + intro e.
    rewrite filter_In.
    rewrite H2.
    unfold Ensembles.In, out_edges.
    destruct_eq_dec (src g e) x; [tauto |].
    assert (~ false = true) by congruence; tauto.
Defined.

Lemma finite_graph_si: forall (g1 g2: PreGraph V E),
  g1 ~=~ g2 ->
  FiniteGraph g1 ->
  FiniteGraph g2.
Proof.
  intros.
  destruct X as [X Y].
  constructor.
  + revert X; apply Enumerable_Same_set.
    destruct H as [? _]; rewrite Same_set_spec; auto.
  + revert Y; apply Enumerable_Same_set.
    destruct H as [_ [? _]]; rewrite Same_set_spec; auto.
Qed.

Lemma gen_dst_preserve_finite: forall (g: PreGraph V E) e t, FiniteGraph g -> FiniteGraph (pregraph_gen_dst g e t).
Proof.
  intros. apply Build_FiniteGraph; simpl.
  + apply finiteV.
  + apply finiteE.
Qed.

Lemma predicate_sub_finitegraph: forall (g: PreGraph V E) (p: NodePred V), FiniteGraph g -> FiniteGraph (predicate_subgraph g p).
Proof.
  intros.
  destruct X as [X Y].
  constructor.
  + destruct X as [l ?].
    exists (filter (fun v => if node_pred_dec p v then true else false) l); split.
    - apply NoDup_filter; tauto.
    - intros.
      unfold predicate_subgraph, predicate_vvalid, predicate_evalid; simpl; intros.
      rewrite filter_In.
      unfold Ensembles.In in *.
      assert (false <> true) by congruence.
      destruct (node_pred_dec p x); firstorder.
  + destruct Y as [l ?].
    exists (filter (fun e => if (Coqlib2.sumbool_dec_and (node_pred_dec p (src g e)) (node_pred_dec p (dst g e))) then true else false) l); split.
    - apply NoDup_filter; tauto.
    - intros e.
      unfold predicate_subgraph, predicate_vvalid, predicate_evalid; simpl; intros.
      rewrite filter_In.
      unfold Ensembles.In in *.
      assert (false <> true) by congruence.
      destruct (Coqlib2.sumbool_dec_and (node_pred_dec p (src g e)) (node_pred_dec p (dst g e))); firstorder.
Qed.

Lemma predicate_partial_finitegraph: forall (g: PreGraph V E) (p: NodePred V), FiniteGraph g -> FiniteGraph (predicate_partialgraph g p).
Proof.
  intros.
  destruct X as [X Y].
  constructor.
  + destruct X as [l ?].
    exists (filter (fun v => if node_pred_dec p v then true else false) l); split.
    - apply NoDup_filter; tauto.
    - intros.
      unfold predicate_subgraph, predicate_vvalid, predicate_evalid; simpl; intros.
      rewrite filter_In.
      unfold Ensembles.In in *.
      assert (false <> true) by congruence.
      destruct (node_pred_dec p x); firstorder.
  + destruct Y as [l ?].
    exists (filter (fun e => if (node_pred_dec p (src g e)) then true else false) l); split.
    - apply NoDup_filter; tauto.
    - intros e.
      unfold predicate_subgraph, predicate_vvalid, predicate_evalid; simpl; intros.
      rewrite filter_In.
      unfold Ensembles.In in *.
      assert (false <> true) by congruence.
      destruct (node_pred_dec p (src g e)); firstorder.
Qed.

Definition predicate_sub_localfinitegraph (g: PreGraph V E) (p: NodePred V) (LF: LocalFiniteGraph g): LocalFiniteGraph (predicate_subgraph g p).
Proof.
  refine (Build_LocalFiniteGraph _ _).
  intros.
  exists (filter (fun e => if (Coqlib2.sumbool_dec_and (node_pred_dec p (src g e)) (node_pred_dec p (dst g e))) then true else false) (edge_func g x)).
  split.
  + apply NoDup_filter.
    unfold edge_func.
    destruct (local_enumerable x); simpl.
    tauto.
  + intros.
    unfold predicate_subgraph, predicate_vvalid, predicate_evalid; simpl; intros.
    rewrite filter_In.
    rewrite edge_func_spec.
    destruct (Coqlib2.sumbool_dec_and (node_pred_dec p (src g x0)) (node_pred_dec p (dst g x0))).
    - unfold out_edges, Ensembles.In in *; simpl.
      assert (true = true) by auto; tauto.
    - unfold out_edges, Ensembles.In in *; simpl.
      assert (~ false = true) by congruence; tauto.
Defined.

Definition predicate_partial_localfinitegraph (g: PreGraph V E) (p: NodePred V) (LF: LocalFiniteGraph g) : LocalFiniteGraph (predicate_partialgraph g p).
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

Lemma finite_graph_join: forall (g: PreGraph V E) (PV1 PV2 PV: V -> Prop) (PE1 PE2 PE: E -> Prop),
  Prop_join PV1 PV2 PV ->
  Prop_join PE1 PE2 PE ->
  FiniteGraph (gpredicate_subgraph PV1 PE1 g) ->
  FiniteGraph (gpredicate_subgraph PV2 PE2 g) ->
  FiniteGraph (gpredicate_subgraph PV PE g).
Proof.
  intros.
  constructor.
  + destruct X as [[l1 [?H ?H]] ?].
    destruct X0 as [[l2 [?H ?H]] ?].
    exists (l1 ++ l2).
    split.
    - apply NoDup_app_inv; auto.
      intros v ? ?.
      rewrite H2 in H5; rewrite H4 in H6.
      unfold Ensembles.In in H5, H6; simpl in H5, H6.
      rewrite Intersection_spec in H5, H6.
      destruct H5, H6, H as [_ ?].
      apply (H v); auto.
    - intros v.
      rewrite in_app_iff.
      rewrite H2, H4.
      unfold Ensembles.In; simpl; rewrite !Intersection_spec.
      destruct H as [? _]; specialize (H v); tauto.
  + destruct X as [? [l1 [?H ?H]]].
    destruct X0 as [? [l2 [?H ?H]]].
    exists (l1 ++ l2).
    split.
    - apply NoDup_app_inv; auto.
      intros e ? ?.
      rewrite H2 in H5; rewrite H4 in H6.
      unfold Ensembles.In in H5, H6; simpl in H5, H6.
      rewrite Intersection_spec in H5, H6.
      destruct H5, H6, H0 as [_ ?].
      apply (H0 e); auto.
    - intros e.
      rewrite in_app_iff.
      rewrite H2, H4.
      unfold Ensembles.In; simpl; rewrite !Intersection_spec.
      destruct H0 as [? _]; specialize (H0 e); tauto.
Qed.

Lemma FiniteGraph_EnumCovered: forall (g: PreGraph V E) (fin: FiniteGraph g) x, EnumCovered V (reachable g x).
Proof.
  intros.
  destruct fin as [[xs [? ?]] _].
  exists xs.
  split; auto.
  intros y ?.
  apply reachable_foot_valid in H1.
  rewrite H0.
  exact H1.
Qed.

Class ReachableFiniteGraph (pg: PreGraph V E) := {
  finiteR: forall x, vvalid pg x -> Enumerable V (reachable pg x)
}.

Lemma construct_reachable_list: forall (g: PreGraph V E) {rfg: ReachableFiniteGraph g} x, Decidable (vvalid g x) -> {l: list V | NoDup l /\ reachable_list g x l}.
Proof.
  intros.
  destruct H.
  + destruct (finiteR x v) as [l ?H].
    exists l.
    unfold reachable_list; auto.
  + exists nil.
    split; [constructor |].
    intro; simpl.
    pose proof reachable_head_valid g x y.
    tauto.
Qed.

Lemma RFG_reachable_decicable: forall (g: PreGraph V E) {rfg: ReachableFiniteGraph g} x y, vvalid g x -> Decidable (reachable g x y).
Proof.
  intros.
  pose proof finiteR x H.
  destruct X as [l [_ ?H]].
  unfold Ensembles.In in H0.
  destruct (in_dec equiv_dec y l); [left | right]; rewrite <- H0; auto.
Qed.

Lemma RFG_reachable_decicable': forall (g: PreGraph V E) {rfg: ReachableFiniteGraph g} x y, Decidable (vvalid g x) -> Decidable (reachable g x y).
Proof.
  intros.
  destruct H; [apply RFG_reachable_decicable; auto | right].
  intro.
  apply reachable_head_valid in H; tauto.
Qed.

Lemma construct_reachable_set_list: forall (g: PreGraph V E) {rfg: ReachableFiniteGraph g} S
  (V_DEC: forall x, In x S -> Decidable (vvalid g x)),
  {l: list V | NoDup l /\ reachable_set_list g S l}.
Proof.
  intros.
  induction S.
  + exists nil.
    split; [constructor |].
    intro.
    pose proof reachable_through_empty g.
    pose proof Empty_set_iff V.
    unfold Same_set, Included, Ensembles.In in *.
    simpl.
    firstorder.
  + spec IHS.
    - intros; apply V_DEC.
      right; auto.
    - destruct IHS as [l2 ?H].
      destruct (construct_reachable_list g a (V_DEC a (or_introl eq_refl))) as [l1 ?H].
      exists (nodup equiv_dec (l1 ++ l2)).
      split; [apply NoDup_nodup |].
      destruct H as [_ ?].
      destruct H0 as [_ ?].
      unfold reachable_set_list, reachable_list in *.
      intros.
      rewrite nodup_In.
      rewrite in_app_iff, reachable_through_set_eq.
      specialize (H x).
      specialize (H0 x).
      tauto.
Qed.

Lemma RFG_reachable_through_set_decicable: forall (g: PreGraph V E) {rfg: ReachableFiniteGraph g} S y, (forall x, In x S -> Decidable (vvalid g x)) -> Decidable (reachable_through_set g S y).
Proof.
  intros.
  destruct (construct_reachable_set_list g S X) as [l [_ ?]].
  destruct (in_dec equiv_dec y l); [left | right]; rewrite <- (H y); auto.
Qed.

End FiniteGraph.
