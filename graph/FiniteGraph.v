Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.lib.EnumEnsembles.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.lib.relation_list.
Require Import CertiGraph.lib.Equivalence_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.path_lemmas.

Section FiniteGraph.

Context {V E: Type} {EV: EqDec V eq} {EE: EqDec E eq}.

Class FiniteGraph (pg: PreGraph V E) :=
{
  finiteV: Enumerable V (vvalid pg);
  finiteE: Enumerable E (evalid pg)
}.

Definition VList (pg: PreGraph V E) {fg: FiniteGraph pg} := proj1_sig (finiteV).
Definition EList (pg: PreGraph V E) {fg: FiniteGraph pg} := proj1_sig (finiteE).

(*trivial lemmas*)
Lemma NoDup_VList:
  forall (pg: PreGraph V E) {fg: FiniteGraph pg}, NoDup (VList pg).
Proof.
unfold VList; intros. destruct finiteV. unfold proj1_sig. apply a.
Qed.

Corollary NoDup_Perm_VList:
  forall (pg: PreGraph V E) {fg: FiniteGraph pg} (l: list V), Permutation l (VList pg) -> NoDup l.
Proof.
intros. apply (Permutation_NoDup (l:=VList pg)). apply Permutation_sym; auto. apply NoDup_VList.
Qed.

Lemma NoDup_EList:
  forall (pg: PreGraph V E) {fg: FiniteGraph pg}, NoDup (EList pg).
Proof.
unfold EList; intros. destruct finiteE. unfold proj1_sig. apply a.
Qed.

Corollary NoDup_Perm_EList:
  forall (pg: PreGraph V E) {fg: FiniteGraph pg} (l: list E), Permutation l (EList pg) -> NoDup l.
Proof.
intros. apply (Permutation_NoDup (l:=EList pg)). apply Permutation_sym; auto. apply NoDup_EList.
Qed.

Lemma VList_vvalid:
  forall (pg: PreGraph V E) {fg: FiniteGraph pg} v, In v (VList pg) <-> vvalid pg v.
Proof.
intros. unfold VList. destruct finiteV. simpl. apply a.
Qed.

Lemma EList_evalid:
  forall (pg: PreGraph V E) {fg: FiniteGraph pg} e, In e (EList pg) <-> evalid pg e.
Proof.
intros. unfold EList. destruct finiteE. simpl. apply a.
Qed.

(*destructing In_dec (VList g) can be slow outside, so adding this here*)
Lemma VList_In_dec:
  forall g {fg: FiniteGraph g} v, In v (VList g) \/ ~ In v (VList g).
Proof.
intros. destruct (in_dec EV v (VList g)); [left; auto | right; auto].
Qed.

Lemma EList_In_dec:
  forall g {fg: FiniteGraph g} e, In e (EList g) \/ ~ In e (EList g).
Proof.
intros. destruct (in_dec EE e (EList g)); [left; auto | right; auto].
Qed.

Corollary vvalid_dec:
  forall g {fg: FiniteGraph g} v, {vvalid g v} + {~ vvalid g v}.
Proof.
intros. destruct (in_dec EV v (VList g)). rewrite VList_vvalid in i; left; auto.
rewrite VList_vvalid in n; right; auto.
Qed.

Corollary evalid_dec:
  forall g {fg: FiniteGraph g} e, {evalid g e} + {~ evalid g e}.
Proof.
intros. destruct (in_dec EE e (EList g)). rewrite EList_evalid in i. left; auto.
rewrite EList_evalid in n. right; auto.
Qed.

Corollary strong_evalid_dec:
  forall g {fg: FiniteGraph g} e, {strong_evalid g e} + {~ strong_evalid g e}.
Proof.
intros. destruct (evalid_dec g e).
destruct (vvalid_dec g (src g e)).
destruct (vvalid_dec g (dst g e)).
left. split. auto. split; auto.
all: right; unfold not; intros Htmp; destruct Htmp as [? [? ?]]; contradiction.
Qed.

(*I'm hoping to use Zlength instead. But maybe we can leave numV and numE in WeightedEdgeListGraph until we need it elsewhere*)
Definition numV' g {fg: FiniteGraph g} := length (VList g).
Definition numE' g {fg: FiniteGraph g} := length (EList g).

(****EDGE ADD/REMOVE*****)
Instance pregraph_add_edge_finite g {fg: FiniteGraph g} e u v:
  FiniteGraph (pregraph_add_edge g e u v).
Proof.
constructor; unfold EnumEnsembles.Enumerable; simpl.
exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold addValidFunc. destruct (in_dec EE e (EList g)).
(*case e already inside*)
exists (EList g). split. apply NoDup_EList. intros; split; intros. left. apply EList_evalid in H; auto.
destruct H. apply EList_evalid; auto. rewrite H; auto.
(*case e not inside*)
exists (e::(EList g)). split. apply NoDup_cons. auto. apply NoDup_EList.
intros; split; intros.
destruct H. right; rewrite H; auto. left; rewrite <- EList_evalid; apply H.
destruct H. rewrite <- EList_evalid in H. apply in_cons. apply H.
rewrite H. simpl. left; auto.
Qed.

Instance pregraph_remove_edge_finite g {fg: FiniteGraph g} e :
  FiniteGraph (pregraph_remove_edge g e).
Proof.
unfold pregraph_remove_edge.
constructor; unfold Enumerable; simpl.
exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold removeValidFunc.
destruct (in_dec EE e (EList g)).
(*case e already inside*)
exists (remove EE e (EList (g))). split.
apply nodup_remove_nodup. apply NoDup_EList.
intros. rewrite remove_In_iff. rewrite EList_evalid. split; auto.
(*case e not inside*)
exists (EList g). split. apply NoDup_EList.
intros; split; intros. split. apply EList_evalid in H; auto.
unfold not; intros; subst x. contradiction.
destruct H. apply EList_evalid. auto.
Qed.

Lemma pregraph_remove_edge_EList:
  forall g {fg: FiniteGraph g} e l, Permutation (e::l) (EList g) ->
    Permutation l (EList (pregraph_remove_edge g e)).
Proof.
intros. assert (Hel: NoDup (e::l)). apply NoDup_Perm_EList in H; auto.
apply NoDup_Permutation.
apply NoDup_cons_1 in Hel; auto.
apply NoDup_EList.
intros. rewrite EList_evalid. simpl. unfold removeValidFunc. rewrite <- EList_evalid. split; intros.
split. apply (Permutation_in (l:=(e::l))). apply H. right; auto.
unfold not; intros. subst e. apply NoDup_cons_2 in Hel. contradiction.
destruct H0. apply Permutation_sym in H. apply (Permutation_in (l':=(e::l))) in H0. 2: auto.
destruct H0. symmetry in H0; contradiction. auto.
Qed.

Lemma pregraph_remove_edge_EList':
  forall g {fg: FiniteGraph g} e l, evalid g e -> Permutation l (EList (pregraph_remove_edge g e)) -> Permutation (e::l) (EList g).
Proof.
intros. assert (~ In e (EList (pregraph_remove_edge g e))).
rewrite EList_evalid. simpl. unfold not, removeValidFunc; intros. destruct H1. contradiction.
assert (~ In e l). unfold not; intros.
apply (Permutation_in (l':= (EList (pregraph_remove_edge g e)))) in H2. contradiction. auto.
apply NoDup_Permutation. apply NoDup_cons; auto. apply NoDup_Perm_EList in H0; auto.
apply NoDup_EList.
intros; split; intros. apply EList_evalid. destruct H3. subst x. auto.
apply (Permutation_in (l':= (EList (pregraph_remove_edge g e)))) in H3; auto.
rewrite EList_evalid in H3. simpl in H3. unfold removeValidFunc in H3. apply H3.
destruct (EE x e). unfold equiv in e0. subst x. left; auto.
unfold complement, equiv in c. right.
assert (evalid (pregraph_remove_edge g e) x). simpl. unfold removeValidFunc. split; auto.
apply EList_evalid in H3; auto.
rewrite <- EList_evalid in H4.
apply (Permutation_in (l:= (EList (pregraph_remove_edge g e)))). apply Permutation_sym; auto. apply H4.
Qed.

(**************LOCAL FINITE GRAPH**************)

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
