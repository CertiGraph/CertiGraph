Require Import Coq.Arith.Arith.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Equivalence.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.Equivalence_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_ind.

Section SubGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

(* TODO: Maybe redefine these three using respectful_set. *)
Definition strong_edge_prop (P: V -> Prop) (g: PreGraph V E): E -> Prop := fun e => P (src g e) /\ P (dst g e).

Definition weak_edge_prop (P: V -> Prop) (g: PreGraph V E): E -> Prop := fun e => P (src g e).

Definition weak'_edge_prop (P: V -> Prop) (g: PreGraph V E): E -> Prop := fun e => P (dst g e).

Instance weak_edge_prop_proper: Proper (Same_set ==> eq ==> Same_set) weak_edge_prop.
Proof.
  do 2 (hnf; intros); subst.
  rewrite Same_set_spec in *.
  intro e; unfold weak_edge_prop.
  auto.
Defined.
Global Existing Instance weak_edge_prop_proper.

Lemma weak_edge_prop_si: forall (P: V -> Prop) (g1 g2: PreGraph V E),
  g1 ~=~ g2 ->
  Same_set
   (Intersection _ (weak_edge_prop P g1) (evalid g1))
   (Intersection _ (weak_edge_prop P g2) (evalid g2)).
Proof.
  intros.
  rewrite Same_set_spec; intro e.
  rewrite !Intersection_spec.
  unfold weak_edge_prop.
  pose proof (proj1 (proj2 H) e).
  pose proof proj1 (proj2 (proj2 H)) e.
  split; intros [? ?]; do 2 (spec H1; [tauto |]); (split; [congruence | tauto]).
Qed.
  
Lemma weak_edge_prop_Disjoint: forall (P1 P2: V -> Prop) (g: PreGraph V E),
  Disjoint _ P1 P2 ->
  Disjoint _ (weak_edge_prop P1 g) (weak_edge_prop P2 g).
Proof.
  intros.
  unfold weak_edge_prop.
  rewrite Disjoint_spec in *.
  firstorder.
Qed.

Lemma weak_edge_prop_Complement: forall (P: V -> Prop) (g: PreGraph V E), Same_set (weak_edge_prop (Complement _ P) g) (Complement _ (weak_edge_prop P g)).
Proof.
  intros.
  unfold weak_edge_prop, Complement, Ensembles.In.
  rewrite Same_set_spec.
  hnf; intros; simpl.
  reflexivity.
Qed.

Lemma weak_edge_prop_Union: forall (P Q: V -> Prop) (g: PreGraph V E), Same_set (weak_edge_prop (Union _ P Q) g) (Union _ (weak_edge_prop P g) (weak_edge_prop Q g)).
Proof.
  intros.
  unfold weak_edge_prop.
  rewrite Same_set_spec; intros ?; rewrite !Union_spec.
  simpl.
  reflexivity.
Qed.

Lemma weak_edge_prop_Decidable: forall (P: V -> Prop) (g: PreGraph V E),
  (forall v, Decidable (P v)) ->
  (forall e, Decidable (weak_edge_prop P g e)).
Proof.
  intros.
  unfold weak_edge_prop.
  apply X.
Qed.

Definition gpredicate_subgraph (PV: V -> Prop) (PE: E -> Prop) (g: PreGraph V E): PreGraph V E :=
  Build_PreGraph EV EE (Intersection _ (vvalid g) PV) (Intersection _ (evalid g) PE) (src g) (dst g).

Context (g: PreGraph V E).

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

Lemma predicate_partialgraph_gpredicate_subgraph (p: V -> Prop): 
  (predicate_partialgraph p) ~=~ (gpredicate_subgraph p (Intersection _ (weak_edge_prop p g) (evalid g)) g).
Proof.
  split; [| split; [| split]]; simpl; intros.
  + rewrite Intersection_spec.
    reflexivity.
  + rewrite !Intersection_spec.
    unfold predicate_weak_evalid.
    unfold weak_edge_prop.
    tauto.
  + auto.
  + auto.
Qed.

Lemma reachable_by_path_subgraph_partialgraph (p q: V -> Prop):
  forall (n1 n2: V) (l: path),
    (predicate_subgraph p) |= l is n1 ~o~> n2 satisfying q <->
    (predicate_partialgraph p) |= l is n1 ~o~> n2 satisfying q.
Proof.
  intros. unfold reachable_by_path, good_path. apply and_iff_split; [|apply and_iff_split].
  + unfold path_endpoints. apply and_iff_compat_l. destruct l as [v l]. revert v. induction l; intros.
    - simpl. intuition.
    - rewrite !pfoot_cons. apply IHl.
  + destruct l as [v l]. revert v. induction l; intros.
    - simpl. intuition.
    - rewrite !valid_path_cons_iff. rewrite IHl. apply and_iff_compat_l, and_iff_compat_r.
      unfold strong_evalid. simpl. apply and_iff_compat_r_weak. intros. destruct H.
      unfold predicate_evalid. unfold predicate_weak_evalid. destruct H0. intuition.
  + destruct l as [v l]. simpl. destruct l. intuition. unfold path_prop'.
    rewrite !Forall_forall. simpl. intuition.
Qed.

Lemma reachable_subgraph_partialgraph (p: V -> Prop):
  forall (n1 n2: V),
    reachable (predicate_subgraph p) n1 n2 <-> reachable (predicate_partialgraph p) n1 n2.
Proof.
  intros. unfold reachable, reachable_by.
  apply ex_iff, reachable_by_path_subgraph_partialgraph.
Qed.

Lemma reachable_by_path_eq_subgraph_reachable (p: V -> Prop):
  forall (n1 n2: V) (path : path),
    g |= path is n1 ~o~> n2 satisfying p <-> (predicate_subgraph p) |= path is n1 ~o~> n2 satisfying (fun _ => True).
Proof.
  intros; split; intros; destruct H as [[? ?] [? ?]]; split.
  + split; auto. clear - H0. destruct path as [v l]. revert v H0. induction l; intros. 1: simpl in *; auto. rewrite pfoot_cons in H0 |-* . apply IHl; auto.
  + split. 2: destruct path; simpl; destruct l; auto; unfold path_prop'; rewrite Forall_forall; intros; auto.
    clear H H0. destruct path as [v l]. revert v H1 H2. induction l; intros. 1: simpl in H1; simpl in *; unfold predicate_vvalid; intuition.
    rewrite valid_path_cons_iff in H1 |-* . destruct H1 as [? [? ?]]. split; auto. split.
    - unfold strong_evalid in *. simpl. unfold predicate_evalid, predicate_vvalid. subst v. simpl in H2. hnf in H2. rewrite Forall_forall in H2.
      assert (In a (a :: l)) by apply in_eq. specialize (H2 _ H). intuition.
    - apply IHl; auto. apply path_prop_tail in H2. unfold ptail in H2. apply H2.
  + split; auto. clear - H0. destruct path as [v l]. revert v H0. induction l; intros. 1: simpl in *; auto. rewrite pfoot_cons in H0 |-* . apply IHl; auto.
  + clear H H0 H2. destruct path. revert v H1. induction l; intros.
    - simpl in H1. unfold good_path. simpl. auto.
    - rewrite valid_path_cons_iff in H1. destruct H1 as [? [? ?]]. simpl in H. subst v. unfold strong_evalid in H0. simpl in H0.
      unfold predicate_vvalid, predicate_evalid in H0. intuition. clear H6 H7. specialize (IHl _ H1).
      unfold predicate_subgraph in IHl; simpl in IHl. destruct IHl. split.
      * rewrite valid_path_cons_iff. do 2 (split; auto). hnf. auto.
      * simpl. hnf. rewrite Forall_forall. intros. simpl in H7. destruct H7. 1: subst; intuition.
        hnf in H6. destruct l. 1: inversion H7. hnf in H6. rewrite Forall_forall in H6. apply H6; auto.
Qed.

Lemma reachable_by_eq_subgraph_reachable (p: V -> Prop):
  forall (n1 n2: V),
    g |= n1 ~o~> n2 satisfying p <-> reachable (predicate_subgraph p) n1 n2.
Proof.
  intros. unfold reachable, reachable_by. apply ex_iff; intros.
  apply reachable_by_path_eq_subgraph_reachable.
Qed.

Lemma reachable_by_path_eq_partialgraph_reachable (p: V -> Prop):
  forall (n1 n2: V) (l : path),
    g |= l is n1 ~o~> n2 satisfying p <->
    (predicate_partialgraph p) |= l is n1 ~o~> n2 satisfying (fun _ => True).
Proof.
  intros. rewrite reachable_by_path_eq_subgraph_reachable.
  apply reachable_by_path_subgraph_partialgraph.
Qed.

Lemma reachable_by_eq_partialgraph_reachable (p: V -> Prop):
  forall (n1 n2: V),
    g |= n1 ~o~> n2 satisfying p <-> reachable (predicate_partialgraph p) n1 n2.
Proof.
  intros.
  rewrite reachable_by_eq_subgraph_reachable.
  apply reachable_subgraph_partialgraph.
Qed.

Lemma reachable_by_eq_partialgraph_reachable' (p: V -> Prop) n:
  Same_set (reachable_by g n p) (reachable (predicate_partialgraph p) n).
Proof.
  intros.
  rewrite Same_set_spec; intro n'.
  apply reachable_by_eq_partialgraph_reachable.
Qed.

Lemma reachable_by_through_set_eq_subgraph_reachable_through_set (p: V -> Prop):
  forall l n,
    reachable_by_through_set g l p n <-> reachable_through_set (predicate_subgraph p) l n.
Proof.
  intros.
  unfold reachable_by_through_set, reachable_through_set.
  pose proof (fun s => reachable_by_eq_subgraph_reachable p s n).
  firstorder.
Qed.

Lemma reachable_by_through_set_eq_subgraph_reachable_through_set' (p: V -> Prop):
  forall l,
    Same_set (reachable_by_through_set g l p) (reachable_through_set (predicate_subgraph p) l).
Proof.
  intros.
  rewrite Same_set_spec; intro n.
  apply reachable_by_through_set_eq_subgraph_reachable_through_set.
Qed.

Lemma reachable_by_through_set_eq_partialgraph_reachable_through_set (p: V -> Prop):
  forall l n,
    reachable_by_through_set g l p n <-> reachable_through_set (predicate_partialgraph p) l n.
Proof.
  intros.
  unfold reachable_by_through_set, reachable_through_set.
  pose proof (fun s => reachable_by_eq_partialgraph_reachable p s n).
  firstorder.
Qed.

Lemma reachable_by_through_set_eq_partialgraph_reachable_through_set' (p: V -> Prop):
  forall l,
    Same_set (reachable_by_through_set g l p) (reachable_through_set (predicate_partialgraph p) l).
Proof.
  intros.
  rewrite Same_set_spec; intro n.
  apply reachable_by_through_set_eq_partialgraph_reachable_through_set.
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

Context {MA: MathGraph g}.
Context {LF: LocalFiniteGraph g}.

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

Lemma is_tree_ppg_spec: forall (P : V -> Prop) root,
    is_tree (predicate_partialgraph P) root <->
    forall y, g |= root ~o~> y satisfying P ->
              exists ! p, g |= p is root ~o~> y satisfying P.
Proof.
  intros. unfold is_tree. split; intros.
  + rewrite reachable_by_eq_partialgraph_reachable in H0. specialize (H _ H0).
    destruct H as [p [? ?]]. exists p. split; intros.
  - rewrite reachable_by_path_eq_partialgraph_reachable; auto.
  - rewrite reachable_by_path_eq_partialgraph_reachable in H2.
    apply H1; auto.
    + rewrite <- reachable_by_eq_partialgraph_reachable in H0. specialize (H _ H0).
      destruct H as [p [? ?]]. exists p. split; intros.
  - rewrite <- reachable_by_path_eq_partialgraph_reachable; auto.
  - rewrite <- reachable_by_path_eq_partialgraph_reachable in H2.
    apply H1; auto.
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

  Lemma is_partial_graph_valid_path: forall (g1 g2: PreGraph V E) (p: path), is_partial_graph g1 g2 -> valid_path g1 p -> valid_path g2 p.
  Proof.
    intros. destruct p as [v p]. revert v H0. induction p; intros.
    + simpl in H0 |-* . destruct H. apply H; auto.
    + rewrite valid_path_cons_iff in H0. destruct H0 as [? [[? [? ?]] ?]]. rewrite valid_path_cons_iff. destruct H as [? [? [? ?]]].
      assert (src g1 a = src g2 a) by (apply H6; auto). assert (dst g1 a = dst g2 a) by (apply H7; auto). unfold strong_evalid.
      rewrite <- H8. rewrite <- H9. split; auto.
  Qed.

  Lemma is_partial_graph_reachable_by_path: forall (g1 g2: PreGraph V E) (p: path) (n: V) (P: Ensemble V) (n': V),
      is_partial_graph g1 g2 -> g1 |= p is n ~o~> n' satisfying P -> g2 |= p is n ~o~> n' satisfying P.
  Proof.
    intros. destruct H0 as [[? ?] [? ?]]. destruct p as [v p]. split; split; auto.
    + clear H0 H3. revert v H2 H1. induction p; intros.
      - simpl in H1 |-* . auto.
      - rewrite pfoot_cons in H1 |-* . destruct H as [? [? [? ?]]].
        assert (strong_evalid g1 a) by (destruct H2; simpl in H5; destruct p; intuition). destruct H5 as [? [? ?]]. assert (dst g1 a = dst g2 a) by (apply H4; auto).
        rewrite <- H8. apply IHp; auto. apply valid_path_cons in H2. auto.
    + apply is_partial_graph_valid_path with g1; auto.
    + destruct p; simpl in H3 |-* ; auto. unfold path_prop' in H3 |-* . rewrite Forall_forall in H3 |-* . intros. specialize (H3 _ H4).
      destruct H as [? [? [? ?]]]. pose proof (valid_path_strong_evalid _ _ _ _ H2 H4). destruct H8 as [? [? ?]].
      assert (src g1 x = src g2 x) by (apply H6; auto). assert (dst g1 x = dst g2 x) by (apply H7; auto). rewrite <- H11. rewrite <- H12. auto.
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

Lemma ppg_valid_path: forall (g: PreGraph V E) (P: V -> Prop) (p: @path V E), (valid_path g p /\ (forall v, In_path g v p -> P v)) <-> valid_path (predicate_partialgraph g P) p.
Proof.
  intros g P p. destruct p as [v p]. revert v. induction p; intros; split; intros.
  + destruct H. simpl in *. split; auto. apply H0. unfold In_path. left; simpl; auto.
  + simpl in H. destruct H. simpl. split; auto. intros. unfold In_path in H1. simpl in H1.
    destruct H1. 1: subst; auto. destruct H1 as [e [? ?]]. exfalso; auto.
  + destruct H. rewrite valid_path_cons_iff in H |-* . destruct H as [? [? ?]]. split; [|split].
    - simpl. auto.
    - unfold strong_evalid. simpl. unfold predicate_vvalid. unfold predicate_weak_evalid. destruct H1 as [? [? ?]].
      assert (In_path g (src g a) (v, a :: p)) by (right; exists a; split; [apply in_eq | left; auto]). apply H0 in H5.
      assert (In_path g (dst g a) (v, a :: p)) by (right; exists a; split; [apply in_eq | right; auto]). apply H0 in H6. intuition.
    - change (dst (predicate_partialgraph g P) a) with (dst g a). apply IHp. split; auto. intros. apply H0.
      apply (in_path_or_cons _ _ _ p v0) in H. rewrite H. right; auto.
  + rewrite valid_path_cons_iff in H. destruct H as [? [? ?]]. change (dst (predicate_partialgraph g P) a) with (dst g a) in H1. simpl in H.
    rewrite <- IHp in H1. destruct H1. hnf in H0. simpl in H0. unfold predicate_weak_evalid, predicate_vvalid in H0. destruct H0 as [[? _] [[? ?] [? ?]]]. split.
    - rewrite valid_path_cons_iff. unfold strong_evalid. split; auto.
    - intros. pose proof (in_path_or_cons _ _ _ p v0 H). rewrite H8 in H7. clear H8. destruct H7. 1: subst; auto. apply H2; auto.
Qed.

Lemma ppg_reachable_by_path_same: forall (g : PreGraph V E) (P Q: V -> Prop) (p: @path V E) (a b: V),
    ((forall v, In_path g v p -> P v) /\ g |= p is a ~o~> b satisfying Q) <-> (predicate_partialgraph g P) |= p is a ~o~> b satisfying Q.
Proof.
  intros. split; intros.
  + destruct H. destruct H0 as [[? ?] [? ?]]. split; split; auto. 2: rewrite <- ppg_valid_path; split; auto.
    destruct p as [v p]. clear H H0 H2 H3. revert v H1. induction p; intros. 1: simpl in *. auto.
    rewrite pfoot_cons in H1 |-* . change (dst (predicate_partialgraph g P) a0) with (dst g a0). apply IHp. auto.
  + destruct H as [[? ?] [? ?]]. rewrite <- ppg_valid_path in H1. destruct H1. split; auto. split; split; auto.
    clear H H1 H3 H2. destruct p as [v p]. revert v H0. induction p; intros. 1: simpl in *; auto.
    rewrite pfoot_cons in H0 |-* . apply IHp. apply H0.
Qed.

Lemma ppg_reachable_by_path_to: forall (g1 g2 : PreGraph V E) (P Q: V -> Prop) (p: @path V E) (a b: V),
    (predicate_partialgraph g1 P) ~=~ (predicate_partialgraph g2 P) ->
    (forall v, In_path g1 v p -> P v) -> g1 |= p is a ~o~> b satisfying Q -> g2 |= p is a ~o~> b satisfying Q.
Proof.
  intros. assert ((predicate_partialgraph g1 P) |= p is a ~o~> b satisfying Q) by (rewrite <- ppg_reachable_by_path_same; split; auto).
  rewrite (reachable_by_path_si _ _ _ _ _ _ H) in H2. rewrite <- ppg_reachable_by_path_same in H2. destruct H2; auto.
Qed.

Lemma ppg_reachable_by_path_eq: forall (g1 g2 : PreGraph V E) (P Q: V -> Prop) (p: @path V E) (a b: V),
    (predicate_partialgraph g1 P) ~=~ (predicate_partialgraph g2 P) ->
    (forall v, In_path g1 v p -> P v) -> (g1 |= p is a ~o~> b satisfying Q <-> g2 |= p is a ~o~> b satisfying Q).
Proof.
  cut (forall (g1 g2 : PreGraph V E) (P Q: V -> Prop) (p: @path V E) (a b: V),
          (predicate_partialgraph g1 P) ~=~ (predicate_partialgraph g2 P) ->
          (forall v, In_path g2 v p -> P v) -> g1 |= p is a ~o~> b satisfying Q -> g2 |= p is a ~o~> b satisfying Q); intros.
  + split; intro; [apply (H g1 g2 P) | apply (H g2 g1 P)]; auto. 2: symmetry; auto.
    assert (valid_path (predicate_partialgraph g1 P) p) by (rewrite <- ppg_valid_path; split; [destruct H2 as [_ [? _]] |]; auto).
    rewrite (valid_path_si _ _ H0) in H3. rewrite <- ppg_valid_path in H3. destruct H3; auto.
  + destruct H1 as [[? ?] [? ?]]. split; split; auto; clear H1.
Abort.

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

Lemma si_stronger_partialgraph': forall (g1 g2: PreGraph V E) (p1 p2 p1' p2' p: V -> Prop),
  Same_set p1' (Intersection _ p1 p) ->
  Same_set p2' (Intersection _ p2 p) ->
  (predicate_partialgraph g1 p1) ~=~ (predicate_partialgraph g2 p2) ->
  (predicate_partialgraph g1 p1') ~=~ (predicate_partialgraph g2 p2').
Proof.
  intros.
  apply si_stronger_partialgraph with (p := p) (p1 := p1) (p2 := p2); auto.
  - intros.
    rewrite Same_set_spec in H; specialize (H v).
    rewrite Intersection_spec in H; auto.
  - intros.
    rewrite Same_set_spec in H0; specialize (H0 v).
    rewrite Intersection_spec in H0; auto.
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

Lemma si_partialgraph_stronger_trans: forall (g1 g g2: PreGraph V E) (P1 P2 P: V -> Prop),
  Included P P1 ->
  Included P P2 ->
  (predicate_partialgraph g1 P1) ~=~ (predicate_partialgraph g P1) ->
  (predicate_partialgraph g P2) ~=~ (predicate_partialgraph g2 P2) ->
  (predicate_partialgraph g1 P) ~=~ (predicate_partialgraph g2 P).
Proof.
  intros.
  transitivity (predicate_partialgraph g P).
  + apply si_stronger_partialgraph_simple with P1; auto.
  + apply si_stronger_partialgraph_simple with P2; auto.
Qed.

Instance subgraph_proper: Proper (structurally_identical ==> @Same_set V ==> structurally_identical) predicate_subgraph.
Proof.
  do 2 (hnf; intros).
  destruct H as [? [? [? ?]]].
  rewrite Same_set_spec in H0; hnf in H0.
  split; [| split; [| split]]; intros; simpl.
  + unfold predicate_vvalid.
    rewrite H0, H.
    reflexivity.
  + unfold predicate_evalid. rewrite !H0, !H1. specialize (H1 e).
    split; intros; destruct H4 as [? [? ?]]; [rewrite <- H2, <- H3 | rewrite H2, H3]; tauto.
  + simpl in * |- . unfold predicate_evalid in * |- . apply H2; tauto.
  + simpl in * |- . unfold predicate_evalid in * |- . apply H3; tauto.
Defined.

Global Existing Instance subgraph_proper.

Instance partialgraph_proper: Proper (structurally_identical ==> @Same_set V ==> structurally_identical) predicate_partialgraph.
Proof.
  do 2 (hnf; intros).
  destruct H as [? [? [? ?]]].
  rewrite Same_set_spec in H0; hnf in H0.
  split; [| split; [| split]]; intros; simpl.
  + unfold predicate_vvalid.
    rewrite H0, H.
    reflexivity.
  + unfold predicate_weak_evalid. rewrite !H0, !H1. specialize (H1 e).
    split; intro; intuition; [rewrite <- H2 | rewrite H2]; auto.
  + simpl in * |- . unfold predicate_weak_evalid in * |- . apply H2; tauto.
  + simpl in * |- . unfold predicate_weak_evalid in * |- . apply H3; tauto.
Defined.

Global Existing Instance partialgraph_proper.

Instance reachable_by_proper: Proper ((@structurally_identical V E _ _) ==> (@eq V) ==> @Same_set V ==> (@eq V) ==> iff) (@reachable_by V E _ _).
Proof.
  intros.
  do 4 (hnf; intros); subst.
  rewrite !reachable_by_eq_partialgraph_reachable.
  rewrite H, H1.
  reflexivity.
Defined.
Global Existing Instance reachable_by_proper.

Instance reachable_by_proper': Proper ((@structurally_identical V E _ _) ==> (@eq V) ==> @Same_set V ==> @Same_set V) (@reachable_by V E _ _).
Proof.
  intros.
  do 3 (hnf; intros); subst.
  rewrite Same_set_spec; hnf; intros.
  rewrite !reachable_by_eq_partialgraph_reachable.
  rewrite H, H1.
  reflexivity.
Defined.
Global Existing Instance reachable_by_proper'.

Instance reachable_by_through_set_proper: Proper ((@structurally_identical V E _ _) ==> eq ==> @Same_set V ==> (@eq V) ==> iff) (@reachable_by_through_set V E _ _).
Proof.
  intros.
  do 4 (hnf; intros); subst.
  rewrite !reachable_by_through_set_eq_partialgraph_reachable_through_set.
  rewrite H, H1.
  reflexivity.
Defined.
Global Existing Instance reachable_by_through_set_proper.

Instance reachable_by_through_set_proper': Proper ((@structurally_identical V E _ _) ==> eq ==> @Same_set V ==> @Same_set V) (@reachable_by_through_set V E _ _).
Proof.
  intros.
  do 3 (hnf; intros); subst.
  rewrite Same_set_spec; hnf; intros.
  rewrite !reachable_by_through_set_eq_partialgraph_reachable_through_set.
  rewrite H, H1.
  reflexivity.
Defined.
Global Existing Instance reachable_by_through_set_proper'.

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
  Same_set (reachable g n) (reachable (predicate_partialgraph g P) n).
Proof.
  intros.
  rewrite Same_set_spec.
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
  Same_set (reachable_by g n p0) (reachable_by (predicate_partialgraph g P) n p0).
Proof.
  intros.
  assert (Same_set (reachable_by g n p0) (reachable (predicate_partialgraph g p0) n)).
  Focus 1. {
    rewrite Same_set_spec.
    hnf; intros.
    apply reachable_by_eq_partialgraph_reachable; auto.
  } Unfocus.
  rewrite H0 in H |- *.
  apply reachable_partialgraph_reachable_equiv in H.
  rewrite H.
  rewrite partial_partialgraph, Intersection_comm, <- partial_partialgraph.
  rewrite Same_set_spec; hnf; intros.
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

Lemma step_list_partialgraph: forall  (g: PreGraph V E) n l (P: Ensemble V),
  vvalid g n ->
  P n ->
  step_list g n l ->
  step_list (predicate_partialgraph g P) n l.
Proof.
  intros.
  intro m; specialize (H1 m).
  rewrite H1; clear H1.
  split.
  + intros; apply partialgraph_step; auto.
  + intro.
    inv H1; simpl in *.
    econstructor.
    - destruct H2; eauto.
    - reflexivity.
    - reflexivity.
Qed.

Lemma reachable_by_through_app_strong: forall (g: PreGraph V E) P l1 l2,
  (forall n, reachable_by_through_set g l1 P n \/ ~ reachable_by_through_set g l1 P n) ->
  (forall n, reachable_by_through_set g (l1 ++ l2) P n <-> reachable_by_through_set g l1 P n \/ reachable_by_through_set (predicate_partialgraph g (Complement _ (reachable_by_through_set g l1 P))) l2 P n).
Proof.
  intros.
  rewrite reachable_by_through_app.
  destruct (H n); [tauto |].
  apply or_iff_compat_l.
  split; intros.
  + destruct H1 as [m [? ?]].
    exists m; split; auto.
    assert (forall m, g |= m ~o~> n satisfying P -> ~ reachable_by_through_set g l1 P m).
    Focus 1. {
      intros m0 ? [s [? ?]].
      apply H0; exists s.
      split; auto.
      apply reachable_by_trans with m0; auto.
    } Unfocus.
    rewrite reachable_by_eq_partialgraph_reachable in H2 |- *.
    rewrite partial_partialgraph.
    clear H1.
    rewrite reachable_ind_reachable in H2.
    induction H2.
    - destruct (H x); [tauto |].
      apply reachable_refl.
      simpl.
      split; [destruct H1; auto |].
      rewrite Intersection_spec.
      split; [auto | destruct H1; auto].
    - assert (Complement V (reachable_by_through_set g l1 P) x).
      Focus 1. {
        apply H3.
        rewrite reachable_by_eq_partialgraph_reachable, reachable_ind_reachable.
        apply ind.reachable_cons with y; auto.
      } Unfocus.
      assert (vvalid (predicate_partialgraph g
       (Intersection V (Complement V (reachable_by_through_set g l1 P)) P)) x).
      Focus 1. {
        split; [destruct H1 as [[? _] _]; auto |].
        rewrite Intersection_spec.
        split; [auto | destruct H1 as [[_ ?] _]; auto].
      } Unfocus.
      assert ((predicate_partialgraph g
        (Intersection V (Complement V (reachable_by_through_set g l1 P)) P)) ~=~
           (predicate_partialgraph
        (predicate_partialgraph g P)
           (Complement V (reachable_by_through_set g l1 P))))
        by (rewrite Intersection_comm, partial_partialgraph; reflexivity).
      apply step_reachable with y; [| auto | auto].
      rewrite (step_si _ _ _ _ H6).
      apply partialgraph_step; [destruct H1 as [? [? ?]]; auto | auto].
  + destruct H1 as [s [? ?]]; exists s; split; auto.
    rewrite reachable_by_eq_partialgraph_reachable in H2 |- *.
    rewrite partial_partialgraph, Intersection_comm, <- partial_partialgraph, <- reachable_by_eq_partialgraph_reachable in H2.
    apply reachable_by_is_reachable in H2; auto.
Qed.

Lemma reachable_by_through_app_strong': forall (g: PreGraph V E) P l1 l2,
  Same_set
   (Union _ (reachable_by_through_set g l1 P) (Complement _ (reachable_by_through_set g l1 P))) (Full_set _) ->
  Same_set
   (reachable_by_through_set g (l1 ++ l2) P)
   (Union _
     (reachable_by_through_set g l1 P)
     (reachable_by_through_set g l2 (Intersection _ P (Complement _ (reachable_by_through_set g l1 P))))).
Proof.
  intros.
  rewrite Same_set_spec.
  intros n.
  rewrite Union_spec.
  rewrite (reachable_by_through_set_eq_partialgraph_reachable_through_set _ _ l2), Intersection_comm, <- partial_partialgraph, <- reachable_by_through_set_eq_partialgraph_reachable_through_set.
  apply reachable_by_through_app_strong.
  clear n; intro n.
  rewrite Same_set_spec in H; specialize (H n).
  rewrite Union_spec in H.
  pose proof Full_set_spec _ n.
  unfold Complement, Ensembles.In in H.
  tauto.
Qed.

Lemma reachable_by_through_app_join: forall (g: PreGraph V E) P l1 l2,
  (forall n, reachable_by_through_set g l1 P n \/ ~ reachable_by_through_set g l1 P n) ->
  Prop_join
   (reachable_by_through_set g l1 P)
   (reachable_by_through_set (predicate_partialgraph g (Complement _ (reachable_by_through_set g l1 P))) l2 P)
   (reachable_by_through_set g (l1 ++ l2) P).
Proof.
  intros.
  split; [apply reachable_by_through_app_strong; auto |].
  intros.
  destruct H0 as [s [? ?]], H1 as [? [? ?]].
  rewrite reachable_by_eq_partialgraph_reachable, partial_partialgraph, Intersection_comm, <- partial_partialgraph, <- reachable_by_eq_partialgraph_reachable in H3.
  apply reachable_by_foot_prop in H3.
  apply H3; exists s; auto.
Qed.

Lemma Complement_reachable_by_through_app_strong: forall (g: PreGraph V E) P l1 l2,
  Same_set 
   (Complement _ (reachable_by_through_set g (l1 ++ l2) P))
   (Intersection _
     (Complement _ (reachable_by_through_set g l1 P)) 
     (Complement _ (reachable_by_through_set (predicate_partialgraph g (Complement _ (reachable_by_through_set g l1 P))) l2 P))).
Proof.
  intros.
  rewrite Same_set_spec; intro n.
  rewrite Intersection_spec; unfold Complement, Ensembles.In.
  rewrite reachable_by_through_app.
  split; intros.
  + split; [tauto |].
    rewrite reachable_by_through_set_eq_partialgraph_reachable_through_set, partial_partialgraph, Intersection_comm, <- partial_partialgraph, <- reachable_by_through_set_eq_partialgraph_reachable_through_set.
    intro.
    apply reachable_by_through_set_is_reachable_through_set in H0.
    rewrite <- reachable_by_through_set_eq_partialgraph_reachable_through_set in H0.
    tauto.
  + destruct H.
    intros [? | ?]; [tauto |].
    apply H0; clear H0.
    rewrite reachable_by_through_set_eq_partialgraph_reachable_through_set in H, H1 |- *.
    rewrite partial_partialgraph, Intersection_comm, <- partial_partialgraph, <- reachable_by_through_set_eq_partialgraph_reachable_through_set.
    assert (Same_set (fun x : V => ~ reachable_by_through_set g l1 P x)
      (Complement _ (reachable_through_set (predicate_partialgraph g P) l1))).
    Focus 1. {
      rewrite Same_set_spec; intro v.
      pose proof reachable_by_through_set_eq_partialgraph_reachable_through_set g P l1 v.
      unfold Complement, Ensembles.In; tauto.
    } Unfocus.
    rewrite H0; clear H0.
    remember (predicate_partialgraph g P) as g'.
    clear g Heqg'.
    apply edge_preserved_rev_foot0; auto.
    intros; eapply reachable_through_set_reachable; eauto.
Qed.

End SI_EQUIV.

Section PartialLabeledGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE: Type}.

Notation Graph := (LabeledGraph V E DV DE).

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition gpredicate_sub_labeledgraph (PV: V -> Prop) (PE: E -> Prop) (g: Graph): Graph :=
  Build_LabeledGraph _ _ (gpredicate_subgraph PV PE g) (vlabel g) (elabel g).

Definition predicate_sub_labeledgraph (g: Graph) (p: V -> Prop) :=
  Build_LabeledGraph _ _ (predicate_subgraph g p) (vlabel g) (elabel g).

Definition predicate_partial_labeledgraph (g: Graph) (p: V -> Prop) :=
  Build_LabeledGraph _ _ (predicate_partialgraph g p) (vlabel g) (elabel g).

Lemma si_stronger_partial_labeledgraph: forall (g1 g2: Graph) (p1 p2 p1' p2' p: V -> Prop),
  (forall v, p1' v <-> p1 v /\ p v) ->
  (forall v, p2' v <-> p2 v /\ p v) ->
  (predicate_partial_labeledgraph g1 p1) ~=~ (predicate_partial_labeledgraph g2 p2)%LabeledGraph ->
  (predicate_partial_labeledgraph g1 p1') ~=~ (predicate_partial_labeledgraph g2 p2')%LabeledGraph.
Proof.
  intros.
  split; [| split].
  + eapply si_stronger_partialgraph; eauto.
    destruct H1 as [? _].
    auto.
  + simpl.
    intros ? [? ?] [? ?].
    destruct H1 as [_ [? _]].
    specialize (H1 v); simpl in H1.
    firstorder.
  + simpl.
    intros ? [? ?] [? ?].
    destruct H1 as [_ [_ ?]].
    specialize (H1 e); simpl in H1.
    firstorder.
Qed.

Lemma si_stronger_partial_labeledgraph_simple: forall (g1 g2: Graph) (p p': V -> Prop),
  Included p' p ->
  (predicate_partial_labeledgraph g1 p) ~=~ (predicate_partial_labeledgraph g2 p)%LabeledGraph ->
  (predicate_partial_labeledgraph g1 p') ~=~ (predicate_partial_labeledgraph g2 p')%LabeledGraph.
Proof.
  intros.
  eapply si_stronger_partial_labeledgraph with (p := p'); [| | exact H0].
  + intro v; specialize (H v); simpl in H; tauto.
  + intro v; specialize (H v); simpl in H; tauto.
Qed.

End PartialLabeledGraph.

Section GuardedIdentical.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE: Type}.

Notation PGraph := (PreGraph V E).
Notation LGraph := (LabeledGraph V E DV DE).

Definition guarded_structurally_identical PV PE: relation PGraph := respectful_relation (gpredicate_subgraph PV PE) structurally_identical.

Definition guarded_labeled_graph_equiv PV PE: relation LGraph := respectful_relation (gpredicate_sub_labeledgraph PV PE) labeled_graph_equiv.

Instance guarded_si_Equivalence PV PE: Equivalence (guarded_structurally_identical PV PE).
Proof.
  apply resp_Equivalence.
  apply si_Equiv.
Qed.
Global Existing Instance guarded_si_Equivalence.

Instance guarded_lge_Equivalence PV PE: Equivalence (guarded_labeled_graph_equiv PV PE).
Proof.
  apply resp_Equivalence.
  apply lge_Equiv.
Qed.
Global Existing Instance guarded_lge_Equivalence.

Lemma guarded_si_spec: forall PV PE (G1 G2: PGraph),
  guarded_structurally_identical PV PE G1 G2 <->
  ((forall v, PV v -> (vvalid G1 v <-> vvalid G2 v)) /\
   (forall e, PE e -> (evalid G1 e <-> evalid G2 e)) /\
   (forall e, PE e -> evalid G1 e -> evalid G2 e -> src G1 e = src G2 e) /\
   (forall e, PE e -> evalid G1 e -> evalid G2 e -> dst G1 e = dst G2 e)).
Proof.
  intros.
  split; intros; (destruct H as [? [? [? ?]]]; split; [| split; [| split]]); intros.
  + specialize (H v); simpl in H.
    rewrite !Intersection_spec in H.
    tauto.
  + specialize (H0 e); simpl in H0.
    rewrite !Intersection_spec in H0.
    tauto.
  + apply H1; simpl; rewrite !Intersection_spec; auto.
  + apply H2; simpl; rewrite !Intersection_spec; auto.
  + specialize (H v); simpl.
    rewrite !Intersection_spec.
    tauto.
  + specialize (H0 e); simpl.
    rewrite !Intersection_spec.
    tauto.
  + apply H1; simpl in H3, H4; rewrite !Intersection_spec in H3, H4; tauto.
  + apply H2; simpl in H3, H4; rewrite !Intersection_spec in H3, H4; tauto.
Qed.

Lemma guarded_si_dst1: forall PV PE (G1 G2: PGraph),
  guarded_structurally_identical PV PE G1 G2 ->
  forall e, PE e -> evalid G1 e -> dst G1 e = dst G2 e.
Proof.
  intros.
  rewrite guarded_si_spec in H.
  apply (proj2 (proj2 (proj2 H))); auto.
  rewrite <- (proj1 (proj2 H)); auto.
Qed.

Instance guarded_si_proper: Proper (@Same_set V ==> @Same_set E ==> eq ==> eq ==> iff) guarded_structurally_identical.
Proof.
  intros.
  hnf; intros PV1 PV2 ?.
  hnf; intros PE1 PE2 ?.
  hnf; intros g1 g1' ?; subst g1'.
  hnf; intros g2 g2' ?; subst g2'.
  rewrite !guarded_si_spec.
  rewrite Same_set_spec in *.
  unfold pointwise_relation in *.
  firstorder.
Defined.
Global Existing Instance guarded_si_proper.

Lemma si_is_guarded_si:
  same_relation PGraph structurally_identical (guarded_structurally_identical (Full_set _) (Full_set _)).
Proof.
  intros.
  rewrite same_relation_spec.
  hnf; intros g1.
  hnf; intros g2.
  rewrite guarded_si_spec.
  unfold structurally_identical.
  pose proof Full_set_spec V.
  pose proof Full_set_spec E.
  firstorder.
Qed.

Lemma guarded_si_weaken: forall (PV1 PV2: V -> Prop) (PE1 PE2: E -> Prop),
  Included PV2 PV1 ->
  Included PE2 PE1 ->
  inclusion PGraph (guarded_structurally_identical PV1 PE1) (guarded_structurally_identical PV2 PE2).
Proof.
  intros.
  hnf; intros.
  rewrite guarded_si_spec in H1 |- *.
  unfold Included, Ensembles.In in H, H0.
  firstorder.
Qed.

Lemma si_guarded_si: forall PV PE,
  inclusion PGraph structurally_identical (guarded_structurally_identical PV PE).
Proof.
  intros.
  rewrite si_is_guarded_si.
  apply guarded_si_weaken; apply Included_Full_set.
Qed.

Lemma guarded_si_strong_trans: forall (PV1 PV2 PV: V -> Prop) (PE1 PE2 PE: E -> Prop) g1 g2 g3,
  Included PV PV1 ->
  Included PV PV2 ->
  Included PE PE1 ->
  Included PE PE2 ->
  guarded_structurally_identical PV1 PE1 g1 g2 ->
  guarded_structurally_identical PV2 PE2 g2 g3 ->
  guarded_structurally_identical PV PE g1 g3.
Proof.
  intros.
  transitivity g2.
  + eapply guarded_si_weaken; [| | eauto]; eauto.
  + eapply guarded_si_weaken; [| | eauto]; eauto.
Qed.

Lemma guarded_si_strong_trans': forall (PV1 PV2 PV: V -> Prop) (PE1 PE2 PE: E -> Prop) g1 g2 g3,
  Included PV1 PV ->
  Included PV2 PV ->
  Included PE1 PE ->
  Included PE2 PE ->
  guarded_structurally_identical (Complement _ PV1) (Complement _ PE1) g1 g2 ->
  guarded_structurally_identical (Complement _ PV2) (Complement _ PE2) g2 g3 ->
  guarded_structurally_identical (Complement _ PV ) (Complement _ PE ) g1 g3.
Proof.
  intros.
  eapply guarded_si_strong_trans.
  + apply Complement_Included_rev, H.
  + apply Complement_Included_rev, H0.
  + apply Complement_Included_rev, H1.
  + apply Complement_Included_rev, H2.
  + eauto.
  + eauto.
Qed.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Lemma guarded_lge_spec: forall PV PE (G1 G2: LGraph),
  guarded_labeled_graph_equiv PV PE G1 G2 <->
  (((forall v, PV v -> (vvalid G1 v <-> vvalid G2 v)) /\
    (forall e, PE e -> (evalid G1 e <-> evalid G2 e)) /\
    (forall e, PE e -> evalid G1 e -> evalid G2 e -> src G1 e = src G2 e) /\
    (forall e, PE e -> evalid G1 e -> evalid G2 e -> dst G1 e = dst G2 e)) /\
   (forall v, PV v -> vvalid G1 v -> vvalid G2 v -> vlabel G1 v = vlabel G2 v) /\
   (forall e, PE e -> evalid G1 e -> evalid G2 e -> elabel G1 e = elabel G2 e)).
Proof.
  split; intros; (destruct H as [[? [? [? ?]]] [? ?]]; split; [split; [| split; [| split]] | split]); intros.
  + specialize (H v); simpl in H.
    rewrite !Intersection_spec in H.
    tauto.
  + specialize (H0 e); simpl in H0.
    rewrite !Intersection_spec in H0.
    tauto.
  + apply H1; simpl; rewrite !Intersection_spec; auto.
  + apply H2; simpl; rewrite !Intersection_spec; auto.
Admitted.
(*
  + specialize (H v); simpl.
    rewrite !Intersection_spec.
    tauto.
  + specialize (H0 e); simpl.
    rewrite !Intersection_spec.
    tauto.
  + apply H1; simpl in H3, H4; rewrite !Intersection_spec in H3, H4; tauto.
  + apply H2; simpl in H3, H4; rewrite !Intersection_spec in H3, H4; tauto.
Qed.
*)

End GuardedIdentical.

Section ExpandPartialGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Notation Graph := (PreGraph V E).

Definition vertex_join (PV: V -> Prop) (G1 G2: Graph) : Prop :=
  Prop_join (vvalid G1) PV (vvalid G2) /\
  (forall e : E, evalid G1 e <-> evalid G2 e /\ ~ PV (src G2 e)) /\
  (forall e : E, evalid G1 e -> evalid G2 e -> src G1 e = src G2 e) /\
  (forall e : E, evalid G1 e -> evalid G2 e -> dst G1 e = dst G2 e).

Definition edge_union (PE: E -> Prop) (G1 G2: Graph) : Prop :=
  (forall v : V, (vvalid G1 v <-> vvalid G2 v)) /\
  (forall e : E, (evalid G1 e \/ PE e <-> evalid G2 e)) /\
  (forall e : E, evalid G1 e -> evalid G2 e -> src G1 e = src G2 e) /\
  (forall e : E, evalid G1 e -> evalid G2 e -> dst G1 e = dst G2 e).

Definition pregraph_join (PV: V -> Prop) (PE: E -> Prop) (G1 G2: Graph) : Prop :=
  Prop_join (vvalid G1) PV (vvalid G2) /\
  Prop_join (evalid G1) PE (evalid G2) /\
  (forall e : E, evalid G1 e -> evalid G2 e -> src G1 e = src G2 e) /\
  (forall e : E, evalid G1 e -> evalid G2 e -> dst G1 e = dst G2 e).

(*
Definition pregraph_join2 (G1 G2 G: Graph) : Prop :=
  Prop_join (vvalid G1) (vvalid G2) (vvalid G) /\
  Prop_join (evalid G1) (evalid G2) (evalid G) /\
  (forall e : E, evalid G1 e -> src G1 e = src G e) /\
  (forall e : E, evalid G2 e -> src G2 e = src G e) /\
  (forall e : E, evalid G1 e -> dst G1 e = dst G e) /\
  (forall e : E, evalid G2 e -> dst G2 e = dst G e).
*)

Lemma pregraph_join_proper_aux: forall (PV1 PV2: V -> Prop) (PE1 PE2: E -> Prop) (G11 G12 G21 G22: Graph),
  Same_set PV1 PV2 ->
  Same_set PE1 PE2 ->
  G11 ~=~ G12 ->
  G21 ~=~ G22 ->
  pregraph_join PV1 PE1 G11 G21 ->
  pregraph_join PV2 PE2 G12 G22.
Proof.
  intros.
  split; [| split; [| split]]; intros.
  + eapply Prop_join_proper; [.. | apply (proj1 H3)]; symmetry; auto.
    - rewrite Same_set_spec; destruct H1; auto.
    - rewrite Same_set_spec; destruct H2; auto.
  + eapply Prop_join_proper; [.. | apply (proj1 (proj2 H3))]; symmetry; auto.
    - rewrite Same_set_spec; destruct H1 as [_ [? _]]; auto.
    - rewrite Same_set_spec; destruct H2 as [_ [? _]]; auto.
  + assert (evalid G11 e) by (rewrite (proj1 (proj2 H1)); auto).
    assert (evalid G21 e) by (rewrite (proj1 (proj2 H2)); auto).
    rewrite <- (proj1 (proj2 (proj2 H1))) by auto.
    rewrite <- (proj1 (proj2 (proj2 H2))) by auto.
    apply (proj1 (proj2 (proj2 H3))); auto.
  + assert (evalid G11 e) by (rewrite (proj1 (proj2 H1)); auto).
    assert (evalid G21 e) by (rewrite (proj1 (proj2 H2)); auto).
    rewrite <- (proj2 (proj2 (proj2 H1))) by auto.
    rewrite <- (proj2 (proj2 (proj2 H2))) by auto.
    apply (proj2 (proj2 (proj2 H3))); auto.
Qed.

Instance pregraph_join_proper: Proper (Same_set ==> Same_set ==> structurally_identical ==> structurally_identical ==> iff) pregraph_join.
Proof.
  do 4 (hnf; intros).
  split; apply pregraph_join_proper_aux; auto; symmetry; auto.
Qed.
Global Existing Instance pregraph_join_proper.

Lemma edge_union_proper_aux: forall (PE1 PE2: E -> Prop) (G11 G12 G21 G22: Graph),
  Same_set PE1 PE2 ->
  G11 ~=~ G12 ->
  G21 ~=~ G22 ->
  edge_union PE1 G11 G21 ->
  edge_union PE2 G12 G22.
Proof.
  intros.
  split; [| split; [| split]]; intros.
  + destruct H0, H1; firstorder.
  + destruct H2 as [_ [? _]].
    rewrite Same_set_spec in H; unfold pointwise_relation in H.
    destruct H0 as [_ [? _]], H1 as [_ [? _]]; firstorder.
  + assert (evalid G11 e) by (rewrite (proj1 (proj2 H0)); auto).
    assert (evalid G21 e) by (rewrite (proj1 (proj2 H1)); auto).
    rewrite <- (proj1 (proj2 (proj2 H0))) by auto.
    rewrite <- (proj1 (proj2 (proj2 H1))) by auto.
    apply (proj1 (proj2 (proj2 H2))); auto.
  + assert (evalid G11 e) by (rewrite (proj1 (proj2 H0)); auto).
    assert (evalid G21 e) by (rewrite (proj1 (proj2 H1)); auto).
    rewrite <- (proj2 (proj2 (proj2 H0))) by auto.
    rewrite <- (proj2 (proj2 (proj2 H1))) by auto.
    apply (proj2 (proj2 (proj2 H2))); auto.
Qed.

Instance edge_union_proper: Proper (Same_set ==> structurally_identical ==> structurally_identical ==> iff) edge_union.
Proof.
  do 3 (hnf; intros).
  split; apply edge_union_proper_aux; auto; symmetry; auto.
Qed.
Global Existing Instance edge_union_proper.

Lemma vertex_join_guarded_si: forall (PV: V -> Prop) (G1 G2: Graph),
  vertex_join PV G1 G2 ->
  guarded_structurally_identical (Complement _ PV) (Complement _ (weak_edge_prop PV G2)) G1 G2.
Proof.
  intros.
  rewrite guarded_si_spec.
  destruct H as [[? ?] [? [? ?]]].
  unfold Complement, Ensembles.In, weak_edge_prop.
  split; [| split; [| split]]; firstorder.
Qed.

Lemma vertex_join_DisjointV: forall (PV: V -> Prop) (G1 G2: Graph),
  vertex_join PV G1 G2 ->
  Disjoint V (vvalid G1) PV.
Proof.
  intros.
  rewrite Disjoint_spec.
  destruct H as [[? ?] _].
  auto.
Qed.

Lemma vertex_join_DisjointE: forall (PV: V -> Prop) (G1 G2: Graph),
  vertex_join PV G1 G2 ->
  Disjoint E (evalid G1) (weak_edge_prop PV G2).
Proof.
  intros.
  rewrite Disjoint_spec.
  unfold weak_edge_prop.
  destruct H as [_ [? _]].
  firstorder.
Qed.

Lemma pregraph_join_guarded_si: forall PV PE (G1 G2: Graph),
  pregraph_join PV PE G1 G2 ->
  guarded_structurally_identical (Complement _ PV) (Complement _ PE) G1 G2.
Proof.
  intros.
  rewrite guarded_si_spec.
  destruct H as [[? ?] [? [? ?]]].
  unfold Complement, Ensembles.In, weak_edge_prop.
  split; [| split; [| split]]; firstorder.
Qed.

Lemma pregraph_join_partial_si: forall PV PE (G1 G2: Graph) PV1,
  pregraph_join PV PE G1 G2 ->
  Disjoint _ PV PV1 ->
  (forall e, PE e -> evalid G2 e -> PV1 (src G2 e) -> False) ->
  (predicate_partialgraph G1 PV1) ~=~ (predicate_partialgraph G2 PV1).
Proof.
  intros.
  destruct H as [[? ?] [[? ?] [? ?]]].
  unfold Complement, Ensembles.In, weak_edge_prop.
  split; [| split; [| split]].
  + simpl; intros.
    unfold predicate_vvalid.
    rewrite H.
    rewrite Disjoint_spec in H0; specialize (H0 v).
    tauto.
  + simpl; intros.
    unfold predicate_weak_evalid.
    split; intros.
    - assert (evalid G2 e) by (rewrite H3; tauto).
      rewrite <- H5 by tauto.
      tauto.
    - pose proof proj1 H7.
      rewrite H3 in H8; destruct H8.
      * rewrite H5 by tauto.
        tauto.
      * exfalso; apply (H1 e); tauto.
  + simpl; unfold predicate_weak_evalid; intros.
    apply H5; tauto.
  + simpl; unfold predicate_weak_evalid; intros.
    apply H6; tauto.
Qed.    

Lemma edge_union_guarded_si: forall (PE: E -> Prop) (G1 G2: Graph),
  edge_union PE G1 G2 ->
  guarded_structurally_identical (Full_set _) (Complement _ PE) G1 G2.
Proof.
  intros.
  rewrite guarded_si_spec.
  destruct H as [? [? [? ?]]].
  unfold Complement, Ensembles.In, weak_edge_prop.
  pose proof Full_set_spec V.
  split; [| split; [| split]]; firstorder.
Qed.

Lemma edge_union_Empty: forall (G: Graph), edge_union (Empty_set _) G G.
Proof.
  intros.
  split; [| split; [| split]]; auto.
  + intros; reflexivity.
  + intros.
    pose proof Empty_set_iff E e.
    tauto.
Qed.

Lemma pregraph_join_Empty: forall (G: Graph),pregraph_join (Empty_set _) (Empty_set _) G G.
Proof.
  intros.
  split; [| split; [| split]]; auto.
  + pose proof Empty_set_iff V.
    split; firstorder.
  + pose proof Empty_set_iff E.
    split; firstorder.
Qed.

Definition remove_pregraph (G: Graph) (PV: V -> Prop) (PE: E -> Prop) : Graph :=
  Build_PreGraph _ _
   (fun v => vvalid G v /\ ~ PV v)
   (fun e => evalid G e /\ ~ PE e)
   (src G)
   (dst G).

Lemma vertex_join_is_pregraph_join: forall G1 G2 PV,
  (forall v, PV v \/ ~ PV v) ->
  (vertex_join PV G1 G2 <-> pregraph_join PV (Intersection _ (weak_edge_prop PV G2) (evalid G2)) G1 G2).
Proof.
  intros.
  unfold vertex_join, pregraph_join.
  split; (split; [| split; [| split]]); try tauto.
  + destruct H0 as [_ [? _]].
    split; intro e; intros.
    - rewrite Intersection_spec.
      unfold weak_edge_prop.
      rewrite H0.
      specialize (H (src G2 e)).
      tauto.
    - rewrite H0 in H1.
      rewrite Intersection_spec in H2.
      unfold weak_edge_prop in H2.
      tauto.
  + destruct H0 as [_ [? _]].
    destruct H0.
    intro e.
    specialize (H0 e); specialize (H1 e).
    rewrite Intersection_spec in H0, H1.
    unfold weak_edge_prop in H0,H1.
    specialize (H (src G2 e)).
    tauto.
Qed.

Lemma remove_pregraph_pregraph_join: forall G PV PE,
  (forall v, PV v \/ ~ PV v) ->
  (forall e, PE e \/ ~ PE e) ->
  Included PV (vvalid G) ->
  Included PE (evalid G) ->
  pregraph_join PV PE (remove_pregraph G PV PE) G.
Proof.
  intros.
  unfold remove_pregraph.
  split; [| split; [| split]]; simpl.
  + split; intro v.
    - specialize (H v); specialize (H1 v).
      tauto.
    - tauto.
  + split; intro e.
    - specialize (H0 e); specialize (H2 e).
      tauto.
    - tauto.
  + intros; auto.
  + intros; auto.
Qed.

Lemma id_edge_union: forall G PE,
  Included PE (evalid G) ->
  edge_union PE G G.
Proof.
  intros.
  split; [| split; [| split]]; intros; try tauto.
  specialize (H e).
  tauto.
Qed.

Lemma pregraph_join_pregraph_join: forall G1 G2 G3 PV PE PV' PE',
  pregraph_join PV PE G1 G2 ->
  pregraph_join PV' PE' G2 G3 ->
  pregraph_join (Union _ PV PV') (Union _ PE PE') G1 G3.
Proof.
  unfold pregraph_join.
  intros.
  destruct H as [? [? [? ?]]], H0 as [? [? [? ?]]].
  split; [| split; [| split]]; intros.
  + apply Prop_join_assoc with (P2 := vvalid G2); auto.
  + apply Prop_join_assoc with (P2 := evalid G2); auto.
  + assert (evalid G2 e) by (destruct H4; firstorder).
    rewrite H2, H5; auto.
  + assert (evalid G2 e) by (destruct H4; firstorder).
    rewrite H3, H6; auto.
Qed.

Lemma edge_union_edge_union: forall G1 G2 G3 PE PE',
  edge_union PE G1 G2 ->
  edge_union PE' G2 G3 ->
  edge_union (Union _ PE PE') G1 G3.
Proof.
  unfold edge_union.
  intros.
  destruct H as [? [? [? ?]]], H0 as [? [? [? ?]]].
  split; [| split; [| split]]; intros.
  + firstorder.
  + rewrite Union_spec, <- H4, <- H1.
    tauto.
  + assert (evalid G2 e) by (rewrite <- H1; firstorder).
    rewrite H2, H5; auto.
  + assert (evalid G2 e) by (rewrite <- H1; firstorder).
    rewrite H3, H6; auto.
Qed.

Lemma pregraph_join_edge_union: forall G1 G2 G3 PV (PE PE': E -> Prop),
  (forall e, evalid G1 e -> PE' e -> False) ->
  pregraph_join PV PE G1 G2 ->
  edge_union PE' G2 G3 ->
  pregraph_join PV (Union _ PE PE') G1 G3.
Proof.
  intros.
  destruct H1 as [? [? [? ?]]], H0 as [? [? [? ?]]].
  split; [| split; [| split]]; intros.
  + clear - H0 H1.
    destruct H0; split; firstorder.
  + clear - H H5 H2.
    pose proof (fun e => Union_spec E e PE PE').
    destruct H5; split; firstorder.
  + assert (evalid G2 e) by (rewrite (proj1 H5); auto).
    rewrite H6, H3; auto.
  + assert (evalid G2 e) by (rewrite (proj1 H5); auto).
    rewrite H7, H4; auto.
Qed.

Lemma edge_union_pregraph_join: forall G1 G3 PV PE PE',
  relation_list (edge_union PE' :: pregraph_join PV PE :: nil) G1 G3 ->
  relation_list (pregraph_join PV PE :: edge_union PE' :: nil) G1 G3.
Proof.
  intros.
  destruct_relation_list G2 in H.
  destruct H as [? [? [? ?]]], H0 as [? [? [? ?]]].
  split_relation_list (gpredicate_subgraph (Full_set _) (Union _ (evalid G1) PE) G3 :: nil);
  unfold remove_pregraph;
  (split; [| split; [| split]]); simpl; auto.
  + rewrite Intersection_Full_right.
    apply Same_set_spec in H0.
    rewrite H0.
    auto.
  + clear - H4 H1.
    destruct H1.
    split.
    - intro e.
      rewrite Intersection_spec, Union_spec.
      firstorder.
    - firstorder.
  + intros.
    rewrite Intersection_spec, Union_spec in H8.
    destruct H8 as [? _].
    assert (evalid G2 e) by firstorder.
    rewrite H5, H2; auto.
  + intros.
    rewrite Intersection_spec, Union_spec in H8.
    destruct H8 as [? _].
    assert (evalid G2 e) by firstorder.
    rewrite H6, H3; auto.
  + intros.
    rewrite (Intersection_Full_right _ v).
    tauto.
  + intros.
    rewrite Intersection_spec, Union_spec.
    destruct H1.
    rewrite H1, <- H4.
    tauto.
Qed.

Lemma pregraph_join_edge_union_absorbe: forall G1 G2 PV PE,
  relation_list (pregraph_join PV PE :: edge_union PE :: nil) G1 G2 ->
  pregraph_join PV PE G1 G2.
Proof.
  intros.
  destruct_relation_list G3 in H.
  destruct H as [? [? [? ?]]], H0 as [? [? [? ?]]].
  split; [| split; [| split]].
  + apply Same_set_spec in H.
    rewrite <- H; auto.
  + clear - H1 H4.
    destruct H4. firstorder.
  + intros.
    assert (evalid G3 e) by (destruct H4; firstorder).
    rewrite H5, H2; auto.
  + intros.
    assert (evalid G3 e) by (destruct H4; firstorder).
    rewrite H6, H3; auto.
Qed.

End ExpandPartialGraph.
