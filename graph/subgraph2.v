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
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.

Section SubGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Definition reachable_subgraph (g: PreGraph V E) (S : list V): PreGraph V E :=
  predicate_subgraph g (reachable_through_set g S).

Definition unreachable_partialgraph (g: PreGraph V E) (S : list V): PreGraph V E :=
  predicate_partialgraph g (fun n => ~ reachable_through_set g S n).

Lemma reachable_by_path_subgraph_partialgraph (g: PreGraph V E) (p q: V -> Prop):
  forall (n1 n2: V) (l: path),
    (predicate_subgraph g p) |= l is n1 ~o~> n2 satisfying q <->
    (predicate_partialgraph g p) |= l is n1 ~o~> n2 satisfying q.
Proof.
  intros. unfold reachable_by_path, good_path. apply and_iff_split; [|apply and_iff_split].
  - unfold path_ends. apply and_iff_compat_l. destruct l as [v l]. revert v. induction l; intros.
    + simpl. intuition.
    + rewrite !pfoot_cons. apply IHl.
  - destruct l as [v l]. revert v. induction l; intros.
    + simpl. intuition.
    + rewrite !valid_path_cons_iff. rewrite IHl. apply and_iff_compat_l, and_iff_compat_r.
      unfold strong_evalid. simpl. apply and_iff_compat_r_weak. intros. destruct H.
      unfold predicate_evalid. unfold predicate_weak_evalid. destruct H0. intuition.
  - destruct l as [v l]. unfold path_prop. simpl. rewrite !Forall_forall. reflexivity.
Qed.

Lemma reachable_subgraph_partialgraph (g: PreGraph V E) (p: V -> Prop):
  forall (n1 n2: V),
    reachable (predicate_subgraph g p) n1 n2 <-> reachable (predicate_partialgraph g p) n1 n2.
Proof.
  intros. unfold reachable, reachable_by.
  apply ex_iff, reachable_by_path_subgraph_partialgraph.
Qed.

Lemma reachable_by_path_eq_subgraph_reachable (g: PreGraph V E) (p: V -> Prop):
  forall (n1 n2: V) (path : path),
    g |= path is n1 ~o~> n2 satisfying p <-> (predicate_subgraph g p) |= path is n1 ~o~> n2 satisfying (fun _ => True).
Proof.
  intros; split; intros; destruct H as [[? ?] [? ?]]; split.
  - split; auto. clear - H0. destruct path as [v l]. revert v H0. induction l; intros. 1: simpl in *; auto. rewrite pfoot_cons in H0 |-* . apply IHl; auto.
  - split. 2: destruct path; red; rewrite Forall_forall; split; intros; auto.
    clear H H0. destruct path as [v l]. revert v H1 H2. induction l; intros.
    1: simpl in H1; simpl in *; unfold path_prop in H2. unfold predicate_vvalid; intuition.
    rewrite valid_path_cons_iff in H1 |-* . destruct H1 as [? [? ?]]. split; auto. split.
    + unfold strong_evalid in *. simpl. unfold predicate_evalid, predicate_vvalid. subst v. simpl in H2. hnf in H2. rewrite Forall_forall in H2. destruct H2.
      assert (In a (a :: l)) by apply in_eq. specialize (H2 _ H3). intuition.
    + apply IHl; auto. apply path_prop_tail in H2. unfold ptail in H2. apply H2.
  - split; auto. clear - H0. destruct path as [v l]. revert v H0. induction l; intros. 1: simpl in *; auto. rewrite pfoot_cons in H0 |-* . apply IHl; auto.
  - clear H H0 H2. destruct path. revert v H1. induction l; intros.
    + simpl in H1. unfold good_path. simpl. unfold path_prop.
      unfold predicate_vvalid in H1. simpl. destruct H1. split; auto.
    + rewrite valid_path_cons_iff in H1. destruct H1 as [? [? ?]]. simpl in H. subst v. unfold strong_evalid in H0. simpl in H0.
      unfold predicate_vvalid, predicate_evalid in H0. intuition. clear H6 H7. specialize (IHl _ H1).
      unfold predicate_subgraph in IHl; simpl in IHl. destruct IHl. split.
      * rewrite valid_path_cons_iff. do 2 (split; auto). hnf. auto.
      * simpl. hnf. rewrite Forall_forall. simpl. split; auto. intros.
        simpl in H7. destruct H7. 1: subst; intuition.
        hnf in H6. destruct l. 1: inversion H7. hnf in H6. rewrite Forall_forall in H6. apply H6; auto.
Qed.

Context (g: PreGraph V E).

Lemma reachable_by_eq_subgraph_reachable (p: V -> Prop):
  forall (n1 n2: V),
    g |= n1 ~o~> n2 satisfying p <-> reachable (predicate_subgraph g p) n1 n2.
Proof.
  intros. unfold reachable, reachable_by. apply ex_iff; intros.
  apply reachable_by_path_eq_subgraph_reachable.
Qed.

Lemma reachable_by_path_eq_partialgraph_reachable (p: V -> Prop):
  forall (n1 n2: V) (l : path),
    g |= l is n1 ~o~> n2 satisfying p <->
    (predicate_partialgraph g p) |= l is n1 ~o~> n2 satisfying (fun _ => True).
Proof.
  intros. rewrite reachable_by_path_eq_subgraph_reachable.
  apply reachable_by_path_subgraph_partialgraph.
Qed.

Lemma reachable_by_eq_partialgraph_reachable (p: V -> Prop):
  forall (n1 n2: V),
    g |= n1 ~o~> n2 satisfying p <-> reachable (predicate_partialgraph g p) n1 n2.
Proof.
  intros.
  rewrite reachable_by_eq_subgraph_reachable.
  apply reachable_subgraph_partialgraph.
Qed.

Lemma reachable_by_eq_partialgraph_reachable' (p: V -> Prop) n:
  Same_set (reachable_by g n p) (reachable (predicate_partialgraph g p) n).
Proof.
  intros.
  rewrite Same_set_spec; intro n'.
  apply reachable_by_eq_partialgraph_reachable.
Qed.

Lemma reachable_by_through_set_eq_subgraph_reachable_through_set (p: V -> Prop):
  forall l n,
    reachable_by_through_set g l p n <-> reachable_through_set (predicate_subgraph g p) l n.
Proof.
  intros.
  unfold reachable_by_through_set, reachable_through_set.
  pose proof (fun s => reachable_by_eq_subgraph_reachable p s n).
  firstorder.
Qed.

Lemma reachable_by_through_set_eq_subgraph_reachable_through_set' (p: V -> Prop):
  forall l,
    Same_set (reachable_by_through_set g l p) (reachable_through_set (predicate_subgraph g p) l).
Proof.
  intros.
  rewrite Same_set_spec; intro n.
  apply reachable_by_through_set_eq_subgraph_reachable_through_set.
Qed.

Lemma reachable_by_through_set_eq_partialgraph_reachable_through_set (p: V -> Prop):
  forall l n,
    reachable_by_through_set g l p n <-> reachable_through_set (predicate_partialgraph g p) l n.
Proof.
  intros.
  unfold reachable_by_through_set, reachable_through_set.
  pose proof (fun s => reachable_by_eq_partialgraph_reachable p s n).
  firstorder.
Qed.

Lemma reachable_by_through_set_eq_partialgraph_reachable_through_set' (p: V -> Prop):
  forall l,
    Same_set (reachable_by_through_set g l p) (reachable_through_set (predicate_partialgraph g p) l).
Proof.
  intros.
  rewrite Same_set_spec; intro n.
  apply reachable_by_through_set_eq_partialgraph_reachable_through_set.
Qed.

Lemma predicate_subgraph_reachable_included (p: V -> Prop): 
  forall (n: V), Included (reachable (predicate_subgraph g p) n) (reachable g n).
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
  forall (n: V), Included (reachable (predicate_partialgraph g p) n) (reachable g n).
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

Lemma is_tree_ppg_spec: forall (P : V -> Prop) root,
    is_tree (predicate_partialgraph g P) root <->
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
    + unfold path_prop in *. simpl fst in *. simpl snd in *. destruct H3. split; auto.
      rewrite Forall_forall in H4 |-* . intros. specialize (H4 _ H5).
      destruct H as [? [? [? ?]]]. pose proof (valid_path_strong_evalid _ _ _ _ H2 H5).
      destruct H9 as [? [? ?]]. assert (src g1 x = src g2 x) by (apply H7; auto).
      assert (dst g1 x = dst g2 x) by (apply H8; auto). rewrite <- H12, <- H13. easy.
  Qed.

  Lemma is_partial_graph_reachable_by: forall (g1 g2: PreGraph V E) (n: V) (P: Ensemble V) (n': V),
      is_partial_graph g1 g2 -> g1 |= n ~o~> n' satisfying P -> g2 |= n ~o~> n' satisfying P.
  Proof. intros. destruct H0 as [p ?]. exists p. apply is_partial_graph_reachable_by_path with g1; auto. Qed.

  Lemma is_partial_graph_reachable: forall (g1 g2: PreGraph V E) (n: V) (n': V),
      is_partial_graph g1 g2 -> reachable g1 n n' -> reachable g2 n n'.
  Proof. intros. apply is_partial_graph_reachable_by with g1; auto. Qed.

  Lemma pregraph_gen_dst_is_partial_graph: forall (g: PreGraph V E) e v,
      ~ vvalid g v -> is_partial_graph (pregraph_gen_dst g e v) g.
  Proof.
    intros. hnf. simpl. unfold updateEdgeFunc.
    split; [|split; [|split]]; intros; auto. destruct_eq_dec e e0; [exfalso|]; auto.
  Qed.

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
  1: {
    rewrite Same_set_spec.
    hnf; intros.
    apply reachable_by_eq_partialgraph_reachable; auto.
  }
  rewrite H0 in H |- *.
  apply reachable_partialgraph_reachable_equiv in H.
  rewrite H.
  rewrite partial_partialgraph, Intersection_comm, <- partial_partialgraph.
  rewrite Same_set_spec; hnf; intros.
  rewrite reachable_by_eq_partialgraph_reachable.
  reflexivity.
Qed.

Lemma reachable_by_reachable_by_equiv (g: PreGraph V E) (P: V -> Prop) (n: V):
  Same_set (reachable_by g n P) (reachable_by g n (reachable_by g n P)).
Proof.
  intros.
  rewrite reachable_by_partialgraph_reachable_by_equiv at 1.
  2: apply Included_refl.
  rewrite reachable_by_eq_partialgraph_reachable', partial_partialgraph, <- reachable_by_eq_partialgraph_reachable'.
  apply reachable_by_proper'; try reflexivity.
  apply Intersection_absort_right.
  intro m; apply reachable_by_foot_prop.
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
  1: {
    intros; simpl; unfold predicate_vvalid.
    destruct H as [? _].
    specialize (H x0).
    specialize (H0 x0).
    hnf in H0.
    tauto.
  }
  assert (forall x y, edge (predicate_subgraph g1 p1) x y <-> edge (predicate_subgraph g2 p2) x y).
  1: {
    apply si_subgraph_edge.
    + auto.
    + intros.
      specialize (H0 x0).
      tauto.
  }
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
    1: {
      intros m0 ? [s [? ?]].
      apply H0; exists s.
      split; auto.
      apply reachable_by_trans with m0; auto.
    }
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
      1: {
        apply H3.
        rewrite reachable_by_eq_partialgraph_reachable, reachable_ind_reachable.
        apply ind.reachable_cons with y; auto.
      }
      assert (vvalid (predicate_partialgraph g
       (Intersection V (Complement V (reachable_by_through_set g l1 P)) P)) x).
      1: {
        split; [destruct H1 as [[? _] _]; auto |].
        rewrite Intersection_spec.
        split; [auto | destruct H1 as [[_ ?] _]; auto].
      }
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
    1: {
      rewrite Same_set_spec; intro v.
      pose proof reachable_by_through_set_eq_partialgraph_reachable_through_set g P l1 v.
      unfold Complement, Ensembles.In; tauto.
    }
    rewrite H0; clear H0.
    remember (predicate_partialgraph g P) as g'.
    clear g Heqg'.
    apply edge_preserved_rev_foot0; auto.
    intros; eapply reachable_through_set_reachable; eauto.
Qed.

Lemma unreachable_eq': forall (g : PreGraph V E) (S1 S2 : list V),
    forall x, reachable_through_set g (S1 ++ S2) x /\ ~ reachable_through_set g S1 x <-> reachable_through_set (predicate_partialgraph g (Intersection _ (vvalid g) (Complement _ (reachable_through_set g S1)))) S2 x.
Proof.
  intros. split; intro.
  + destruct H.
    destruct H as [s [? ?]]. exists s. split.
    - apply in_app_or in H. destruct H; auto.
      exfalso. apply H0. exists s. auto.
    - rewrite reachable_ind_reachable in H1. clear -H1 H0.
      induction H1.
      * apply reachable_refl. simpl. hnf. rewrite Intersection_spec; auto.
      * apply edge_reachable with y. apply IHreachable; auto.
        rewrite <- reachable_ind_reachable in H1.
        assert (~ reachable_through_set g S1 y). {
          intro. apply H0.
          destruct H2 as [s [? ?]]. exists s. split; auto.
          apply reachable_trans with y; auto.
        }
        assert (~ reachable_through_set g S1 x). {
          intro. apply H2.
          destruct H3 as [s [? ?]]. exists s. split; auto.
          apply reachable_edge with x; auto.
        }
        pose proof H; destruct H as [? [?  ?]].
        apply partialgraph_edge; auto;
        rewrite Intersection_spec; auto.
  + destruct H as [s [? ?]]. split.
    - exists s. split; [apply in_or_app; auto |].
      revert H0. apply (predicate_partialgraph_reachable_included g _ s x).
    - intro. apply reachable_foot_valid in H0.
      hnf in H0. simpl in H0. destruct H0.
      rewrite Intersection_spec in H2; destruct H2; auto.
Qed.

End SI_EQUIV.

Section PartialLabeledGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE DG: Type}.

Notation Graph := (LabeledGraph V E DV DE DG).

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition reachable_sub_labeledgraph (g: Graph) (S : list V): Graph :=
  predicate_sub_labeledgraph g (reachable_through_set g S).

Definition unreachable_partial_labeledgraph (g: Graph) (S : list V): Graph :=
  predicate_partial_labeledgraph g (fun n => ~ reachable_through_set g S n).

End PartialLabeledGraph.

Section GRAPH_DISJOINT_UNION.

  Context {V E: Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.
  Context {DV DE DG: Type}.

  Local Coercion pg_lg: LabeledGraph >-> PreGraph.

  Definition disjointed_guard (PV1 PV2: V -> Prop) (PE1 PE2: E -> Prop) :=
    Disjoint _ PV1 PV2 /\ Disjoint _ PE1 PE2.

  (* In assumption, why need decidability in Type? Because we need at least an existence (in Prop) of a function, which requires decidability in Type. *)
  (* In conclusion, it is possible to generate this stronger existential (In Type) property. *) 
  Definition disjointed_union_labeledgraph_sig_ll: forall (G1 G2: LabeledGraph V E DV DE DG),
    disjointed_guard (vvalid G1) (vvalid G2) (evalid G1) (evalid G2) ->
    (forall v, Decidable (vvalid G1 v)) ->
    (forall e, Decidable (evalid G1 e)) ->
    { G: LabeledGraph V E DV DE DG | 
      guarded_labeled_graph_equiv (vvalid G1) (evalid G1) G1 G /\
      guarded_labeled_graph_equiv (vvalid G2) (evalid G2) G2 G /\
      Prop_join (vvalid G1) (vvalid G2) (vvalid G) /\
      Prop_join (evalid G1) (evalid G2) (evalid G)}.
  Proof.
    intros.
    exists
      (Build_LabeledGraph _ _ _
        (@Build_PreGraph V E _ _
          (fun v => vvalid G1 v \/ vvalid G2 v)
          (fun e => evalid G1 e \/ evalid G2 e)
          (fun e => if (X0 e) then src G1 e else src G2 e)
          (fun e => if (X0 e) then dst G1 e else dst G2 e))
        (fun v => if (X v) then vlabel G1 v else vlabel G2 v)
        (fun e => if (X0 e) then elabel G1 e else elabel G2 e)
        (glabel G1)).
    split; [| split; [| split]].
    + rewrite guarded_lge_spec.
      simpl; split; [split; [| split; [| split]] | split].
      - firstorder.
      - firstorder.
      - intros.
        destruct (X0 e); tauto.
      - intros.
        destruct (X0 e); tauto.
      - intros.
        destruct (X v); tauto.
      - intros.
        destruct (X0 e); tauto.
    + rewrite guarded_lge_spec.
      simpl; split; [split; [| split; [| split]] | split].
      - firstorder.
      - firstorder.
      - intros.
        destruct H as [_ H].
        rewrite Disjoint_spec in H.
        destruct (X0 e); auto. firstorder.
      - intros.
        destruct H as [_ H].
        rewrite Disjoint_spec in H.
        destruct (X0 e); auto. firstorder.
      - intros.
        destruct H as [H _].
        rewrite Disjoint_spec in H.
        destruct (X v); auto. firstorder.
      - intros.
        destruct H as [_ H].
        rewrite Disjoint_spec in H.
        destruct (X0 e); auto. firstorder.
    + simpl; split.
      - firstorder.
      - destruct H as [? _]; rewrite Disjoint_spec in H; auto.
    + simpl; split.
      - firstorder.
      - destruct H as [_ ?]; rewrite Disjoint_spec in H; auto.
  Qed.

  Definition disjointed_union_pregraph_sig_l: forall (G1 G2: PreGraph V E),
    Disjoint _ (evalid G1) (evalid G2) ->
    (forall e, Decidable (evalid G1 e)) ->
    { G: PreGraph V E | 
      guarded_structurally_identical (vvalid G1) (evalid G1) G1 G /\
      guarded_structurally_identical (vvalid G2) (evalid G2) G2 G /\
      Same_set (Union _ (vvalid G1) (vvalid G2)) (vvalid G) /\
      Prop_join (evalid G1) (evalid G2) (evalid G)}.
  Proof.
    intros.
    exists
      (@Build_PreGraph V E _ _
        (fun v => vvalid G1 v \/ vvalid G2 v)
        (fun e => evalid G1 e \/ evalid G2 e)
        (fun e => if (X e) then src G1 e else src G2 e)
        (fun e => if (X e) then dst G1 e else dst G2 e)).
    split; [| split; [| split]].
    + rewrite guarded_si_spec.
      simpl; split; [| split; [| split]].
      - firstorder.
      - firstorder.
      - intros.
        destruct (X e); tauto.
      - intros.
        destruct (X e); tauto.
    + rewrite guarded_si_spec.
      simpl; split; [| split; [| split]].
      - firstorder.
      - firstorder.
      - intros.
        rewrite Disjoint_spec in H.
        destruct (X e); auto. firstorder.
      - intros.
        rewrite Disjoint_spec in H.
        destruct (X e); auto. firstorder.
    + simpl.
      rewrite Same_set_spec; intro v.
      rewrite Union_spec; tauto.
    + simpl; split.
      - firstorder.
      - rewrite Disjoint_spec in H; auto.
  Qed.

  Definition disjointed_union_pregraph_sig_r: forall (G1 G2: PreGraph V E),
    Disjoint _ (evalid G1) (evalid G2) ->
    (forall e, Decidable (evalid G2 e)) ->
    { G: PreGraph V E | 
      guarded_structurally_identical (vvalid G1) (evalid G1) G1 G /\
      guarded_structurally_identical (vvalid G2) (evalid G2) G2 G /\
      Same_set (Union _ (vvalid G1) (vvalid G2)) (vvalid G) /\
      Prop_join (evalid G1) (evalid G2) (evalid G)}.
  Proof.
    intros.
    rewrite Disjoint_comm in H.
    destruct (disjointed_union_pregraph_sig_l G2 G1 H X) as [G ?H].
    exists G.
    rewrite Union_comm.
    rewrite Prop_join_comm.
    tauto.
  Qed.

  Definition disjointed_union_labeledgraph_exists_ll: forall (G1 G2: LabeledGraph V E DV DE DG),
    disjointed_guard (vvalid G1) (vvalid G2) (evalid G1) (evalid G2) ->
    (exists f: forall v, Decidable (vvalid G1 v), True) ->
    (exists f: forall e, Decidable (evalid G1 e), True) ->
    exists G: LabeledGraph V E DV DE DG,
      guarded_labeled_graph_equiv (vvalid G1) (evalid G1) G1 G /\
      guarded_labeled_graph_equiv (vvalid G2) (evalid G2) G2 G /\
      Prop_join (vvalid G1) (vvalid G2) (vvalid G) /\
      Prop_join (evalid G1) (evalid G2) (evalid G).
  Proof.
    intros.
    destruct H0 as [X _].
    destruct H1 as [X0 _].
    destruct (disjointed_union_labeledgraph_sig_ll _ _ H X X0) as [G ?].
    exists G; auto.
  Qed.

End GRAPH_DISJOINT_UNION.

