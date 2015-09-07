Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Logic.Classical.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.Coqlib.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.dag.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Local Open Scope logic.

Class SpatialGraph (V E: Type) {VE: EqDec V eq} {EE: EqDec E eq} (DV DE: Type): Type := {
  pg: PreGraph V E;
  vgamma: V -> DV;
  egamma: E -> DE
}.

Arguments vgamma {V E _ _ DV DE} _ _.
Arguments egamma {V E _ _ DV DE} _ _.

Coercion pg : SpatialGraph >-> PreGraph.

Class SpatialGraphPred (V E DV DE Pred: Type): Type := {
  vertex_at: V -> DV -> Pred;
  edge_at: E -> DE -> Pred
}.

Definition spatialgraph_gen {V E VE EE DV DE} (g: @SpatialGraph V E VE EE DV DE) (x: V) (a: DV) : @SpatialGraph V E VE EE DV DE := Build_SpatialGraph _ _ _ _ _ _ pg (fun v => if (equiv_dec x v) then a else vgamma g v) (egamma g).

Class SpatialGraphBasicAssum (V E: Type) := {
  VE: EqDec V eq;
  EE: EqDec E eq
}.

Existing Instances VE EE.

Class SpatialGraphAssum {V E DV DE Pred: Type} (SGP: SpatialGraphPred V E DV DE Pred) {SGBA: SpatialGraphBasicAssum V E}:= {
  SGP_ND: NatDed Pred;
  SGP_SL : SepLog Pred;
  SGP_ClSL: ClassicalSep Pred;
  SGP_CoSL: CorableSepLog Pred;
  vertex_at_sep: (forall x d1 d2, vertex_at x d1 * vertex_at x d2 |-- FF) \/ (forall x d, vertex_at x d |-- emp);
  edge_at_sep: (forall e d1 d2, edge_at e d1 * edge_at e d2 |-- FF) \/ (forall e d, edge_at e d |-- emp)
}.

Existing Instances SGP_ND SGP_SL SGP_ClSL SGP_CoSL.

Instance AAV {V E DV DE Pred: Type} (SGP: SpatialGraphPred V E DV DE Pred) {SGBA: SpatialGraphBasicAssum V E} : AbsAddr V DV.
  apply (mkAbsAddr V DV (fun x y => if equiv_dec x y then true else false)); simpl; intros.
  + destruct_eq_dec p1 p2; destruct_eq_dec p2 p1; congruence.
  + destruct_eq_dec p1 p1; destruct_eq_dec p1 p2; congruence.
Defined.

Instance AAE {V E DV DE Pred: Type} (SGP: SpatialGraphPred V E DV DE Pred) {SGBA: SpatialGraphBasicAssum V E} : AbsAddr E DE.
  apply (mkAbsAddr E DE (fun x y => if equiv_dec x y then true else false)); simpl; intros.
  + destruct_eq_dec p1 p2; destruct_eq_dec p2 p1; congruence.
  + destruct_eq_dec p1 p1; destruct_eq_dec p1 p2; congruence.
Defined.

Class SpatialGraphStrongAssum {V E DV DE Pred: Type} (SGP: SpatialGraphPred V E DV DE Pred) {SGBA: SpatialGraphBasicAssum V E} {SGA: SpatialGraphAssum SGP} := {
  SGP_PSL: PreciseSepLog Pred;
  SGP_OSL: OverlapSepLog Pred;
  SGP_DSL: DisjointedSepLog Pred;
  SGP_COSL: CorableOverlapSepLog Pred;

  VP_MSL: MapstoSepLog (AAV SGP) vertex_at;
  VP_sMSL: StaticMapstoSepLog (AAV SGP) vertex_at;
  EP_MSL: MapstoSepLog (AAE SGP) edge_at;
  EP_sMSL: StaticMapstoSepLog (AAE SGP) edge_at
}.

Existing Instances SGP_PSL SGP_OSL SGP_DSL SGP_COSL VP_MSL VP_sMSL EP_MSL EP_sMSL.

Section GENERAL_SPATIAL_GRAPH.

Context {V : Type}.
Context {E : Type}.
Context {DV : Type}.
Context {DE : Type}.

Context {SGBA: SpatialGraphBasicAssum V E}.

Section PURE_FACTS.
Definition validly_identical (g1 g2: SpatialGraph V E DV DE) : Prop :=
  g1 ~=~ g2 /\
  (forall v, vvalid g1 v -> vvalid g2 v -> vgamma g1 v = vgamma g2 v) /\
  (forall e, evalid g1 e -> evalid g2 e -> egamma g1 e = egamma g2 e).

Notation "g1 '-=-' g2" := (validly_identical g1 g2) (at level 1).

Lemma vi_refl: forall (g : SpatialGraph V E DV DE), g -=- g.
Proof. intros. split; auto. apply si_refl. Qed.

Lemma vi_sym: forall (g1 g2 : SpatialGraph V E DV DE), g1 -=- g2 -> g2 -=- g1.
Proof.
  intros. destruct H as [? [? ?]]. split; [|split]; intros.
  + apply si_sym; auto.
  + specialize (H0 _ H3 H2). auto.
  + specialize (H1 _ H3 H2). auto.
Qed.

Lemma vi_trans: forall (g1 g2 g3: SpatialGraph V E DV DE), g1 -=- g2 -> g2 -=- g3 -> g1 -=- g3.
Proof.
  intros. destruct H as [? [? ?]]. destruct H0 as [? [? ?]].
  split; [| split]; intros.
  + apply si_trans with g2; auto.
  + assert (vvalid g2 v) by (destruct H; rewrite <- H; auto).
    specialize (H1 _ H5 H7). specialize (H3 _ H7 H6). transitivity (vgamma g2 v); auto.
  + assert (evalid g2 e) by (destruct H as [_ [? _]]; rewrite <- H; auto).
    specialize (H2 _ H5 H7). specialize (H4 _ H7 H6). transitivity (egamma g2 e); auto.
Qed.

Add Parametric Relation : (SpatialGraph V E DV DE) validly_identical
    reflexivity proved by vi_refl
    symmetry proved by vi_sym
    transitivity proved by vi_trans as vi_equal.

Global Existing Instance vi_equal.

Definition predicate_sub_spatialgraph  (g: SpatialGraph V E DV DE: Type) (p: V -> Prop) :=
  Build_SpatialGraph V E _ _ DV DE (predicate_subgraph g p) (vgamma g) (egamma g).

Definition predicate_partial_spatialgraph  (g: SpatialGraph V E DV DE: Type) (p: V -> Prop) :=
  Build_SpatialGraph V E _ _ DV DE (predicate_partialgraph g p) (vgamma g) (egamma g).

Definition reachable_sub_spatialgraph (g: SpatialGraph V E DV DE: Type) (S : list V) : SpatialGraph V E DV DE :=
  predicate_sub_spatialgraph g (reachable_through_set g S).

Definition unreachable_partial_spatialgraph (g: SpatialGraph V E DV DE: Type) (S : list V) : SpatialGraph V E DV DE :=
  predicate_partial_spatialgraph g (Complement _ (reachable_through_set g S)).

Lemma vi_stronger_partial_spatialgraph: forall (g1 g2: SpatialGraph V E DV DE: Type) (p1 p2 p1' p2' p: V -> Prop),
  (forall v, p1' v <-> p1 v /\ p v) ->
  (forall v, p2' v <-> p2 v /\ p v) ->
  (predicate_partial_spatialgraph g1 p1) -=- (predicate_partial_spatialgraph g2 p2) ->
  (predicate_partial_spatialgraph g1 p1') -=- (predicate_partial_spatialgraph g2 p2').
Proof.
  intros.
  split; [| split].
  + eapply si_stronger_partialgraph; eauto.
    exact (proj1 H1).
  + destruct H1 as [_ [? _]].
    intros.
    apply H1; simpl in H2, H3 |- *; unfold predicate_vvalid in *; firstorder.
  + destruct H1 as [_ [_ ?]].
    intros.
    apply H1; simpl in H2, H3 |- *; unfold predicate_evalid in *; firstorder.
Qed.

Instance sub_spatialgraph_proper: Proper (validly_identical ==> (pointwise_relation V iff) ==> validly_identical) predicate_sub_spatialgraph.
  do 3 (hnf; intros).
  destruct H as [? [? ?]].
  split; [| split].
  + simpl; rewrite H, H0; reflexivity.
  + simpl; intros.
    unfold predicate_vvalid in *.
    firstorder.
  + simpl; intros.
    unfold predicate_vvalid in *.
    firstorder.
Defined.

Global Existing Instance sub_spatialgraph_proper.

Instance partial_spatialgraph_proper: Proper (validly_identical ==> (pointwise_relation V iff) ==> validly_identical) predicate_partial_spatialgraph.
  do 3 (hnf; intros).
  destruct H as [? [? ?]].
  split; [| split].
  + simpl; rewrite H, H0; reflexivity.
  + simpl; intros.
    unfold predicate_vvalid in *.
    firstorder.
  + simpl; intros.
    unfold predicate_vvalid in *.
    firstorder.
Defined.

Global Existing Instance partial_spatialgraph_proper.

Lemma update_self: forall (g: SpatialGraph V E DV DE) (x: V) (d: DV), vgamma g x = d -> g -=- (spatialgraph_gen g x d).
Proof.
  intros.
  split; [reflexivity | split; [| auto]].
  intros.
  simpl.
  destruct_eq_dec x v; subst; auto.
Qed.

Lemma update_invalid: forall (g: SpatialGraph V E DV DE) (x: V) (d: DV), ~ vvalid g x -> g -=- (spatialgraph_gen g x d).
Proof.
  intros.
  split; [reflexivity | split; [| auto]].
  intros.
  simpl.
  destruct_eq_dec x v; subst; auto.
  tauto.
Qed.

Lemma spacialgraph_gen_vgamma: forall (g: SpatialGraph V E DV DE) (x: V) (d: DV), vgamma (spatialgraph_gen g x d) x = d.
Proof.
  intros.
  simpl.
  destruct_eq_dec x x; auto.
  congruence.
Qed.

End PURE_FACTS.

Notation "g1 '-=-' g2" := (validly_identical g1 g2) (at level 1).

Section SPATIAL_FACTS.

Context {Pred: Type}.
Context {SGP: SpatialGraphPred V E DV DE Pred}.
Context {SGA: SpatialGraphAssum SGP}.
Notation Graph := (SpatialGraph V E DV DE).

Definition graph_cell (g: Graph) (v : V) : Pred := vertex_at v (vgamma g v).

Definition vertices_at (P: V -> Prop) (g: Graph): Pred := pred_sepcon P (graph_cell g).

Definition graph (x : V) (g: Graph) : Pred := vertices_at (reachable g x) g.

Definition graphs' (S : list V) (g : Graph) := vertices_at (reachable_through_set g S) g.

Definition Gamma (g: Graph) x := (x, vgamma g x).

Definition Graph_cell (p : V * DV) := vertex_at (fst p) (snd p).

Lemma Gamma_injective: forall g x y, Gamma g x = Gamma g y -> x = y.
Proof. intros. unfold Gamma in H. inversion H. auto. Qed.

Lemma weak_sepcon_unique_graph_cell: (forall g, sepcon_unique (graph_cell g)) \/ (forall x d, graph_cell x d |-- emp).
Proof.
  destruct vertex_at_sep; [left | right; unfold graph_cell]; auto.
  repeat intro. unfold graph_cell.
  apply H.
Qed.

(*
Lemma vertices_at_NoDup: forall (g: Graph) (P: V -> Prop),
  vertices_at g P = EX l: list V, !!(forall x, In x l <-> P x) && !! (NoDup l) && iter_sepcon l (graph_cell g).
Proof.
  intros.
  unfold vertices_at.
  unfold graph_cell.
  apply pred_ext; [destruct vertex_at_sep |].
  + apply exp_left; intro l; apply (exp_right l).
    pose proof (@iter_sepcon_unique_nodup Pred _ _ _ _ _ (fun v : V => vertex_at v (vgamma g v)) l).
    spec H0; [hnf; intros; simpl; apply H |].
    rewrite (add_andp _ _ H0) at 1.
    normalize.
  + apply exp_left; intro l; apply (exp_right (remove_dup equiv_dec l)).
    normalize.
    assert (NoDup (remove_dup equiv_dec l)) by apply remove_dup_nodup.
    assert (forall x, In x (remove_dup equiv_dec l) <-> P x) by (intros; rewrite <- remove_dup_in_inv; auto).
    normalize.
    apply iter_sepcon_emp; auto.
    intro x. rewrite H0, H2; auto.
  + apply exp_left; intro l; apply (exp_right l).
    normalize.
Qed.
   
Lemma vertices_at_eq: forall (g: Graph) (P: V -> Prop),
  vertices_at g P = EX l: list V, !!(forall x, In x l <-> P x) && !! (NoDup l) && iter_sepcon (map (Gamma g) l) Graph_cell.
Proof.
  intros.
  unfold vertices_at.
  unfold Gamma, Graph_cell, graph_cell.
  apply pred_ext; [destruct vertex_at_sep |].
  + apply exp_left; intro l; apply (exp_right l).
    rewrite <- !iter_sepcon_map; simpl.
    pose proof (@iter_sepcon_unique_nodup Pred _ _ _ _ _ (fun v : V => vertex_at v (vgamma g v)) l).
    spec H0; [hnf; intros; simpl; apply H |].
    rewrite (add_andp _ _ H0) at 1.
    normalize.
  + apply exp_left; intro l; apply (exp_right (remove_dup equiv_dec l)).
    normalize.
    assert (NoDup (remove_dup equiv_dec l)) by apply remove_dup_nodup.
    assert (forall x, In x (remove_dup equiv_dec l) <-> P x) by (intros; rewrite <- remove_dup_in_inv; auto).
    normalize.
    rewrite <- iter_sepcon_map.
    apply iter_sepcon_emp; auto.
    intro x. rewrite H0, H2; auto.
  + apply exp_left; intro l; apply (exp_right l).
    rewrite <- iter_sepcon_map.
    normalize.
Qed.

Lemma vertices_at_eq': forall {A} (PureF: A -> Prop) (g: A -> Graph) (P: A -> V -> Prop),
  EX a: A, !! PureF a && vertices_at (g a) (P a) = EX a: A, !! PureF a && (EX l: list V, !!(forall x, In x l <-> P a x) && !! (NoDup l) && iter_sepcon (map (Gamma (g a)) l) Graph_cell).
Proof.
  intros.
  apply exp_f_equal; intros a.
  f_equal.
  apply vertices_at_eq.
Qed.

Definition graphs'_eq: forall (g : Graph) (S : list V) (H1: ReachableFiniteGraph g)
                              (H2: (forall x : V, In x S -> Decidable (vvalid g x))),
    graphs' S g = iter_sepcon (map (Gamma g) (proj1_sig (construct_reachable_set_list g S H2))) Graph_cell.
Proof.
  intros. apply pred_ext.
  + unfold graphs'. normalize. intro l; intros.
    destruct (construct_reachable_set_list g S H2) as [l' [?H ?H]]. unfold proj1_sig.
    rewrite <- iter_sepcon_map. rewrite (iter_sepcon_func l' _ (graph_cell g)).
    - destruct weak_sepcon_unique_graph_cell.
      * rewrite (add_andp _ _ (iter_sepcon_unique_nodup l (H4 g))).
        normalize. rewrite (@iter_sepcon_permutation _ _ _ _ l l'); auto.
        apply NoDup_Permutation; auto. intro y. specialize (H y). specialize (H3 y). tauto.
      * apply iter_sepcon_emp; auto.
        intro x.
        rewrite (H x), (H3 x).
        auto.
    - intros. unfold Gamma. unfold Graph_cell. unfold graph_cell. simpl. auto.
  + unfold graphs'. apply (exp_right (proj1_sig (construct_reachable_set_list g S H2))).
    normalize. destruct (construct_reachable_set_list g S H2) as [l [?H ?H]].
    unfold proj1_sig. apply andp_right.
    - apply prop_right; auto.
    - rewrite <- iter_sepcon_map. rewrite (iter_sepcon_func _ _ (graph_cell g)); auto.
Qed.

Definition graph_eq: forall (g : Graph) (x : V) (H1: ReachableFiniteGraph g)
                              (H2: Decidable (vvalid g x)),
    graph x g = iter_sepcon (map (Gamma g) (proj1_sig (construct_reachable_list g x H2))) Graph_cell.
Proof.
  intros.
  assert (forall y, reachable_through_set g (x :: nil) y <-> reachable g x y).
  Focus 1. {
    intros; split; intros.
    * destruct H as [s ?H]. destruct H as [[? | ?] ?]; [subst; auto | tauto].
    * exists x; simpl; auto.
  } Unfocus.
  transitivity (graphs' (x :: nil) g).
  + unfold graph, graphs'.
    apply exp_f_equal; intros l.
    f_equal.
    apply ND_prop_ext.
    unfold reachable_list, reachable_set_list.
    split; intros HH y; [rewrite H | rewrite <- H]; auto.
  + assert (forall x0, In x0 (x :: nil) -> Decidable (vvalid g x0)).
    Focus 1. {
      intros x0 HH.
      destruct_eq_dec x0 x; [subst; auto |].
      exfalso.
      apply H0; destruct HH; [congruence | tauto].
    } Unfocus.
    rewrite (graphs'_eq g (x :: nil) H1 X).
    assert (Permutation (map (Gamma g) (proj1_sig (construct_reachable_set_list g (x :: nil) X)))
                        (map (Gamma g) (proj1_sig (construct_reachable_list g x H2)))); [| rewrite H0; auto].
    apply Permutation_map.
    destruct (construct_reachable_set_list g (x :: nil) X) as [l ?], (construct_reachable_list g x H2) as [l' ?].
    simpl.
    apply eq_as_set_permutation; try tauto.
    - apply equiv_dec.
    - apply eq_as_set_spec; intros.
      destruct a as [_ ?H], a0 as [_ ?H].
      rewrite (H0 x0), (H3 x0).
      auto.
Qed.
*)
Lemma graph_graphs: forall g x, graph x g = graphs' (x :: nil) g.
Proof.
  intros.
  unfold graph, graphs'.
  apply pred_sepcon_proper; [| reflexivity].
  intro y.
  pose proof reachable_through_set_single g x y.
  tauto.
Qed.

Lemma vertices_at_subgraph_eq:
  forall (g1 g2: Graph) (P1 P2: V -> Prop),
    Included P1 (vvalid g1) ->
    Included P2 (vvalid g2) ->
    ((predicate_sub_spatialgraph g1 P1) -=- (predicate_sub_spatialgraph g2 P2)) ->
    vertices_at P1 g1 = vertices_at P2 g2.
Proof.
  intros.
  apply pred_sepcon_strong_proper.
  + destruct H1 as [[? _] _].
    intro x; specialize (H1 x).
    simpl in H1; unfold predicate_vvalid in H1.
    specialize (H x); specialize (H0 x); unfold Ensembles.In in *.
    tauto.
  + intros.
    unfold graph_cell.
    f_equal.
    destruct H1 as [_ [? _]].
    simpl in H1; unfold predicate_vvalid in H1.
    specialize (H x); specialize (H0 x); unfold Ensembles.In in *.
    apply H1; tauto.
Qed.

Lemma vertices_at_vi_eq: forall (g1 g2 : Graph) (P : V -> Prop),
    Included P (vvalid g1) -> g1 -=- g2 -> vertices_at P g1 = vertices_at P g2.
Proof.
  intros. apply vertices_at_subgraph_eq; auto.
  + destruct H0 as [[? _] _]. intro y; unfold Ensembles.In; intros. apply H0. apply H. auto.
  + rewrite H0. reflexivity.
Qed.

Lemma graph_reachable_subgraph_eq:
  forall (g1 g2 : Graph) x,
    ((reachable_sub_spatialgraph g1 (x :: nil)) -=- (reachable_sub_spatialgraph g2 (x :: nil))) -> graph x g1 = graph x g2.
Proof.
  intros.
  apply vertices_at_subgraph_eq; auto.
  + intros y ?; eapply reachable_foot_valid; eauto.
  + intros y ?; eapply reachable_foot_valid; eauto.
  + assert (pointwise_relation V iff (reachable g1 x) (reachable_through_set g1 (x :: nil)))
      by (symmetry; intro; apply reachable_through_set_single).
    assert (pointwise_relation V iff (reachable g2 x) (reachable_through_set g2 (x :: nil)))
      by (symmetry; intro; apply reachable_through_set_single).
    rewrite H0, H1.
    apply H.
Qed.
  
Lemma graph_vi_eq: forall (g1 g2 : Graph) x, g1 -=- g2 -> graph x g1 = graph x g2.
Proof.
  intros. apply graph_reachable_subgraph_eq.
  destruct H as [? [? ?]]. split.
  + apply si_reachable_subgraph. auto.
  + split; intro; intros.
    apply H0; [destruct H2 | destruct H3]; tauto.
    apply H1; [destruct H2 | destruct H3]; tauto.
Qed.

Instance graph_proper: Proper (eq ==> validly_identical ==> eq) graph.
Proof.
  do 2 (hnf; intros); subst.
  apply graph_vi_eq; auto.
Defined.

Global Existing Instance graph_proper.

Lemma graphs_reachable_subgraph_eq:
  forall (g1 g2 : Graph) S,
    ((reachable_sub_spatialgraph g1 S) -=- (reachable_sub_spatialgraph g2 S)) -> graphs' S g1 = graphs' S g2.
Proof.
  intros.
  apply vertices_at_subgraph_eq; auto.
  + intros y ?; eapply reachable_through_set_foot_valid; eauto.
  + intros y ?; eapply reachable_through_set_foot_valid; eauto.
Qed.
  
Lemma graphs_vi_eq: forall (g1 g2 : Graph) S, g1 -=- g2 -> graphs' S g1 = graphs' S g2.
Proof.
  intros. apply graphs_reachable_subgraph_eq.
  destruct H as [? [? ?]]. split.
  + apply si_reachable_subgraph. auto.
  + split; intro; intros.
    apply H0; [destruct H2 | destruct H3]; tauto.
    apply H1; [destruct H2 | destruct H3]; tauto.
Qed.

Instance graphs_proper: Proper (eq ==> validly_identical ==> eq) graphs'.
Proof.
  do 2 (hnf; intros); subst.
  apply graphs_vi_eq; auto.
Defined.
(*
Lemma reachable_subtract_perm:
  forall (g: Graph) (S1 S2 l1 l2 : list V),
    Included (reachable_through_set g S2) (reachable_through_set g S1) ->
    reachable_set_list g S1 l1 -> NoDup l1 -> reachable_set_list g S2 l2 -> NoDup l2 ->
    Permutation (map (Gamma g) l1) (map (Gamma g) l2 ++ map (Gamma g) (subtract equiv_dec l1 l2)).
Proof.
  intros. rewrite <- (map_app (Gamma g)).
  apply Permutation_map. apply perm_trans with (subtract equiv_dec l1 l2 ++ l2).
  + apply subtract_permutation; auto.
    intro y. rewrite (H0 y), (H2 y).
    specialize (H y). auto.
  + apply Permutation_app_comm.
Qed.
*)
Lemma unreachable_eq': forall (g : Graph) (S1 S2 : list V),
    forall x, reachable_through_set g (S1 ++ S2) x /\ ~ reachable_through_set g S1 x <-> reachable_through_set (unreachable_partial_spatialgraph g S1) S2 x.
Proof.
  intros. split; intro.
  + destruct H.
    destruct H as [s [? ?]]. exists s. split.
    - apply in_app_or in H. destruct H; auto.
      exfalso. apply H0. exists s. auto.
    - rewrite reachable_ind_reachable in H1. clear -H1 H0.
      induction H1.
      * apply reachable_refl. simpl. hnf. simpl. auto.
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
        apply partialgraph_edge; auto.
  + destruct H as [s [? ?]]. split.
    - exists s. split; [apply in_or_app; auto |].
      revert H0. apply (predicate_partialgraph_reachable_included g _ s x).
    - intro. apply reachable_foot_valid in H0.
      hnf in H0. simpl in H0. destruct H0. auto.
Qed.

(*
Lemma unreachable_eq: forall (g : Graph) (S1 S2 l12 l1 : list V),
    reachable_set_list g (S1 ++ S2) l12 -> reachable_set_list g S1 l1 ->
    forall x, In x l12 /\ ~ In x l1 <-> reachable_through_set (unreachable_partial_spatialgraph g S1) S2 x.
Proof.
  intros.
  rewrite (H x), (H0 x).
  apply unreachable_eq'.
Qed.

Lemma partialgraph_update_prime:
  forall (g g': Graph) (S1 S1' S2 S2': list V),
    ((predicate_partial_spatialgraph g (fun x => In x S2 /\ ~ In x S1)) -=-
     (predicate_partial_spatialgraph g' (fun x => In x S2' /\ ~ In x S1'))) ->
   Sublist S1 S2 ->
   Sublist S1' S2' ->
    (forall x, In x S2 -> vvalid g x) ->
    (forall x, In x S2' -> vvalid g' x) ->
    NoDup S1 -> NoDup S1' -> NoDup S2 -> NoDup S2' ->
    iter_sepcon (map (Gamma g) S2) Graph_cell |--
      iter_sepcon (map (Gamma g) S1) Graph_cell * 
       (iter_sepcon (map (Gamma g') S1') Graph_cell -* iter_sepcon (map (Gamma g') S2') Graph_cell).
Proof.
  intros.
  apply iter_sepcon_ramification.
  exists (map (Gamma g) (subtract equiv_dec S2 S1)).
  split; [| apply perm_trans with (map (Gamma g') S1' ++ map (Gamma g') (subtract equiv_dec S2' S1'))].
  + rewrite <- map_app.
    apply Permutation_map.
    rewrite Permutation_app_comm.
    apply subtract_permutation; auto.
  + rewrite <- map_app.
    apply Permutation_map.
    rewrite Permutation_app_comm.
    apply subtract_permutation; auto.
  + apply Permutation_app_head.
    eapply perm_trans; [apply Permutation_map | rewrite (compcert.lib.Coqlib.list_map_exten (Gamma g') (Gamma g)); [apply Permutation_refl |]].
    - apply NoDup_Permutation; try solve [apply subtract_nodup; auto].
      intros. rewrite <- !subtract_property.
      destruct H as [[? _] _].
      specialize (H x); specialize (H2 x); specialize (H3 x).
      simpl in H; unfold predicate_vvalid in H.
      tauto.
    - intros. unfold Gamma. f_equal.
      rewrite <- subtract_property in H8. destruct H8.
      destruct H as [[? _] [? _]].
      specialize (H x); specialize (H10 x); simpl in H, H10; unfold predicate_vvalid in H, H10.
      specialize (H2 x); specialize (H3 x); symmetry; tauto.
Qed.
*)
Lemma partialgraph_update:
  forall (g g': Graph) {rfg: ReachableFiniteGraph g} {rfg': ReachableFiniteGraph g'} (S1 S1' S2: list V),
    (unreachable_partial_spatialgraph g S1) -=- (unreachable_partial_spatialgraph g' S1') ->
    (forall x : V, In x (S1 ++ S2) -> Decidable (vvalid g x)) ->
    (forall x : V, In x (S1' ++ S2) -> Decidable (vvalid g' x)) ->
    graphs' (S1 ++ S2) g |-- graphs' S1 g * (graphs' S1' g' -* graphs' (S1' ++ S2) g').
Proof.
  intros.
  assert (forall x : V, In x S1 -> Decidable (vvalid g x)) by (intros; apply X; apply in_or_app; left; auto).
  assert (forall x : V, In x S1' -> Decidable (vvalid g' x)) by (intros; apply X0; apply in_or_app; left; auto).
  apply pred_sepcon_ramify_pred with (reachable_through_set (unreachable_partialgraph g S1) S2).
  + intros.
    destruct (RFG_reachable_through_set_decicable g S1 x X1); [left; auto | right].
    apply unreachable_eq'; auto.
  + intros.
    rewrite <- (unreachable_eq' g S1 S2).
    rewrite <- reachable_through_set_app; tauto.
  + intros.
    rewrite <- (unreachable_eq' g S1 S2) in H1.
    tauto.
  + intros.
    destruct H as [? _].
    rewrite H.
    rewrite <- (unreachable_eq' g' S1' S2).
    rewrite <- reachable_through_set_app; tauto.
  + intros.
    destruct H as [? _].
    rewrite H in H1.
    rewrite <- (unreachable_eq' g' S1' S2) in H1.
    tauto.
  + intros.
    destruct H as [HH [? _]].
    simpl in H.
    unfold predicate_vvalid in H.
    unfold graph_cell.
    f_equal.
    apply H.
    - rewrite <- (unreachable_eq' g S1 S2) in H0.
      destruct H0; split; [| auto].
      eapply reachable_through_set_foot_valid; eauto.
    - rewrite HH in H0.
      rewrite <- (unreachable_eq' g' S1' S2) in H0.
      destruct H0; split; [| auto].
      eapply reachable_through_set_foot_valid; eauto.
Qed.

(*
Lemma predicate_partialgraph_vi_spec: forall (g g': Graph) (P P': V -> Prop) (l l': list V),
  (predicate_partial_spatialgraph g P) -=- (predicate_partial_spatialgraph g' P') ->
  (forall x, In x l <-> vvalid g x /\ P x) ->
  (forall x, In x l' <-> vvalid g' x /\ P' x) ->
  NoDup l ->
  NoDup l' ->
  Permutation (map (Gamma g) l) (map (Gamma g') l').
Proof.
  intros.
  transitivity (map (Gamma g') l).
  + erewrite Coqlib.list_map_exten; [reflexivity |].
    intros.
    apply H0 in H4.
    destruct H as [[? _] [? _]].
    specialize (H x); specialize (H5 x); simpl in H, H5.
    unfold predicate_vvalid in H, H5.
    unfold Gamma.
    rewrite H5; auto.
    tauto.
  + apply Permutation_map.
    apply eq_as_set_permutation; auto.
    - apply equiv_dec.
    - apply eq_as_set_spec; intro x.
      rewrite H0, H1.
      destruct H as [[? _] _].
      apply H.
Qed.
*)

Lemma existential_partialgraph_update_prime':
  forall (g: Graph) (PureS1 PureS2: V -> Prop),
  (forall x, PureS1 x -> PureS2 x) ->
  (forall x, PureS2 x -> vvalid g x) ->
  (forall x, PureS2 x -> Decidable (PureS1 x)) ->
  forall {A: Type} (g': A -> Graph) (PureF PureF': A -> Prop) (PureS1' PureS2': A -> V -> Prop),
  (forall a x, PureF a -> PureS1' a x -> PureS2' a x) ->
  (forall a x, PureF a -> PureS2' a x -> vvalid (g' a) x) ->
  (forall a, PureF a ->
    ((predicate_partial_spatialgraph g (fun x => PureS2 x /\ ~ PureS1 x)) -=-
     (predicate_partial_spatialgraph (g' a) (fun x => PureS2' a x /\ ~ PureS1' a x)))) ->
  (forall a, PureF a -> PureF' a) ->
  vertices_at PureS2 g |-- vertices_at PureS1 g *
     ((EX a: A, !!PureF a && vertices_at (PureS1' a) (g' a)) -*
      (EX a: A, !!PureF' a && vertices_at (PureS2' a) (g' a))).
Proof.
  intros.
  unfold vertices_at.
  apply existential_pred_sepcon_ramify_pred' with (PF := fun x => PureS2 x /\ ~ PureS1 x) (p2 := (fun a => graph_cell (g' a))).
  + intros.
    destruct (X x H5); [left | right]; auto.
  + intros; specialize (H x); tauto.
  + intros; tauto.
  + intros a x HH.
    specialize (H1 a x HH).
    specialize (H2 a x HH).
    specialize (H x).
    specialize (H0 x).
    specialize (H3 a HH).
    destruct H3 as [[? _] _].
    specialize (H3 x); simpl in H3.
    unfold predicate_vvalid in H3.
    tauto.
  + intros a x HH.
    specialize (H1 a x HH).
    specialize (H2 a x HH).
    specialize (H x).
    specialize (H0 x).
    specialize (H3 a HH).
    destruct H3 as [[? _] _].
    specialize (H3 x); simpl in H3.
    unfold predicate_vvalid in H3.
    tauto.
  + intros a x HH ?.
    specialize (H1 a x HH).
    specialize (H2 a x HH).
    specialize (H x).
    specialize (H0 x).
    specialize (H3 a HH).
    destruct H3 as [[? _] [? _]].
    specialize (H3 x); simpl in H3, H6.
    unfold predicate_vvalid in H3, H6.
    specialize (H6 x).
    spec H6; [tauto |].
    spec H6; [tauto |].
    unfold graph_cell.
    f_equal.
    auto.
  + auto.
Qed.

Lemma existential_partialgraph_update_prime:
  forall (g: Graph) (PureS1 PureS2: V -> Prop),
  (forall x, PureS1 x -> PureS2 x) ->
  (forall x, PureS2 x -> vvalid g x) ->
  (forall x, PureS2 x -> Decidable (PureS1 x)) ->
  forall {A: Type} (g': A -> Graph) (PureF PureF': A -> Prop) (PureS1' PureS2': A -> V -> Prop),
  (forall a x, PureF a -> PureS1' a x -> PureS2' a x) ->
  (forall a x, PureF a -> PureS2' a x -> vvalid (g' a) x) ->
  (forall a, PureF a ->
    ((predicate_partial_spatialgraph g (fun x => PureS2 x /\ ~ PureS1 x)) -=-
     (predicate_partial_spatialgraph (g' a) (fun x => PureS2' a x /\ ~ PureS1' a x)))) ->
  vertices_at PureS2 g |-- vertices_at PureS1 g *
     ((EX a: A, !!PureF a && vertices_at (PureS1' a) (g' a)) -*
      (EX a: A, !!PureF a && vertices_at (PureS2' a) (g' a))).
Proof. intros. apply existential_partialgraph_update_prime'; auto. Qed.

Lemma vertices_at_ramify: forall (g: Graph) {rfg: ReachableFiniteGraph g} (P: V -> Prop) x d d',
  vvalid g x -> P x -> vgamma g x = d ->
  vertices_at P g |-- vertex_at x d * (vertex_at x d' -* vertices_at P (spatialgraph_gen g x d')).
Proof.
  intros.
  replace (@vertex_at _ _ _ _ _ SGP x d) with (graph_cell g x).
  Focus 2. {
    simpl.
    unfold graph_cell; simpl.
    rewrite H1; auto.
  } Unfocus.
  replace (@vertex_at _ _ _ _ _ SGP x d') with (graph_cell (spatialgraph_gen g x d') x).
  Focus 2. {
    simpl.
    unfold graph_cell; simpl.
    destruct_eq_dec x x; [auto | congruence].
  } Unfocus.
  apply pred_sepcon_ramify1_simpl; auto.
  intros.
  unfold graph_cell.
  f_equal.
  simpl.
  destruct_eq_dec x y; [congruence |].
  auto.
Qed.

Lemma graph_ramify_aux0: forall (g: Graph) {rfg: ReachableFiniteGraph g} x d d',
  vvalid g x -> vgamma g x = d ->
  graph x g |-- vertex_at x d * (vertex_at x d' -* graph x (spatialgraph_gen g x d')).
Proof.
  intros.
  apply vertices_at_ramify; auto.
  apply reachable_refl; auto.
Qed.

Lemma graph_ramify_aux1: forall (g: Graph) x l {A: Type} (PureF: A -> Prop) (g': A -> Graph)
  {rfg: ReachableFiniteGraph g}
  {rfg': forall a, ReachableFiniteGraph (g' a)}
  {V_DEC: Decidable (vvalid g l)},
  vvalid g x ->
  Included (reachable g l) (reachable g x) ->
  (forall a, PureF a ->
   (vvalid (g' a) x /\
    Included (reachable (g' a) l) (reachable (g' a) x)) /\
   (unreachable_partial_spatialgraph g (l :: nil)) -=-
   (unreachable_partial_spatialgraph (g' a) (l :: nil))) ->
  graph x g |-- graph l g *
   ((EX a: A, !! PureF a && graph l (g' a)) -*
    (EX a: A, !! PureF a && graph x (g' a))).
Proof.
  intros.
  apply existential_partialgraph_update_prime; auto.
  + intros; eapply reachable_foot_valid; eauto.
  + intros; apply RFG_reachable_decicable'; auto.
  + intros.
    destruct (H1 a H2) as [[_ ?] _].
    specialize (H4 x0); tauto.
  + intros.
    apply reachable_foot_valid in H3; auto.
  + intros.
    destruct (H1 a H2) as [[_ _] ?]; auto.
    assert (pointwise_relation V iff 
              (fun x0 : V => reachable g x x0 /\ ~ reachable g l x0)
              (reachable (unreachable_partial_spatialgraph g (l :: nil)) x)).
    Focus 1. {
      intro y.
      specialize (H0 y).
      assert (reachable g x y <-> reachable g l y \/ reachable g x y) by tauto.
      rewrite H4; clear H4.
      rewrite <- (reachable_through_set_single g x), <- reachable_through_set_eq, <- !reachable_through_set_single.
      apply (unreachable_eq' g (l :: nil) (x :: nil)).
    } Unfocus.
    assert (pointwise_relation V iff 
              (fun x0 : V => reachable (g' a) x x0 /\ ~ reachable (g' a) l x0)
              (reachable (unreachable_partial_spatialgraph (g' a) (l :: nil)) x)).
    Focus 1. {
      intro y.
      destruct (H1 a H2) as [[_ ?] _].
      specialize (H5 y).
      assert (reachable (g' a) x y <-> reachable (g' a) l y \/ reachable (g' a) x y) by tauto.
      rewrite H6; clear H6.
      rewrite <- (reachable_through_set_single (g' a) x), <- reachable_through_set_eq, <- !reachable_through_set_single.
      apply (unreachable_eq' (g' a) (l :: nil) (x :: nil)).
    } Unfocus.
    rewrite H4, H5; clear H4 H5.
    eapply vi_stronger_partial_spatialgraph
      with (p := reachable (unreachable_partial_spatialgraph g (l :: nil)) x); [| | exact H3].
    - intros; simpl.
      pose proof reachable_foot_valid
       (predicate_partialgraph g (fun n : V => ~ reachable_through_set g (l :: nil) n)) x v.
      simpl (vvalid
         (predicate_partialgraph g
            (fun n : V => ~ reachable_through_set g (l :: nil) n)) v) in H4; unfold predicate_vvalid in H4.
      tauto.
    - intros.
      destruct H3 as [? _].
      rewrite H3.
      pose proof reachable_foot_valid
       (predicate_partialgraph (g' a) (fun n : V => ~ reachable_through_set (g' a) (l :: nil) n)) x v.
      simpl (vvalid
         (predicate_partialgraph (g' a)
            (fun n : V => ~ reachable_through_set (g' a) (l :: nil) n)) v) in H4; unfold predicate_vvalid in H4.
      tauto.
Qed.

Lemma dag_graph_unfold: forall (g: Graph) x S, vvalid g x -> localDag g x -> step_list g x S -> graph x g = vertex_at x (vgamma g x) * graphs' S g.
Proof.
  intros.
  change (vertex_at x (vgamma g x)) with (graph_cell g x).
  pose proof localDag_reachable_spec g x S.
  do 3 (spec H2; [auto |]).
  destruct H2.
  apply pred_sepcon_or1; auto.
Qed.

Lemma dag_graph_gen_step_list: forall (g: Graph) x S d, vvalid g x -> localDag g x -> step_list g x S -> graphs' S g = graphs' S (spatialgraph_gen g x d).
Proof.
  intros.
  apply graphs_reachable_subgraph_eq.
  split; [reflexivity | split; intros; [| reflexivity]].
  simpl.
  destruct_eq_dec x v; [exfalso | auto].
  subst v.
  simpl in H2; clear H3.
  destruct H2 as [? [y [? ?]]].
  specialize (H0 x).
  spec H0; [apply reachable_refl; auto |].
  apply (H0 y); auto.
  rewrite (H1 y) in H3.
  split; [| split]; auto.
  apply reachable_head_valid in H4; auto.
Qed.

Context {SGSA: SpatialGraphStrongAssum SGP}.

Lemma precise_graph_cell: forall g v, precise (graph_cell g v).
Proof. intros. unfold graph_cell. apply (@mapsto_precise _ _ _ _ _ _ _ _ VP_MSL). Qed.  

Lemma sepcon_unique_graph_cell: forall g, sepcon_unique (graph_cell g).
Proof.
  repeat intro. unfold graph_cell.
  apply (@mapsto_conflict _ _ _ _ _ _ _ _ _ _ _ VP_sMSL).
  simpl.
  destruct_eq_dec x x; congruence.
Qed.

Lemma joinable_graph_cell : forall g, joinable (graph_cell g).
Proof.
  intros. unfold joinable; intros. unfold graph_cell. apply (@disj_mapsto _ _ (AAV SGP) _ _ _ _ _ _ VP_MSL _ VP_sMSL).
  simpl.
  destruct_eq_dec x y; congruence.
Qed.  

Fixpoint graphs (l : list V) (g: Graph) :=
  match l with
    | nil => emp
    | v :: l' => graph v g ⊗ graphs l' g
  end.

Lemma graphs_app: forall (g : Graph) S1 S2, graphs (S1 ++ S2) g = graphs S1 g ⊗ graphs S2 g.
Proof.
  intros. induction S1; simpl.
  + rewrite ocon_comm, ocon_emp. auto.
  + rewrite IHS1. rewrite ocon_assoc. auto.
Qed.

Lemma graphs_graphs': forall S (g: Graph) {rfg: ReachableFiniteGraph g}
  (V_DEC: forall x : V, In x S -> Decidable (vvalid g x)),
  graphs S g = graphs' S g.
Proof.
  induction S; intros until g; intros rfg V_DEC.
  + unfold graphs. unfold graphs', vertices_at, pred_sepcon. apply pred_ext.
    - apply (exp_right nil). simpl. apply andp_right; auto.
      apply andp_right; [| apply prop_right; constructor].
      apply prop_right. intro x. split; intros.
      * inversion H.
      * unfold reachable_through_set in H. destruct H as [s [? _]]. inversion H.
    - normalize. intro l; intros. normalize. destruct l; simpl; auto.
      specialize (H v). assert (In v (v :: l)) by apply in_eq.
      rewrite H in H1. unfold reachable_through_set in H1.
      destruct H1 as [s [? _]]. inversion H1.
  + unfold graphs. fold graphs. rewrite IHS; [| auto | intros; apply V_DEC; right; auto].
    unfold graphs', graph, vertices_at, pred_sepcon. clear IHS. apply pred_ext.
    - normalize_overlap. intros. rename x into la.
      normalize_overlap. rename x into lS. normalize_overlap.
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup la (sepcon_unique_graph_cell g))).
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup lS (sepcon_unique_graph_cell g))).
      normalize_overlap.
      rewrite (iter_sepcon_ocon equiv_dec); auto. apply (exp_right (remove_dup equiv_dec (la ++ lS))).
      apply andp_right; [apply andp_right |].
      * apply prop_right.
        unfold reachable_set_list in *.
        unfold reachable_list in *. intros.
        rewrite <- remove_dup_in_inv.
        rewrite reachable_through_set_eq.
        specialize (H1 x). specialize (H x).
        split; intro; [apply in_app_or in H3 | apply in_or_app];
        destruct H3; [left | right | left | right]; tauto.
      * apply prop_right.
        apply remove_dup_nodup.
      * auto.
      * apply precise_graph_cell.
      * apply joinable_graph_cell.
    - normalize. intro l; intros. assert (In a (a :: S)) by apply in_eq.
      destruct (construct_reachable_list g a) as [la [? ?]]; [apply V_DEC; left; auto |].
      normalize_overlap. apply (exp_right la).
      destruct (construct_reachable_set_list g S) as [lS [? ?]]; [intros; apply V_DEC; right; auto |].
      normalize_overlap. apply (exp_right lS). normalize_overlap.
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup l (sepcon_unique_graph_cell g))).
      normalize. rewrite (iter_sepcon_ocon equiv_dec); auto.
      2: apply precise_graph_cell.
      2: apply joinable_graph_cell.
      rewrite iter_sepcon_permutation with (l2 := remove_dup equiv_dec (la ++ lS)); auto.
      apply NoDup_Permutation; auto. apply remove_dup_nodup.
      intros. rewrite <- remove_dup_in_inv. clear -H H2 H5.
      specialize (H x). specialize (H2 x). specialize (H5 x). rewrite H.
      rewrite reachable_through_set_eq. rewrite in_app_iff. tauto.
Qed.

Lemma subgraph_update:
  forall (g g': Graph) {rfg: ReachableFiniteGraph g} {rfg': ReachableFiniteGraph g'} (S1 S1' S2: list V),
    (forall x : V, In x (S1 ++ S2) -> Decidable (vvalid g x)) ->
    (forall x : V, In x (S1' ++ S2) -> Decidable (vvalid g' x)) ->
    (unreachable_partial_spatialgraph g S1) -=- (unreachable_partial_spatialgraph g' S1') ->
    graphs S1 g ⊗ graphs S2 g |-- graphs S1 g * (graphs S1' g' -* graphs S1' g' ⊗ graphs S2 g').
Proof.
  intros. rewrite <- !graphs_app.
  rewrite !graphs_graphs'; auto.
  2: intros; apply X0; rewrite in_app_iff; left; auto.
  2: intros; apply X; rewrite in_app_iff; left; auto.
  apply partialgraph_update; auto.
Qed.

End SPATIAL_FACTS.

End GENERAL_SPATIAL_GRAPH.

Notation "g1 '-=-' g2" := (validly_identical g1 g2) (at level 1).
