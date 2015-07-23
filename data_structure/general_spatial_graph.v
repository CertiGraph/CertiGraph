Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
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
Require Import Coq.Logic.Classical.
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

Class SpatialGraphAssum (V E Pred: Type) := {
  VE: EqDec V eq;
  EE: EqDec E eq;
  SGP_ND: NatDed Pred;
  SGP_SL : SepLog Pred;
  SGP_ClSL: ClassicalSep Pred;
  SGP_CoSL: CorableSepLog Pred
}.

Existing Instances VE EE SGP_ND SGP_SL SGP_ClSL SGP_CoSL.

Instance AAV (V E DV DE Pred: Type) {SGA: SpatialGraphAssum V E Pred} : AbsAddr V DV.
  apply (mkAbsAddr V DV (fun x y => if equiv_dec x y then true else false)); simpl; intros.
  + destruct_eq_dec p1 p2; destruct_eq_dec p2 p1; congruence.
  + destruct_eq_dec p1 p1; destruct_eq_dec p1 p2; congruence.
Defined.

Instance AAE (V E DV DE Pred: Type) {SGA: SpatialGraphAssum V E Pred} : AbsAddr E DE.
  apply (mkAbsAddr E DE (fun x y => if equiv_dec x y then true else false)); simpl; intros.
  + destruct_eq_dec p1 p2; destruct_eq_dec p2 p1; congruence.
  + destruct_eq_dec p1 p1; destruct_eq_dec p1 p2; congruence.
Defined.

Class SpatialGraphStrongAssum {V E DV DE Pred: Type} (SGP: SpatialGraphPred V E DV DE Pred) {SGA: SpatialGraphAssum V E Pred} := {
  SGP_PSL: PreciseSepLog Pred;
  SGP_OSL: OverlapSepLog Pred;
  SGP_DSL: DisjointedSepLog Pred;
  SGP_COSL: CorableOverlapSepLog Pred;

  VP_MSL: MapstoSepLog (AAV V E DV DE Pred) vertex_at;
  VP_sMSL: StaticMapstoSepLog (AAV V E DV DE Pred) vertex_at;
  EP_MSL: MapstoSepLog (AAE V E DV DE Pred) edge_at;
  EP_sMSL: StaticMapstoSepLog (AAE V E DV DE Pred) edge_at
}.

Existing Instances SGP_PSL SGP_OSL SGP_DSL SGP_COSL VP_MSL VP_sMSL EP_MSL EP_sMSL.

Section GENERAL_SPATIAL_GRAPH.

Context {V : Type}.
Context {E : Type}.
Context {DV : Type}.
Context {DE : Type}.

Section PURE_FACTS.

Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

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
  
Definition predicate_sub_spatialgraph  (g: SpatialGraph V E DV DE: Type) (p: V -> Prop) :=
  Build_SpatialGraph V E _ _ DV DE (predicate_subgraph g p) (vgamma g) (egamma g).

Definition predicate_partial_spatialgraph  (g: SpatialGraph V E DV DE: Type) (p: V -> Prop) :=
  Build_SpatialGraph V E _ _ DV DE (predicate_partialgraph g p) (vgamma g) (egamma g).

Definition unreachable_partial_spatialgraph (g: SpatialGraph V E DV DE: Type) (S : list V) : SpatialGraph V E DV DE :=
  predicate_partial_spatialgraph g (fun n => ~ reachable_through_set g S n).

End PURE_FACTS.

Notation "g1 '-=-' g2" := (validly_identical g1 g2) (at level 1).

Section SPATIAL_FACTS.

Context {Pred: Type}.
Context {SGA: SpatialGraphAssum V E Pred}.
Context {SGP: SpatialGraphPred V E DV DE Pred}.
Context {SGSA: SpatialGraphStrongAssum SGP}.
Notation Graph := (SpatialGraph V E DV DE).

Definition graph_cell (g: Graph) (v : V) : Pred := vertex_at v (vgamma g v).

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
  intros. unfold joinable; intros. unfold graph_cell. apply (@disj_mapsto _ _ (AAV V E DV DE Pred) _ _ _ _ _ _ VP_MSL _ VP_sMSL).
  simpl.
  destruct_eq_dec x y; congruence.
Qed.  

Definition graph (x : V) (g: Graph) : Pred :=
  EX l : list V, !!reachable_list g x l && iter_sepcon l (graph_cell g).

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

Definition graphs' (S : list V) (g : Graph) := 
  EX l: list V, !!reachable_set_list g S l && iter_sepcon l (graph_cell g).

Lemma graphs_graphs': forall S (g: Graph) {rfg: ReachableFiniteGraph g}
  (V_DEC: forall x : V, In x S -> Decidable (vvalid g x)),
  graphs S g = graphs' S g.
Proof.
  induction S; intros until g; intros rfg V_DEC.
  + unfold graphs. unfold graphs'. apply pred_ext.
    - apply (exp_right nil). simpl. apply andp_right; auto.
      apply prop_right. intro x. split; intros.
      * unfold reachable_through_set in H. destruct H as [s [? _]]. inversion H.
      * inversion H.
    - normalize. intro l; intros. destruct l; simpl; auto.
      specialize (H v). assert (In v (v :: l)) by apply in_eq.
      rewrite <- H in H0. unfold reachable_through_set in H0.
      destruct H0 as [s [? _]]. inversion H0.
  + unfold graphs. fold graphs. rewrite IHS; [| auto | intros; apply V_DEC; right; auto].
    unfold graphs'. unfold graph. clear IHS. apply pred_ext.
    - normalize_overlap. intros. rename x into la.
      normalize_overlap. rename x into lS. normalize_overlap.
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup la (sepcon_unique_graph_cell g))).
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup lS (sepcon_unique_graph_cell g))).
      normalize_overlap.
      rewrite (iter_sepcon_ocon equiv_dec); auto. apply (exp_right (remove_dup equiv_dec (la ++ lS))).
      apply andp_right.
      * apply prop_right.
        unfold reachable_set_list in *.
        unfold reachable_list in *. intros.
        rewrite <- remove_dup_in_inv.
        rewrite reachable_through_set_eq.
        specialize (H0 x). specialize (H x).
        split; intro; [apply in_or_app | apply in_app_or in H3];
        destruct H3; [left | right | left | right]; tauto.
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
      intros. rewrite <- remove_dup_in_inv. clear -H H2 H4.
      specialize (H x). specialize (H2 x). specialize (H4 x). rewrite <- H.
      rewrite reachable_through_set_eq. rewrite in_app_iff. tauto.
Qed.

Definition Gamma (g: Graph) x := (x, vgamma g x).

Definition Graph_cell (p : V * DV) := vertex_at (fst p) (snd p).

Lemma Gamma_injective: forall g x y, Gamma g x = Gamma g y -> x = y.
Proof. intros. unfold Gamma in H. inversion H. auto. Qed.

Definition graphs'_eq: forall (g : Graph) (S : list V) (H1: ReachableFiniteGraph g)
                              (H2: (forall x : V, In x S -> Decidable (vvalid g x))),
    graphs' S g = iter_sepcon (map (Gamma g) (proj1_sig (construct_reachable_set_list g S H2))) Graph_cell.
Proof.
  intros. apply pred_ext.
  + unfold graphs'. normalize. intro l; intros.
    destruct (construct_reachable_set_list g S H2) as [l' [?H ?H]]. unfold proj1_sig.
    rewrite <- iter_sepcon_map. rewrite (iter_sepcon_func l' _ (graph_cell g)).
    - rewrite (add_andp _ _ (iter_sepcon_unique_nodup l (sepcon_unique_graph_cell g))).
      normalize. rewrite (@iter_sepcon_permutation _ _ _ _ l l'); auto.
      apply NoDup_Permutation; auto. intro y. specialize (H y). specialize (H3 y). tauto.
    - intros. unfold Gamma. unfold Graph_cell. unfold graph_cell. simpl. auto.
  + unfold graphs'. apply (exp_right (proj1_sig (construct_reachable_set_list g S H2))).
    normalize. destruct (construct_reachable_set_list g S H2) as [l [?H ?H]].
    unfold proj1_sig. apply andp_right.
    - apply prop_right; auto.
    - rewrite <- iter_sepcon_map. rewrite (iter_sepcon_func _ _ (graph_cell g)); auto.
Qed.

Lemma reachable_subtract_perm:
  forall (g: Graph) (S1 S2 l1 l2 : list V),
    Included (reachable_through_set g S2) (reachable_through_set g S1) ->
    reachable_set_list g S1 l1 -> NoDup l1 -> reachable_set_list g S2 l2 -> NoDup l2 ->
    Permutation (map (Gamma g) l1) (map (Gamma g) l2 ++ map (Gamma g) (subtract equiv_dec l1 l2)).
Proof.
  intros. rewrite <- (compcert.lib.Coqlib.list_append_map (Gamma g)).
  apply Permutation_map. apply perm_trans with (subtract equiv_dec l1 l2 ++ l2).
  + apply subtract_permutation; auto.
    intro y. rewrite <- (H0 y). rewrite <- (H2 y).
    specialize (H y). auto.
  + apply Permutation_app_comm.
Qed.

Lemma unreachable_eq: forall (g : Graph) (S1 S2 l12 l1 : list V),
    reachable_set_list g (S1 ++ S2) l12 -> reachable_set_list g S1 l1 ->
    forall x, In x l12 /\ ~ In x l1 <-> reachable_through_set (unreachable_partial_spatialgraph g S1) S2 x.
Proof.
  intros. split; intro.
  + destruct H1. rewrite <- (H x) in H1.
    assert (~ reachable_through_set g S1 x) by (intro; apply H2; rewrite <- (H0 x); auto).
    destruct H1 as [s [? ?]]. exists s. split.
    - apply in_app_or in H1. destruct H1; auto.
      exfalso. apply H3. exists s. auto.
    - rewrite reachable_ind_reachable in H4. clear -H4 H3.
      induction H4.
      * apply reachable_refl. simpl. hnf. simpl. auto.
      * apply edge_reachable with y. apply IHreachable; auto.
        rewrite <- reachable_ind_reachable in H4.
        assert (~ reachable_through_set g S1 y). {
          intro. apply H3.
          destruct H0 as [s [? ?]]. exists s. split; auto.
          apply reachable_trans with y; auto.
        }
        assert (~ reachable_through_set g S1 x). {
          intro. apply H0.
          destruct H1 as [s [? ?]]. exists s. split; auto.
          apply reachable_edge with x; auto.
        }
        apply partialgraph_edge; auto.
  + destruct H1 as [s [? ?]]. split.
    - rewrite <- (H x). exists s. split. 1: apply in_or_app; auto.
      revert H2. apply (predicate_partialgraph_reachable_included g _ s x).
    - intro. rewrite <- (H0 x) in H3. apply reachable_foot_valid in H2.
      hnf in H2. simpl in H2. destruct H2. auto.
Qed.

Lemma subgraph_update':
  forall (g g': Graph) {rfg: ReachableFiniteGraph g} {rfg': ReachableFiniteGraph g'} (S1 S1' S2: list V),
    (unreachable_partial_spatialgraph g S1) -=- (unreachable_partial_spatialgraph g' S1') ->
    (forall x : V, In x (S1 ++ S2) -> Decidable (vvalid g x)) ->
    (forall x : V, In x (S1' ++ S2) -> Decidable (vvalid g' x)) ->
    graphs' (S1 ++ S2) g |-- graphs' S1 g * (graphs' S1' g' -* graphs' (S1' ++ S2) g').
Proof.
  intros.
  assert (forall x : V, In x S1 -> Decidable (vvalid g x)) by (intros; apply X; apply in_or_app; left; auto).
  assert (forall x : V, In x S1' -> Decidable (vvalid g' x)) by (intros; apply X0; apply in_or_app; left; auto).
  rewrite (graphs'_eq _ _ rfg X).
  rewrite (graphs'_eq _ _ rfg' X0).
  rewrite (graphs'_eq _ _ rfg X1).
  rewrite (graphs'_eq _ _ rfg' X2).
  destruct (construct_reachable_set_list g (S1 ++ S2) X) as [lgS12 [?H ?H]].
  destruct (construct_reachable_set_list g S1 X1) as [lgS1 [?H ?H]].
  destruct (construct_reachable_set_list g' S1' X2) as [lg'S1' [?H ?H]].
  destruct (construct_reachable_set_list g' (S1' ++ S2) X0) as [lg'S1'S2 [?H ?H]].
  unfold proj1_sig. apply iter_sepcon_ramification.
  exists (map (Gamma g) (subtract equiv_dec lgS12 lgS1)). split.
  + apply (reachable_subtract_perm _ (S1 ++ S2) S1); auto.
    intro y. unfold reachable_through_set. intros. destruct H8 as [s [? ?]].
    exists s. split; auto. apply in_or_app. auto.
  + assert (Sublist lgS1 lgS12). {
      intro y. rewrite <- (H1 y). rewrite <- (H3 y).
      unfold reachable_through_set. intros. destruct H8 as [s [? ?]]. exists s. split; auto.
      apply in_or_app; auto. }
    apply perm_trans with (map (Gamma g') lg'S1' ++ map (Gamma g') (subtract equiv_dec lg'S1'S2 lg'S1')).
    - apply (reachable_subtract_perm _ (S1' ++ S2) S1'); auto.
      intro y. unfold reachable_through_set. intros. destruct H9 as [s [? ?]].
      exists s. split; auto. apply in_or_app. auto.
    - apply Permutation_app_head. apply perm_trans with (map (Gamma g') (subtract equiv_dec lgS12 lgS1)).
      * apply Permutation_map. apply NoDup_Permutation.
        apply subtract_nodup; auto. apply subtract_nodup; auto.
        intros. rewrite <- !subtract_property.
        rewrite (unreachable_eq g' _ _ _ _ H7 H5 x).
        rewrite (unreachable_eq g _ _ _ _ H1 H3 x).
        destruct H as [? _].
        apply si_reachable_through_set. symmetry. auto.
      * rewrite (compcert.lib.Coqlib.list_map_exten (Gamma g') (Gamma g)). apply Permutation_refl.
        intros. unfold Gamma. f_equal.
        rewrite <- subtract_property in H9. destruct H9.
        rewrite <- (H1 x) in H9.
        assert (~ reachable_through_set g S1 x) by (intro; apply H10; rewrite <- (H3 x); auto).
        assert (vvalid (unreachable_partial_spatialgraph g S1) x). simpl. unfold predicate_vvalid.
        split; auto. destruct H9 as [? [? ?]]. apply reachable_foot_valid in H12. auto.
        destruct H as [? [? _]]. specialize (H13 _ H12). destruct H as [? [? [? ?]]].
        simpl in H15, H16. rewrite H in H12. specialize (H13 H12). simpl in H13. auto.
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
  apply subgraph_update'; auto.
Qed.

End SPATIAL_FACTS.

End GENERAL_SPATIAL_GRAPH.
