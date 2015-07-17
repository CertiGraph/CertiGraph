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
Require Import RamifyCoq.graph.marked_graph.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_gen.
Require Import Coq.Logic.Classical.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Local Open Scope logic.

Class SpatialGraph (V E DV DE: Type): Type := {
  pg: PreGraph V E;
  vgamma: V -> DV;
  egamma: E -> DE
}.

Arguments vgamma {V E DV DE} _ _.
Arguments egamma {V E DV DE} _ _.

Coercion pg : SpatialGraph >-> PreGraph.

Definition validly_identical {V E DV DE} (g1 g2: SpatialGraph V E DV DE) : Prop :=
  g1 ~=~ g2 /\
  (forall v, @vvalid _ _ g1 v -> @vvalid _ _ g2 v -> vgamma g1 v = vgamma g2 v) /\
  (forall e, @evalid _ _ g1 e -> @evalid _ _ g2 e -> egamma g1 e = egamma g2 e).

Notation "g1 '-=-' g2" := (validly_identical g1 g2) (at level 1).

Lemma vi_refl {V E DV DE}: forall (g : SpatialGraph V E DV DE), g -=- g.
Proof. intros. split; auto. apply si_refl. Qed.

Lemma vi_sym {V E DV DE}: forall (g1 g2 : SpatialGraph V E DV DE), g1 -=- g2 -> g2 -=- g1.
Proof.
  intros. destruct H as [? [? ?]]. split; [|split]; intros.
  + apply si_sym; auto.
  + specialize (H0 _ H3 H2). auto.
  + specialize (H1 _ H3 H2). auto.
Qed.

Lemma vi_trans {V E DV DE}: forall (g1 g2 g3: SpatialGraph V E DV DE), g1 -=- g2 -> g2 -=- g3 -> g1 -=- g3.
Proof.
  intros. destruct H as [? [? ?]]. destruct H0 as [? [? ?]].
  split; [| split]; intros.
  + apply si_trans with g2; auto.
  + assert (@vvalid V E g2 v) by (destruct H; rewrite <- H; auto).
    specialize (H1 _ H5 H7). specialize (H3 _ H7 H6). transitivity (vgamma g2 v); auto.
  + assert (@evalid V E g2 e) by (destruct H as [_ [? _]]; rewrite <- H; auto).
    specialize (H2 _ H5 H7). specialize (H4 _ H7 H6). transitivity (egamma g2 e); auto.
Qed.

Add Parametric Relation {V E DV DE} : (SpatialGraph V E DV DE) validly_identical
    reflexivity proved by vi_refl
    symmetry proved by vi_sym
    transitivity proved by vi_trans as vi_equal.
  
Definition predicate_sub_spatialgraph {V E DV DE: Type} (g: SpatialGraph V E DV DE: Type) (p: V -> Prop) :=
  Build_SpatialGraph V E DV DE (predicate_subgraph g p) (vgamma g) (egamma g).

Definition unreachable_sub_spatialgraph {V E DV DE: Type}
           (g: SpatialGraph V E DV DE: Type) (S : list V) : SpatialGraph V E DV DE :=
  predicate_sub_spatialgraph g (fun n => ~ reachable_through_set g S n).

Class SpatialGraphPred (V E DV DE Pred: Type): Type := {
  vertex_at: V -> DV -> Pred;
  edge_at: E -> DE -> Pred
}.

Class SpatialGraphAssum {V E DV DE Pred: Type} (SGP: SpatialGraphPred V E DV DE Pred) := {
  SGP_ND: NatDed Pred;
  SGP_SL : SepLog Pred;
  SGP_ClSL: ClassicalSep Pred;
  SGP_CoSL: CorableSepLog Pred
}.

Existing Instances SGP_ND SGP_SL SGP_ClSL SGP_CoSL.

Class SpatialGraphStrongAssum {V E DV DE Pred: Type} (SGP: SpatialGraphPred V E DV DE Pred) := {
  SGA: SpatialGraphAssum SGP;
  SGP_PSL: PreciseSepLog Pred;
  SGP_OSL: OverlapSepLog Pred;
  SGP_DSL: DisjointedSepLog Pred;
  SGP_COSL: CorableOverlapSepLog Pred;

  AAV: AbsAddr V DV;
  VSELF_CONFLICT: forall x, @addr_conflict _ _ AAV x x = true;
  AAE: AbsAddr E DE;
  VP_MSL: MapstoSepLog AAV vertex_at;
  VP_sMSL: StaticMapstoSepLog AAV vertex_at;
  EP_MSL: MapstoSepLog AAE edge_at;
  EP_sMSL: StaticMapstoSepLog AAE edge_at
}.

Existing Instances SGA SGP_PSL SGP_OSL SGP_DSL SGP_COSL VP_MSL VP_sMSL EP_MSL EP_sMSL.

Section SpatialGraph.

  Context {V E DV DE Pred: Type}.
  Context {SGP: SpatialGraphPred V E DV DE Pred}.
  (* Context {SGA: SpatialGraphAssum SGP}. *)
  Context {SGSA: SpatialGraphStrongAssum SGP}.
  Notation Graph := (SpatialGraph V E DV DE).

  Definition graph_cell (g: Graph) (v : V) : Pred := vertex_at v (vgamma g v).

  Lemma sepcon_unique_graph_cell: forall g, sepcon_unique (graph_cell g).
  Proof.
    repeat intro. unfold graph_cell.
    apply (@mapsto_conflict _ _ _ _ _ _ _ _ _ _ _ VP_sMSL).
    apply VSELF_CONFLICT.
  Qed.
  
  Definition graph (x : V) (g: Graph) : Pred :=
    EX l : list V, !!reachable_list g x l && iter_sepcon l (graph_cell g).

  Fixpoint graphs (l : list V) (g: Graph) :=
    match l with
      | nil => emp
      | v :: l' => graph v g ⊗ graphs l' g
    end.

  Definition graphs' (S : list V) (g : Graph) :=
    EX l: list V, !!reachable_set_list pg S l &&
                    iter_sepcon l (graph_cell g).

  Lemma graphs_unfold: forall S g, graphs S g = graphs' S g.
  Proof.
    induction S; intros.
    + unfold graphs. unfold graphs'. apply pred_ext.
      - apply (exp_right nil). simpl. apply andp_right; auto.
        apply prop_right. intro x. split; intros.
        * unfold reachable_through_set in H. destruct H as [s [? _]]. inversion H.
        * inversion H.
      - normalize. intro l; intros. destruct l; simpl; auto.
        specialize (H v). assert (In v (v :: l)) by apply in_eq.
        rewrite <- H in H0. unfold reachable_through_set in H0.
        destruct H0 as [s [? _]]. inversion H0.
    + unfold graphs. fold graphs. rewrite IHS.
      unfold graphs'. unfold graph. clear IHS. apply pred_ext.
      - normalize_overlap. intros. rename x into la.
        normalize_overlap. rename x into lS. normalize_overlap.
        rewrite (add_andp _ _ (iter_sepcon_unique_nodup la (sepcon_unique_graph_cell g))).
        rewrite (add_andp _ _ (iter_sepcon_unique_nodup lS (sepcon_unique_graph_cell g))).
        normalize_overlap.
        (* rewrite (iter_sepcon_ocon t_eq_dec); auto. apply (exp_right (remove_dup t_eq_dec (la ++ lS))). *)
  Abort.

End SpatialGraph.
