Require Import Coq.Logic.Classical.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.msl.ramification_lemmas.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.Equivalence_ext.
Require Import RamifyCoq.lib.Morphisms_ext.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.msl_ext.ramification_lemmas.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.dag.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Local Open Scope logic.

Class SpatialGraph (V E: Type) {VE: EqDec V eq} {EE: EqDec E eq} (GV GE: Type): Type := {
  pg_sg: PreGraph V E;
  vgamma: V -> GV;
  egamma: E -> GE
}.

Arguments pg_sg {V E _ _ GV GE} _.
Arguments vgamma {V E _ _ GV GE} _ _.
Arguments egamma {V E _ _ GV GE} _ _.

Class SpatialGraphPred (V E GV GE Pred: Type): Type := {
  vertex_at: V -> GV -> Pred;
  edge_at: E -> GE -> Pred
}.

Class SpatialGraphBasicAssum (V E: Type) := {
  SGBA_VE: EqDec V eq;
  SGBA_EE: EqDec E eq
}.

Existing Instances SGBA_VE SGBA_EE.

Class SpatialGraphAssum {V E GV GE Pred: Type} (SGP: SpatialGraphPred V E GV GE Pred) {SGBA: SpatialGraphBasicAssum V E}:= {
  SGP_ND: NatDed Pred;
  SGP_SL : SepLog Pred;
  SGP_ClSL: ClassicalSep Pred;
  SGP_CoSL: CorableSepLog Pred
}.

Existing Instances SGP_ND SGP_SL SGP_ClSL SGP_CoSL.

Class SpatialGraphAssum_vs {V E GV GE Pred: Type} (SGP: SpatialGraphPred V E GV GE Pred) {SGBA: SpatialGraphBasicAssum V E} {SGA: SpatialGraphAssum SGP} :=
  vertex_at_sep: sepcon_unique2 (@vertex_at _ _ _ _ _ SGP).

Class SpatialGraphAssum_es {V E GV GE Pred: Type} (SGP: SpatialGraphPred V E GV GE Pred) {SGBA: SpatialGraphBasicAssum V E} {SGA: SpatialGraphAssum SGP} :=
  edge_at_sep: sepcon_unique2 (@edge_at _ _ _ _ _ SGP).

Class SpatialGraphAssum_vn {V E GV GE Pred: Type} (SGP: SpatialGraphPred V E GV GE Pred) {SGBA: SpatialGraphBasicAssum V E} {SGA: SpatialGraphAssum SGP} (vnull: V) :=
  vertex_at_not_null: forall gx, @derives Pred _ (vertex_at vnull gx) FF.

Class SpatialGraphAssum_en {V E GV GE Pred: Type} (SGP: SpatialGraphPred V E GV GE Pred) {SGBA: SpatialGraphBasicAssum V E} {SGA: SpatialGraphAssum SGP} (enull: E) :=
  edge_at_not_null: forall ge, @derives Pred _ (edge_at enull ge) FF.

Instance AAV {V E GV GE Pred: Type} (SGP: SpatialGraphPred V E GV GE Pred) {SGBA: SpatialGraphBasicAssum V E} : AbsAddr V GV.
  apply (mkAbsAddr V GV (fun x y => if equiv_dec x y then true else false)); simpl; intros.
  + destruct_eq_dec p1 p2; destruct_eq_dec p2 p1; congruence.
  + destruct_eq_dec p1 p1; destruct_eq_dec p1 p2; congruence.
Defined.

Instance AAE {V E GV GE Pred: Type} (SGP: SpatialGraphPred V E GV GE Pred) {SGBA: SpatialGraphBasicAssum V E} : AbsAddr E GE.
  apply (mkAbsAddr E GE (fun x y => if equiv_dec x y then true else false)); simpl; intros.
  + destruct_eq_dec p1 p2; destruct_eq_dec p2 p1; congruence.
  + destruct_eq_dec p1 p1; destruct_eq_dec p1 p2; congruence.
Defined.

Class SpatialGraphStrongAssum {V E GV GE Pred: Type} (SGP: SpatialGraphPred V E GV GE Pred) {SGBA: SpatialGraphBasicAssum V E} {SGA: SpatialGraphAssum SGP} := {
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

Class SpatialGraphConstructor (V E DV DE GV GE: Type) {SGBA: SpatialGraphBasicAssum V E}:= {
  compute_vgamma: LabeledGraph V E DV DE -> V -> GV;
  compute_egamma: LabeledGraph V E DV DE -> E -> GE
}.

Section Local_SpatialGraphConstructor.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Class Local_SpatialGraphConstructor (V E DV DE GV GE: Type) {SGBA: SpatialGraphBasicAssum V E} {SGC: SpatialGraphConstructor V E DV DE GV GE} := {
  vguard: LabeledGraph V E DV DE -> V -> Prop;
  compute_vgamma_local: forall (G1 G2: LabeledGraph V E DV DE) (x: V),
    vguard G1 x ->
    vguard G2 x ->
    vlabel G1 x = vlabel G2 x ->
    (forall e, evalid G1 e /\ src G1 e = x <-> evalid G2 e /\ src G2 e = x) ->
    (forall e, evalid G1 e -> src G1 e = x -> evalid G2 e -> src G2 e = x -> dst G1 e = dst G2 e) ->
    (forall e, evalid G1 e -> src G1 e = x -> evalid G2 e -> src G2 e = x -> elabel G1 e = elabel G2 e) ->
    compute_vgamma G1 x = compute_vgamma G2 x;
  eguard: LabeledGraph V E DV DE -> E -> Prop;
  compute_egamma_local: forall (G1 G2: LabeledGraph V E DV DE) (e: E),
    eguard G1 e ->
    eguard G2 e ->
    elabel G1 e = elabel G2 e ->
    src G1 e = src G2 e ->
    dst G1 e = dst G2 e ->
    compute_egamma G1 e = compute_egamma G2 e
}.

End Local_SpatialGraphConstructor.

Section GENERAL_SPATIAL_GRAPH.

Context {V E GV GE: Type}.
Context {SGBA: SpatialGraphBasicAssum V E}.

Section PURE_FACTS.

Definition vertices_identical (PV: Ensemble V): relation (SpatialGraph V E GV GE) :=
  respectful_relation vgamma (guarded_pointwise_relation PV eq).

Definition vertices_identical0: relation (SpatialGraph V E GV GE) :=
  vertices_identical (fun _ => True).

Definition vertices_identical2 (PV1 PV2: Ensemble V) (g1 g2: SpatialGraph V E GV GE) : Prop :=
  Same_set PV1 PV2 /\ vertices_identical PV1 g1 g2.

Lemma vertices_identical_spec: forall PV g1 g2,
  vertices_identical PV g1 g2 <-> (forall x, PV x -> vgamma g1 x = vgamma g2 x).
Proof.
  intros.
  unfold vertices_identical, respectful_relation.
  rewrite guarded_pointwise_relation_spec; intros.
  tauto.
Qed.
 
Lemma vertices_identical2_spec: forall PV1 PV2 g1 g2,
  vertices_identical2 PV1 PV2 g1 g2 <->
  Same_set PV1 PV2 /\
  (forall x, PV1 x -> PV2 x -> vgamma g1 x = vgamma g2 x).
Proof.
  intros.
  unfold vertices_identical2.
  rewrite vertices_identical_spec.
  assert (Same_set PV1 PV2 -> (forall x, PV1 x -> PV2 x)) by (rewrite Same_set_spec; intros; firstorder).
  firstorder.
Qed.
 
Instance vertices_identical_Equivalence (PV: Ensemble V): Equivalence (vertices_identical PV).
  apply resp_Equivalence.
  apply guarded_pointwise_equivalence.
  apply eq_equivalence.
Defined.

Instance vertices_identical0_Equivalence: Equivalence vertices_identical0.
  apply vertices_identical_Equivalence.
Defined.

(* vertices_identical2 is not a equivalence relation, because it is not reflexive. *)
Global Existing Instance vertices_identical0_Equivalence.
Global Existing Instance vertices_identical_Equivalence.

Lemma vertices_identical_weaken: forall PV1 PV2 g1 g2,
  Included PV2 PV1 ->
  vertices_identical PV1 g1 g2 ->
  vertices_identical PV2 g1 g2.
Proof.
  intros.
  unfold vertices_identical, respectful_relation in *.
  eapply guarded_pointwise_relation_weaken; eauto.
Qed.

Lemma vertices_identical0_vertices_identical: forall PV g1 g2,
  vertices_identical0 g1 g2 ->
  vertices_identical PV g1 g2.
Proof.
  intros.
  eapply vertices_identical_weaken; eauto.
  hnf; intros.
  exact I.
Qed.

Lemma vertices_identical0_is_vertices_identical: forall g1 g2,
  vertices_identical0 g1 g2 <-> vertices_identical (fun _ => True) g1 g2.
Proof.
  reflexivity.
Qed.

Lemma vertices_identical_vertices_identical2: forall PV g1 g2,
  vertices_identical PV g1 g2 <-> vertices_identical2 PV PV g1 g2.
Proof.
  intros.
  unfold vertices_identical2.
  assert (Same_set PV PV) by reflexivity.
  tauto.
Qed.

Definition spatialgraph_vgen (g: SpatialGraph V E GV GE) (x: V) (a: GV) : SpatialGraph V E GV GE := Build_SpatialGraph _ _ _ _ _ _ (pg_sg g) (fun v => if (equiv_dec x v) then a else vgamma g v) (egamma g).

Definition single_vertex_spatialgraph (x: V) (a: GV) (default_e: GE) : SpatialGraph V E GV GE := Build_SpatialGraph _ _ _ _ _ _ (single_vertex_pregraph x) (fun _ => a) (fun _ => default_e).

Lemma update_self: forall (g: SpatialGraph V E GV GE) (x: V) (d: GV), vgamma g x = d -> vertices_identical0 g (spatialgraph_vgen g x d).
Proof.
  intros.
  unfold vertices_identical0.
  rewrite vertices_identical_spec; intros.
  intros.
  simpl.
  destruct_eq_dec x x0; subst; auto.
Qed.

Lemma update_irr: forall (PV: Ensemble V) (g: SpatialGraph V E GV GE) (x: V) (d: GV), ~ PV x -> vertices_identical PV g (spatialgraph_vgen g x d).
Proof.
  intros.
  unfold vertices_identical0.
  rewrite vertices_identical_spec; intros.
  intros.
  simpl.
  destruct_eq_dec x x0; subst; auto.
  tauto.
Qed.

Definition edges_identical (PE: Ensemble E) (g1 g2: SpatialGraph V E GV GE) : Prop :=
  guarded_pointwise_relation PE eq (egamma g1) (egamma g2).

Definition edges_identical0 (g1 g2: SpatialGraph V E GV GE) : Prop :=
  pointwise_relation _ eq (egamma g1) (egamma g2).

Definition edges_identical2 (PE1 PE2: Ensemble E) (g1 g2: SpatialGraph V E GV GE) : Prop :=
  Same_set PE1 PE2 /\
  guarded_pointwise_relation PE1 eq (egamma g1) (egamma g2).

(* TODO: add some properties for edges_identical. *)

Lemma spacialgraph_gen_vgamma: forall (g: SpatialGraph V E GV GE) (x: V) (d: GV), vgamma (spatialgraph_vgen g x d) x = d.
Proof.
  intros.
  simpl.
  destruct_eq_dec x x; auto.
  congruence.
Qed.

End PURE_FACTS.

Section SPATIAL_FACTS.

Context {Pred: Type}.
Context {SGP: SpatialGraphPred V E GV GE Pred}.
Context {SGA: SpatialGraphAssum SGP}.
Notation Graph := (SpatialGraph V E GV GE).

Definition graph_vcell (g: Graph) (v : V) : Pred := vertex_at v (vgamma g v).
Definition graph_ecell (g: Graph) (e : E) : Pred := edge_at e (egamma g e).
Definition vertices_at (P: V -> Prop) (g: Graph): Pred := pred_sepcon P (graph_vcell g).
Definition edges_at (P: E -> Prop) (g: Graph): Pred := pred_sepcon P (graph_ecell g).

Definition Gamma (g: Graph) x := (x, vgamma g x).

Definition Graph_vcell (p : V * GV) := vertex_at (fst p) (snd p).

Lemma Gamma_injective: forall g x y, Gamma g x = Gamma g y -> x = y.
Proof. intros. unfold Gamma in H. inversion H. auto. Qed.

Lemma vertices_at_vertices_identical2: forall (g1 g2: Graph) (P1 P2: V -> Prop),
  vertices_identical2 P1 P2 g1 g2 ->
  vertices_at P1 g1 = vertices_at P2 g2.
Proof.
  intros.
  apply pred_sepcon_strong_proper.
  + destruct H.
    rewrite Same_set_spec in H; auto.
  + intros.
    unfold graph_vcell.
    f_equal.
    destruct H.
    rewrite vertices_identical_spec in H2.
    apply H2; auto.
Qed.

Lemma vertices_at_vertices_identical: forall (g1 g2 : Graph) (P : V -> Prop),
  vertices_identical P g1 g2 -> vertices_at P g1 = vertices_at P g2.
Proof.
  intros.
  apply vertices_at_vertices_identical2.
  split; [reflexivity | auto].
Qed.

Lemma vertices_at_vertices_identical0: forall (g1 g2 : Graph) (P : V -> Prop),
  vertices_identical0 g1 g2 -> vertices_at P g1 = vertices_at P g2.
Proof.
  intros.
  apply vertices_at_vertices_identical.
  apply vertices_identical0_vertices_identical; auto.
Qed.

Lemma vertices_at_Same_set: forall (g : Graph) (P Q: V -> Prop),
  Same_set P Q -> vertices_at P g = vertices_at Q g.
Proof.
  intros.
  apply vertices_at_vertices_identical2.
  split; [auto | reflexivity].
Qed.

(*************************************

Ramification Lemmas

*************************************)

Lemma vertices_at_ramif_1Q: forall {A: Type} (Pure: A -> Prop) (g: Graph) (P: V -> Prop) x (g': A -> Graph) (P': A -> V -> Prop) (x': A -> V),
  (exists F,
     Prop_join (eq x) F P /\
     (forall a, Pure a -> Prop_join (eq (x' a)) F (P' a)) /\
     (forall a, Pure a -> vertices_identical F g (g' a))) ->
  vertices_at P g |-- vertex_at x (vgamma g x) *
    (ALL a: A, !! Pure a -->
      (vertex_at (x' a) (vgamma (g' a) (x' a)) -* vertices_at (P' a) (g' a))).
Proof.
  intros.
  unfold vertices_at.
  change (@vertex_at _ _ _ _ _ SGP x (vgamma g x)) with (graph_vcell g x).
  RAMIF_Q'.formalize.
  change ((fun a : A => vertex_at (x' a) (vgamma (g' a) (x' a)))) with
    ((fun a : A => graph_vcell (g' a) (x' a))).
  simpl.
  apply (pred_sepcon_ramif_1Q Pure P P' (graph_vcell g) (fun a => graph_vcell (g' a)) x x').
  destruct H as [F [? [? ?]]].
  exists F; split; [| split]; auto.
  intros.
  unfold graph_vcell; f_equal.
  specialize (H1 a H2).
  rewrite vertices_identical_spec in H1.
  apply H1; auto.
Qed.

Lemma vertices_at_ramif_xQ: forall {A: Type} (Pure: A -> Prop) (g: Graph) (G L: V -> Prop) (g': A -> Graph) (L' G': A -> V -> Prop),
  (exists F,
     Prop_join L F G /\
     (forall a, Pure a -> Prop_join (L' a) F (G' a)) /\
     (forall a, Pure a -> vertices_identical F g (g' a))) ->
  vertices_at G g |-- vertices_at L g *
    (ALL a: A, !! Pure a -->
      (vertices_at (L' a) (g' a) -* vertices_at (G' a) (g' a))).
Proof.
  intros.
  unfold vertices_at.
  apply pred_sepcon_ramif_xQ.
  destruct H as [F [? [? ?]]].
  exists F; split; [| split]; auto.
  intros.
  unfold graph_vcell; f_equal.
  specialize (H1 a H2).
  rewrite vertices_identical_spec in H1.
  apply H1; auto.
Qed.

Lemma vertices_at_ramif_1: forall (g g': Graph) (P P': V -> Prop) x x' d d',
  (exists F,
     Prop_join (eq x) F P /\
     Prop_join (eq x') F P' /\
     vertices_identical F g g') ->
  vgamma g x = d ->
  vgamma g' x' = d' ->
  vertices_at P g |-- vertex_at x d * (vertex_at x' d' -* vertices_at P' g').
Proof.
  intros.
  subst.
  change (@vertex_at _ _ _ _ _ SGP x (vgamma g x)) with (graph_vcell g x).
  change (@vertex_at _ _ _ _ _ SGP x' (vgamma g' x')) with (graph_vcell g' x').
  apply pred_sepcon_ramif_1.
  destruct H as [F [? [? ?]]].
  exists F; split; [| split]; auto.
  intros.
  unfold graph_vcell; f_equal.
  rewrite vertices_identical_spec in H1.
  apply H1; auto.
Qed.

Lemma vertices_at_ramif_x: forall (g g': Graph) (G L L' G': V -> Prop),
  (exists F,
     Prop_join L F G /\
     Prop_join L' F G' /\
     vertices_identical F g g') ->
  vertices_at G g |-- vertices_at L g * (vertices_at L' g' -* vertices_at G' g').
Proof.
  intros.
  apply pred_sepcon_ramif_x.
  destruct H as [F [? [? ?]]].
  exists F; split; [| split]; auto.
  intros.
  unfold graph_vcell; f_equal.
  rewrite vertices_identical_spec in H1.
  apply H1; auto.
Qed.

Lemma vertices_at1: forall (g: Graph) P x0 d,
  (forall x, P x <-> x0 = x) ->
  vgamma g x0 = d ->
  vertices_at P g = vertex_at x0 d.
Proof.
  intros.
  replace (@vertex_at _ _ _ _ _ SGP x0 d) with (graph_vcell g x0).
  Focus 2. {
    simpl.
    unfold graph_vcell; simpl.
    rewrite H0; auto.
  } Unfocus.
  erewrite vertices_at_Same_set.
  + apply pred_sepcon1.
  + rewrite Same_set_spec.
    intro x; specialize (H x).
    assert (x = x0 <-> x0 = x) by (split; congruence).
    tauto.
Qed.

Lemma vertices_at_sepcon_x1: forall (g: Graph) x P P' d,
  Prop_join P (eq x) P' ->
  vgamma g x = d ->
  vertices_at P g * vertex_at x d = vertices_at P' g.
Proof.
  intros.
  subst d.
  change (vertex_at x (vgamma g x)) with (graph_vcell g x).
  destruct H.
  symmetry; apply pred_sepcon_sepcon1.
  + firstorder.
  + firstorder.
Qed.

Lemma vertices_at_sepcon_1x: forall (g: Graph) x P P' d,
  Prop_join P (eq x) P' ->
  vgamma g x = d ->
  vertex_at x d * vertices_at P g = vertices_at P' g.
Proof.
  intros.
  rewrite sepcon_comm.
  apply vertices_at_sepcon_x1; auto.
Qed.

Lemma vertices_at_sepcon_xx: forall (g: Graph) P1 P2 P,
  Prop_join P1 P2 P ->
  vertices_at P1 g * vertices_at P2 g = vertices_at P g.
Proof.
  intros.
  apply pred_sepcon_sepcon; auto.
Qed.

Lemma sepcon_unique_graph_vcell {SGA_vs: SpatialGraphAssum_vs SGP}:
  sepcon_unique1 graph_vcell.
Proof.
  pose proof vertex_at_sep.
  unfold sepcon_unique1, sepcon_unique2, graph_vcell in *.
  simpl.
  intros.
  apply H.
Qed.

Lemma vertices_at_sepcon_unique_x1 {SGA_vs: SpatialGraphAssum_vs SGP}: forall (g: Graph) x P d,
  vertices_at P g * vertex_at x d |-- !! (~ P x).
Proof.
  intros.
  apply not_prop_right; intros.
  eapply derives_trans; [apply sepcon_derives; [apply pred_sepcon_prop_true; eauto | apply derives_refl] |].
  unfold graph_vcell.
  rewrite sepcon_comm, <- sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply vertex_at_sep | apply derives_refl] |].
  normalize.
Qed.

Lemma vertices_at_sepcon_unique_1x {SGA_vs: SpatialGraphAssum_vs SGP}: forall (g: Graph) x P d,
  vertex_at x d * vertices_at P g |-- !! (~ P x).
Proof.
  intros.
  rewrite sepcon_comm.
  apply vertices_at_sepcon_unique_x1; auto.
Qed.

Lemma vertices_at_sepcon_unique_xx {SGA_vs: SpatialGraphAssum_vs SGP}: forall (g1 g2: Graph) P1 P2,
  vertices_at P1 g1 * vertices_at P2 g2 |-- !! Disjoint _ P1 P2.
Proof.
  intros.
  eapply derives_trans with (!! (forall x, P1 x -> P2 x -> False)).
  2: apply prop_derives; rewrite Disjoint_spec; auto.
  rewrite prop_forall_allp.
  apply allp_right; intro x.
  rewrite !prop_impl_imp.
  apply imp_andp_adjoint; normalize.
  apply imp_andp_adjoint; normalize.
  eapply derives_trans; [apply sepcon_derives; apply pred_sepcon_prop_true; eauto |].
  rewrite sepcon_assoc, (sepcon_comm TT), !sepcon_assoc.
  rewrite TT_sepcon_TT, <- sepcon_assoc.
  unfold graph_vcell.
  eapply derives_trans; [apply sepcon_derives; [apply vertex_at_sep | apply derives_refl] |].
  normalize.
Qed.

Lemma neg_pure_from_vertices_at: forall (g: Graph) (P Q: V -> Prop),
  (forall (x: V) (gx: GV), Q x -> @derives _ SGP_ND (vertex_at x gx) FF) ->
  vertices_at P g |-- !! (Disjoint _ P Q).
Proof.
  intros.
  unfold vertices_at.
  apply neg_pure_from_pred_sepcon.
  intros.
  unfold graph_vcell.
  apply H; auto.
Qed.

Section SPATIAL_FACTS_STRONG_ASSU.

Context {SGSA: SpatialGraphStrongAssum SGP}.

Lemma precise_graph_cell: forall g v, precise (graph_vcell g v).
Proof. intros. unfold graph_vcell. apply (@mapsto_precise _ _ _ _ _ _ _ _ VP_MSL). Qed.  

Lemma sepcon_unique_graph_cell: forall g, sepcon_unique1 (graph_vcell g).
Proof.
  repeat intro. unfold graph_vcell.
  apply (@mapsto_conflict _ _ _ _ _ _ _ _ _ _ _ VP_sMSL).
  simpl.
  destruct_eq_dec x x; congruence.
Qed.

Lemma joinable_graph_cell : forall g, joinable (graph_vcell g).
Proof.
  intros. unfold joinable; intros. unfold graph_vcell. apply (@disj_mapsto _ _ (AAV SGP) _ _ _ _ _ _ VP_MSL _ VP_sMSL).
  simpl.
  destruct_eq_dec x y; congruence.
Qed.  

End SPATIAL_FACTS_STRONG_ASSU.

End SPATIAL_FACTS.

Section SPATIAL_CONSTRUCTOR.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Context {DV DE: Type}.
Context {SGC: SpatialGraphConstructor V E DV DE GV GE}.
Context {L_SGC: Local_SpatialGraphConstructor V E DV DE GV GE}.

Section PURE_FACTS.

Definition Graph_SpatialGraph (G: LabeledGraph V E DV DE) : SpatialGraph V E GV GE :=
  Build_SpatialGraph _ _ _ _ _ _ G (compute_vgamma G) (compute_egamma G).

Lemma GSG_VGenPreserve: forall P (G: LabeledGraph V E DV DE) x lx gx,
  gx = vgamma (Graph_SpatialGraph (labeledgraph_vgen G x lx)) x ->
  Included P (vguard G) ->
  Included P (vguard (labeledgraph_vgen G x lx)) ->
  vertices_identical P (Graph_SpatialGraph (labeledgraph_vgen G x lx)) (spatialgraph_vgen (Graph_SpatialGraph G) x gx).
Proof.
  intros.
  rewrite vertices_identical_spec.
  intros.
  simpl.
  destruct_eq_dec x x0.
  + subst; auto.
  + apply compute_vgamma_local; auto.
    - apply H1; auto.
    - apply H0; auto.
    - simpl.
      unfold update_vlabel.
      destruct_eq_dec x x0; congruence.
    - simpl; intros.
      tauto.
Qed.

(* The counterpart of subgraph version is not true. *)
Lemma GSG_PartialGraphPreserve: forall P (G1 G2: LabeledGraph V E DV DE),
  Included P (vguard G1) ->
  Included P (vguard G2) ->
  Included P (vvalid G1) ->
  Included P (vvalid G2) ->
  ((predicate_partial_labeledgraph G1 P) ~=~ (predicate_partial_labeledgraph G2 P))%LabeledGraph ->
  vertices_identical P (Graph_SpatialGraph G1) (Graph_SpatialGraph G2).
Proof.
  intros.
  unfold vertices_identical, respectful_relation.
  rewrite guarded_pointwise_relation_spec.
  intros.
  simpl.
  rename H4 into HP.
  unfold Included, Ensembles.In in H, H0, H1, H2.
  destruct H3 as [[? [? [? ?]]] [? ?]].
  simpl in H3, H4, H5, H6, H7, H8.
  unfold predicate_weak_evalid, predicate_vvalid in H3, H4, H5, H6, H7, H8.
  apply compute_vgamma_local; auto.
  + intros.
    split; intros [? ?]; subst; firstorder.
  + intros; subst.
    firstorder.
  + intros; subst.
    firstorder.
Qed.

Lemma GSG_PartialGraphPreserve2: forall P1 P2 (G1 G2: LabeledGraph V E DV DE),
  Included P1 (vguard G1) ->
  Included P2 (vguard G2) ->
  Included P1 (vvalid G1) ->
  Included P2 (vvalid G2) ->
  ((predicate_partial_labeledgraph G1 P1) ~=~ (predicate_partial_labeledgraph G2 P2))%LabeledGraph ->
  vertices_identical2 P1 P2 (Graph_SpatialGraph G1) (Graph_SpatialGraph G2).
Proof.
  intros.
  assert (Same_set P1 P2).
  + destruct H3 as [[? _] _].
    rewrite Same_set_spec; unfold pointwise_relation.
    simpl in H3; unfold predicate_vvalid in H3.
    unfold Included, Ensembles.In in H1, H2.
    firstorder.
  + rewrite <- H4 in *.
    split; auto.
    apply GSG_PartialGraphPreserve; auto.
Qed.

End PURE_FACTS.

Section SPATIAL_FACTS.

Context {Pred: Type}.
Context {SGP: SpatialGraphPred V E GV GE Pred}.
Context {SGA: SpatialGraphAssum SGP}.
Notation Graph := (LabeledGraph V E DV DE).

Definition full_vertices_at (g: Graph): Pred := vertices_at (vvalid g) (Graph_SpatialGraph g).

Definition reachable_vertices_at (x : V) (g: Graph): Pred := vertices_at (reachable g x) (Graph_SpatialGraph g).

Definition reachable_dag_vertices_at (x: V) (g: Graph): Pred := !! localDag g x && vertices_at (reachable g x) (Graph_SpatialGraph g).

Definition reachable_through_vertices_at (S : list V) (g : Graph): Pred := vertices_at (reachable_through_set g S) (Graph_SpatialGraph g).

Definition reachable_through_dag_vertices_at (S : list V) (g : Graph): Pred := !! (Forall (localDag g) S) && vertices_at (reachable_through_set g S) (Graph_SpatialGraph g).

Lemma va_reachable_reachable_through: forall g x, reachable_vertices_at x g = reachable_through_vertices_at (x :: nil) g.
Proof.
  intros.
  unfold reachable_vertices_at, reachable_through_vertices_at.
  apply pred_sepcon_proper; [| reflexivity].
  intro y.
  pose proof reachable_through_set_single g x y.
  tauto.
Qed.

Lemma va_reachable_vertices_identical2: forall (g1 g2 : Graph) x,
  vertices_identical2 (reachable g1 x) (reachable g2 x) (Graph_SpatialGraph g1) (Graph_SpatialGraph g2) ->
  reachable_vertices_at x g1 = reachable_vertices_at x g2.
Proof.
  intros.
  apply vertices_at_vertices_identical2; auto.
Qed.

Lemma va_reachable_partialgraph_eq: forall (g1 g2 : Graph) x,
  Included (reachable g1 x) (vguard g1) ->
  Included (reachable g2 x) (vguard g2) ->
  ((predicate_partial_labeledgraph g1 (reachable g1 x)) ~=~ (predicate_partial_labeledgraph g2 (reachable g2 x)))%LabeledGraph ->
  reachable_vertices_at x g1 = reachable_vertices_at x g2.
Proof.
  intros. apply va_reachable_vertices_identical2.
  apply GSG_PartialGraphPreserve2; auto.
  + hnf; intros.
    apply reachable_foot_valid in H2; auto.
  + hnf; intros.
    apply reachable_foot_valid in H2; auto.
Qed.

Lemma va_reachable_eq: forall (g1 g2 : Graph) x,
  Included (reachable g1 x) (vguard g1) ->
  Included (reachable g2 x) (vguard g2) ->
  (g1 ~=~ g2)%LabeledGraph ->
  reachable_vertices_at x g1 = reachable_vertices_at x g2.
Proof.
  intros.
  apply va_reachable_partialgraph_eq; auto.
  rewrite H1 at 1.
  destruct H1 as [? _].
  rewrite H1.
  reflexivity.
Qed.

Lemma va_reachable_through_vertices_identical2: forall (g1 g2 : Graph) S,
  vertices_identical2 (reachable_through_set g1 S) (reachable_through_set g2 S) (Graph_SpatialGraph g1) (Graph_SpatialGraph g2) ->
  reachable_through_vertices_at S g1 = reachable_through_vertices_at S g2.
Proof.
  intros.
  apply vertices_at_vertices_identical2; auto.
Qed.

Lemma va_reachable_through_partialgraph_eq: forall (g1 g2 : Graph) S,
  Included (reachable_through_set g1 S) (vguard g1) ->
  Included (reachable_through_set g2 S) (vguard g2) ->
  ((predicate_partial_labeledgraph g1 (reachable_through_set g1 S)) ~=~ (predicate_partial_labeledgraph g2 (reachable_through_set g2 S)))%LabeledGraph ->
  reachable_through_vertices_at S g1 = reachable_through_vertices_at S g2.
Proof.
  intros. apply va_reachable_through_vertices_identical2.
  apply GSG_PartialGraphPreserve2; auto.
  + hnf; intros.
    apply reachable_through_set_foot_valid in H2; auto.
  + hnf; intros.
    apply reachable_through_set_foot_valid in H2; auto.
Qed.

Lemma va_reachable_through_eq: forall (g1 g2 : Graph) S,
  Included (reachable_through_set g1 S) (vguard g1) ->
  Included (reachable_through_set g2 S) (vguard g2) ->
  (g1 ~=~ g2)%LabeledGraph ->
  reachable_through_vertices_at S g1 = reachable_through_vertices_at S g2.
Proof.
  intros.
  apply va_reachable_through_partialgraph_eq; auto.
  rewrite H1 at 1.
  destruct H1 as [? _].
  rewrite H1.
  reflexivity.
Qed.

Lemma localDag_vertices_unfold: forall (g: Graph) x S, vvalid g x -> localDag g x -> step_list g x S -> reachable_vertices_at x g = vertex_at x (vgamma (Graph_SpatialGraph g) x) * reachable_through_vertices_at S g.
Proof.
  intros.
  symmetry.
  apply vertices_at_sepcon_1x; auto.
  apply localDag_reachable_spec'; auto.
Qed.

Lemma localDag_graph_gen_step_list: forall (g: Graph) x S d,
  vvalid g x ->
  localDag g x ->
  step_list g x S ->
  Included (reachable_through_set g S) (vguard g) ->
  Included (reachable_through_set g S) (vguard (labeledgraph_vgen g x d)) ->
  reachable_through_vertices_at S g = reachable_through_vertices_at S (labeledgraph_vgen g x d).
Proof.
  intros.
  apply va_reachable_through_partialgraph_eq; auto.
  split; [reflexivity | split; intros; [| reflexivity]].
  simpl.
  unfold update_vlabel.
  destruct_eq_dec x v; [exfalso | auto].
  destruct (localDag_reachable_spec g x S H H0 H1).
  destruct H4.
  symmetry in H6; revert H6.
  apply H8; auto.
Qed.

Lemma va_reachable_dag_unfold {SGA_vs: SpatialGraphAssum_vs SGP}: forall (g: Graph) x S d,
  vvalid g x ->
  step_list g x S ->
  vgamma (Graph_SpatialGraph g) x = d ->
  reachable_dag_vertices_at x g = vertex_at x d * reachable_through_dag_vertices_at S g.
Proof.
  intros.
  subst.
  unfold reachable_dag_vertices_at, reachable_through_dag_vertices_at.
  apply pred_ext; normalize.
  + apply andp_right.
    - apply prop_right.
      rewrite Forall_forall; intros.
      eapply local_dag_step; eauto.
      rewrite (H0 x0) in H2; auto.
    - apply derives_refl'.
      apply localDag_vertices_unfold; auto.
  + assert ((vertex_at x (vgamma (Graph_SpatialGraph g) x): Pred) * vertices_at (reachable_through_set g S) (Graph_SpatialGraph g)
   |-- !!localDag g x).
    - eapply derives_trans; [apply vertices_at_sepcon_unique_1x; auto |].
      apply prop_derives; intro.
      eapply localDag_step_rev; eauto.
    - rewrite (add_andp _ _ H2); normalize.
      apply derives_refl'.
      symmetry; apply localDag_vertices_unfold; auto.
Qed.

Lemma va_reachable_dag_update_unfold {SGA_vs: SpatialGraphAssum_vs SGP}: forall (g: Graph) x S d d',
  vvalid g x ->
  step_list g x S ->
  vgamma (Graph_SpatialGraph (labeledgraph_vgen g x d)) x = d' ->
  Included (reachable_through_set g S) (vguard g) ->
  Included (reachable_through_set g S) (vguard (labeledgraph_vgen g x d)) ->
  reachable_dag_vertices_at x (labeledgraph_vgen g x d) = vertex_at x d' * reachable_through_dag_vertices_at S g.
Proof.
  intros.
  erewrite va_reachable_dag_unfold by eauto.
  unfold reachable_through_dag_vertices_at.
  normalize.
  f_equal.
  rewrite (add_andp _ _ (vertices_at_sepcon_unique_1x _ _ _ _)).
  rewrite (add_andp _ _ (vertices_at_sepcon_unique_1x (Graph_SpatialGraph g) _ _ d')).
  rewrite !(andp_comm _ (!! _)).
  apply andp_prop_ext; [reflexivity |].
  intros.
  f_equal.
  apply va_reachable_through_partialgraph_eq; auto.
  split; [reflexivity | split; intros; [| reflexivity]].
  simpl.
  unfold update_vlabel.
  destruct_eq_dec x v; [exfalso | auto].
  subst v.
  simpl in H6; clear H5.
  destruct H6 as [? [y [? ?]]].
  simpl in H4.
  apply H4.
  exists y; split; auto.
Qed.

Lemma va_reachable_root_stable_ramify: forall (g: Graph) (x: V) (gx: GV),
  vgamma (Graph_SpatialGraph g) x = gx ->
  vvalid g x ->
  @derives Pred _
    (reachable_vertices_at x g)
    (vertex_at x gx * (vertex_at x gx -* reachable_vertices_at x g)).
Proof.
  intros.
  subst.
  unfold reachable_vertices_at.
  apply vertices_at_ramif_1; auto.
  eexists.
  split; [| split].
  + apply Ensemble_join_Intersection_Complement.
    - unfold Included, Ensembles.In; intros; subst.
      apply reachable_refl; auto.
    - intros.
      apply decidable_prop_decidable.
      apply equiv_dec.
  + apply Ensemble_join_Intersection_Complement.
    - unfold Included, Ensembles.In; intros; subst.
      apply reachable_refl; auto.
    - intros.
      apply decidable_prop_decidable.
      apply equiv_dec.
  + reflexivity.
Qed.

Lemma va_reachable_root_update_ramify: forall (g: Graph) (x: V) (lx: DV) (gx gx': GV),
  vvalid g x ->
  vgamma (Graph_SpatialGraph g) x = gx ->
  vgamma (Graph_SpatialGraph (labeledgraph_vgen g x lx)) x = gx' ->
  Included (Intersection V (reachable g x) (Complement V (eq x))) (vguard g) ->
  Included (Intersection V (reachable g x) (Complement V (eq x))) (vguard (labeledgraph_vgen g x lx)) ->
  @derives Pred _
    (reachable_vertices_at x g)
    (vertex_at x gx *
      (vertex_at x gx' -* reachable_vertices_at x (labeledgraph_vgen g x lx))).
Proof.
  intros.
  subst.
  unfold reachable_vertices_at.
  apply vertices_at_ramif_1; auto.
  eexists.
  split; [| split].
  + apply Ensemble_join_Intersection_Complement.
    - unfold Included, Ensembles.In; intros; subst.
      apply reachable_refl; auto.
    - intros.
      apply decidable_prop_decidable.
      apply equiv_dec.
  + apply Ensemble_join_Intersection_Complement.
    - unfold Included, Ensembles.In; intros; subst.
      apply reachable_refl; auto.
    - intros.
      apply decidable_prop_decidable.
      apply equiv_dec.
  + apply GSG_PartialGraphPreserve; auto.
    - unfold Included, Ensembles.In; intros; subst.
      rewrite Intersection_spec in H0.
      destruct H0 as [? _].
      apply reachable_foot_valid in H0; auto.
    - unfold Included, Ensembles.In; intros; subst.
      rewrite Intersection_spec in H0.
      destruct H0 as [? _].
      apply reachable_foot_valid in H0; auto.
    - apply si_stronger_partial_labeledgraph_simple with (Complement V (eq x)).
      * apply Intersection2_Included, Included_refl.
      * apply lg_vgen_stable.
Qed.

(* TODO: move this one into subgraph2.v *)
Lemma unreachable_eq': forall (g : Graph) (S1 S2 : list V),
    forall x, reachable_through_set g (S1 ++ S2) x /\ ~ reachable_through_set g S1 x <-> reachable_through_set (unreachable_partial_labeledgraph g S1) S2 x.
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
(* TODO: resume these lemmas *)

Lemma partialgraph_update:
  forall (g g': Graph) (S1 S1' S2: list V),
    (unreachable_partial_labeledgraph g S1) ~=~ (unreachable_partial_labeledgraph g' S1')%LabeledGraph ->
    Included (reachable_through_set (unreachable_partialgraph g S1) S2) (vguard g) ->
    Included (reachable_through_set (unreachable_partialgraph g' S1') S2) (vguard g') ->
    reachable_through_vertices_at (S1 ++ S2) g |-- reachable_through_vertices_at S1 g * (reachable_through_vertices_at S1' g' -* reachable_through_vertices_at (S1' ++ S2) g').
Proof.
  intros.
  unfold reachable_through_vertices_at.
  apply vertices_at_ramif_x.
  exists (reachable_through_set (unreachable_partialgraph g S1) S2).
  split; [| split].
  + split.
    - intros.
      rewrite <- (unreachable_eq' g S1 S2).
      rewrite <- reachable_through_set_app; tauto. (* TODO: This tauto use LEM automatically. *)
    - intros.
      rewrite <- (unreachable_eq' g S1 S2) in H3.
      tauto.
  + split.
    - intros.
      destruct H as [? _].
      rewrite H.
      rewrite <- (unreachable_eq' g' S1' S2).
      rewrite <- reachable_through_set_app; tauto.
    - intros.
      destruct H as [? _].
      rewrite H in H3.
      rewrite <- (unreachable_eq' g' S1' S2) in H3.
      tauto.
  + apply GSG_PartialGraphPreserve.
    - auto.
    - destruct H as [? _]; rewrite H; auto.
    - hnf; unfold Ensembles.In; intros.
      rewrite <- (unreachable_eq' g S1 S2) in H2.
      destruct H2.
      eapply reachable_through_set_foot_valid; eauto.
    - hnf; unfold Ensembles.In; intros.
      destruct H as [? _].
      rewrite H in H2.
      rewrite <- (unreachable_eq' g' S1' S2) in H2.
      destruct H2.
      eapply reachable_through_set_foot_valid; eauto.
    - 

Lemma full_vertices_at_ramify1: forall (g: Graph) x d d',
  vvalid g x ->
  vgamma g x = d ->
  full_vertices_at g |-- vertex_at x d * (vertex_at x d' -* full_vertices_at (spatialgraph_vgen g x d')).
Proof.
  intros.
  apply vertices_at_ramify1; auto.
Qed.

Lemma graph_ramify_aux0: forall (g: Graph) {rfg: ReachableFiniteGraph g} x d d',
  vvalid g x -> vgamma g x = d ->
  graph x g |-- vertex_at x d * (vertex_at x d' -* graph x (spatialgraph_vgen g x d')).
Proof.
  intros.
  apply vertices_at_ramify1; auto.
  apply reachable_refl; auto.
Qed.


Context {SGSA: SpatialGraphStrongAssum SGP}.

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

Lemma graph_unfold:
  forall (g: Graph) {rfg: ReachableFiniteGraph g} x S
         (V_DEC: forall x : V, In x S -> Decidable (vvalid g x)),
    vvalid g x ->
    step_list g x S ->
    graph x g = vertex_at x (vgamma g x) ⊗ graphs S g.
Proof.
  intros. rewrite graphs_graphs'; auto. unfold graph. unfold graphs'.
  change (vertex_at x (vgamma g x)) with (graph_vcell g x).
  assert (forall y, reachable g x y <-> x = y \/ reachable_through_set g S y). {
    intros. rewrite (reachable_ind' g x S); intuition.
  } symmetry. apply pred_sepcon_ocon1; intros.
  + apply SGBA_VE.
  + apply RFG_reachable_through_set_decicable; auto.
  + specialize (H1 a). intuition.
  + apply precise_graph_cell.
  + apply joinable_graph_cell.
Qed.

Lemma precise_graph: forall (g: Graph) {rfg: ReachableFiniteGraph g} x,
    Decidable (vvalid g x) -> precise (graph x g).
Proof.
  intros. unfold graph. unfold vertices_at. rewrite pred_sepcon_eq.
  apply (precise_exp_iter_sepcon).
  + apply sepcon_unique_graph_cell.
  + destruct (construct_reachable_list g x H) as [l [? ?]].
    left; exists l. intuition.
  + apply precise_graph_cell.
  + intros. apply eq_as_set_permutation; auto. 1: apply SGBA_VE.
    destruct H0, H1. hnf. unfold Sublist.
    split; intros; specialize (H0 a); specialize (H1 a); intuition.
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

*)
End SPATIAL_FACTS.

End SPATIAL_CONSTRUCTOR.

End GENERAL_SPATIAL_GRAPH.
