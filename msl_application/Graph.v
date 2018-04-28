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
Require Import RamifyCoq.graph.FiniteGraph.

Local Open Scope logic.

Class PointwiseGraph (V E: Type) {VE: EqDec V eq} {EE: EqDec E eq} (GV GE: Type): Type := {
  pg_sg: PreGraph V E;
  vgamma: V -> GV;
  egamma: E -> GE
}.

Arguments pg_sg {V E _ _ GV GE} _.
Arguments vgamma {V E _ _ GV GE} _ _.
Arguments egamma {V E _ _ GV GE} _ _.

Class PointwiseGraphPred (V E GV GE Pred: Type): Type := {
  vertex_at: V -> GV -> Pred;
  edge_at: E -> GE -> Pred
}.

Class PointwiseGraphBasicAssum (V E: Type) := {
  SGBA_VE: EqDec V eq;
  SGBA_EE: EqDec E eq
}.

Existing Instances SGBA_VE SGBA_EE.

Class PointwiseGraphAssum {V E GV GE Pred: Type} (SGP: PointwiseGraphPred V E GV GE Pred) {SGBA: PointwiseGraphBasicAssum V E}:= {
  SGP_ND: NatDed Pred;
  SGP_SL : SepLog Pred;
  SGP_ClSL: ClassicalSep Pred;
  SGP_CoSL: CorableSepLog Pred
}.

Existing Instances SGP_ND SGP_SL SGP_ClSL SGP_CoSL.

Class PointwiseGraphAssum_vs {V E GV GE Pred: Type} (SGP: PointwiseGraphPred V E GV GE Pred) {SGBA: PointwiseGraphBasicAssum V E} {SGA: PointwiseGraphAssum SGP} :=
  vertex_at_sep: sepcon_unique2 (@vertex_at _ _ _ _ _ SGP).

Class PointwiseGraphAssum_es {V E GV GE Pred: Type} (SGP: PointwiseGraphPred V E GV GE Pred) {SGBA: PointwiseGraphBasicAssum V E} {SGA: PointwiseGraphAssum SGP} :=
  edge_at_sep: sepcon_unique2 (@edge_at _ _ _ _ _ SGP).

Class PointwiseGraphAssum_vn {V E GV GE Pred: Type} (SGP: PointwiseGraphPred V E GV GE Pred) {SGBA: PointwiseGraphBasicAssum V E} {SGA: PointwiseGraphAssum SGP} (vnull: V) :=
  vertex_at_not_null: forall gx, @derives Pred _ (vertex_at vnull gx) FF.

Class PointwiseGraphAssum_en {V E GV GE Pred: Type} (SGP: PointwiseGraphPred V E GV GE Pred) {SGBA: PointwiseGraphBasicAssum V E} {SGA: PointwiseGraphAssum SGP} (enull: E) :=
  edge_at_not_null: forall ge, @derives Pred _ (edge_at enull ge) FF.

(*
Instance AAV {V E GV GE Pred: Type} (SGP: PointwiseGraphPred V E GV GE Pred) {SGBA: PointwiseGraphBasicAssum V E} : AbsAddr V GV.
  apply (mkAbsAddr V GV (fun x y => if equiv_dec x y then true else false)); simpl; intros.
  + destruct_eq_dec p1 p2; destruct_eq_dec p2 p1; congruence.
  + destruct_eq_dec p1 p1; destruct_eq_dec p1 p2; congruence.
Defined.

Instance AAE {V E GV GE Pred: Type} (SGP: PointwiseGraphPred V E GV GE Pred) {SGBA: PointwiseGraphBasicAssum V E} : AbsAddr E GE.
  apply (mkAbsAddr E GE (fun x y => if equiv_dec x y then true else false)); simpl; intros.
  + destruct_eq_dec p1 p2; destruct_eq_dec p2 p1; congruence.
  + destruct_eq_dec p1 p1; destruct_eq_dec p1 p2; congruence.
Defined.

Class PointwiseGraphStrongAssum {V E GV GE Pred: Type} (SGP: PointwiseGraphPred V E GV GE Pred) {SGBA: PointwiseGraphBasicAssum V E} {SGA: PointwiseGraphAssum SGP} := {
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
 *)

Class PointwiseGraphConstructor (V E DV DE DG GV GE: Type) {SGBA: PointwiseGraphBasicAssum V E}:= {
  compute_vgamma: LabeledGraph V E DV DE DG -> V -> GV;
  compute_egamma: LabeledGraph V E DV DE DG -> E -> GE
}.

Section Local_PointwiseGraphConstructor.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Class Local_PointwiseGraphConstructor (V E DV DE DG GV GE: Type) {SGBA: PointwiseGraphBasicAssum V E} {SGC: PointwiseGraphConstructor V E DV DE DG GV GE} := {
  vguard: LabeledGraph V E DV DE DG -> V -> Prop;
  compute_vgamma_local: forall (G1 G2: LabeledGraph V E DV DE DG) (x: V),
    vguard G1 x ->
    vguard G2 x ->
    vlabel G1 x = vlabel G2 x ->
    (forall e, evalid G1 e /\ src G1 e = x <-> evalid G2 e /\ src G2 e = x) ->
    (forall e, evalid G1 e -> src G1 e = x -> evalid G2 e -> src G2 e = x -> dst G1 e = dst G2 e) ->
    (forall e, evalid G1 e -> src G1 e = x -> evalid G2 e -> src G2 e = x -> elabel G1 e = elabel G2 e) ->
    compute_vgamma G1 x = compute_vgamma G2 x;
  eguard: LabeledGraph V E DV DE DG -> E -> Prop;
  compute_egamma_local: forall (G1 G2: LabeledGraph V E DV DE DG) (e: E),
    eguard G1 e ->
    eguard G2 e ->
    elabel G1 e = elabel G2 e ->
    src G1 e = src G2 e ->
    dst G1 e = dst G2 e ->
    compute_egamma G1 e = compute_egamma G2 e
}.

End Local_PointwiseGraphConstructor.

Section GENERAL_SPATIAL_GRAPH.

Context {V E GV GE: Type}.
Context {SGBA: PointwiseGraphBasicAssum V E}.

Section PURE_FACTS.

Definition vertices_identical (PV: Ensemble V): relation (PointwiseGraph V E GV GE) :=
  respectful_relation vgamma (guarded_pointwise_relation PV eq).

Definition vertices_identical0: relation (PointwiseGraph V E GV GE) :=
  vertices_identical (fun _ => True).

Definition vertices_identical2 (PV1 PV2: Ensemble V) (g1 g2: PointwiseGraph V E GV GE) : Prop :=
  Same_set PV1 PV2 /\ vertices_identical PV1 g1 g2.

Instance vertices_identical_proper: Proper (Same_set ==> eq ==> eq ==> iff) vertices_identical.
Proof.
  hnf; intros.
  hnf; intros G1 G1' ?; subst G1'.
  hnf; intros G2 G2' ?; subst G2'.
  unfold vertices_identical, respectful_relation.
  split; intros.
  + rewrite guarded_pointwise_relation_spec in H0 |- *.
    intros; apply H0.
    rewrite (app_same_set H); auto.
  + rewrite guarded_pointwise_relation_spec in H0 |- *.
    intros; apply H0.
    rewrite <- (app_same_set H); auto.
Qed.
Global Existing Instance vertices_identical_proper.

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

Definition spatialgraph_vgen (g: PointwiseGraph V E GV GE) (x: V) (a: GV) : PointwiseGraph V E GV GE := Build_PointwiseGraph _ _ _ _ _ _ (pg_sg g) (fun v => if (equiv_dec x v) then a else vgamma g v) (egamma g).

Definition single_vertex_spatialgraph (x: V) (a: GV) (default_e: GE) : PointwiseGraph V E GV GE := Build_PointwiseGraph _ _ _ _ _ _ (single_vertex_pregraph x) (fun _ => a) (fun _ => default_e).

Lemma update_self: forall (g: PointwiseGraph V E GV GE) (x: V) (d: GV), vgamma g x = d -> vertices_identical0 g (spatialgraph_vgen g x d).
Proof.
  intros.
  unfold vertices_identical0.
  rewrite vertices_identical_spec; intros.
  intros.
  simpl.
  destruct_eq_dec x x0; subst; auto.
Qed.

Lemma update_irr: forall (PV: Ensemble V) (g: PointwiseGraph V E GV GE) (x: V) (d: GV), ~ PV x -> vertices_identical PV g (spatialgraph_vgen g x d).
Proof.
  intros.
  unfold vertices_identical0.
  rewrite vertices_identical_spec; intros.
  intros.
  simpl.
  destruct_eq_dec x x0; subst; auto.
  tauto.
Qed.

Definition edges_identical (PE: Ensemble E) (g1 g2: PointwiseGraph V E GV GE) : Prop :=
  guarded_pointwise_relation PE eq (egamma g1) (egamma g2).

Definition edges_identical0 (g1 g2: PointwiseGraph V E GV GE) : Prop :=
  pointwise_relation _ eq (egamma g1) (egamma g2).

Definition edges_identical2 (PE1 PE2: Ensemble E) (g1 g2: PointwiseGraph V E GV GE) : Prop :=
  Same_set PE1 PE2 /\
  guarded_pointwise_relation PE1 eq (egamma g1) (egamma g2).

Instance edges_identical_proper: Proper (Same_set ==> eq ==> eq ==> iff) edges_identical.
Proof.
  hnf; intros. hnf; intros G1 G1' ?; subst G1'. hnf; intros G2 G2' ?; subst G2'. unfold edges_identical, respectful_relation. split; intros.
  + rewrite guarded_pointwise_relation_spec in H0 |- *. intros; apply H0. rewrite (app_same_set H); auto.
  + rewrite guarded_pointwise_relation_spec in H0 |- *. intros; apply H0. rewrite <- (app_same_set H); auto.
Qed.
Global Existing Instance edges_identical_proper.

(* TODO: add some properties for edges_identical. *)

Lemma spacialgraph_gen_vgamma: forall (g: PointwiseGraph V E GV GE) (x: V) (d: GV), vgamma (spatialgraph_vgen g x d) x = d.
Proof.
  intros.
  simpl.
  destruct_eq_dec x x; auto.
  congruence.
Qed.

End PURE_FACTS.

Section SPATIAL_FACTS.

Context {Pred: Type}.
Context {SGP: PointwiseGraphPred V E GV GE Pred}.
Context {SGA: PointwiseGraphAssum SGP}.
Notation Graph := (PointwiseGraph V E GV GE).

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

Lemma vertices_at_False: forall (g: Graph),
  vertices_at (fun _ => False) g = emp.
Proof.
  intros.
  apply pred_sepcon_False.
Qed.

Lemma vertices_at_Empty: forall (g: Graph),
  vertices_at (Empty_set _) g = emp.
Proof.
  intros.
  apply pred_sepcon_Empty.
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

Lemma vertices_at_ramif_1_stable: forall (g: Graph) (P: V -> Prop) x d,
  vgamma g x = d ->
  P x ->
  vertices_at P g |-- vertex_at x d * (vertex_at x d -* vertices_at P g).
Proof.
  intros.
  apply vertices_at_ramif_1.
  eexists.
  split; [| split].
  + apply Ensemble_join_Intersection_Complement.
    - unfold Included, Ensembles.In; intros; subst.
      auto.
    - intros.
      apply decidable_prop_decidable.
      apply equiv_dec.
  + apply Ensemble_join_Intersection_Complement.
    - unfold Included, Ensembles.In; intros; subst.
      auto.
    - intros.
      apply decidable_prop_decidable.
      apply equiv_dec.
  + reflexivity.
  + auto.
  + auto.
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
  2: {
    simpl.
    unfold graph_vcell; simpl.
    rewrite H0; auto.
  }
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

Lemma sepcon_unique_graph_vcell {SGA_vs: PointwiseGraphAssum_vs SGP}:
  sepcon_unique1 graph_vcell.
Proof.
  pose proof vertex_at_sep.
  unfold sepcon_unique1, sepcon_unique2, graph_vcell in *.
  simpl.
  intros.
  apply H.
Qed.

Lemma vertices_at_sepcon_unique_x1 {SGA_vs: PointwiseGraphAssum_vs SGP}: forall (g: Graph) x P d,
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

Lemma vertices_at_sepcon_unique_1x {SGA_vs: PointwiseGraphAssum_vs SGP}: forall (g: Graph) x P d,
  vertex_at x d * vertices_at P g |-- !! (~ P x).
Proof.
  intros.
  rewrite sepcon_comm.
  apply vertices_at_sepcon_unique_x1; auto.
Qed.

Lemma vertices_at_sepcon_unique_xx {SGA_vs: PointwiseGraphAssum_vs SGP}: forall (g1 g2: Graph) P1 P2,
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

(*
Section SPATIAL_FACTS_STRONG_ASSU.

Context {SGSA: PointwiseGraphStrongAssum SGP}.

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
 *)

End SPATIAL_FACTS.

Section SPATIAL_CONSTRUCTOR.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Context {DV DE DG: Type}.
Context {SGC: PointwiseGraphConstructor V E DV DE DG GV GE}.
Context {L_SGC: Local_PointwiseGraphConstructor V E DV DE DG GV GE}.

Section PURE_FACTS.

Definition Graph_PointwiseGraph (G: LabeledGraph V E DV DE DG) : PointwiseGraph V E GV GE :=
  Build_PointwiseGraph _ _ _ _ _ _ G (compute_vgamma G) (compute_egamma G).

Lemma GSG_VGenPreserve: forall P (G: LabeledGraph V E DV DE DG) x lx gx,
  gx = vgamma (Graph_PointwiseGraph (labeledgraph_vgen G x lx)) x ->
  Included P (vguard G) ->
  Included P (vguard (labeledgraph_vgen G x lx)) ->
  vertices_identical P (Graph_PointwiseGraph (labeledgraph_vgen G x lx)) (spatialgraph_vgen (Graph_PointwiseGraph G) x gx).
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
Lemma GSG_PartialGraphPreserve: forall P (G1 G2: LabeledGraph V E DV DE DG),
  Included P (vguard G1) ->
  Included P (vguard G2) ->
  Included P (vvalid G1) ->
  Included P (vvalid G2) ->
  ((predicate_partial_labeledgraph G1 P) ~=~ (predicate_partial_labeledgraph G2 P))%LabeledGraph ->
  vertices_identical P (Graph_PointwiseGraph G1) (Graph_PointwiseGraph G2).
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

Lemma GSG_PartialGraphPreserve2: forall P1 P2 (G1 G2: LabeledGraph V E DV DE DG),
  Included P1 (vguard G1) ->
  Included P2 (vguard G2) ->
  Included P1 (vvalid G1) ->
  Included P2 (vvalid G2) ->
  ((predicate_partial_labeledgraph G1 P1) ~=~ (predicate_partial_labeledgraph G2 P2))%LabeledGraph ->
  vertices_identical2 P1 P2 (Graph_PointwiseGraph G1) (Graph_PointwiseGraph G2).
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
Context {SGP: PointwiseGraphPred V E GV GE Pred}.
Context {SGA: PointwiseGraphAssum SGP}.
Notation Graph := (LabeledGraph V E DV DE DG).

Definition full_vertices_at (g: Graph): Pred := vertices_at (vvalid g) (Graph_PointwiseGraph g).

Definition reachable_vertices_at (x : V) (g: Graph): Pred := vertices_at (reachable g x) (Graph_PointwiseGraph g).

Definition reachable_vertices_at' (x : V) (g1 g2: Graph): Pred := vertices_at (reachable g2 x) (Graph_PointwiseGraph g1).

Definition reachable_dag_vertices_at (x: V) (g: Graph): Pred := !! localDag g x && vertices_at (reachable g x) (Graph_PointwiseGraph g).

Definition reachable_through_vertices_at (S : list V) (g : Graph): Pred := vertices_at (reachable_through_set g S) (Graph_PointwiseGraph g).

Definition reachable_through_dag_vertices_at (S : list V) (g : Graph): Pred := !! (Forall (localDag g) S) && vertices_at (reachable_through_set g S) (Graph_PointwiseGraph g).

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
  vertices_identical2 (reachable g1 x) (reachable g2 x) (Graph_PointwiseGraph g1) (Graph_PointwiseGraph g2) ->
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
  vertices_identical2 (reachable_through_set g1 S) (reachable_through_set g2 S) (Graph_PointwiseGraph g1) (Graph_PointwiseGraph g2) ->
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

Lemma va_reachable_invalid: forall(g: Graph) x, ~ vvalid g x -> reachable_vertices_at x g = emp.
Proof.
  intros.
  unfold reachable_vertices_at.
  erewrite <- vertices_at_False.
  apply vertices_at_Same_set.
  rewrite Same_set_spec; intros ?.
  split; try tauto.
  intros.
  apply reachable_head_valid in H0; auto.
Qed.

Lemma localDag_vertices_unfold: forall (g: Graph) x S, vvalid g x -> localDag g x -> step_list g x S -> reachable_vertices_at x g = vertex_at x (vgamma (Graph_PointwiseGraph g) x) * reachable_through_vertices_at S g.
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

Lemma va_reachable_dag_unfold {SGA_vs: PointwiseGraphAssum_vs SGP}: forall (g: Graph) x S d,
  vvalid g x ->
  step_list g x S ->
  vgamma (Graph_PointwiseGraph g) x = d ->
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
  + assert ((vertex_at x (vgamma (Graph_PointwiseGraph g) x): Pred) * vertices_at (reachable_through_set g S) (Graph_PointwiseGraph g)
   |-- !!localDag g x).
    - eapply derives_trans; [apply vertices_at_sepcon_unique_1x; auto |].
      apply prop_derives; intro.
      eapply localDag_step_rev; eauto.
    - rewrite (add_andp _ _ H2); normalize.
      apply derives_refl'.
      symmetry; apply localDag_vertices_unfold; auto.
Qed.

Lemma va_reachable_dag_update_unfold {SGA_vs: PointwiseGraphAssum_vs SGP}: forall (g: Graph) x S d d',
  vvalid g x ->
  step_list g x S ->
  vgamma (Graph_PointwiseGraph (labeledgraph_vgen g x d)) x = d' ->
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
  rewrite (add_andp _ _ (vertices_at_sepcon_unique_1x (Graph_PointwiseGraph g) _ _ d')).
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
  vgamma (Graph_PointwiseGraph g) x = gx ->
  vvalid g x ->
  @derives Pred _
    (reachable_vertices_at x g)
    (vertex_at x gx * (vertex_at x gx -* reachable_vertices_at x g)).
Proof.
  intros.
  subst.
  unfold reachable_vertices_at.
  apply vertices_at_ramif_1_stable; auto.
  apply reachable_refl; auto.
Qed.

Lemma va_reachable_root_update_ramify: forall (g: Graph) (x: V) (lx: DV) (gx gx': GV),
  vvalid g x ->
  vgamma (Graph_PointwiseGraph g) x = gx ->
  vgamma (Graph_PointwiseGraph (labeledgraph_vgen g x lx)) x = gx' ->
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

Lemma va_reachable_internal_stable_ramify: forall (g: Graph) (x y: V) (gy: GV),
  vvalid g y ->
  vgamma (Graph_PointwiseGraph g) y = gy ->
  reachable g x y ->
  @derives _ _
    (reachable_vertices_at x g)
    (vertex_at y gy *
      (vertex_at y gy -* reachable_vertices_at x g)).
Proof.
  intros.
  subst.
  apply vertices_at_ramif_1_stable; auto.
Qed.

Lemma va_labeledgraph_add_edge_eq: forall (g: Graph) e s d data,
  ~ evalid g e ->
  let g' := labeledgraph_add_edge g e s d data in
(*  vertices_identical (Intersection V (vvalid g) (fun x : V => s <> x))
     (Graph_PointwiseGraph g) (Graph_PointwiseGraph g') -> *)
  Included (Intersection _ (vvalid g) (fun x => s <> x)) (vguard g) ->
  Included (Intersection _ (vvalid g') (fun x => s <> x)) (vguard g') ->
  vertices_at (Intersection _ (vvalid g) (fun x => s <> x)) (Graph_PointwiseGraph g) = vertices_at (Intersection _ (vvalid g') (fun x => s <> x)) (Graph_PointwiseGraph g').
Proof.
  intros.
  apply vertices_at_vertices_identical2.
  split; [simpl; reflexivity |].
  rewrite vertices_identical_spec; intros.
  apply compute_vgamma_local.
  + apply H0; auto.
  + apply H1; auto.
  + reflexivity.
  + intros.
    simpl.
    unfold addValidFunc, updateEdgeFunc.
    rewrite Intersection_spec in H2.
    destruct H2.
    destruct_eq_dec e e0.
    - subst e0; tauto.
    - assert (e0 <> e) by congruence; tauto.
  + simpl; unfold addValidFunc, updateEdgeFunc; intros.
    destruct_eq_dec e e0.
    - subst e0; exfalso; tauto.
    - reflexivity.
  + simpl; unfold addValidFunc, updateEdgeFunc, update_elabel; intros.
    destruct_eq_dec e e0.
    - subst e0; exfalso; tauto.
    - reflexivity.
Qed.

Lemma partialgraph_update:
  forall (g g': Graph) (S1 S1' S2: list V),
    (vertices_identical2 (reachable_through_set (predicate_partialgraph g (Intersection _ (vvalid g) (Complement _ (reachable_through_set g S1)))) S2) (reachable_through_set (predicate_partialgraph g' (Intersection _ (vvalid g') (Complement _ (reachable_through_set g' S1')))) S2) (Graph_PointwiseGraph g) (Graph_PointwiseGraph g')) ->
    Included (reachable_through_set (predicate_partialgraph g (Intersection _ (vvalid g) (Complement _ (reachable_through_set g S1)))) S2) (vguard g) ->
    Included (reachable_through_set (predicate_partialgraph g' (Intersection _ (vvalid g') (Complement _ (reachable_through_set g' S1')))) S2) (vguard g') ->
    reachable_through_vertices_at (S1 ++ S2) g |-- reachable_through_vertices_at S1 g * (reachable_through_vertices_at S1' g' -* reachable_through_vertices_at (S1' ++ S2) g').
Proof.
  intros.
  unfold reachable_through_vertices_at.
  apply vertices_at_ramif_x.
  exists (reachable_through_set (predicate_partialgraph g (Intersection _ (vvalid g) (Complement _ (reachable_through_set g S1)))) S2).
  split; [| split].
  + split.
    - intros.
      rewrite <- (unreachable_eq' g S1 S2).
      rewrite <- reachable_through_set_app. tauto. (* TODO: This tauto use LEM automatically. *)
    - intros.
      rewrite <- (unreachable_eq' g S1 S2) in H3.
      tauto.
  + split.
    - intros.
      destruct H as [? _].
      rewrite (app_same_set H).
      rewrite <- (unreachable_eq' g' S1' S2).
      rewrite <- reachable_through_set_app; tauto.
    - intros.
      destruct H as [? _].
      rewrite (app_same_set H) in H3.
      rewrite <- (unreachable_eq' g' S1' S2) in H3.
      tauto.
  + destruct H; auto.
Qed.

(*
(* TODO: resume these lemmas *)

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
 *)

(*

Context {SGSA: PointwiseGraphStrongAssum SGP}.

Fixpoint graphs (l : list V) (g: Graph) :=
  match l with
    | nil => emp
    | v :: l' => reachable_vertices_at v g ⊗ graphs l' g
  end.

Lemma graphs_app: forall (g : Graph) S1 S2, graphs (S1 ++ S2) g = graphs S1 g ⊗ graphs S2 g.
Proof.
  intros. induction S1; simpl.
  + rewrite ocon_comm, ocon_emp. auto.
  + rewrite IHS1. rewrite ocon_assoc. auto.
Qed.

Lemma graphs_graphs': forall S (g: Graph) {rfg: ReachableFiniteGraph g}
  (V_DEC: forall x : V, In x S -> Decidable (vvalid g x)),
  graphs S g = reachable_through_vertices_at S g.
Proof.
  induction S; intros until g; intros rfg V_DEC.
  + unfold graphs. unfold reachable_through_vertices_at, vertices_at, pred_sepcon. apply pred_ext.
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
    unfold reachable_through_vertices_at, reachable_vertices_at, vertices_at, pred_sepcon. clear IHS. apply pred_ext.
    - normalize_overlap. intros. rename x into la.
      normalize_overlap. rename x into lS. normalize_overlap.
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup la (sepcon_unique_graph_cell (Graph_PointwiseGraph g)))).
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup lS (sepcon_unique_graph_cell (Graph_PointwiseGraph g)))).
      normalize_overlap.
      rewrite (iter_sepcon_ocon equiv_dec); auto. apply (exp_right (nodup equiv_dec (la ++ lS))).
      apply andp_right; [apply andp_right |].
      * apply prop_right.
        unfold reachable_set_list in *.
        unfold reachable_list in *. intros.
        rewrite nodup_In.
        rewrite reachable_through_set_eq.
        specialize (H1 x). specialize (H x).
        split; intro; [apply in_app_or in H3 | apply in_or_app];
        destruct H3; [left | right | left | right]; tauto.
      * apply prop_right.
        apply NoDup_nodup.
      * auto.
      * apply precise_graph_cell.
      * apply joinable_graph_cell.
    - normalize. intro l; intros. assert (In a (a :: S)) by apply in_eq.
      destruct (construct_reachable_list g a) as [la [? ?]]; [apply V_DEC; left; auto |].
      normalize_overlap. apply (exp_right la).
      destruct (construct_reachable_set_list g S) as [lS [? ?]]; [intros; apply V_DEC; right; auto |].
      normalize_overlap. apply (exp_right lS). normalize_overlap.
      rewrite (add_andp _ _ (iter_sepcon_unique_nodup l (sepcon_unique_graph_cell (Graph_PointwiseGraph g)))).
      normalize. rewrite (iter_sepcon_ocon equiv_dec); auto.
      2: apply precise_graph_cell.
      2: apply joinable_graph_cell.
      rewrite iter_sepcon_permutation with (l2 := nodup equiv_dec (la ++ lS)); auto.
      apply NoDup_Permutation; auto. apply NoDup_nodup.
      intros. rewrite nodup_In. clear -H H2 H5.
      specialize (H x). specialize (H2 x). specialize (H5 x). rewrite H.
      rewrite reachable_through_set_eq. rewrite in_app_iff. tauto.
Qed.

Lemma graph_unfold:
  forall (g: Graph) {rfg: ReachableFiniteGraph g} x S
         (V_DEC: forall x : V, In x S -> Decidable (vvalid g x)),
    vvalid g x ->
    step_list g x S ->
    reachable_vertices_at x g = vertex_at x (vgamma (Graph_PointwiseGraph g) x) ⊗ graphs S g.
Proof.
  intros. rewrite graphs_graphs'; auto. unfold reachable_vertices_at. unfold reachable_through_vertices_at.
  change (vertex_at x (vgamma (Graph_PointwiseGraph g) x)) with (graph_vcell (Graph_PointwiseGraph g) x).
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
    Decidable (vvalid g x) -> precise (reachable_vertices_at x g).
Proof.
  intros. unfold reachable_vertices_at. unfold vertices_at. rewrite pred_sepcon_eq.
  apply (precise_exp_iter_sepcon).
  + apply sepcon_unique_graph_cell.
  + destruct (construct_reachable_list g x H) as [l [? ?]].
    left; exists l. intuition.
  + apply precise_graph_cell.
  + intros. apply NoDup_Permutation; auto. 
    destruct H0, H1. split; intros; specialize (H0 x0); specialize (H1 x0); intuition.
Qed.

Lemma subgraph_update:
  forall (g g': Graph) {rfg: ReachableFiniteGraph g} {rfg': ReachableFiniteGraph g'} (S1 S1' S2: list V),
    (forall x : V, In x (S1 ++ S2) -> Decidable (vvalid g x)) ->
    (forall x : V, In x (S1' ++ S2) -> Decidable (vvalid g' x)) ->
    vertices_identical2
     (reachable_through_set
        (predicate_partialgraph g
           (Intersection V (vvalid g)
              (Complement V (reachable_through_set g S1)))) S2)
     (reachable_through_set
        (predicate_partialgraph g'
           (Intersection V (vvalid g')
              (Complement V (reachable_through_set g' S1')))) S2)
     (Graph_PointwiseGraph g) (Graph_PointwiseGraph g') ->
    Included
     (reachable_through_set
        (predicate_partialgraph g
           (Intersection V (vvalid g)
              (Complement V (reachable_through_set g S1)))) S2) 
     (vguard g) ->
    Included
     (reachable_through_set
        (predicate_partialgraph g'
           (Intersection V (vvalid g')
              (Complement V (reachable_through_set g' S1')))) S2) 
     (vguard g') ->
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
