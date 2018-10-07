Require Import RamifyCoq.lib.Ensembles_ext.
Require Import Coq.Lists.List.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_gen.
Require Export RamifyCoq.graph.BiGraph.
Require Export RamifyCoq.graph.MathGraph.
Require Export RamifyCoq.graph.FiniteGraph.
Require Import RamifyCoq.msl_application.Graph.
Require Import Coq.Logic.Classical.

Local Open Scope logic.

Inductive LR :=
  | L
  | R.

Class pPointwiseGraph_Graph_Bi: Type := {
  addr: Type;
  null: addr;
  SGBA: PointwiseGraphBasicAssum addr (addr * LR)
}.

Existing Instance SGBA.

Definition is_null_SGBA {pSGGB: pPointwiseGraph_Graph_Bi} : DecidablePred addr := (existT (fun P => forall a, {P a} + {~ P a}) (fun x => x = null) (fun x => SGBA_VE x null)).

Class sPointwiseGraph_Graph_Bi {pSGG_Bi: pPointwiseGraph_Graph_Bi} (DV DE: Type): Type := {
  pred: Type;
  SGP: PointwiseGraphPred addr (addr * LR) (DV * addr * addr) unit pred;
  SGA: PointwiseGraphAssum SGP;
  SGAvs: PointwiseGraphAssum_vs SGP;
  SGAvn: PointwiseGraphAssum_vn SGP null
}.

Existing Instances SGP SGA SGAvs.

Section GRAPH_BI.

(*********************************************************

Pure Facts Part

*********************************************************)

Context {pSGG_Bi: pPointwiseGraph_Graph_Bi}.
Context {DV DE DG: Type}.

Class BiMaFin (g: PreGraph addr (addr * LR)) := {
  bi: BiGraph g (fun x => (x, L)) (fun x => (x, R));
  ma: MathGraph g is_null_SGBA;
  fin: FiniteGraph g
}.

Definition Graph := (GeneralGraph addr (addr * LR) DV DE DG (fun g => BiMaFin (pg_lg g))).
Definition LGraph := (LabeledGraph addr (addr * LR) DV DE DG).
Definition SGraph := (PointwiseGraph addr (addr * LR) (DV * addr * addr) unit).

Instance SGC_Bi: PointwiseGraphConstructor addr (addr * LR) DV DE DG (DV * addr * addr) unit.
Proof.
  refine (Build_PointwiseGraphConstructor _ _ _ _ _ _ _ SGBA _ _).
  + exact (fun G v => (vlabel G v, dst (pg_lg G) (v, L), dst (pg_lg G) (v, R))).
  + exact (fun _ _ => tt).
Defined.

Instance L_SGC_Bi: Local_PointwiseGraphConstructor addr (addr * LR) DV DE DG (DV * addr * addr) unit.
Proof.
  refine (Build_Local_PointwiseGraphConstructor _ _ _ _ _ _ _ SGBA SGC_Bi
    (fun G v => evalid (pg_lg G) (v, L) /\ evalid (pg_lg G) (v, R) /\
                src (pg_lg G) (v, L) = v /\ src (pg_lg G) (v, R) = v) _
    (fun _ _ => True) _).
  + intros.
    simpl.
    destruct H as [? [? [? ?]]], H0 as [? [? [? ?]]].
    f_equal; [f_equal |]; auto.
  + intros; simpl.
    auto.
Defined.

Global Existing Instances SGC_Bi L_SGC_Bi.

Definition Graph_LGraph (G: Graph): LGraph := lg_gg G.
Definition LGraph_SGraph (G: LGraph): SGraph := Graph_PointwiseGraph G.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_PointwiseGraph: SGraph >-> PointwiseGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Instance biGraph (G: Graph): BiGraph G (fun x => (x, L)) (fun x => (x, R)) :=
  @bi G (@sound_gg _ _ _ _ _ _ _ _ G).

Instance maGraph(G: Graph): MathGraph G is_null_SGBA :=
  @ma G (@sound_gg _ _ _ _ _ _ _ _ G).

Instance finGraph (G: Graph): FiniteGraph G :=
  @fin G (@sound_gg _ _ _ _ _ _ _ _ G).

Instance RGF (G: Graph): ReachableFiniteGraph G.
  apply Build_ReachableFiniteGraph.
  intros.
  apply finite_reachable_computable with (is_null := is_null_SGBA) in H.
  + destruct H as [l [? ?]].
    exists l; auto.
  + apply maGraph.
  + apply (LocalFiniteGraph_FiniteGraph G), finGraph.
  + apply (FiniteGraph_EnumCovered G), finGraph.
Defined.

Definition Graph_vgen (G: Graph) (x: addr) (d: DV) : Graph :=
  generalgraph_vgen G x d (sound_gg G).

Definition Graph_egen (G: Graph) (e: addr * LR) (d: DE) : Graph :=
  generalgraph_egen G e d (sound_gg G).

Definition empty_BiGraph: BiGraph (empty_pregraph (fun e => fst e) (fun e => null)) (fun x => (x, L)) (fun x => (x, R)).
  constructor.
  + intros ? [].
  + intros ? ? [].
Defined.
      
Definition empty_MathGraph: MathGraph (empty_pregraph (fun e => fst e) (fun e => null)) is_null_SGBA.
  apply (Build_MathGraph _ is_null_SGBA).
  + intros ? [].
  + intros ? [].
Defined.

Definition empty_FiniteGraph: FiniteGraph (empty_pregraph (fun e => fst e) (fun e => null)).
  constructor.
  + exists nil.
    split; [constructor | intros].
    simpl.
    unfold Ensembles.In; reflexivity. 
  + exists nil.
    split; [constructor | intros].
    simpl.
    unfold Ensembles.In; reflexivity. 
Defined.

Definition empty_sound: BiMaFin (empty_pregraph (fun e => fst e) (fun e => null)) :=
  Build_BiMaFin _ empty_BiGraph empty_MathGraph empty_FiniteGraph.

Definition empty_Graph (default_v: DV) (default_e: DE) (default_g : DG) : Graph :=
  Build_GeneralGraph _ _ _ _ (empty_labeledgraph (fun e => fst e) (fun e => null) default_v default_e default_g) empty_sound.

Definition is_BiMaFin (g: LGraph): Prop := exists X: BiMaFin (pg_lg g), True.

Definition is_guarded_BiMaFin (PV: addr -> Prop) (PE: addr * LR -> Prop) (g: LGraph): Prop := is_BiMaFin (gpredicate_sub_labeledgraph PV PE g).

Definition left_right_sound: forall (g: Graph) (x: addr) lr,
  vvalid g x ->
  src g (x, lr) = x.
Proof.
  intros.
  destruct lr.
  + apply (@left_sound _ _ _ _ _ _ g (biGraph _) x); auto.
  + apply (@right_sound _ _ _ _ _ _ g (biGraph _) x); auto.
Qed.

Definition left_right_sound0: forall (g: Graph) (x: addr) lr,
  evalid g (x, lr) ->
  src g (x, lr) = x.
Proof.
  intros.
  destruct lr.
  + destruct (@valid_graph _ _ _ _ g _ (maGraph _) (x, L) H) as [? _].
    pose proof (@only_two_edges _ _ _ _ g _ _ (biGraph _) _ (x, L) H0).
    simpl in H1.
    destruct H1 as [? _].
    specialize (H1 (conj eq_refl H)).
    destruct H1; inversion H1.
    rewrite <- ! H3; auto.
  + destruct (@valid_graph _ _ _ _ g _ (maGraph _) (x, R) H) as [? _].
    pose proof (@only_two_edges _ _ _ _ g _ _ (biGraph _) _ (x, R) H0).
    simpl in H1.
    destruct H1 as [? _].
    specialize (H1 (conj eq_refl H)).
    destruct H1; inversion H1.
    rewrite <- ! H3; auto.
Qed.

Lemma weak_valid_vvalid_dec: forall (g : Graph) (x: addr),
  weak_valid g x -> Decidable (vvalid g x).
Proof.
  intros.
  apply null_or_valid in H.
  destruct H; [right | left]; auto.
  pose proof valid_not_null g x; tauto.
Qed.
Hint Resolve weak_valid_vvalid_dec : GraphDec.

Lemma invalid_null: forall (g: Graph), ~ vvalid g null.
Proof.
  intros.
  pose proof @valid_not_null _ _ _ _ g _ (maGraph g) null.
  cbv beta delta [is_null_SGBA] in H; simpl in H.
  tauto.
Qed.

Lemma vvalid_vguard: forall (g: Graph) x,
  vvalid g x ->
  vguard g x.
Proof.
  intros.
  pose proof biGraph g.
  simpl.
  split; [| split; [| split]].
  + apply left_valid with (x0 := x) in H0; auto.
  + apply right_valid with (x0 := x) in H0; auto.
  + pose proof (proj2 (only_two_edges x (x, L) H)).
    specialize (H1 (or_introl eq_refl)).
    tauto.
  + pose proof (proj2 (only_two_edges x (x, R) H)).
    specialize (H1 (or_intror eq_refl)).
    tauto.
Qed.

Definition Graph_gen_left_null (G : Graph) (x : addr) : Graph.
Proof.
  refine (generalgraph_gen_dst G (x, L) null _).
  assert (weak_valid G null) by (left; reflexivity).
  refine (Build_BiMaFin _ (gen_dst_preserve_bi G (x, L) null _)
                        (gen_dst_preserve_math G (x, L) null ma H)
                        (gen_dst_preserve_finite G (x, L) null (finGraph G))).
Defined.

Definition Graph_gen_right_null (G : Graph) (x : addr) : Graph.
Proof.
  refine (generalgraph_gen_dst G (x, R) null _).
  assert (weak_valid G null) by (left; reflexivity).
  refine (Build_BiMaFin _ (gen_dst_preserve_bi G (x, R) null _)
                        (gen_dst_preserve_math G (x, R) null ma H)
                        (gen_dst_preserve_finite G (x, R) null (finGraph G))).
Defined.

Ltac s_rewrite p :=
  let H := fresh "H" in
  pose proof p as H;
  simpl in H;
  rewrite H;
  clear H.

Lemma Graph_vgen_vgamma: forall (G: Graph) (x: addr) (d d': DV) l r,
  vgamma G x = (d, l, r) ->
  vgamma (Graph_vgen G x d') x = (d', l, r).
Proof.
  intros.
  simpl in H |- *.
  inversion H; subst.
  f_equal.
  f_equal.
  unfold update_vlabel.
  destruct_eq_dec x x; [| congruence].
  auto.
Qed.

(*
Lemma Graph_gen_spatial_spec: forall (G: Graph) (x: addr) (d d': DV) l r,
  vgamma G x = (d, l, r) ->
  (Graph_gen G x d') -=- (spatialgraph_vgen G x (d', l, r)).
Proof.
  intros.
  split; [reflexivity | split; [| auto]].
  simpl in *; intros.
  simpl in *; unfold update_vlabel.
  destruct_eq_dec x v; subst.
  + inversion H; subst; f_equal; f_equal.
  + auto.
Qed.

(* TODO: This lemma is not true. They are not even structural identical.
   But we should change the definition of validly identical or some how fix this. *)
Lemma Graph_gen_left_null_spatial_spec: forall (G: Graph) (x: addr) (d : DV) l r,
    vgamma G x = (d, l, r) ->
    (Graph_gen_left_null G x) -=- (spatialgraph_vgen G x (d, null, r)).
Proof.
  intros.
  split; [|split; [| auto]].
  + split; [|split; [|split]]; intros; simpl; intuition.
    unfold Graph_gen_left_null in H0. simpl in H0. unfold spatialgraph_vgen in H1. simpl in H1.
    unfold update_dst. destruct_eq_dec (x, L) e; auto. admit.
  + intros. simpl. unfold Graph_gen_left_null. unfold generalgraph_gen_dst. simpl.
    unfold update_dst. destruct_eq_dec (x, L) (v, L).
    - destruct_eq_dec (x, L) (v, R). inversion H3. inversion H2. destruct_eq_dec v v. 2: exfalso; auto.
      simpl in H. inversion H; subst; auto.
    - destruct_eq_dec (x, L) (v, R). inversion H3. destruct_eq_dec x v.
      * subst. exfalso; auto.
      * auto.
Qed.
*)

Lemma weak_valid_si: forall (g1 g2: Graph) n, g1 ~=~ g2 -> (weak_valid g1 n <-> weak_valid g2 n).
Proof.
  intros.
  unfold weak_valid.
  destruct H as [? _].
  rewrite H.
  reflexivity.
Qed.

Lemma gamma_step: forall (g : Graph) x (d: DV) (l r: addr), vvalid g x -> vgamma g x = (d, l, r) -> forall y, step g x y <-> y = l \/ y = r.
Proof.
  intros. simpl in H0; inversion H0; subst.
  rewrite step_spec; split; intros.
  + destruct H1 as [e [? [? ?]]].
    pose proof (only_two_edges x e H).
    cbv beta in H4.
    pose proof (proj1 H4 (conj H2 H1)).
    destruct H5; subst e; auto.
  + destruct H1.
    - exists (x, L).
      s_rewrite (left_sound g); auto.
      apply (left_valid g) in H.
      auto.
    - exists (x, R).
      s_rewrite (right_sound g); auto.
      apply (right_valid g) in H.
      auto.
Qed.

Lemma gamma_left_weak_valid: forall (g : Graph) x d l r, vvalid g x -> vgamma g x = (d, l, r) -> weak_valid g l.
Proof.
  intros.
  simpl in H0.
  inversion H0.
  pose proof valid_graph g (x, L).
  spec H1; [pose proof (left_valid g); auto |].
  tauto.
Qed.
Hint Resolve gamma_left_weak_valid : GraphDec.

Lemma gamma_right_weak_valid: forall (g : Graph) x d l r, vvalid g x -> vgamma g x = (d, l, r) -> weak_valid g r.
Proof.
  intros.
  simpl in H0.
  inversion H0.
  pose proof valid_graph g (x, R).
  spec H1; [pose proof (right_valid g); auto |].
  tauto.
Qed.
Hint Resolve gamma_right_weak_valid : GraphDec.

Lemma gamma_step_list: forall (g : Graph) x d l r, vvalid g x -> vgamma g x = (d, l, r) -> step_list g x (l :: r :: nil).
Proof.
  intros.
  unfold step_list.
  intros y.
  rewrite gamma_step by eauto.
  simpl.
  pose proof (@eq_sym _ l y).
  pose proof (@eq_sym _ r y).
  pose proof (@eq_sym _ y l).
  pose proof (@eq_sym _ y r).
  tauto.
Qed.

Lemma gamma_step_list': forall (g : Graph) x d l r, vvalid g x -> vgamma g x = (d, l, r) -> step_list g x (r :: l :: nil).
Proof.
  intros.
  unfold step_list.
  intros y.
  rewrite gamma_step by eauto.
  simpl.
  pose proof (@eq_sym _ l y).
  pose proof (@eq_sym _ r y).
  pose proof (@eq_sym _ y l).
  pose proof (@eq_sym _ y r).
  tauto.
Qed.

Lemma Graph_reachable_dec: forall (G: Graph) x,
    Decidable (vvalid G x) -> forall y, Decidable (reachable G x y).
Proof.
  intros.
  apply reachable_decidable with (is_null := is_null_SGBA); auto.
  + apply maGraph.
  + apply LocalFiniteGraph_FiniteGraph, finGraph.
  + apply FiniteGraph_EnumCovered, finGraph.
Qed.
Hint Resolve Graph_reachable_dec : GraphDec.

Lemma Graph_reachable_by_dec: forall (G: Graph) x (P: NodePred addr),
    Decidable (vvalid G x) -> ReachDecidable G x P.
Proof.
  intros.
  intro y.
  apply reachable_by_decidable with (is_null := is_null_SGBA); auto.
  + apply maGraph.
  + apply LocalFiniteGraph_FiniteGraph, finGraph.
  + apply FiniteGraph_EnumCovered, finGraph.
Qed.
(*
Lemma Graph_partialgraph_vi_spec: forall (G G': Graph) (P P': addr -> Prop),
  (predicate_partialgraph G P) ~=~ (predicate_partialgraph G' P') ->
  (forall v, vvalid G v -> P v -> vvalid G' v -> P' v -> vlabel G v = vlabel G' v) ->
  (predicate_partial_spatialgraph G P) -=- (predicate_partial_spatialgraph G' P').
Proof.
  intros.
  split; [auto |].
  split; [| intros; simpl; auto].
  simpl; unfold predicate_vvalid.
  intros.
  f_equal; [f_equal |].
  + apply H0; tauto.
  + destruct H as [_ [_ [_ ?]]].
    generalize (left_sound G v); intro.
    generalize (left_sound G' v); intro.
    apply H; simpl; unfold predicate_weak_evalid.
    - destruct H1. apply (left_valid G) in H1. change (pg_lg G) with (G: PGraph). rewrite H3. auto.
    - destruct H2. apply (left_valid G') in H2. change (pg_lg G') with (G': PGraph). rewrite H4. auto.
  + destruct H as [_ [_ [_ ?]]].
    generalize (right_sound G v); intro.
    generalize (right_sound G' v); intro.
    apply H; simpl; unfold predicate_weak_evalid.
    - destruct H1. apply (right_valid G) in H1. change (pg_lg G) with (G: PGraph). rewrite H3. auto.
    - destruct H2. apply (right_valid G') in H2. change (pg_lg G') with (G': PGraph). rewrite H4. auto.
Qed.
*)
Lemma gamma_left_reachable_included: forall (g: Graph) x d l r,
                                       vvalid g x -> vgamma g x = (d, l, r) -> Included (reachable g l) (reachable g x).
Proof.
  intros. intro y; intros. apply edge_reachable_by with l; auto. split; auto. split.
  + apply reachable_head_valid in H1; auto.
  + rewrite (gamma_step _ _ _ _ _ H H0). auto.
Qed.

Lemma gamma_right_reachable_included: forall (g: Graph) x d l r,
                                        vvalid g x -> vgamma g x = (d, l, r) -> Included (reachable g r) (reachable g x).
Proof.
  intros. intro y; intros. apply edge_reachable_by with r; auto. split; auto. split.
  + apply reachable_head_valid in H1; auto.
  + rewrite (gamma_step _ _ _ _ _ H H0). auto.
Qed.

Lemma Prop_join_reachable_left: forall (g: Graph) x d l r,
  vvalid g x ->
  vgamma g x = (d, l, r) ->
  Prop_join
    (reachable g l)
    (Intersection _ (reachable g x) (Complement addr (reachable g l)))
    (reachable g x).
Proof.
  intros.
  apply Ensemble_join_Intersection_Complement.
  - eapply gamma_left_reachable_included; eauto.
  - intros.
    apply gamma_left_weak_valid in H0; [| auto].
    apply decidable_prop_decidable, Graph_reachable_dec, weak_valid_vvalid_dec; auto.
Qed.

Lemma Prop_join_reachable_right: forall (g: Graph) x d l r,
  vvalid g x ->
  vgamma g x = (d, l, r) ->
  Prop_join
    (reachable g r)
    (Intersection _ (reachable g x) (Complement addr (reachable g r)))
    (reachable g x).
Proof.
  intros.
  apply Ensemble_join_Intersection_Complement.
  - eapply gamma_right_reachable_included; eauto.
  - intros.
    apply gamma_right_weak_valid in H0; [| auto].
    apply decidable_prop_decidable, Graph_reachable_dec, weak_valid_vvalid_dec; auto.
Qed.

Lemma dst_L_eq: forall (g1 g2: Graph) x,
  vvalid g1 x ->
  g1 ~=~ g2 ->
  dst g1 (x, L) = dst g2 (x, L).
Proof.
  intros.
  destruct H0 as [? [? [? ?]]].
  assert (vvalid g2 x) by (clear - H H0; firstorder).
  apply H3.
  + eapply left_valid in H; [| apply biGraph].
    auto.
  + eapply left_valid in H4; [| apply biGraph].
    auto.
Qed.

Lemma dst_R_eq: forall (g1 g2: Graph) x,
  vvalid g1 x ->
  g1 ~=~ g2 ->
  dst g1 (x, R) = dst g2 (x, R).
Proof.
  intros.
  destruct H0 as [? [? [? ?]]].
  assert (vvalid g2 x) by (clear - H H0; firstorder).
  apply H3.
  + eapply right_valid in H; [| apply biGraph].
    auto.
  + eapply right_valid in H4; [| apply biGraph].
    auto.
Qed.

Instance BiMaFin_Normal: NormalGeneralGraph (fun g: LGraph => BiMaFin g).
Proof.
  constructor.
  + intros.
    destruct X as [?H ?H ?H].
    apply (bi_graph_si _ _ (proj1 H)) in H0.
    apply (math_graph_si _ _ (proj1 H)) in H1.
    apply (finite_graph_si _ _ (proj1 H)) in H2.
    constructor; auto.
  + intros.
    destruct X as [?H ?H ?H].
    destruct X0 as [?H ?H ?H].
    constructor.
    - eapply bi_graph_join; eauto.
    - eapply math_graph_join; eauto.
    - eapply finite_graph_join; eauto.
Qed.

Lemma Graph_is_BiMaFin: forall (g: Graph), is_BiMaFin g.
Proof.
  intros.
  destruct g.
  exists sound_gg; auto.
Qed.

Lemma single_vertex_guarded_BiMaFin: forall (x0: addr) dv de dg,
  is_guarded_BiMaFin (fun v : addr => x0 <> v) (fun _ : addr * LR => ~ False)
    (single_vertex_labeledgraph x0 dv de dg).
Proof.
  intros.
  constructor; auto.
  simpl.
  constructor.
  + constructor; simpl; intros.
    - congruence.
    - rewrite Intersection_spec in H; destruct H; congruence.
  + constructor; simpl; intros.
    - rewrite Intersection_spec in H; destruct H; tauto.
    - rewrite Intersection_spec in H; destruct H; congruence.
  + constructor; exists nil; repeat constructor.
    - inversion H.
    - inversion H.
    - simpl; intros.
      unfold Ensembles.In in H; rewrite Intersection_spec in H; destruct H; congruence.
    - inversion H.
    - inversion H.
    - simpl; intros.
      unfold Ensembles.In in H; rewrite Intersection_spec in H; destruct H; congruence.
Qed.
  
Lemma is_BiMaFin_si: forall (g1 g2: LGraph),
  g1 ~=~ g2 ->
  is_BiMaFin g1 ->
  is_BiMaFin g2.
Proof.
  intros.
  destruct H0 as [[?H ?H ?H] _].
  apply (bi_graph_si _ _ H) in H0.
  apply (math_graph_si _ _ H) in H1.
  apply (finite_graph_si _ _ H) in H2.
  constructor; constructor; auto.
Qed.

Lemma is_guarded_BiMaFin_labeledgraph_add_edge: forall (g: LGraph) PV PE PE' e s d data_e,
  ~ evalid g e ->
  Same_set PE' (Intersection _ PE (fun e0 => e0 <> e)) ->
  is_guarded_BiMaFin PV PE g ->
  is_guarded_BiMaFin PV PE' (labeledgraph_add_edge g e s d data_e).
Proof.
  unfold is_guarded_BiMaFin.
  intros.
  eapply is_BiMaFin_si; [| eassumption].
  simpl.
  rewrite Same_set_spec in H0.
  split; [| split; [| split]].
  + intros; simpl; reflexivity.
  + intros; simpl.
    specialize (H0 e0).
    rewrite !Intersection_spec in *.
    unfold addValidFunc.
    rewrite H0.
    destruct_eq_dec e0 e; [subst |]; try tauto.
  + simpl; intros.
    unfold updateEdgeFunc.
    destruct_eq_dec e e0; auto; subst.
    specialize (H0 e0).
    rewrite Intersection_spec in *.
    destruct H3.
    tauto.
  + simpl; intros.
    unfold updateEdgeFunc.
    destruct_eq_dec e e0; auto; subst.
    specialize (H0 e0).
    rewrite Intersection_spec in *.
    destruct H3.
    tauto.
Qed.

(*********************************************************

Spatial Facts Part

*********************************************************)

Context {sSGG_Bi: sPointwiseGraph_Graph_Bi DV DE}.

Lemma va_reachable_dag_unfold: forall (g: Graph) x d l r,
  vvalid g x ->
  vgamma g x = (d, l, r) ->
  reachable_dag_vertices_at x g = vertex_at x (d, l, r) * reachable_through_dag_vertices_at (l :: r :: nil) g.
Proof.
  intros.
  apply va_reachable_dag_unfold; auto.
  eapply gamma_step_list; eauto.
Qed.

Lemma va_reachable_dag_update_unfold: forall (g: Graph) x d l r v,
  vvalid g x ->
  vgamma g x = (d, l, r) ->
  reachable_dag_vertices_at x (Graph_vgen g x v) = vertex_at x (v, l, r) * reachable_through_dag_vertices_at (l :: r :: nil) g.
Proof.
  intros.
  apply va_reachable_dag_update_unfold; auto.
  + eapply gamma_step_list; eauto.
  + eapply Graph_vgen_vgamma; eauto.
  + unfold Included, Ensembles.In; intros.
    apply vvalid_vguard.
    apply reachable_through_set_foot_valid in H1; auto.
  + unfold Included, Ensembles.In; intros.
    apply vvalid_vguard.
    apply reachable_through_set_foot_valid in H1; auto.
Qed.

Lemma va_reachable_root_stable_ramify: forall (g: Graph) (x: addr) (gx: DV * addr * addr),
  vgamma g x = gx ->
  vvalid g x ->
  @derives pred _
    (reachable_vertices_at x g)
    (vertex_at x gx * (vertex_at x gx -* reachable_vertices_at x g)).
Proof. intros; apply va_reachable_root_stable_ramify; auto. Qed.

Lemma va_reachable_root_update_ramify: forall (g: Graph) (x: addr) (lx: DV) (gx gx': DV * addr * addr),
  vvalid g x ->
  vgamma g x = gx ->
  vgamma (Graph_vgen g x lx) x = gx' ->
  @derives pred _
    (reachable_vertices_at x g)
    (vertex_at x gx *
      (vertex_at x gx' -* reachable_vertices_at x (Graph_vgen g x lx))).
Proof.
  intros.
  apply va_reachable_root_update_ramify; auto.
  + unfold Included, Ensembles.In; intros.
    apply vvalid_vguard.
    rewrite Intersection_spec in H2.
    destruct H2 as [? _].
    apply reachable_foot_valid in H2; auto.
  + unfold Included, Ensembles.In; intros.
    apply vvalid_vguard.
    rewrite Intersection_spec in H2.
    destruct H2 as [? _].
    apply reachable_foot_valid in H2; auto.
Qed.

Lemma va_reachable_internal_stable_ramify: forall (g: Graph) (x y: addr) (gy: DV * addr * addr),
  vvalid g y ->
  vgamma g y = gy ->
  reachable g x y ->
  @derives pred _
    (reachable_vertices_at x g)
    (vertex_at y gy *
      (vertex_at y gy -* reachable_vertices_at x g)).
Proof. intros. apply va_reachable_internal_stable_ramify; auto. Qed.

(*
TODO: maybe as a general lemma for normal_general_graph
Lemma is_guarded_BiMaFin_si: forall (g1 g2: LGraph),
*)

Lemma is_BiMaFin_LGraph_Graph: forall (g: LGraph) (P: LGraph -> pred),
  is_BiMaFin g ->
  P g |-- EX g: Graph, P g.
Proof.
  intros.
  destruct H as [X _].
  apply (exp_right (Build_GeneralGraph _ _ _ BiMaFin g X)).
  simpl.
  auto.
Qed.

Lemma va_labeledgraph_add_edge_eq: forall (g: LGraph) es e s d data,
  ~ evalid g e ->
  is_guarded_BiMaFin (fun x => s <> x) (fun e => ~ In e es) g ->
  let g' := labeledgraph_add_edge g e s d data in
  @vertices_at _ _ _ _ _ _ SGP _
   (Intersection _ (vvalid g) (fun x => s <> x)) (Graph_PointwiseGraph g) =
  @vertices_at _ _ _ _ _ _ SGP _
   (Intersection _ (vvalid g') (fun x => s <> x)) (Graph_PointwiseGraph g').
Proof.
  intros.
  apply va_labeledgraph_add_edge_eq; auto.
  + unfold Included, Ensembles.In.
    intros x0 ?.
    destruct H0 as [X _].
    pose (g0 := Build_GeneralGraph _ _ _ (fun g => BiMaFin (pg_lg g)) _ X: Graph).
    assert (vvalid g0 x0) by auto.
    apply vvalid_vguard in H0.
    simpl in H0 |- *.
    rewrite !Intersection_spec in H0.
    tauto.
  + unfold Included, Ensembles.In.
    intros x0 ?.
    destruct H0 as [X _].
    pose (g0 := Build_GeneralGraph _ _ _ (fun g => BiMaFin (pg_lg g)) _ X: Graph).
    assert (vvalid g0 x0) by auto.
    apply vvalid_vguard in H0.
    simpl in H0 |- *.
    rewrite !Intersection_spec in H0.
    unfold addValidFunc, updateEdgeFunc.
    split; [| split]; [tauto | tauto |].
    destruct_eq_dec e (x0, L); subst; [tauto |].
    destruct_eq_dec e (x0, R); subst; [tauto |].
    tauto.
Qed.

Lemma va_labeledgraph_egen_eq: forall (g: LGraph) e data P,
  @vertices_at _ _ _ _ _ _ SGP _
   P (Graph_PointwiseGraph g) =
  @vertices_at _ _ _ _ _ _ SGP _
   P (Graph_PointwiseGraph (labeledgraph_egen g e data)).
Proof.
  intros.
  apply vertices_at_vertices_identical.
  rewrite vertices_identical_spec; intros.
  simpl; auto.
Qed.

(*********************************************************

Spatial Facts (with Strong Assumption) Part

*********************************************************)

(*
  Context {SGSA: PointwiseGraphStrongAssum SGP}.

  Notation graph x g := (@reachable_vertices_at _ _ _ _ _ _ _ _ (_) _ (@SGP pSGG_Bi DV DE sSGG_Bi) _ x g).

  Lemma bi_graph_unfold: forall (g: Graph) x d l r,
      vvalid g x -> vgamma g x = (d, l, r) ->
      graph x g = vertex_at x (d, l, r) ⊗ graph l g ⊗ graph r g.
  Proof.
    intros. rewrite graph_unfold with (S := (l :: r :: nil)); auto.
    + change (Graph_PointwiseGraph g) with (LGraph_SGraph g).
      rewrite H0. simpl. rewrite ocon_emp. rewrite <- ocon_assoc. auto.
    + apply RGF.
    + intros. apply weak_valid_vvalid_dec. simpl in H1.
      destruct H1; [|destruct H1]; [subst x0 ..|exfalso; auto].
      - apply (gamma_left_weak_valid _ x d l r); auto.
      - apply (gamma_right_weak_valid _ x d l r); auto.
    + apply (gamma_step_list _ _ d l r); auto.
  Qed.

  Lemma bi_graph_precise_left: forall (g: Graph) x l,
      vvalid g x -> dst g (x, L) = l -> precise (graph l g).
  Proof.
    intros. apply precise_graph. 1: apply RGF.
    apply weak_valid_vvalid_dec.
    pose proof (left_valid g x H). simpl in H1.
    destruct (@valid_graph _ _ _ _ g _ (maGraph g) (x, L) H1).
    rewrite H0 in H3. apply H3.
  Qed.

  Lemma bi_graph_precise_right: forall (g: Graph) x r,
      vvalid g x -> dst g (x, R) = r -> precise (graph r g).
  Proof.
    intros. apply precise_graph. 1: apply RGF.
    apply weak_valid_vvalid_dec.
    pose proof (right_valid g x H). simpl in H1.
    destruct (@valid_graph _ _ _ _ g _ (maGraph g) (x, R) H1).
    rewrite H0 in H3. apply H3.
  Qed.

  Lemma reachable_through_set_unreachable: forall (g: Graph) (S1 S2: list addr) (v: addr),
      reachable_through_set (predicate_partialgraph g (Intersection addr (vvalid g) (Complement addr (reachable_through_set g S1)))) S2 v ->
      Complement addr (reachable_through_set g S1) v.
  Proof.
    intros. hnf in H. destruct H as [s [? ?]]. unfold Complement. unfold Ensembles.In . rewrite <- reachable_by_eq_partialgraph_reachable in H0.
    apply reachable_by_foot_prop in H0. rewrite Intersection_spec in H0. destruct H0. unfold Complement, Ensembles.In in H1. auto.
  Qed.

  Lemma unreachable_partialgraph_si_vertices_identical: forall (g g': Graph) (S1 S1' S2: list addr),
      (predicate_partial_labeledgraph g (Complement addr (reachable_through_set g S1)))
        ~=~
        (predicate_partial_labeledgraph g' (Complement addr (reachable_through_set g' S1')))%LabeledGraph ->
      vertices_identical2 (reachable_through_set (predicate_partialgraph g (Intersection addr (vvalid g) (Complement addr (reachable_through_set g S1)))) S2)
                          (reachable_through_set (predicate_partialgraph g' (Intersection addr (vvalid g') (Complement addr (reachable_through_set g' S1')))) S2)
                          (Graph_PointwiseGraph g) (Graph_PointwiseGraph g').
  Proof.
  intros.
  apply GSG_PartialGraphPreserve2.
  - unfold Included, Ensembles.In.
    intros.
    apply vvalid_vguard.
    apply reachable_through_set_foot_valid in H0.
    destruct H0; auto.
  - unfold Included, Ensembles.In.
    intros.
    apply vvalid_vguard.
    apply reachable_through_set_foot_valid in H0.
    destruct H0; auto.
  - unfold Included, Ensembles.In.
    intros.
    apply reachable_through_set_foot_valid in H0.
    destruct H0; auto.
  - unfold Included, Ensembles.In.
    intros.
    apply reachable_through_set_foot_valid in H0.
    destruct H0; auto.
  - assert ((predicate_partialgraph g (Intersection addr (vvalid g) (Complement addr (reachable_through_set g S1))))
              ~=~
              (predicate_partialgraph g' (Intersection addr (vvalid g') (Complement addr (reachable_through_set g' S1'))))). {
      destruct H as [[? [? [? ?]]] _]. hnf. simpl in *. unfold predicate_vvalid in *. unfold predicate_weak_evalid in *.
      split; [|split; [|split]]; intros; rewrite !Intersection_spec in *.
      - clear -H. specialize (H v). intuition.
      - clear H2. specialize (H0 e). specialize (H1 e). intuition.
        + rewrite <- H2 in *. specialize (H (src g e)). intuition.
        + rewrite H2 in *. specialize (H (src g' e)). intuition.
      - apply H1; intuition.
      - apply H2; intuition.
    } rewrite <- H0. destruct H as [[? [? [? ?]]] [? ?]]. hnf. unfold structurally_identical. simpl in *. unfold predicate_vvalid in *. unfold predicate_weak_evalid in *.
    split; [split; [|split; [|split]] |split]; intros.
    + clear -H H0. intuition.
      * apply reachable_through_set_unreachable in H3. specialize (H v). intuition.
      * rewrite H0 in H3. apply reachable_through_set_unreachable in H3. specialize (H v). intuition.
    + clear -H1 H2 H0. specialize (H1 e). specialize (H2 e). intuition.
      * apply reachable_through_set_unreachable in H5. apply H1 in H5. intuition.
      * pose proof H5. apply reachable_through_set_unreachable in H5. specialize (H3 H5). specialize (H1 H5). specialize (H3 H1). rewrite <- H3. auto.
      * rewrite H0 in H5. apply reachable_through_set_unreachable in H5. specialize (H3 H5). intuition.
      * pose proof H5. rewrite H0 in H5. apply reachable_through_set_unreachable in H5. specialize (H3 H5). destruct H3. specialize (H1 H3 H6).
        assert (src g e = src g' e) by (apply H1; auto). rewrite H7. auto.
    + destruct H6, H7. rewrite H0 in H9. apply reachable_through_set_unreachable in H8. apply reachable_through_set_unreachable in H9. apply H2; auto.
    + destruct H6, H7. rewrite H0 in H9. apply reachable_through_set_unreachable in H8. apply reachable_through_set_unreachable in H9. apply H3; auto.
    + destruct H6, H7. rewrite H0 in H9. apply reachable_through_set_unreachable in H8. apply reachable_through_set_unreachable in H9. apply H4; auto.
    + destruct H6, H7. rewrite H0 in H9. apply reachable_through_set_unreachable in H8. apply reachable_through_set_unreachable in H9. apply H5; auto.
  Qed.

  Lemma subgraph_update:
    forall (g g': Graph) (S1 S1' S2: list addr),
      (forall x : addr, In x (S1 ++ S2) -> Decidable (vvalid g x)) ->
      (forall x : addr, In x (S1' ++ S2) -> Decidable (vvalid g' x)) ->
      (predicate_partial_labeledgraph g (Complement addr (reachable_through_set g S1))) ~=~
      (predicate_partial_labeledgraph g' (Complement addr (reachable_through_set g' S1')))%LabeledGraph ->
      @derives pred _ (graphs S1 g ⊗ graphs S2 g) (graphs S1 g * (graphs S1' g' -* graphs S1' g' ⊗ graphs S2 g')).
  Proof.
    intros.
    apply subgraph_update; auto.
    + apply RGF.
    + apply RGF.
    + apply unreachable_partialgraph_si_vertices_identical; auto.
    + apply Included_trans with (vvalid g).
      - hnf; intros.
        apply reachable_through_set_foot_valid in H0.
        destruct H0; auto.
      - intro v; apply vvalid_vguard.
    + apply Included_trans with (vvalid g').
      - hnf; intros.
        apply reachable_through_set_foot_valid in H0.
        destruct H0; auto.
      - intro v; apply vvalid_vguard.
  Qed.

*)

End GRAPH_BI.
