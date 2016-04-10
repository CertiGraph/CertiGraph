Require Import RamifyCoq.lib.Ensembles_ext.
Require Import Coq.Lists.List.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.msl_application.Graph.
Require Import Coq.Logic.Classical.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Local Open Scope logic.

Inductive LR :=
  | L
  | R.

Class pSpatialGraph_Graph_Bi: Type := {
  addr: Type;
  null: addr;
  pred: Type;
  SGBA: SpatialGraphBasicAssum addr (addr * LR)
}.

Existing Instance SGBA.

Class sSpatialGraph_Graph_Bi {pSGG_Bi: pSpatialGraph_Graph_Bi} (DV DE: Type): Type := {
  SGP: SpatialGraphPred addr (addr * LR) (DV * addr * addr) unit pred;
  SGA: SpatialGraphAssum SGP;
  SGAv: SpatialGraphAssum_vs SGP
}.

Existing Instances SGP SGA SGAv.

Section GRAPH_BI.

(*********************************************************

Pure Facts Part

*********************************************************)

Context {pSGG_Bi: pSpatialGraph_Graph_Bi}.
Context {DV DE: Type}.

Class BiMaFin (g: PreGraph addr (addr * LR)) := {
  bi: BiGraph g (fun x => (x, L)) (fun x => (x, R));
  ma: MathGraph g;
  fin: FiniteGraph g;
  is_null_def': forall x: addr, is_null g x = (x = null)
}.

Definition Graph := (GeneralGraph addr (addr * LR) DV DE (fun g => BiMaFin (pg_lg g))).
Definition LGraph := (LabeledGraph addr (addr * LR) DV DE).
Definition SGraph := (SpatialGraph addr (addr * LR) (DV * addr * addr) unit).
Definition PGraph := (PreGraph addr (addr * LR)).

Instance SGC_Bi: SpatialGraphConstructor addr (addr * LR) DV DE (DV * addr * addr) unit.
Proof.
  refine (Build_SpatialGraphConstructor _ _ _ _ _ _ SGBA _ _).
  + exact (fun G v => (vlabel G v, dst (pg_lg G) (v, L), dst (pg_lg G) (v, R))).
  + exact (fun _ _ => tt).
Defined.

Instance L_SGC_Bi: Local_SpatialGraphConstructor addr (addr * LR) DV DE (DV * addr * addr) unit.
Proof.
Check Build_Local_SpatialGraphConstructor.
  refine (Build_Local_SpatialGraphConstructor _ _ _ _ _ _ SGBA SGC_Bi
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

Definition Graph_LGraph (G: Graph): LGraph := lg_gg G.
Definition LGraph_SGraph (G: LGraph): SGraph := Graph_SpatialGraph G.
Definition SGraph_PGraph (G: SGraph): PGraph := @pg_sg _ _ _ _ _ _ G.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Coercion SGraph_PGraph: SGraph >-> PGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_SpatialGraph: SGraph >-> SpatialGraph.
Local Identity Coercion PGraph_PreGraph: PGraph >-> PreGraph.

Instance biGraph (G: Graph): BiGraph G (fun x => (x, L)) (fun x => (x, R)) :=
  @bi G (@sound_gg _ _ _ _ _ _ _ G).

Instance maGraph(G: Graph): MathGraph G :=
  @ma G (@sound_gg _ _ _ _ _ _ _ G).

Instance finGraph (G: Graph): FiniteGraph G :=
  @fin G (@sound_gg _ _ _ _ _ _ _ G).

Definition is_null_def (g: Graph): forall x: addr, is_null g x = (x = null) := is_null_def'.

Instance RGF (G: Graph): ReachableFiniteGraph G.
  apply Build_ReachableFiniteGraph.
  intros.
  apply finite_reachable_computable in H.
  + destruct H as [l [? ?]].
    exists l; auto.
  + apply maGraph.
  + apply (LocalFiniteGraph_FiniteGraph G), finGraph.
  + apply (FiniteGraph_EnumCovered G), finGraph.
Defined.

Definition Graph_gen (G: Graph) (x: addr) (d: DV) : Graph :=
  generalgraph_vgen G x d (sound_gg G).

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
  pose proof @valid_not_null _ _ _ _ g (maGraph g) null.
  rewrite is_null_def in H.
  tauto.
Qed.

Definition Graph_gen_left_null (G : Graph) (x : addr) : Graph.
Proof.
  refine (generalgraph_gen_dst G (x, L) null _).
  assert (weak_valid G null) by (left; rewrite is_null_def; auto).
  refine (Build_BiMaFin _ (gen_dst_preserve_bi G (x, L) null _ _ (biGraph G))
                        (gen_dst_preserve_math G (x, L) null ma H)
                        (gen_dst_preserve_finite G (x, L) null (finGraph G)) _).
  intro y; intros. simpl. apply is_null_def.
Defined.

Definition Graph_gen_right_null (G : Graph) (x : addr) : Graph.
Proof.
  refine (generalgraph_gen_dst G (x, R) null _).
  assert (weak_valid G null) by (left; rewrite is_null_def; auto).
  refine (Build_BiMaFin _ (gen_dst_preserve_bi G (x, R) null _ _ (biGraph G))
                        (gen_dst_preserve_math G (x, R) null ma H)
                        (gen_dst_preserve_finite G (x, R) null (finGraph G)) _).
  intro y; intros. simpl. apply is_null_def.
Defined.

(*
Definition Graph_gen_update (G: Graph) (x : addr) (d: DV) (l r: addr) (Hi: in_math G x l r) (Hn: ~ is_null G x) : Graph.
Proof.
  refine (Graph_gen (@update_GeneralGraph _ _ _ _ _ _ _ G _ _ (biGraph G) x l r _) x d).
  unfold update_LabeledGraph.
  refine (Build_BiMaFin _
                        (@update_BiGraph _ _ _ _ G _ _ (biGraph G) x l r)
                        (@update_MathGraph _ _ _ _ G _ _ (biGraph G) (maGraph G) x l r Hi Hn)
                        (@update_FiniteGraph _ _ _ _ G _ _ (biGraph G) (finGraph G) x l r) _).
  intro y; intros. simpl. apply is_null_def.
Defined.
*)
Ltac s_rewrite p :=
  let H := fresh "H" in
  pose proof p as H;
  simpl in H;
  rewrite H;
  clear H.

(*
Lemma Graph_gen_update_vgamma: forall (G: Graph) (x: addr) (d: DV) l r (Hi: in_math G x l r) (Hn: ~ is_null G x),
    vgamma (Graph_gen_update G x d l r Hi Hn) x = (d, l, r).
Proof.
  intros; simpl; unfold gamma; simpl. f_equal; [f_equal |].
  + unfold update_vlabel. destruct (equiv_dec x x); auto. unfold complement, equiv in c. exfalso; auto.
  + unfold change_dst. destruct (equiv_dec (src G (x, L)) x).
    - destruct (left_or_right G (biGraph G) x (x, L) e); auto. inversion e0.
    - exfalso. apply c. unfold equiv. s_rewrite (left_sound G); auto.
  + unfold change_dst. destruct (equiv_dec (src G (x, R)) x).
    - destruct (left_or_right G (biGraph G) x (x, R) e); auto. inversion e0.
    - exfalso. apply c. unfold equiv. s_rewrite (right_sound G); auto.
Qed.

Lemma Graph_gen_update_spatial_spec: forall (G: Graph) (x: addr) (d d': DV) l r (Hi: in_math G x l r) (Hn: ~ is_null G x),
  vvalid G x -> vgamma G x = (d, l, r) ->
  (Graph_gen_update G x d' l r Hi Hn) -=- (spatialgraph_vgen G x (d', l, r)).
Proof.
  intros. split; [|split]; intros; simpl; auto.
  + hnf. simpl. split; [|split;[|split]]; intros; auto.
    - unfold change_vvalid. intuition. subst v. auto.
    - unfold change_evalid. intuition. rewrite (only_two_edges G) in H2.
      destruct H2; rewrite H1;
      [apply (@left_valid _ _ _ _ G _ _ (biGraph G)) | apply (@right_valid _ _ _ _ G _ _ (biGraph G))]; auto.
    - unfold change_dst. simpl. destruct (equiv_dec (src G e) x); auto.
      simpl in H0. unfold gamma in H0. inversion H0.
      destruct (left_or_right G (biGraph G) x e e0); subst; auto.
  + simpl in *. unfold gamma. simpl. unfold update_vlabel, change_dst.
    assert (forall v', (src G (v', L)) = v') by (intros; s_rewrite (left_sound G); auto).
    assert (forall v', (src G (v', R)) = v') by (intros; s_rewrite (right_sound G); auto).
    destruct (equiv_dec x v).
    - unfold equiv in e. subst v. specialize (H3 x). specialize (H4 x). f_equal; [f_equal|].
      * destruct (equiv_dec (src G (x, L)) x). 2: unfold complement, equiv in c; exfalso; auto.
        destruct (left_or_right G (biGraph G) x (x, L) e); auto. inversion e0.
      * destruct (equiv_dec (src G (x, R)) x). 2: unfold complement, equiv in c; exfalso; auto.
        destruct (left_or_right G (biGraph G) x (x, R) e); auto. inversion e0.
    - unfold complement, equiv in c. specialize (H3 v). specialize (H4 v). f_equal; [f_equal|].
      * destruct (equiv_dec (src G (v, L)) x); auto. unfold equiv in e; exfalso; rewrite H3 in e; auto.
      * destruct (equiv_dec (src G (v, R)) x); auto. unfold equiv in e; exfalso; rewrite H4 in e; auto.
Qed.
*)
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
  rewrite !is_null_def.
  destruct H as [? _].
  rewrite H.
  reflexivity.
Qed.

Lemma gamma_step: forall (g : Graph) x (d: DV) (l r: addr), vvalid g x -> vgamma g x = (d, l, r) -> forall y, step g x y <-> y = l \/ y = r.
Proof.
  intros. simpl in H0; inversion H0; subst.
  rewrite step_spec; split; intros.
  + destruct H1 as [? [? [? ?]]].
    rewrite (only_two_edges g) in H2.
    destruct H2; subst; auto.
  + destruct H1.
    - exists (x, L).
      apply (left_valid g) in H.
      s_rewrite (left_sound g); auto.
    - exists (x, R).
      apply (right_valid g) in H.
      s_rewrite (right_sound g); auto.
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
  apply reachable_decidable; auto.
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
  apply reachable_by_decidable; auto.
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

(*********************************************************

Spatial Facts (with Strong Assumption) Part

*********************************************************)

  Context {sSGG_Bi: sSpatialGraph_Graph_Bi DV DE}.
  Context {SGSA: SpatialGraphStrongAssum SGP}.

  Notation graph x g := (@reachable_vertices_at _ _ _ _ _ _ _ (_) _ (@SGP pSGG_Bi DV DE sSGG_Bi) _ x g).

  Lemma bi_graph_unfold: forall (g: Graph) x d l r,
      vvalid g x -> vgamma g x = (d, l, r) ->
      graph x g = vertex_at x (d, l, r) ⊗ graph l g ⊗ graph r g.
  Proof.
  Abort.
(* TODO: resume these lemmas. *)
(*
    intros. rewrite graph_unfold with (S := (l :: r :: nil)); auto.
    + rewrite H0. simpl. rewrite ocon_emp. rewrite <- ocon_assoc. auto.
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
    destruct (@valid_graph _ _ _ _ g (maGraph g) (x, L) H1).
    rewrite H0 in H3. apply H3.
  Qed.

  Lemma bi_graph_precise_right: forall (g: Graph) x r,
      vvalid g x -> dst g (x, R) = r -> precise (graph r g).
  Proof.
    intros. apply precise_graph. 1: apply RGF.
    apply weak_valid_vvalid_dec.
    pose proof (right_valid g x H). simpl in H1.
    destruct (@valid_graph _ _ _ _ g (maGraph g) (x, R) H1).
    rewrite H0 in H3. apply H3.
  Qed.
*)  
End GRAPH_BI.
