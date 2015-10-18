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
Require Import RamifyCoq.data_structure.general_spatial_graph.
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

Section pSpatialGraph_Graph_Bi.

Context {pSGG_Bi: pSpatialGraph_Graph_Bi}.

Class BiMaFin (g: PreGraph addr (addr * LR)) := {
  bi: BiGraph g (fun x => (x, L)) (fun x => (x, R));
  ma: MathGraph g;
  fin: FiniteGraph g;
  is_null_def': forall x: addr, is_null g x = (x = null)
}.

Definition Graph := (GeneralGraph addr (addr * LR) bool unit (fun g _ _ => BiMaFin g)).

Identity Coercion G_GG : Graph >-> GeneralGraph.

Definition gamma (G : Graph) (v: addr) : bool * addr * addr := 
  (vlabel G v, dst G (v, L), dst G (v, R)).

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

Definition Graph_SpatialGraph (G: Graph): SpatialGraph addr (addr * LR) (bool * addr * addr) unit := Build_SpatialGraph _ _ _ _ _ _ G (gamma G) (fun _ => tt).

Coercion Graph_SpatialGraph: Graph >-> SpatialGraph.

Lemma weak_valid_vvalid_dec: forall (g : Graph) (x: addr),
  weak_valid g x -> {vvalid g x} + {~ vvalid g x}.
Proof.
  intros.
  apply null_or_valid in H.
  destruct H; [right | left]; auto.
  pose proof valid_not_null g x; tauto.
Qed.

Definition Graph_gen (G: Graph) (x: addr) (d: bool) : Graph :=
  generalgraph_gen G x d (sound_gg G).

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

Lemma Graph_gen_spatial_spec: forall (G: Graph) (x: addr) (d d': bool) l r,
  vgamma G x = (d, l, r) ->
  (Graph_gen G x d') -=- (spatialgraph_vgen G x (d', l, r)).
Proof.
  intros.
  split; [reflexivity | split; [| auto]].
  simpl in *; intros.
  unfold gamma in *; simpl in *; unfold update_vlabel.
  destruct_eq_dec x v; subst.
  + inversion H; subst; f_equal; f_equal.
  + auto.
Qed.

Lemma Graph_gen_left_null_spatial_spec: forall (G: Graph) (x: addr) (d : bool) l r,
    vgamma G x = (d, l, r) ->
    (Graph_gen_left_null G x) -=- (spatialgraph_vgen G x (d, null, r)).
Proof.
  intros.
  split; [|split; [| auto]].
  + split; [|split; [|split]]; intros; simpl; intuition.
    unfold Graph_gen_left_null in H0. simpl in H0. unfold spatialgraph_vgen in H1. simpl in H1.
    unfold update_dst. destruct_eq_dec (x, L) e; auto. admit.
  + intros. simpl. unfold Graph_gen_left_null. unfold generalgraph_gen_dst. unfold gamma. simpl.
    unfold update_dst. destruct_eq_dec (x, L) (v, L).
    - destruct_eq_dec (x, L) (v, R). inversion H3. inversion H2. destruct_eq_dec v v. 2: exfalso; auto.
      simpl in H. unfold gamma in H. inversion H; subst; auto.
    - destruct_eq_dec (x, L) (v, R). inversion H3. destruct_eq_dec x v.
      * subst. exfalso; auto.
      * auto.
Qed.

Lemma weak_valid_si: forall (g1 g2: Graph) n, g1 ~=~ g2 -> (weak_valid g1 n <-> weak_valid g2 n).
Proof.
  intros.
  unfold weak_valid.
  rewrite !is_null_def.
  destruct H as [? _].
  rewrite H.
  reflexivity.
Qed.

Ltac s_rewrite p :=
  let H := fresh "H" in
  pose proof p as H;
  simpl in H;
  rewrite H;
  clear H.

Lemma gamma_step: forall (g : Graph) x (d: bool) (l r: addr), vvalid g x -> vgamma g x = (d, l, r) -> forall y, step g x y <-> y = l \/ y = r.
Proof.
  intros. simpl in H0; unfold gamma in H0; inversion H0; subst.
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
  assert (snd (fst (gamma g x)) = l) by (rewrite H0; auto).
  clear H0.
  unfold gamma in H1; simpl in H1.
  pose proof valid_graph g (x, L).
  spec H0; [pose proof (left_valid g); auto |].
  rewrite <- H1.
  simpl in H0; tauto.
Qed.

Lemma gamma_right_weak_valid: forall (g : Graph) x d l r, vvalid g x -> vgamma g x = (d, l, r) -> weak_valid g r.
Proof.
  intros.
  simpl in H0.
  assert (snd (gamma g x) = r) by (rewrite H0; auto).
  clear H0.
  unfold gamma in H1; simpl in H1.
  pose proof valid_graph g (x, R).
  spec H0; [pose proof (right_valid g); auto |].
  rewrite <- H1.
  simpl in H0; tauto.
Qed.

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
  unfold gamma.
  f_equal; [f_equal |].
  + apply H0; tauto.
  + destruct H as [_ [_ [_ ?]]].
    generalize (left_sound G v); intro.
    generalize (left_sound G' v); intro.
    apply H; simpl; unfold predicate_weak_evalid.
    - destruct H1. apply (left_valid G) in H1. rewrite H3. auto.
    - destruct H2. apply (left_valid G') in H2. rewrite H4. auto.
  + destruct H as [_ [_ [_ ?]]].
    generalize (right_sound G v); intro.
    generalize (right_sound G' v); intro.
    apply H; simpl; unfold predicate_weak_evalid.
    - destruct H1. apply (right_valid G) in H1. rewrite H3. auto.
    - destruct H2. apply (right_valid G') in H2. rewrite H4. auto.
Qed.

End pSpatialGraph_Graph_Bi.

Class sSpatialGraph_Graph_Bi {pSGG_Bi: pSpatialGraph_Graph_Bi}: Type := {
  SGP: SpatialGraphPred addr (addr * LR) (bool * addr * addr) unit pred;
  SGA: SpatialGraphAssum SGP
}.

Existing Instances SGP SGA biGraph.
