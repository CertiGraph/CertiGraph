Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Equivalence_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.MathGraph.

Section BiGraph.

Context {V E: Type} {EV: EqDec V eq} {EE: EqDec E eq}.

Class BiGraph (pg: PreGraph V E) (left_out_edge right_out_edge: V -> E): Prop :=
{
  bi_consist: forall x, vvalid pg x -> left_out_edge x <> right_out_edge x;
  only_two_edges: forall x e, vvalid pg x -> (src pg e = x /\ evalid pg e <-> e = left_out_edge x \/ e = right_out_edge x)
}.

Context {left_out_edge right_out_edge: V -> E}.

Lemma left_valid (pg: PreGraph V E) {bi: BiGraph pg left_out_edge right_out_edge}: forall x, vvalid pg x -> evalid pg (left_out_edge x).
Proof.
  intros.
  pose proof only_two_edges x (left_out_edge x).
  tauto.
Qed.

Lemma right_valid (pg: PreGraph V E) {bi: BiGraph pg left_out_edge right_out_edge}: forall x, vvalid pg x -> evalid pg (right_out_edge x).
Proof.
  intros.
  pose proof only_two_edges x (right_out_edge x).
  tauto.
Qed.

Lemma left_sound (pg: PreGraph V E) {bi: BiGraph pg left_out_edge right_out_edge}: forall x, vvalid pg x -> src pg (left_out_edge x) = x.
Proof.
  intros.
  pose proof only_two_edges x (left_out_edge x).
  pose proof left_valid pg x.
  tauto.
Qed.

Lemma right_sound (pg: PreGraph V E) {bi: BiGraph pg left_out_edge right_out_edge}: forall x, vvalid pg x -> src pg (right_out_edge x) = x.
Proof.
  intros.
  pose proof only_two_edges x (right_out_edge x).
  pose proof right_valid pg x.
  tauto.
Qed.

Lemma left_or_right (pg: PreGraph V E) (bi: BiGraph pg left_out_edge right_out_edge): forall x e, vvalid pg x -> evalid pg e -> src pg e = x -> {e = left_out_edge x} + {e = right_out_edge x}.
Proof.
  intros.
  pose proof only_two_edges x e.  
  destruct_eq_dec e (left_out_edge x); [left | right]; tauto.
Qed.

Lemma biGraph_out_edges (pg: PreGraph V E) (bi: BiGraph pg left_out_edge right_out_edge): forall x e, vvalid pg x -> (In e (left_out_edge x :: right_out_edge x :: nil) <-> out_edges pg x e).
Proof.
  intros.
  unfold out_edges.
  simpl.
  pose proof only_two_edges x e H.
  firstorder; subst; tauto.
Qed.

Definition biE (pg : PreGraph V E) {bi: BiGraph pg left_out_edge right_out_edge} (v: V) : V * V := (dst pg (left_out_edge v), dst pg (right_out_edge v)).

Lemma biE_only2 (pg : PreGraph V E) {bi: BiGraph pg left_out_edge right_out_edge} :
  forall v v1 v2 n, vvalid pg v -> biE pg v = (v1 ,v2) -> (step pg v n <-> n = v1 \/ n = v2).
Proof.
  intros; unfold biE in H.
  split; intros.
  + inversion H1; subst.
    inversion H0; subst.
    assert (e = left_out_edge (src pg e) \/ e = right_out_edge (src pg e)) by (rewrite <- only_two_edges; eauto).
    destruct H3; rewrite <- H3; auto.
  + rewrite step_spec; inversion H0; subst.
    destruct H1; [exists (left_out_edge v) | exists (right_out_edge v)]; subst.
    - split; [| split]; [eapply left_valid | rewrite left_sound |]; eauto.
    - split; [| split]; [eapply right_valid | rewrite right_sound |]; eauto.
Qed.

Lemma bi_graph_si: forall (g1 g2: PreGraph V E),
  g1 ~=~ g2 ->
  BiGraph g1 left_out_edge right_out_edge ->
  BiGraph g2 left_out_edge right_out_edge.
Proof.
  intros.
  constructor.
  + intros.
    apply (bi_consist).
    rewrite (proj1 H); auto.
  + destruct H as [? [? [? ?]]].
    intros.
    pose proof only_two_edges x e.
    rewrite <- H in H4.
    rewrite <- H1.
    rewrite <- H5 by auto.
    apply and_iff_compat_r_weak.
    intros.
    pose proof proj1 (H1 e) H6.
    rewrite H2 by auto.
    reflexivity.
Qed.

Lemma gen_dst_preserve_bi: forall (g: PreGraph V E) e t,
    BiGraph g left_out_edge right_out_edge -> BiGraph (pregraph_gen_dst g e t) left_out_edge right_out_edge.
Proof.
  intros. apply Build_BiGraph; intros.
  + apply bi_consist; auto.
  + simpl. apply (only_two_edges); auto.
Qed.

Context {is_null: DecidablePred V}.

Lemma bi_graph_join: forall (g: PreGraph V E) (PV1 PV2 PV: V -> Prop) (PE1 PE2 PE: E -> Prop),
  Prop_join PV1 PV2 PV ->
  Prop_join PE1 PE2 PE ->
  MathGraph (gpredicate_subgraph PV1 PE1 g) is_null ->
  MathGraph (gpredicate_subgraph PV2 PE2 g) is_null ->
  BiGraph (gpredicate_subgraph PV1 PE1 g) left_out_edge right_out_edge ->
  BiGraph (gpredicate_subgraph PV2 PE2 g) left_out_edge right_out_edge ->
  BiGraph (gpredicate_subgraph PV PE g) left_out_edge right_out_edge.
Proof.
  intros.
  constructor.
  + intros.
    simpl in H5.
    rewrite Intersection_spec in H5.
    destruct H5.
    destruct H as [? _].
    rewrite H in H6; destruct H6.
    - apply (@bi_consist _ _ _ H3).
      split; auto.
    - apply (@bi_consist _ _ _ H4).
      split; auto.
  + intros.
    simpl in H5.
    rewrite Intersection_spec in H5.
    destruct H5.
    destruct H as [HH HH0].
    rewrite HH in H6.
    destruct H6 as [H6 | H6]; [pose proof HH0 _ H6 | pose proof (fun H => HH0 _ H H6)].
    - pose proof @only_two_edges _ _ _ H3 x e.
      simpl in H7; rewrite !Intersection_spec in H7; specialize (H7 (conj H5 H6)).
      rewrite <- H7; simpl.
      rewrite Intersection_spec.
      apply and_iff_compat_l_weak; intros.
      apply and_iff_compat_l_weak; intros.
      destruct H0 as [HH1 HH2].
      rewrite HH1.
      assert (~ PE2 e); [intro | tauto].
      pose proof valid_graph (gpredicate_subgraph PV2 PE2 g) e.
      simpl in H10; rewrite !Intersection_spec in H10.
      specialize (H10 (conj H9 H0)).
      subst x.
      pose proof (fun H => HH2 _ H H0).
      tauto.
    - pose proof @only_two_edges _ _ _ H4 x e.
      simpl in H7; rewrite !Intersection_spec in H7; specialize (H7 (conj H5 H6)).
      rewrite <- H7; simpl.
      rewrite Intersection_spec.
      apply and_iff_compat_l_weak; intros.
      apply and_iff_compat_l_weak; intros.
      destruct H0 as [HH1 HH2].
      rewrite HH1.
      assert (~ PE1 e); [intro | tauto].
      pose proof valid_graph (gpredicate_subgraph PV1 PE1 g) e.
      simpl in H10; rewrite !Intersection_spec in H10.
      specialize (H10 (conj H9 H0)).
      subst x.
      pose proof (HH2 _ H0).
      tauto.
Qed.

End BiGraph.
