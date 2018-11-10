Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.lib.EquivDec_ext.

Generalizable All Variables.

Record pregraph_isomorphism_explicit
       `(g: @PreGraph V E EV EE) `(g': @PreGraph V' E' EV' EE')
       (vmap: V -> V') (vmap': V' -> V) (emap: E -> E') (emap': E' -> E): Prop :=
  {
    vertex_bij: bijective vmap vmap';
    edge_bij: bijective emap emap';
    vvalid_bij: forall v, vvalid g v -> vvalid g' (vmap v);
    vvalid_bij_inv: forall v', vvalid g' v' -> vvalid g (vmap' v');
    evalid_bij: forall e, evalid g e -> evalid g' (emap e);
    evalid_bij_inv: forall e', evalid g' e' -> evalid g (emap' e');
    src_bij: forall e, evalid g e -> vmap (src g e) = src g' (emap e);
    dst_bij: forall e, evalid g e -> vmap (dst g e) = dst g' (emap e);
  }.

Lemma pregraph_iso_exp_refl: forall `(g: @PreGraph V E EV EE),
    pregraph_isomorphism_explicit g g id id id id.
Proof. intros. split; auto; apply bijective_refl. Qed.

Lemma pregraph_iso_exp_sym: forall
    `(g: @PreGraph V E EV EE) `(g': @PreGraph V' E' EV' EE') vmap vmap' emap emap',
    pregraph_isomorphism_explicit g g' vmap vmap' emap emap' ->
    pregraph_isomorphism_explicit g' g vmap' vmap emap' emap.
Proof.
  intros. destruct H. split; try assumption.
  - apply bijective_sym; assumption.
  - apply bijective_sym; assumption.
  - intros. destruct edge_bij0. apply evalid_bij_inv0 in H.
    rewrite <- (surjective e) at 1. rewrite <- src_bij0 by assumption.
    apply bijective_sym in vertex_bij0. destruct vertex_bij0.
    rewrite surjective0. reflexivity.
  - intros. destruct edge_bij0. apply evalid_bij_inv0 in H.
    rewrite <- (surjective e) at 1. rewrite <- dst_bij0 by assumption.
    apply bijective_sym in vertex_bij0. destruct vertex_bij0.
    rewrite surjective0. reflexivity.
Qed.

Lemma pregraph_iso_exp_trans: forall
    `(g1: @PreGraph V1 E1 EV1 EE1) `(g2: @PreGraph V2 E2 EV2 EE2)
    `(g3: @PreGraph V3 E3 EV3 EE3) v12 v21 e12 e21 v23 v32 e23 e32,
    pregraph_isomorphism_explicit g1 g2 v12 v21 e12 e21 ->
    pregraph_isomorphism_explicit g2 g3 v23 v32 e23 e32 ->
    pregraph_isomorphism_explicit g1 g3 (compose v23 v12) (compose v21 v32)
                                  (compose e23 e12) (compose e21 e32).
Proof.
  intros. destruct H, H0. split; intros; [| | unfold compose..]; auto.
  - eapply bijective_trans; auto.
  - eapply bijective_trans; auto.
  - rewrite <- src_bij1, <- src_bij0; auto.
  - rewrite <- dst_bij1, <- dst_bij0; auto.
Qed.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Record label_preserving_graph_isomorphism_explicit
       `(g: @LabeledGraph V E EV EE DV DE DG) (g': @LabeledGraph V E EV EE DV DE DG)
       (vmap vmap': V -> V) (emap emap': E -> E): Prop :=
  {
    lp_pregraph_iso: pregraph_isomorphism_explicit g g' vmap vmap' emap emap';
    vlabel_iso: forall v, vvalid g v -> vlabel g v = vlabel g' (vmap v);
    elabel_iso: forall e, evalid g e -> elabel g e = elabel g' (emap e);
  }.

Lemma lp_graph_iso_exp_refl: forall `(g: @LabeledGraph V E EV EE DV DE DG),
    label_preserving_graph_isomorphism_explicit g g id id id id.
Proof. intros; split; auto. apply pregraph_iso_exp_refl. Qed.

Lemma lp_graph_iso_exp_sym: forall
    `(g: @LabeledGraph V E EV EE DV DE DG) g' vmap vmap' emap emap',
    label_preserving_graph_isomorphism_explicit g g' vmap vmap' emap emap' ->
    label_preserving_graph_isomorphism_explicit g' g vmap' vmap emap' emap.
Proof.
  intros. destruct H. split.
  - apply pregraph_iso_exp_sym. assumption.
  - intros. destruct lp_pregraph_iso0. destruct vertex_bij0.
    rewrite <- (surjective v) at 1. rewrite <- vlabel_iso0; auto.
  - intros. destruct lp_pregraph_iso0. destruct edge_bij0.
    rewrite <- (surjective e) at 1. rewrite <- elabel_iso0; auto.
Qed.

Lemma lp_graph_iso_exp_trans: forall
    `(g1: @LabeledGraph V E EV EE DV DE DG) g2 g3 v12 v21 e12 e21 v23 v32 e23 e32,
    label_preserving_graph_isomorphism_explicit g1 g2 v12 v21 e12 e21 ->
    label_preserving_graph_isomorphism_explicit g2 g3 v23 v32 e23 e32 ->
    label_preserving_graph_isomorphism_explicit
      g1 g3 (compose v23 v12) (compose v21 v32) (compose e23 e12) (compose e21 e32).
Proof.
  intros. destruct H, H0. split; intros; [|unfold compose..].
  - eapply pregraph_iso_exp_trans; eauto.
  - destruct lp_pregraph_iso0. rewrite vlabel_iso0, vlabel_iso1; auto.
  - destruct lp_pregraph_iso0. rewrite elabel_iso0, elabel_iso1; auto.
Qed.

Definition label_preserving_graph_isomorphism
           `(g: @LabeledGraph V E EV EE DV DE DG) g': Prop :=
  exists vmap vmap' emap emap',
    label_preserving_graph_isomorphism_explicit g g' vmap vmap' emap emap'.

Lemma lp_graph_iso_refl: forall `(g: @LabeledGraph V E EV EE DV DE DG),
    label_preserving_graph_isomorphism g g.
Proof. intros. exists id, id, id, id. apply lp_graph_iso_exp_refl. Qed.

Lemma lp_graph_iso_syn: forall `(g: @LabeledGraph V E EV EE DV DE DG) g',
    label_preserving_graph_isomorphism g g' -> label_preserving_graph_isomorphism g' g.
Proof.
  intros. destruct H as [vmap [vmap' [emap [emap' ?]]]].
  exists vmap', vmap, emap', emap. eapply lp_graph_iso_exp_sym; eauto.
Qed.

Lemma lp_graph_iso_trans: forall `(g1: @LabeledGraph V E EV EE DV DE DG) g2 g3,
    label_preserving_graph_isomorphism g1 g2 ->
    label_preserving_graph_isomorphism g2 g3 ->
    label_preserving_graph_isomorphism g1 g3.
Proof.
  intros. destruct H as [v12 [v21 [e12 [e21 ?]]]].
  destruct H0 as [v23 [v32 [e23 [e32 ?]]]].
  exists (compose v23 v12), (compose v21 v32), (compose e23 e12), (compose e21 e32).
  eapply lp_graph_iso_exp_trans; eauto.
Qed.
