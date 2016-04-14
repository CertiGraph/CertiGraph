Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Morphisms_ext.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.msl_ext.ramification_lemmas.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.dag.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.graph_morphism.
Require Import RamifyCoq.graph.local_graph_copy.
Require Import RamifyCoq.msl_application.Graph.
Require Import Coq.Logic.Classical.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Local Open Scope logic.

Class CompactCopySpatialSetting {V E GV GE Pred} {SGBA: SpatialGraphBasicAssum V E} (SGP: SpatialGraphPred V E GV GE Pred) {SGA: SpatialGraphAssum SGP} := {
  default_v: V;
  default_e: E;
  SGA_vn_default: SpatialGraphAssum_vn SGP default_v
}.

Section SpatialGraph_Copy.

Context {V E: Type}.
Context {SGBA: SpatialGraphBasicAssum V E}.
Context {GV GE Pred: Type}.
Context {SGP: SpatialGraphPred V E GV GE Pred}.
Context {SGA: SpatialGraphAssum SGP}.
Context {SGC: SpatialGraphConstructor V E V E GV GE}.
Context {L_SGC: Local_SpatialGraphConstructor V E V E GV GE}.
Context {CCSS: CompactCopySpatialSetting SGP}.

Instance MGS: WeakMarkGraph.MarkGraphSetting V.
Proof.
  apply (WeakMarkGraph.Build_MarkGraphSetting _ (fun x => default_v <> x)).
  intros; destruct_eq_dec default_v x; [right | left]; simpl; congruence.
Defined.

Global Existing Instance MGS.

Instance GMS: GraphMorphismSetting V E V E V E :=
  Build_GraphMorphismSetting _ _ _ _ _ _ (fun v => v) (fun e => e) default_v default_e.

Global Existing Instance GMS.

Notation Graph := (LabeledGraph V E V E).
Notation SGraph := (SpatialGraph V E V E).

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition vcopy1 x (g1 g2: Graph) :=
  g1 ~=~ g2 /\
  WeakMarkGraph.mark1 x g1 g2 /\
  LocalGraphCopy.vcopy1 x g1 g2.

Definition ecopy1 e (p1 p2: Graph * Graph) :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  WeakMarkGraph.nothing (src g1 e) g1 g2 /\
  LocalGraphCopy.ecopy1 e (g1, g1') (g2, g2').

Definition copy x (g1 g2: Graph) (g2': Graph) :=
  g1 ~=~ g2 /\
  WeakMarkGraph.mark x g1 g2 /\
  LocalGraphCopy.copy (WeakMarkGraph.marked g1) x g1 g2 g2'.

Definition extended_copy x (p1 p2: Graph * Graph) :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  WeakMarkGraph.mark x g1 g2 /\
  LocalGraphCopy.extended_copy (WeakMarkGraph.marked g1) x (g1, g1') (g2, g2').

Definition edge_copy g e := relation_list ((extended_copy (dst g e)) :: (ecopy1 e) :: nil).

Definition edge_copy_list g es := relation_list (map (edge_copy g) es).

Lemma edge_copy_spec: forall (g g1 g2 g1' g2': Graph) (root: V) (es_done: list E) (e0: E),
  edge_copy g e0 (g1, g1') (g2, g2') ->
  evalid g1 e0 ->
  src g1 e0 = root ->
  Same_set
    (WeakMarkGraph.marked g1)
    (let M0 := Union _ (WeakMarkGraph.marked g) (eq root) in
     let PV1 := reachable_by_through_set g (map (dst g) es_done) (Complement _ M0) in
     let M_rec := Union _ M0 PV1 in
     M_rec) ->
  LocalGraphCopy.edge_copy g root (WeakMarkGraph.marked g) (es_done, e0) (g1, g1') (g2, g2') /\
  WeakMarkGraph.componded root (WeakMarkGraph.mark (dst g e0)) g1 g2.
Proof.
  intros.
  unfold edge_copy in H.
  destruct_relation_list gg in H; destruct gg as [g3 g3'].
  destruct H as [? [? ?]], H3 as [? [? ?]].
  split.
  + cbv iota zeta in H2.
    unfold LocalGraphCopy.edge_copy.
    erewrite app_same_relation by (rewrite <- H2; reflexivity).
    split_relation_list ((g3, g3') :: nil); auto.
  + unfold WeakMarkGraph.componded.
    apply compond_intro with g3.
    Focus 2. {
      erewrite <- si_src1 in H4; [| exact H3 | exact H0].
      rewrite <- H1; auto.
    } Unfocus.
    apply compond_intro with g1; [apply WeakMarkGraph.eq_do_nothing; auto |].
    auto.
Qed.

Lemma edge_copy_spec': forall root es e0 es_done es_later (g g1 g2 g3 g2' g3': Graph),
  let g1' := single_vertex_labeledgraph (LocalGraphCopy.vmap g1 root) default_DV' default_DE' in
  vvalid g root ->
  WeakMarkGraph.unmarked g root ->
  es = es_done ++ e0 :: es_later ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  vcopy1 root g g1 ->
  relation_list
   (map (LocalGraphCopy.edge_copy g root (WeakMarkGraph.marked g))
     (cprefix es_done)) (g1, g1') (g2, g2') ->
  relation_list
   (map (fun v => WeakMarkGraph.componded root (WeakMarkGraph.mark v)) (map (dst g) es_done))
      g1 g2->
  edge_copy g e0 (g2, g2') (g3, g3') ->
  LocalGraphCopy.edge_copy g root (WeakMarkGraph.marked g) (es_done, e0) (g2, g2') (g3, g3') /\
  WeakMarkGraph.componded root (WeakMarkGraph.mark (dst g e0)) g2 g3.
Proof.
  intros.
  destruct H4 as [_ [? ?]].
  pose proof WeakMarkGraph.triple_mark1_componded_mark_list root (map (dst g) es_done) (map (dst g) (e0 :: es_later)) (map (dst g) es) g g2 H H0.
  spec H9; [apply out_edges_step_list; auto |].
  spec H9; [rewrite <- map_app; f_equal; auto |].
  spec H9; [split_relation_list (g :: g1 :: g1 :: nil) |].
    1: apply WeakMarkGraph.eq_do_nothing; auto.
    1: auto.
    1: apply WeakMarkGraph.eq_do_nothing; auto.
    1: auto.
  cbv iota zeta in H9.

  pose proof LocalGraphCopy.triple_vcopy1_edge_copy_list g g1 g2 g2' root es es_done (e0 :: es_later) (WeakMarkGraph.marked g) H H0 H2 H3 H1.
  spec H10; [intro v; destruct (node_pred_dec (WeakMarkGraph.marked g) v); auto |].
  specialize (H10 H8 H5).
  cbv iota zeta in H10.

  assert (evalid g2 e0 /\ src g e0 = root).
  Focus 1. {
    destruct H10 as [_ [? _]].
    rewrite <- (proj1 (proj2 H10)); auto.
    assert (In e0 es) by (rewrite H1, in_app_iff; simpl; auto).
    rewrite H2 in H11. auto.
  } Unfocus.

  apply edge_copy_spec; auto.
  + tauto.
  + destruct H10 as [_ [? _]], H11 as [? ?].
    erewrite <- si_src2 by eauto.
    auto.
  + destruct H9 as [_ ?]; auto.
Qed.

Lemma edge_copy_list_spec: forall root es (g g1 g2 g2': Graph),
  let g1' := single_vertex_labeledgraph (LocalGraphCopy.vmap g1 root) default_DV' default_DE' in
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  vvalid g root ->
  WeakMarkGraph.unmarked g root ->
  vcopy1 root g g1 ->
  edge_copy_list g es (g1, g1') (g2, g2') ->
  LocalGraphCopy.edge_copy_list g root es (WeakMarkGraph.marked g) (g1, g1') (g2, g2') /\
  WeakMarkGraph.componded_mark_list root (map (dst g) es) g1 g2.
Proof.
  intros.
  unfold edge_copy_list in H4.
  rewrite map_snd_cprefix' in H4.
  eapply relation_list_weaken_ind' with
    (R' := fun (p: list E * E) =>
           relation_conjunction
            (LocalGraphCopy.edge_copy g root (WeakMarkGraph.marked g) p)
            (fst_relation (WeakMarkGraph.componded root (WeakMarkGraph.mark (dst g (snd p))))))
     in H4.
  + apply relation_list_conjunction in H4.
    destruct H4.
    split; auto.
    rewrite <- map_map in H5.
    unfold fst_relation in H5.
    apply respectful_relation_list in H5.
    unfold respectful_relation in H5; simpl in H5.
    unfold WeakMarkGraph.componded_mark_list.
    rewrite map_map.
    rewrite map_snd_cprefix'.
    auto.
  + clear g2 g2' H4.
    intros.
    clear H5.
    unfold relation_conjunction, predicate_intersection; simpl.
    destruct a2 as [g2 g2'], a3 as [g3 g3'].
    unfold fst_relation, respectful_relation; simpl.
    pose proof in_cprefix _ _ _ H4.
    apply in_cprefix_cprefix in H4.
    subst bs_done.
    destruct b0 as [es_done e0]; simpl in H6 |- *.
    pose proof in_cprefix' _ _ _ H5.
    destruct H4 as [es_later ?].
    apply relation_list_conjunction in H6.
    destruct H6.
    rewrite <- (map_map (snd) (fun e => fst_relation
               (WeakMarkGraph.componded root
                  (WeakMarkGraph.mark (dst g e))))) in H8.
    rewrite map_snd_cprefix in H8.
    rewrite <- map_map in H8.
    unfold fst_relation in H8.
    apply respectful_relation_list in H8.
    unfold respectful_relation in H8; simpl in H8.
    eapply edge_copy_spec'; try eassumption.
    rewrite map_map; auto.
Qed.

Lemma vcopy1_edge_copy_list_copy: forall root es (g1 g2 g3 g3': Graph),
  let g2' := single_vertex_labeledgraph (LocalGraphCopy.vmap g2 root) default_DV' default_DE' in
  vvalid g1 root ->
  WeakMarkGraph.unmarked g1 root ->
  (forall e, In e es <-> out_edges g1 root e) ->
  NoDup es ->
  vcopy1 root g1 g2 ->
  edge_copy_list g1 es (g2, g2') (g3, g3') ->
  copy root g1 g3 g3'.
Proof.
  intros.
  pose proof edge_copy_list_spec root es g1 g2 g3 g3' H1 H2 H H0 H3 H4.
  destruct H5.
  split; [| split].
  + pose proof LocalGraphCopy.triple_vcopy1_edge_copy_list g1 g2 g3 g3' root es es nil (WeakMarkGraph.marked g1) H H0 H1 H2 (eq_sym (app_nil_r _)).
    spec H7; [intro v; destruct (node_pred_dec (WeakMarkGraph.marked g1) v); auto |].
    destruct H3 as [_ [_ ?]].
    specialize (H7 H3 H5).
    destruct H7 as [_ [? _]]; auto.
  + pose proof WeakMarkGraph.mark1_componded_mark_list_mark root (map (dst g1) es) g1 g3 H H0.
    apply H7.
    - apply out_edges_step_list; auto.
    - destruct H3 as [_ [? _]].
      split_relation_list (g1 :: g2 :: g2 :: g3 :: nil); auto; apply WeakMarkGraph.eq_do_nothing; auto.
  + destruct H3 as [_ [_ ?]].
    apply (LocalGraphCopy.vcopy1_edge_copy_list_copy g1 g2 g3 g3' root es (WeakMarkGraph.marked g1)); auto.
    intro v; destruct (node_pred_dec (WeakMarkGraph.marked g1) v); auto.
Qed.

End SpatialGraph_Copy.


