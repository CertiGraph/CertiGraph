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

Section SpatialGraph_Copy.

Context {V E: Type}.
Context {SGBA: SpatialGraphBasicAssum V E}.
Context {DV DE: Type}.
Context {GV GE Pred: Type}.
Context {SGP: SpatialGraphPred V E GV GE Pred}.
Context {SGA: SpatialGraphAssum SGP}.
Context {MGS: WeakMarkGraph.MarkGraphSetting DV}.
Context {GMS: GraphMorphismSetting DV DE V E DV DE}.

Notation Graph := (LabeledGraph V E DV DE).
Notation SGraph := (SpatialGraph V E GV GE).

Variable compute_vgamma: Graph -> V -> GV.
Variable compute_egamma: Graph -> E -> GE.

Hypothesis compute_vgamma_local: forall (G1 G2: Graph) (x: V),
  ((predicate_partial_labeledgraph G1 (eq x)) ~=~ (predicate_partial_labeledgraph G1 (eq x)))%LabeledGraph ->
  compute_vgamma G1 x = compute_vgamma G2 x.

Hypothesis compute_egamma_local: forall (G1 G2: Graph) (e: E),
  evalid G1 e ->
  evalid G2 e ->
  elabel G1 e = elabel G2 e ->
  src G1 e = src G2 e ->
  dst G1 e = dst G2 e ->
  compute_egamma G1 e = compute_egamma G2 e.

Definition Graph_SpatialGraph (G: Graph) : SGraph :=
  Build_SpatialGraph _ _ _ _ _ _ G (compute_vgamma G) (compute_egamma G).

Lemma GSG_VGenPreserve: forall (G: Graph) x lx gx,
  gx = vgamma (Graph_SpatialGraph (labeledgraph_vgen G x lx)) x ->
  (Graph_SpatialGraph (labeledgraph_vgen G x lx)) -=- (spatialgraph_vgen (Graph_SpatialGraph G) x gx).
Proof.
  intros. subst.
  split; [| split].
  + reflexivity.
  + intros; simpl.
    destruct_eq_dec x v.
    - subst; auto.
    - apply compute_vgamma_local; auto.
      eapply si_stronger_partial_labeledgraph_simple; [| apply lg_vgen_stable].
      hnf; unfold Ensembles.In; intros.
      congruence.
  + intros; simpl.
    apply compute_egamma_local; auto.
Qed.

Lemma GSG_PartialGraphPreserve: forall (G: Graph) (p: V -> Prop),
  (predicate_partial_spatialgraph (Graph_SpatialGraph G) p) -=-
  (Graph_SpatialGraph (predicate_partial_labeledgraph G p)).
Proof.
  intros.
  split; [| split].
  + reflexivity.
  + simpl; intros.
    apply compute_vgamma_local; auto.
    reflexivity.
  + simpl; intros.
    apply compute_egamma_local; auto.
    destruct H; auto.
Qed.

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
  vcopy1 root g g1 ->
  vvalid g root ->
  WeakMarkGraph.unmarked g root ->
  vcopy1 root g g1 ->
  (forall e, In e es <-> out_edges g root e) ->
  WeakMarkGraph.mark1 root g g1 ->
  edge_copy_list g es (g1, g1') (g2, g2') ->
  LocalGraphCopy.edge_copy_list g root es (WeakMarkGraph.marked g) (g1, g1') (g2, g2') /\
  WeakMarkGraph.componded_mark_list root (map (dst g) es) g1 g2.
Proof.
  intros.
  unfold edge_copy_list in H7.
  rewrite map_snd_cprefix' in H7.
  eapply relation_list_weaken_ind' with
    (R' := fun (p: list E * E) =>
           relation_conjunction
            (LocalGraphCopy.edge_copy g root (WeakMarkGraph.marked g) p)
            (fst_relation (WeakMarkGraph.componded root (WeakMarkGraph.mark (dst g (snd p))))))
     in H7.
  + apply relation_list_conjunction in H7.
    destruct H7.
    split; auto.
    rewrite <- map_map in H8.
    unfold fst_relation in H8.
    apply respectful_relation_list in H8.
    unfold respectful_relation in H8; simpl in H8.
    unfold WeakMarkGraph.componded_mark_list.
    rewrite map_map.
    rewrite map_snd_cprefix'.
    auto.
  + clear g2 g2' H7.
    intros.
    clear H8.
    unfold relation_conjunction, predicate_intersection; simpl.
    destruct a2 as [g2 g2'], a3 as [g3 g3'].
    unfold fst_relation, respectful_relation; simpl.
    pose proof in_cprefix _ _ _ H7.
    apply in_cprefix_cprefix in H7.
    subst bs_done.
    destruct b0 as [es_done e0]; simpl in H9 |- *.
    pose proof in_cprefix' _ _ _ H8.
    destruct H7 as [es_later ?].
    apply relation_list_conjunction in H9.
    destruct H9.
    rewrite <- (map_map (snd) (fun e => fst_relation
               (WeakMarkGraph.componded root
                  (WeakMarkGraph.mark (dst g e))))) in H11.
    rewrite map_snd_cprefix in H11.
    rewrite <- map_map in H11.
    unfold fst_relation in H11.
    apply respectful_relation_list in H11.
    unfold respectful_relation in H11; simpl in H11.
    eapply edge_copy_spec'; try eassumption.
    rewrite map_map; auto.
Qed.

Lemma vcopy1_edge_copy_list_copy: forall root es (g1 g2 g3 g3': Graph),
  let g2' := single_vertex_labeledgraph (LocalGraphCopy.vmap g1 root) default_DV' default_DE' in
  vvalid g1 root ->
  WeakMarkGraph.unmarked g1 root ->
  (forall e, In e es <-> out_edges g1 root e) ->
  vcopy1 root g1 g2 ->
  edge_copy_list g1 es (g2, g2') (g3, g3') ->
  copy root g1 g3 g3'.
Proof.
  intros.
  destruct H2 as [? [? ?]].
Abort.

End SpatialGraph_Copy.


(*

https://www.zhihu.com/question/34406872#answer-20111906
https://www.zhihu.com/question/24375292#answer-24963090
https://www.zhihu.com/question/37703381#answer-24711147
https://www.zhihu.com/question/38303758#answer-25773456
http://www.lwxsw.org/books/23/23978/7948501.html
https://www.zhihu.com/search?type=question&q=%E5%BF%AB%E6%92%AD+%E6%96%B0%E5%8D%8E%E7%A4%BE
https://www.zhihu.com/question/39334589
https://www.zhihu.com/question/39265386
http://finance.sina.com.cn/review/jcgc/2016-01-11/doc-ifxnkkuy7861463.shtml
http://media.people.com.cn/n1/2016/0112/c40606-28039812.html
http://zqb.cyol.com/html/2016-01/12/nw.D110000zgqnb_20160112_1-06.htm

*)