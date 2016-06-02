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
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.dag.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.graph_morphism.
Require Import RamifyCoq.graph.local_graph_copy.
Require Import RamifyCoq.msl_application.Graph.
Require Import Coq.Logic.Classical.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Local Open Scope logic.

Class CompactCopySetting V E := {
  default_v: V;
  default_e: E
}.

Section SpatialGraph_Copy.

Context {V E: Type}.
Context {SGBA: SpatialGraphBasicAssum V E}.
Context {CCS: CompactCopySetting V E}.
Context {GV GE Pred: Type}.
Context {SGP: SpatialGraphPred V E GV GE Pred}.
Context {SGA: SpatialGraphAssum SGP}.
Context {SGC: SpatialGraphConstructor V E V E GV GE}.
Context {L_SGC: Local_SpatialGraphConstructor V E V E GV GE}.
Context {SGA_vn: SpatialGraphAssum_vn SGP default_v}.
Context {SGA_vs: SpatialGraphAssum_vs SGP}.

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

Definition vcopy1 x (g1 g2 g2': Graph) :=
  g1 ~=~ g2 /\
  WeakMarkGraph.mark1 x g1 g2 /\
  LocalGraphCopy.vcopy1 x g1 g2 g2'.

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

Lemma copy_invalid_refl: forall (g: Graph) (root: V) (src0 dst0: E -> V) (default_v: V) (default_e: E),
  ~ vvalid g root ->
  copy root g g (empty_labeledgraph src0 dst0 default_v default_e).
Proof.
  intros.
  split; [| split].
  + reflexivity.
  + apply WeakMarkGraph.mark_invalid_refl; auto.
  + apply LocalGraphCopy.copy_invalid_refl; auto.
Qed.

Lemma marked_root_copy_refl: forall (g: Graph) (root: V) (src0 dst0: E -> V) (default_v: V) (default_e: E),
  WeakMarkGraph.marked g root ->
  copy root g g (empty_labeledgraph src0 dst0 default_v default_e).
Proof.
  intros.
  split; [| split].
  + reflexivity.
  + apply WeakMarkGraph.mark_marked_root_refl; auto.
  + apply LocalGraphCopy.copy_marked_root_refl; auto.
Qed.

Lemma edge_copy_si: forall (g g1 g2 g1' g2': Graph) (e0: E),
  edge_copy g e0 (g1, g1') (g2, g2') ->
  g1 ~=~ g2.
Proof.
  intros.
  unfold edge_copy in H.
  destruct_relation_list GG in H.
  destruct GG as [G G'].
  destruct H0 as [? _].
  destruct H as [? _].
  transitivity G; auto.
Qed.

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

Lemma edge_copy_spec': forall root es e0 es_done es_later (g g1 g2 g3 g1' g2' g3': Graph),
  vvalid g root ->
  WeakMarkGraph.unmarked g root ->
  es = es_done ++ e0 :: es_later ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  vcopy1 root g g1 g1' ->
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

  pose proof LocalGraphCopy.triple_vcopy1_edge_copy_list g g1 g2 g1' g2' root es es_done (e0 :: es_later) (WeakMarkGraph.marked g) H H0 H2 H3 H1.
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

Lemma vcopy1_edge_copy_list_spec: forall root es es_done es_later (g g1 g2 g1' g2': Graph),
  vvalid g root ->
  WeakMarkGraph.unmarked g root ->
  es = es_done ++ es_later ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  vcopy1 root g g1 g1' ->
  edge_copy_list g es_done (g1, g1') (g2, g2') ->
  LocalGraphCopy.edge_copy_list g root es_done (WeakMarkGraph.marked g) (g1, g1') (g2, g2') /\
  WeakMarkGraph.componded_mark_list root (map (dst g) es_done) g1 g2.
Proof.
  intros.
  unfold edge_copy_list in H5.
  rewrite map_snd_cprefix' in H5.
  eapply relation_list_weaken_ind' with
    (R' := fun (p: list E * E) =>
           relation_conjunction
            (LocalGraphCopy.edge_copy g root (WeakMarkGraph.marked g) p)
            (fst_relation (WeakMarkGraph.componded root (WeakMarkGraph.mark (dst g (snd p))))))
     in H5.
  + apply relation_list_conjunction in H5.
    destruct H5.
    split; auto.
    rewrite <- map_map in H6.
    unfold fst_relation in H6.
    apply respectful_relation_list in H6.
    unfold respectful_relation in H6; simpl in H6.
    unfold WeakMarkGraph.componded_mark_list.
    rewrite map_map.
    rewrite map_snd_cprefix'.
    auto.
  + clear g2 g2' H5.
    intros.
    clear H6.
    unfold relation_conjunction, predicate_intersection; simpl.
    destruct a2 as [g2 g2'], a3 as [g3 g3'].
    unfold fst_relation, respectful_relation; simpl.
    pose proof in_cprefix _ _ _ H5.
    apply in_cprefix_cprefix in H5.
    subst bs_done.
    destruct b0 as [es_done0 e0]; simpl in H7 |- *.
    pose proof in_cprefix' _ _ _ H6.
    destruct H5 as [es_later0 ?].
    apply relation_list_conjunction in H7.
    destruct H7.
    rewrite <- (map_map (snd) (fun e => fst_relation
               (WeakMarkGraph.componded root
                  (WeakMarkGraph.mark (dst g e))))) in H9.
    rewrite map_snd_cprefix in H9.
    rewrite <- map_map in H9.
    unfold fst_relation in H9.
    apply respectful_relation_list in H9.
    unfold respectful_relation in H9; simpl in H9.
    subst es_done.
    rewrite <- app_assoc in H1.
    eapply edge_copy_spec'; try eassumption.
    rewrite map_map; auto.
Qed.

Lemma vcopy1_edge_copy_list_copy: forall root es (g1 g2 g3 g2' g3': Graph),
  vvalid g1 root ->
  WeakMarkGraph.unmarked g1 root ->
  (forall e, In e es <-> out_edges g1 root e) ->
  NoDup es ->
  vcopy1 root g1 g2 g2' ->
  edge_copy_list g1 es (g2, g2') (g3, g3') ->
  copy root g1 g3 g3'.
Proof.
  intros.
  pose proof vcopy1_edge_copy_list_spec root es es nil g1 g2 g3 g2' g3' H H0 (eq_sym (app_nil_r _)) H1 H2 H3 H4.
  destruct H5.
  split; [| split].
  + pose proof LocalGraphCopy.triple_vcopy1_edge_copy_list g1 g2 g3 g2' g3' root es es nil (WeakMarkGraph.marked g1) H H0 H1 H2 (eq_sym (app_nil_r _)).
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
    apply (LocalGraphCopy.vcopy1_edge_copy_list_copy g1 g2 g3 g2' g3' root es (WeakMarkGraph.marked g1)); auto.
    intro v; destruct (node_pred_dec (WeakMarkGraph.marked g1) v); auto.
Qed.

Lemma vcopy1_edge_copy_list_copy_extended_copy: forall root es es_done e0 es_later (g1 g2 g3 g2' g3' g4 g4'': Graph) (x x0: V),
  vvalid g1 root ->
  WeakMarkGraph.unmarked g1 root ->
  es = es_done ++ e0 :: es_later ->
  (forall e, In e es <-> out_edges g1 root e) ->
  NoDup es ->
  vcopy1 root g1 g2 g2' ->
  edge_copy_list g1 es_done (g2, g2') (g3, g3') ->
  x = dst g1 e0 ->
  copy (dst g1 e0) g3 g4 g4'' ->
  disjointed_guard (vvalid g4'') (vvalid g3') (evalid g4'') (evalid g3') ->
  exists g4': Graph,
  extended_copy (dst g1 e0) (g3, g3') (g4, g4') /\
  guarded_labeled_graph_equiv (vvalid g4'') (evalid g4'') g4'' g4' /\
  guarded_labeled_graph_equiv (vvalid g3') (evalid g3') g3' g4'.
Proof.
  intros.
  unfold reachable_vertices_at.
  pose proof vcopy1_edge_copy_list_spec root es es_done _ g1 g2 g3 g2' g3' H H0 H1 H2 H3 H4 H5.
  destruct H9.
  pose proof LocalGraphCopy.copy_extend_copy g1 g3 g4 g3' g4'' root es es_done e0 es_later (WeakMarkGraph.marked g1) H H0 H2 H3 H1.
  spec H11; [intro v; destruct (node_pred_dec (WeakMarkGraph.marked g1) v); auto |].
  cbv zeta in H11.
  pose proof WeakMarkGraph.triple_mark1_componded_mark_list root (map (dst g1) es_done) (map (dst g1) (e0 :: es_later)) (map (dst g1) es) g1 g3 H H0.
  spec H12; [apply out_edges_step_list; auto |].
  spec H12; [rewrite <- map_app; f_equal; auto |].
  spec H12; [split_relation_list (g1 :: g2 :: g2 :: nil) |].
    1: apply WeakMarkGraph.eq_do_nothing; auto.
    1: destruct H4 as [? [? ?]]; auto.
    1: apply WeakMarkGraph.eq_do_nothing; auto.
    1: auto.
  cbv iota zeta in H12.
  destruct H12 as [_ ?].

  rewrite <- H12 in H11.
  spec H11; [destruct H7 as [? [? ?]]; auto |].
  spec H11; [auto |].
  spec H11; [intros v; rewrite <- (app_same_set H12); destruct (node_pred_dec (WeakMarkGraph.marked g3) v); auto |].
  destruct H11 as [g4' [? [? ?]]].
  rewrite <- H12 in H11.
  exists g4'.
  split; [| split]; auto.
  destruct H7 as [? [? ?]]; split; [| split]; auto.
Qed.

Lemma vcopy1_edge_copy_list_weak_copy_extended_copy: forall {P: Graph -> Type} {NP: NormalGeneralGraph P},
  forall root es es_done e0 es_later (g1 g2 g3 g2' g3' g4 g4'': Graph) (x x0: V),
  vvalid g1 root ->
  WeakMarkGraph.unmarked g1 root ->
  es = es_done ++ e0 :: es_later ->
  (forall e, In e es <-> out_edges g1 root e) ->
  NoDup es ->
  vcopy1 root g1 g2 g2' ->
  edge_copy_list g1 es_done (g2, g2') (g3, g3') ->
  x = dst g1 e0 ->
  copy (dst g1 e0) g3 g4 g4'' ->
  disjointed_guard (vvalid g4'') (vvalid g3') (evalid g4'') (evalid g3') ->
  (exists Pg3': P (gpredicate_sub_labeledgraph
                    (fun v' => LocalGraphCopy.vmap g3 root <> v')
                    (fun e' => ~ In e' (map (LocalGraphCopy.emap g3) es_done)) g3'), True) ->
  (exists Pg4'': P g4'', True) ->
  exists g4': Graph,
  extended_copy (dst g1 e0) (g3, g3') (g4, g4') /\
  (exists Pg4': P (gpredicate_sub_labeledgraph
                    (fun v' => v' <> LocalGraphCopy.vmap g4 root)
                    (fun e' => ~ In e' (map (LocalGraphCopy.emap g4) es_done)) g4'), True) /\
  guarded_labeled_graph_equiv (vvalid g4'') (evalid g4'') g4'' g4' /\
  guarded_labeled_graph_equiv (vvalid g3') (evalid g3') g3' g4'.
Proof.
Admitted.

End SpatialGraph_Copy.


