Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Morphisms_ext.
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

Local Open Scope logic.

Class CompactCopySetting V E M := {
  default_v: V;
  default_e: E;
  default_g: M
}.

Section PointwiseGraph_Copy.

Context {V E M: Type}.
Context {SGBA: PointwiseGraphBasicAssum V E}.
Context {CCS: CompactCopySetting V E M}.
Context {GV GE Pred: Type}.
Context {SGP: PointwiseGraphPred V E GV GE Pred}.
Context {SGA: PointwiseGraphAssum SGP}.
Context {SGC: PointwiseGraphConstructor V E V E M GV GE}.
Context {L_SGC: Local_PointwiseGraphConstructor V E V E M GV GE}.
Context {SGA_vn: PointwiseGraphAssum_vn SGP default_v}.
Context {SGA_vs: PointwiseGraphAssum_vs SGP}.

Instance MGS: WeakMarkGraph.MarkGraphSetting V.
Proof.
  apply (WeakMarkGraph.Build_MarkGraphSetting _ (fun x => default_v <> x)).
  intros; destruct_eq_dec default_v x; [right | left]; simpl; congruence.
Defined.

Global Existing Instance MGS.

Instance GMS: GraphMorphismSetting V E M V E V E M :=
  Build_GraphMorphismSetting _ _ _ _ _ _ _ _ (fun v => v) (fun e => e) default_v default_e default_g.

Global Existing Instance GMS.

Notation Graph := (LabeledGraph V E V E M).
Notation SGraph := (PointwiseGraph V E V E).

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

Lemma copy_invalid_refl: forall (g: Graph) (root: V) (src0 dst0: E -> V) (default_v: V) (default_e: E) (default_g : M),
  ~ vvalid g root ->
  copy root g g (empty_labeledgraph src0 dst0 default_v default_e default_g).
Proof.
  intros.
  split; [| split].
  + reflexivity.
  + apply WeakMarkGraph.mark_invalid_refl; auto.
  + apply LocalGraphCopy.copy_invalid_refl; auto.
Qed.

Lemma marked_root_copy_refl: forall (g: Graph) (root: V) (src0 dst0: E -> V) (default_v: V) (default_e: E) (default_g : M),
  WeakMarkGraph.marked g root ->
  copy root g g (empty_labeledgraph src0 dst0 default_v default_e default_g).
Proof.
  intros.
  split; [| split].
  + reflexivity.
  + apply WeakMarkGraph.mark_marked_root_refl; auto.
  + apply LocalGraphCopy.copy_marked_root_refl; auto.
Qed.

Lemma copy_vvalid_weak_eq: forall (g1 g2 g2'': Graph) x x0,
  ~ vvalid g1 x /\ ~ vvalid g2'' x0 \/ x0 = LocalGraphCopy.vmap g2 x ->
  copy x g1 g2 g2'' ->
  Same_set (vvalid g2'') (reachable g2'' x0).
Proof.
  intros.
  eapply (LocalGraphCopy.copy_vvalid_weak_eq g1 g2 g2'' _ x x0); auto.
  destruct H0 as [_ [_ ?]]; eauto.
Qed.

Lemma vcopy1_copied_root_valid: forall (G G1 G1': Graph) x x0,
  vcopy1 x G G1 G1' ->
  x0 = LocalGraphCopy.vmap G1 x ->
  vvalid G1' x0.
Proof.
  intros.
  apply (LocalGraphCopy.vcopy1_copied_root_valid G G1 G1' x x0); auto.
  destruct H as [_ [_ ?]]; eauto.
Qed.

Lemma extended_copy_vvalid_mono: forall (G1 G2 G1' G2': Graph) x x0,
  extended_copy x (G1, G1') (G2, G2') ->
  vvalid G1' x0 ->
  vvalid G2' x0.
Proof.
  intros.
  eapply (LocalGraphCopy.extended_copy_vvalid_mono G1 G2 G1' G2' _ x x0); auto.
  destruct H as [_ [_ ?]]; eauto.
Qed.

Lemma ecopy1_vvalid_mono: forall (G1 G2 G1' G2': Graph) e x0,
  ecopy1 e (G1, G1') (G2, G2') ->
  vvalid G1' x0 ->
  vvalid G2' x0.
Proof.
  intros.
  eapply (LocalGraphCopy.ecopy1_vvalid_mono G1 G2 G1' G2' e x0); auto.
  destruct H as [_ [_ ?]]; eauto.
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
    2: {
      erewrite <- si_src1 in H4; [| exact H3 | exact H0].
      rewrite <- H1; auto.
    }
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
  1: {
    destruct H10 as [_ [? _]].
    rewrite <- (proj1 (proj2 H10)); auto.
    assert (In e0 es) by (rewrite H1, in_app_iff; simpl; auto).
    rewrite H2 in H11. auto.
  }

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

Lemma extend_copy_emap_root: forall (g g1 g2 g3 g1' g2' g3' : Graph) root es es_done e0 es_later,
  vvalid g root ->
  WeakMarkGraph.unmarked g root ->
  es = es_done ++ e0 :: es_later ->
  (forall e : E, In e es <-> out_edges g root e) ->
  NoDup es ->
  vcopy1 root g g1 g1' ->
  edge_copy_list g es_done (g1, g1') (g2, g2') ->
  extended_copy (dst g e0) (g2, g2') (g3, g3') ->
  map (LocalGraphCopy.emap g2) es_done = map (LocalGraphCopy.emap g3) es_done.
Proof.
  intros.
  destruct (vcopy1_edge_copy_list_spec root es es_done _ g g1 g2 g1' g2' H H0 H1 H2 H3 H4 H5).
  pose proof WeakMarkGraph.triple_mark1_componded_mark_list root (map (dst g) es_done) (map (dst g) (e0 :: es_later)) (map (dst g) es) g g2 H H0.
  spec H9; [apply out_edges_step_list; auto |].
  spec H9; [rewrite <- map_app; f_equal; auto |].
  spec H9; [split_relation_list (g :: g1 :: g1 :: nil) |].
    1: apply WeakMarkGraph.eq_do_nothing; auto.
    1: destruct H4 as [? [? ?]]; auto.
    1: apply WeakMarkGraph.eq_do_nothing; auto.
    1: auto.
  cbv iota zeta in H9.
  destruct H9 as [_ ?].

  eapply LocalGraphCopy.extend_copy_emap_root; eauto.
  + intros; destruct (node_pred_dec (WeakMarkGraph.marked g) v); auto.
  + destruct H4 as [_ [_ ?]]; auto.
  + intros; rewrite <- (app_same_set H9).
    destruct (node_pred_dec (WeakMarkGraph.marked g2) v); auto.
  + rewrite <- H9.
    destruct H6 as [_ [_ ?]]. exact e.
Qed.

Lemma extended_copy_vmap_root: forall (g1 g2 g1' g2': Graph) x x0,
  WeakMarkGraph.marked g1 x0 ->
  extended_copy x (g1, g1') (g2, g2') ->
  LocalGraphCopy.vmap g1 x0 = LocalGraphCopy.vmap g2 x0.
Proof.
  intros.
  destruct H0 as [_ [_ ?]]; eapply (LocalGraphCopy.extended_copy_vmap_root g1 g2 g1' g2' x x0); eauto.
Qed.

Lemma ecopy1_vmap_root: forall (g1 g2 g1' g2': Graph) e x0,
  ecopy1 e (g1, g1') (g2, g2') ->
  LocalGraphCopy.vmap g1 x0 = LocalGraphCopy.vmap g2 x0.
Proof.
  intros.
  destruct H as [_ [_ ?]].
  apply (LocalGraphCopy.ecopy1_vmap_root g1 g2 g1' g2' e x0); auto.
Qed.


(*
(* might be useful for non-bigraph cases *)
Lemma vcopy1_edge_copy_list_vmap_root: forall root es es_done es_later (g g1 g2 g1' g2': Graph),
  vvalid g root ->
  WeakMarkGraph.unmarked g root ->
  es = es_done ++ es_later ->
  (forall e, In e es <-> out_edges g root e) ->
  NoDup es ->
  vcopy1 root g g1 g1' ->
  edge_copy_list g es_done (g1, g1') (g2, g2') ->
  LocalGraphCopy.vmap g1 root = LocalGraphCopy.vmap g2 root.
Proof.
  intros.
  destruct (vcopy1_edge_copy_list_spec root es es_done _ g g1 g2 g1' g2' H H0 H1 H2 H3 H4 H5).
  pose proof WeakMarkGraph.triple_mark1_componded_mark_list root (map (dst g) es_done) (map (dst g) es_later) (map (dst g) es) g g2 H H0.
  spec H8; [apply out_edges_step_list; auto |].
  spec H8; [rewrite <- map_app; f_equal; auto |].
  spec H8; [split_relation_list (g :: g1 :: g1 :: nil) |].
    1: apply WeakMarkGraph.eq_do_nothing; auto.
    1: destruct H4 as [? [? ?]]; auto.
    1: apply WeakMarkGraph.eq_do_nothing; auto.
    1: auto.
  cbv iota zeta in H8.
  destruct H8 as [_ ?].

  pose proof LocalGraphCopy.triple_vcopy1_edge_copy_list g g1 g2 g1' g2' root es es_done es_later (WeakMarkGraph.marked g) H H0 H2 H3 H1.
  spec H9; [intro v; destruct (node_pred_dec (WeakMarkGraph.marked g) v); auto |].
  specialize (H9 (proj2 (proj2 H4)) H6).

  destruct H9 as [_ [_ [_ [? _]]]].

Lemma vcopy1_edge_copy_list_extended_copy_vmap_root: forall root es es_done e0 es_later (g1 g2 g3 g2' g3' g4 g4'': Graph),
  vvalid g1 root ->
  WeakMarkGraph.unmarked g1 root ->
  es = es_done ++ e0 :: es_later ->
  (forall e, In e es <-> out_edges g1 root e) ->
  NoDup es ->
  vcopy1 root g1 g2 g2' ->
  edge_copy_list g1 es_done (g2, g2') (g3, g3') ->
  copy (dst g1 e0) g3 g4 g4'' ->
  disjointed_guard (vvalid g4'') (vvalid g3') (evalid g4'') (evalid g3') ->
  exists g4': Graph,
  extended_copy (dst g1 e0) (g3, g3') (g4, g4') /\
*)
Lemma vcopy1_edge_copy_list_copy_extended_copy: forall root es es_done e0 es_later (g1 g2 g3 g2' g3' g4 g4'': Graph),
  vvalid g1 root ->
  WeakMarkGraph.unmarked g1 root ->
  es = es_done ++ e0 :: es_later ->
  (forall e, In e es <-> out_edges g1 root e) ->
  NoDup es ->
  vcopy1 root g1 g2 g2' ->
  edge_copy_list g1 es_done (g2, g2') (g3, g3') ->
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
  destruct H8.
  pose proof LocalGraphCopy.copy_extend_copy g1 g3 g4 g3' g4'' root es es_done e0 es_later (WeakMarkGraph.marked g1) H H0 H2 H3 H1.
  spec H10; [intro v; destruct (node_pred_dec (WeakMarkGraph.marked g1) v); auto |].
  cbv zeta in H10.
  pose proof WeakMarkGraph.triple_mark1_componded_mark_list root (map (dst g1) es_done) (map (dst g1) (e0 :: es_later)) (map (dst g1) es) g1 g3 H H0.
  spec H11; [apply out_edges_step_list; auto |].
  spec H11; [rewrite <- map_app; f_equal; auto |].
  spec H11; [split_relation_list (g1 :: g2 :: g2 :: nil) |].
    1: apply WeakMarkGraph.eq_do_nothing; auto.
    1: destruct H4 as [? [? ?]]; auto.
    1: apply WeakMarkGraph.eq_do_nothing; auto.
    1: auto.
  cbv iota zeta in H11.
  destruct H11 as [_ ?].

  rewrite <- H11 in H10.
  spec H10; [destruct H6 as [? [? ?]]; auto |].
  spec H10; [auto |].
  spec H10; [intros v; rewrite <- (app_same_set H11); destruct (node_pred_dec (WeakMarkGraph.marked g3) v); auto |].
  destruct H10 as [g4' [? [? ?]]].
  rewrite <- H11 in H10.
  exists g4'.
  split; [| split]; auto.
  destruct H6 as [? [? ?]]; split; [| split]; auto.
Qed.

Lemma copy_and_extended_copy: forall g1 g1' g2 g2' g2'' x0,
  copy x0 g1 g2 g2'' ->
  extended_copy x0 (g1, g1') (g2, g2') ->
  Prop_join (vvalid g1') (vvalid g2'') (vvalid g2').
Proof.
  intros.
  destruct H as [_ [_ ?]].
  destruct H0 as [_ [_ ?]].
  destruct H as [_ [_ [_ [? [? _]]]]].
  destruct H0 as [_ [_ [_ [? _]]]].
  destruct H0 as [? [? _]].
  rewrite <- H in H0.
  rewrite <- H1 in H2.
  auto.
Qed.
(*
Lemma vcopy1_edge_copy_list_copy_extended_copy': forall root es es_done e0 es_later (g1 g2 g3 g2' g3' g4 g4'': Graph),
  vvalid g1 root ->
  WeakMarkGraph.unmarked g1 root ->
  es = es_done ++ e0 :: es_later ->
  (forall e, In e es <-> out_edges g1 root e) ->
  NoDup es ->
  vcopy1 root g1 g2 g2' ->
  edge_copy_list g1 es_done (g2, g2') (g3, g3') ->
  copy (dst g1 e0) g3 g4 g4'' ->
  disjointed_guard (vvalid g4'') (vvalid g3') (evalid g4'') (evalid g3') ->
  exists g4': Graph,
  extended_copy (dst g1 e0) (g3, g3') (g4, g4') /\
  (Included (vvalid g4'') (vguard g4'') -> Included (vvalid g4'') (vguard g4') -> vertices_identical (vvalid g4'') (Graph_PointwiseGraph g4'') (Graph_PointwiseGraph g4')) /\
  (Included
     (Intersection _ (vvalid g3') (fun x1 => LocalGraphCopy.vmap g2 root <> x1)) 
     (vguard g3') -> Included
     (Intersection _ (vvalid g3') (fun x1 => LocalGraphCopy.vmap g2 root <> x1)) 
     (vguard g4') -> vertices_identical
     (Intersection _ (vvalid g3') (fun x1 => LocalGraphCopy.vmap g2 root <> x1)) (Graph_PointwiseGraph g3') (Graph_PointwiseGraph g4')).
Proof.
  intros.
  unfold reachable_vertices_at.
  pose proof vcopy1_edge_copy_list_spec root es es_done _ g1 g2 g3 g2' g3' H H0 H1 H2 H3 H4 H5.
  destruct H8.
  pose proof LocalGraphCopy.copy_extend_copy' g1 g3 g4 g3' g4'' root es es_done e0 es_later (WeakMarkGraph.marked g1) H H0 H2 H3 H1.
  spec H10; [intro v; destruct (node_pred_dec (WeakMarkGraph.marked g1) v); auto |].
  cbv zeta in H10.
  pose proof WeakMarkGraph.triple_mark1_componded_mark_list root (map (dst g1) es_done) (map (dst g1) (e0 :: es_later)) (map (dst g1) es) g1 g3 H H0.
  spec H11; [apply out_edges_step_list; auto |].
  spec H11; [rewrite <- map_app; f_equal; auto |].
  spec H11; [split_relation_list (g1 :: g2 :: g2 :: nil) |].
    1: apply WeakMarkGraph.eq_do_nothing; auto.
    1: destruct H4 as [? [? ?]]; auto.
    1: apply WeakMarkGraph.eq_do_nothing; auto.
    1: auto.
  cbv iota zeta in H11.
  destruct H11 as [_ ?].

  rewrite <- H11 in H10.
  spec H10; [destruct H6 as [? [? ?]]; auto |].
  spec H10; [auto |].
  spec H10; [intros v; rewrite <- (app_same_set H11); destruct (node_pred_dec (WeakMarkGraph.marked g3) v); auto |].
  spec H10; [admit |].
  destruct H10 as [g4' [? [? ?]]].
  rewrite <- H11 in H10.
  exists g4'.
  assert (extended_copy (dst g1 e0) (g3, g3') (g4, g4')) by (destruct H6 as [? [? ?]]; split; [| split]; auto).
  split; [| split]; auto.
  + intros; apply GSG_PartialGraphPreserve; auto.
    - apply Included_refl.
    - pose proof copy_and_extended_copy _ _ _ _ _ _ H6 H14.
      unfold Included, Ensembles.In; intros.
      rewrite (proj1 H17); auto.
  + intros; apply GSG_PartialGraphPreserve; auto.
    - apply Intersection1_Included, Included_refl.
    - apply Intersection1_Included.
      pose proof copy_and_extended_copy _ _ _ _ _ _ H6 H14.
      unfold Included, Ensembles.In; intros.
      rewrite (proj1 H17); auto.
    - eapply si_stronger_partial_labeledgraph_simple; [| exact H13].
      apply Intersection1_Included, Included_refl.
Qed.
*)
Lemma vcopy1_edge_copy_list_weak_copy_extended_copy: forall {P: Graph -> Type} {NP: NormalGeneralGraph P},
  forall root es es_done e0 es_later (g1 g2 g3 g2' g3' g4 g4'': Graph) (root0: V),
  vvalid g1 root ->
  WeakMarkGraph.unmarked g1 root ->
  es = es_done ++ e0 :: es_later ->
  (forall e, In e es <-> out_edges g1 root e) ->
  NoDup es ->
  vcopy1 root g1 g2 g2' ->
  edge_copy_list g1 es_done (g2, g2') (g3, g3') ->
  root0 = LocalGraphCopy.vmap g2 root ->
  copy (dst g1 e0) g3 g4 g4'' ->
  disjointed_guard (vvalid g4'') (vvalid g3') (evalid g4'') (evalid g3') ->
  (exists Pg3': P (gpredicate_sub_labeledgraph
                    (fun v' => root0 <> v')
                    (fun e' => ~ In e' (map (LocalGraphCopy.emap g3) es_done)) g3'), True) ->
  (exists Pg4'': P g4'', True) ->
  exists g4': Graph,
  extended_copy (dst g1 e0) (g3, g3') (g4, g4') /\
  (exists Pg4': P (gpredicate_sub_labeledgraph
                    (fun v' => root0 <> v')
                    (fun e' => ~ In e' (map (LocalGraphCopy.emap g4) es_done)) g4'), True) /\
  guarded_labeled_graph_equiv (vvalid g4'') (evalid g4'') g4'' g4' /\
  guarded_labeled_graph_equiv (vvalid g3') (evalid g3') g3' g4'.
Proof.
  intros.
  pose proof vcopy1_edge_copy_list_copy_extended_copy root es es_done e0 es_later g1 g2 g3 g2' g3' g4 g4''.
  repeat (spec H11; [auto |]).
  destruct H11 as [g4' [? [? ?]]].
  exists g4'; split; [| split; [| split]]; auto.
  destruct H9 as [? _], H10 as [? _].
  apply (lge_preserved _
          (gpredicate_sub_labeledgraph
            (Intersection _ (vvalid g3') (fun v' : V => root0 <> v'))
            (Intersection _ (evalid g3') (fun e' : E => ~ In e' (map (LocalGraphCopy.emap g3) es_done))) g4')) in x.
  2: {
    etransitivity.
    + apply gpredicate_sub_labeledgraph_equiv.
      - symmetry; apply Intersection_absort_left.
        apply Intersection1_Included, Included_refl.
      - symmetry; apply Intersection_absort_left.
        apply Intersection1_Included, Included_refl.
    + eapply stronger_gpredicate_sub_labeledgraph_simple; [| | eauto].
      - apply Intersection1_Included, Included_refl.
      - apply Intersection1_Included, Included_refl.
  }
  apply (lge_preserved _ (gpredicate_sub_labeledgraph (vvalid g4'') (evalid g4'') g4')) in x0.
  2: {
    etransitivity.
    + symmetry; apply gpredicate_sub_labeledgraph_self.
    + eapply stronger_gpredicate_sub_labeledgraph_simple; [| | eauto].
      - apply Included_refl.
      - apply Included_refl.
  }
  eexists; auto.
  apply (lge_preserved
          (gpredicate_sub_labeledgraph
            (Intersection _ (vvalid g4') (fun v' : V => root0 <> v'))
            (Intersection _ (evalid g4') (fun e' : E => ~ In e' (map (LocalGraphCopy.emap g4) es_done))) g4')).
  1: {
    apply gpredicate_sub_labeledgraph_equiv.
    + apply Intersection_absort_left.
      apply Intersection1_Included, Included_refl.
    + apply Intersection_absort_left.
      apply Intersection1_Included, Included_refl.
  }
  eapply join_preserved; [| | exact x | exact x0].
  + destruct H11 as [_ [_ HH]].
    destruct HH as [_ [_ [_ [HH _]]]].
    destruct H7 as [_ [_ ?]].
    destruct HH as [? _].
    destruct H7 as [_ [_ [_ [? _]]]].
    rewrite <- H7 in H9.
    apply Prop_join_shrink1; auto.
    destruct (vcopy1_edge_copy_list_spec root _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5).
    eapply LocalGraphCopy.edge_copy_list_vvalid_mono in H10; [exact H10 |].
    destruct H4 as [_ [_ ?]].
    eapply LocalGraphCopy.vcopy1_copied_root_valid in H4; eauto.
  + replace (map (@LocalGraphCopy.emap V E V E (@SGBA_VE V E SGBA)
                    (@SGBA_EE V E SGBA) V E M V E M GMS g4) es_done) with (map (LocalGraphCopy.emap g3) es_done)
      by (apply (extend_copy_emap_root g1 g2 g3 g4 g2' g3' g4' root es es_done e0 es_later); auto).
    destruct H11 as [_ [_ HH]].
    destruct HH as [_ [_ [_ [HH _]]]].
    destruct H7 as [_ [_ ?]].
    destruct HH as [_ [? _]].
    destruct H7 as [_ [_ [_ [_ [? _]]]]].
    rewrite <- H7 in H9.
    apply Prop_join_shrink; auto.
    unfold Included, Ensembles.In.
    intros e ? ?.
    destruct H9 as [_ ?].
    apply (H9 e); auto.
    destruct (vcopy1_edge_copy_list_spec root _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5).
    eapply (LocalGraphCopy.vcopy1_edge_copy_list_mapped_root_edge_evalid g1 g2 g3 g2' g3'); eauto.
      1: intros; destruct (node_pred_dec (WeakMarkGraph.marked g1) v); auto.
      1: destruct H4 as [? [? ?]]; auto.
Qed.

Lemma vcopy1_edge_copy_list_weak_copy_extended_copy': forall {P: Graph -> Type} {NP: NormalGeneralGraph P},
  forall root es es_done e0 es_later (g1 g2 g3 g2' g3' g4 g4'': Graph) (root0: V),
  vvalid g1 root ->
  WeakMarkGraph.unmarked g1 root ->
  es = es_done ++ e0 :: es_later ->
  (forall e, In e es <-> out_edges g1 root e) ->
  NoDup es ->
  vcopy1 root g1 g2 g2' ->
  edge_copy_list g1 es_done (g2, g2') (g3, g3') ->
  root0 = LocalGraphCopy.vmap g2 root ->
  copy (dst g1 e0) g3 g4 g4'' ->
  disjointed_guard (vvalid g4'') (vvalid g3') (evalid g4'') (evalid g3') ->
  (exists Pg3': P (gpredicate_sub_labeledgraph
                    (fun v' => root0 <> v')
                    (fun e' => ~ In e' (map (LocalGraphCopy.emap g3) es_done)) g3'), True) ->
  (exists Pg4'': P g4'', True) ->
  exists g4': Graph,
  extended_copy (dst g1 e0) (g3, g3') (g4, g4') /\
  (exists Pg4': P (gpredicate_sub_labeledgraph
                    (fun v' => root0 <> v')
                    (fun e' => ~ In e' (map (LocalGraphCopy.emap g4) es_done)) g4'), True) /\
  (Included (vvalid g4'') (vguard g4'') -> Included (vvalid g4'') (vguard g4') -> vertices_identical (vvalid g4'') (Graph_PointwiseGraph g4'') (Graph_PointwiseGraph g4')) /\
  (Included
     (Intersection _ (vvalid g3') (fun x1 => LocalGraphCopy.vmap g2 root <> x1)) 
     (vguard g3') -> Included
     (Intersection _ (vvalid g3') (fun x1 => LocalGraphCopy.vmap g2 root <> x1)) 
     (vguard g4') -> vertices_identical
     (Intersection _ (vvalid g3') (fun x1 => LocalGraphCopy.vmap g2 root <> x1)) (Graph_PointwiseGraph g3') (Graph_PointwiseGraph g4')).
Proof.
  intros.
  pose proof vcopy1_edge_copy_list_copy_extended_copy root es es_done e0 es_later g1 g2 g3 g2' g3' g4 g4''.
  repeat (spec H11; [auto |]).
  destruct H11 as [g4' [? [? ?]]].
  exists g4'; split; [| split]; auto.
  1: {
    destruct H9 as [? _], H10 as [? _].
    apply (lge_preserved _
            (gpredicate_sub_labeledgraph
              (Intersection _ (vvalid g3') (fun v' : V => root0 <> v'))
              (Intersection _ (evalid g3') (fun e' : E => ~ In e' (map (LocalGraphCopy.emap g3) es_done))) g4')) in x.
    2: {
      etransitivity.
      + apply gpredicate_sub_labeledgraph_equiv.
        - symmetry; apply Intersection_absort_left.
          apply Intersection1_Included, Included_refl.
        - symmetry; apply Intersection_absort_left.
          apply Intersection1_Included, Included_refl.
      + eapply stronger_gpredicate_sub_labeledgraph_simple; [| | eauto].
        - apply Intersection1_Included, Included_refl.
        - apply Intersection1_Included, Included_refl.
    }
    apply (lge_preserved _ (gpredicate_sub_labeledgraph (vvalid g4'') (evalid g4'') g4')) in x0.
    2: {
      etransitivity.
      + symmetry; apply gpredicate_sub_labeledgraph_self.
      + eapply stronger_gpredicate_sub_labeledgraph_simple; [| | eauto].
        - apply Included_refl.
        - apply Included_refl.
    }
    eexists; auto.
    apply (lge_preserved
            (gpredicate_sub_labeledgraph
              (Intersection _ (vvalid g4') (fun v' : V => root0 <> v'))
              (Intersection _ (evalid g4') (fun e' : E => ~ In e' (map (LocalGraphCopy.emap g4) es_done))) g4')).
    1: {
      apply gpredicate_sub_labeledgraph_equiv.
      + apply Intersection_absort_left.
        apply Intersection1_Included, Included_refl.
      + apply Intersection_absort_left.
        apply Intersection1_Included, Included_refl.
    }
    eapply join_preserved; [| | exact x | exact x0].
    + destruct H11 as [_ [_ HH]].
      destruct HH as [_ [_ [_ [HH _]]]].
      destruct H7 as [_ [_ ?]].
      destruct HH as [? _].
      destruct H7 as [_ [_ [_ [? _]]]].
      rewrite <- H7 in H9.
      apply Prop_join_shrink1; auto.
      destruct (vcopy1_edge_copy_list_spec root _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5).
      eapply LocalGraphCopy.edge_copy_list_vvalid_mono in H10; [exact H10 |].
      destruct H4 as [_ [_ ?]].
      eapply LocalGraphCopy.vcopy1_copied_root_valid in H4; eauto.
    + replace (map (@LocalGraphCopy.emap V E V E (@SGBA_VE V E SGBA)
                      (@SGBA_EE V E SGBA) V E M V E M GMS g4) es_done) with (map (LocalGraphCopy.emap g3) es_done)
        by (apply (extend_copy_emap_root g1 g2 g3 g4 g2' g3' g4' root es es_done e0 es_later); auto).
      destruct H11 as [_ [_ HH]].
      destruct HH as [_ [_ [_ [HH _]]]].
      destruct H7 as [_ [_ ?]].
      destruct HH as [_ [? _]].
      destruct H7 as [_ [_ [_ [_ [? _]]]]].
      rewrite <- H7 in H9.
      apply Prop_join_shrink; auto.
      unfold Included, Ensembles.In.
      intros e ? ?.
      destruct H9 as [_ ?].
      apply (H9 e); auto.
      destruct (vcopy1_edge_copy_list_spec root _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5).
      eapply (LocalGraphCopy.vcopy1_edge_copy_list_mapped_root_edge_evalid g1 g2 g3 g2' g3'); eauto.
        1: intros; destruct (node_pred_dec (WeakMarkGraph.marked g1) v); auto.
        1: destruct H4 as [? [? ?]]; auto.
  }
  1: {
    intros.
    pose proof vcopy1_edge_copy_list_spec root es es_done (e0 :: es_later) g1 g2 g3 g2' g3' H H0 H1 H2 H3 H4 H5.
    destruct H14.
    pose proof WeakMarkGraph.triple_mark1_componded_mark_list root (map (dst g1) es_done) (map (dst g1) (e0 :: es_later)) (map (dst g1) es) g1 g3 H H0.
    spec H16; [apply out_edges_step_list; auto |].
    spec H16; [rewrite <- map_app; f_equal; auto |].
    spec H16; [split_relation_list (g1 :: g2 :: g2 :: nil) |].
      1: apply WeakMarkGraph.eq_do_nothing; auto.
      1: destruct H4 as [? [? ?]]; auto.
      1: apply WeakMarkGraph.eq_do_nothing; auto.
      1: auto.
    cbv iota zeta in H16.
    destruct H16 as [_ ?].

    pose proof LocalGraphCopy.vcopy1_edge_copy_list_copy_and_copy_extend g1 g2 g3 g4 g2' g3' g4'' g4' root es es_done e0 es_later (WeakMarkGraph.marked g1) H H0 H2 H3 H1.
    spec H17; [intros; apply decidable_prop_decidable; apply node_pred_dec |].
    spec H17; [destruct H4 as [? [? ?]]; auto |].
    spec H17; [auto |].
    cbv zeta in H17.
    rewrite <- H16 in H17.
    spec H17; [destruct H7 as [? [? ?]]; auto |].
    spec H17; [auto |].
    spec H17; [intros; rewrite <- (app_same_set H16); apply decidable_prop_decidable; apply node_pred_dec |].
    spec H17; [destruct H11 as [? [? ?]]; auto |].
    spec H17; [auto |].
    spec H17; [auto |].
    destruct H17 as [? [? [? ?]]].
    split; intros; apply GSG_PartialGraphPreserve; auto.
    + apply Included_refl.
    + destruct H17.
      intros ? ?; unfold Ensembles.In; rewrite H17; tauto.
    + apply Intersection1_Included, Included_refl.
    + apply Intersection1_Included.
      destruct H17.
      intros ? ?; unfold Ensembles.In; rewrite H17; tauto.
    + eapply si_stronger_partial_labeledgraph_simple; [| eassumption].
      apply Intersection1_Included, Included_refl.
  }
Qed.

End PointwiseGraph_Copy.
