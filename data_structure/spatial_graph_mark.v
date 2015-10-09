Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.Coqlib.
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
Require Import RamifyCoq.graph.dag.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.data_structure.general_spatial_graph.
Require Import Coq.Logic.Classical.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Local Open Scope logic.

Section SpatialGraph_Mark.

Context {V E: Type}.
Context {SGBA: SpatialGraphBasicAssum V E}.
Context {DV DE: Type}.
Context {GV GE Pred: Type}.
Context {SGP: SpatialGraphPred V E GV GE Pred}.
Context {SGA: SpatialGraphAssum SGP}.
Context {MGS: WeakMarkGraph.MarkGraphSetting DV}.

Notation Graph := (LabeledGraph V E DV DE).
Notation SGraph := (SpatialGraph V E GV GE).

Variable compute_vgamma: Graph -> V -> GV.
Variable compute_egamma: Graph -> E -> GE.

Hypothesis compute_vgamma_local: forall (G1 G2: Graph) (x: V),
  vvalid G1 x ->
  vvalid G2 x ->
  vlabel_lg G1 x = vlabel_lg G2 x ->
  (forall e, src G1 e = x /\ evalid G1 e <-> src G2 e = x /\ evalid G2 e) ->
  (forall e, src G1 e = x -> evalid G1 e -> src G2 e = x -> evalid G2 e ->
     elabel_lg G1 e = elabel_lg G2 e /\ dst G1 e = dst G2 e) ->
  compute_vgamma G1 x = compute_vgamma G2 x.

Hypothesis compute_egamma_local: forall (G1 G2: Graph) (e: E),
  evalid G1 e ->
  evalid G2 e ->
  elabel_lg G1 e = elabel_lg G2 e ->
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
      * simpl.
        destruct_eq_dec x v; [tauto | auto].
      * intros; simpl; tauto.
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
    - unfold predicate_vvalid in H; tauto.
    - intros; simpl.
      unfold predicate_weak_evalid.
      destruct H.
      assert (src G e = v -> p (src G e)) by (intros; subst v; auto).
      tauto.
  + simpl; intros.
    apply compute_egamma_local; auto.
    destruct H; auto.
Qed.

Definition mark1 (G1: Graph) x (G2: Graph) := WeakMarkGraph.mark1 G1 x G2.
Definition mark (G1: Graph) x (G2: Graph) := WeakMarkGraph.mark G1 x G2 /\ G1 ~=~ G2.

Definition mark_list g1 xs g2 := relation_list (fun x g1 g2 => mark g1 x g2) xs g1 g2.

Lemma mark1_mark_list_mark: forall (g1: Graph) root l (g2 g3: Graph)
  (V_DEC: forall x, In x l -> Decidable (vvalid g1 x)),
  vvalid g1 root ->
  (WeakMarkGraph.unmarked g1) root ->
  step_list g1 root l ->
  mark1 g1 root g2 ->
  mark_list g2 l g3 ->
  mark g1 root g3.
Proof.
  intros.
  eapply relation_list_Intersection in H3.
  Focus 2. {
    (* This should be more trivial *)
    intros; rewrite same_relation_spec.
    instantiate (1 := (fun _ => structurally_identical)).
    instantiate (1 := (fun x g1 g2 => WeakMarkGraph.mark g1 x g2)).
    do 2 (hnf; intros); unfold relation_conjunction, predicate_intersection; simpl; reflexivity.
  } Unfocus.
  destruct H3; simpl in H3, H4.
  split.
  + eapply WeakMarkGraph.mark1_mark_list_mark; eauto.
  + destruct H2.
    rewrite H2.
    eapply si_list. exact H4.
Qed.

Lemma vertex_update_ramify: forall (g: Graph) (x: V) (lx: DV) (gx: GV),
  vvalid g x ->
  gx = vgamma (Graph_SpatialGraph (labeledgraph_vgen g x lx)) x ->
  @derives Pred _
    (graph x (Graph_SpatialGraph g))
    (vertex_at x (vgamma (Graph_SpatialGraph g) x) *
      (vertex_at x gx -* graph x (Graph_SpatialGraph (labeledgraph_vgen g x lx)))).
Proof.
  intros.
  rewrite GSG_VGenPreserve by eassumption.
  apply vertices_at_ramify; auto.
  apply reachable_refl.
  simpl; auto.
Qed.

Lemma exists_mark1: forall (g: Graph) (x: V) (lx: DV),
  WeakMarkGraph.label_marked lx ->
  @derives Pred _ (graph x (Graph_SpatialGraph (labeledgraph_vgen g x lx))) (EX g': Graph, !! (mark1 g x g') && graph x (Graph_SpatialGraph g')).
Proof.
  intros.
  apply (exp_right (labeledgraph_vgen g x lx)).
  apply andp_right; [apply prop_right | auto].
  apply WeakMarkGraph.vertex_update_mark1; auto.
Qed.

Lemma mark_list_mark_ramify: forall {A} (g1 g2 g3: Graph) (g4: A -> Graph) x l y l',
  vvalid g1 x ->
  step_list g1 x (l ++ y :: l') ->
  mark1 g1 x g2 ->
  mark_list g2 l g3 ->
  @derives Pred _
    (graph x (Graph_SpatialGraph g3))
    (graph y (Graph_SpatialGraph g3) *
      (ALL a: A,
        (!! mark g3 y (g4 a) && graph y (Graph_SpatialGraph (g4 a))) -*
        (!! mark g3 y (g4 a) && graph x (Graph_SpatialGraph (g4 a))))).
Proof.
  intros.
Abort.