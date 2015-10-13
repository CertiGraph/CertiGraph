Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import RamifyCoq.Coqlib.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas. Import RamifyCoq.graph.path_lemmas.PathNotation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.dual_graph.

Section PartialLabeledGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE: Type}.

Notation Graph := (LabeledGraph V E DV DE).

Definition labeledgraph_vgen (g: Graph) (x: V) (a: DV) : Graph := Build_LabeledGraph _ _ g (fun v => if (equiv_dec x v) then a else vlabel_lg g v) (elabel_lg g).

Definition predicate_sub_labeledgraph (g: Graph) (p: V -> Prop) :=
  Build_LabeledGraph _ _ (predicate_subgraph g p) (vlabel_lg g) (elabel_lg g).

Definition predicate_partial_labeledgraph (g: Graph) (p: V -> Prop) :=
  Build_LabeledGraph _ _ (predicate_partialgraph g p) (vlabel_lg g) (elabel_lg g).

End PartialLabeledGraph.

Definition DFS_acc {V E} {EV: EqDec V eq} {EE: EqDec E eq} (g: PreGraph V E) (P: V -> Prop) (x y: V) :=
  vvalid g x /\ x = y \/
  reachable_by g x P y \/
  exists z, reachable_by g x P z /\ edge g z y.

Lemma DFS_acc_self: forall {V E} {EV: EqDec V eq} {EE: EqDec E eq} (g: PreGraph V E) (P: V -> Prop) x,
  vvalid g x -> 
  DFS_acc g P x x.
Proof.
  intros.
  left.
  tauto.
Qed.

Module WeakMarkGraph.

Class MarkGraphSetting (DV: Type) := {
  label_marked: DV -> Prop;
  marked_dec: forall x, {label_marked x} + {~ label_marked x}
}.

Section WeakMarkGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE: Type}.
Context {MGS: MarkGraphSetting DV}.

Notation Graph := (LabeledGraph V E DV DE).

Definition marked (g: Graph) : NodePred V.
  refine (existT _ (fun v => label_marked (vlabel_lg g v)) _).
  intros.
  apply marked_dec.
Defined.

Definition unmarked (g: Graph) : NodePred V := negateP (marked g).

Hypothesis R_DEC: forall (g: Graph) x, vvalid g x -> ReachDecidable g x (unmarked g).

Definition mark1 (g1 : Graph) (n : V) (g2 : Graph) : Prop :=
  g1 ~=~ g2 /\
  marked g2 n /\
  (forall n', n <> n' -> vvalid g1 n' -> vvalid g2 n' -> vlabel_lg g1 n' = vlabel_lg g2 n') /\
  (forall e, evalid g1 e -> evalid g2 e -> elabel_lg g1 e = elabel_lg g2 e).

Definition mark (g1 : Graph) (root : V) (g2 : Graph) : Prop :=
  (predicate_partialgraph (dualgraph g1) (unmarked g2)) ~=~
  (predicate_partialgraph (dualgraph g2) (unmarked g2)) /\
  (forall n, g1 |= root ~o~> n satisfying (unmarked g1) -> marked g2 n) /\
  (forall n, ~ g1 |= root ~o~> n satisfying (unmarked g1) -> (marked g1 n <-> marked g2 n)).

Definition mark_list g1 xs g2 := relation_list (fun x g1 g2 => mark g1 x g2) xs g1 g2.

(*
Lemma mark_marked: forall (g1: Graph) root (g2: Graph),
  mark g1 root g2 ->
  forall n, marked g1 n -> marked g2 n.
Proof.
  intros.
  destruct H as [_ [_ ?]].
  rewrite <- H; [auto |].
  intro.
  apply reachable_by_foot_prop in H1.
  unfold unmarked in H1; rewrite negateP_spec in H1; auto.
Qed.
*)
Lemma mark1_mark_list_mark: forall (g1: Graph) root l (g2 g3: Graph)
  (V_DEC: forall x, In x l -> Decidable (vvalid g1 x)),
  vvalid g1 root ->
  (unmarked g1) root ->
  step_list g1 root l ->
  mark1 g1 root g2 ->
  mark_list g2 l g3 ->
  mark g1 root g3.
Admitted.

Lemma vertex_update_mark1: forall (g: Graph) x lx,
  label_marked lx ->
  mark1 g x (labeledgraph_vgen g x lx).
Proof.
  intros.
  split; [| split; [| split]].
  + reflexivity.
  + simpl.
    destruct_eq_dec x x; [auto | congruence].
  + simpl; intros.
    destruct_eq_dec x n'; [tauto | auto].
  + simpl; intros.
    auto.
Qed.

(*
Lemma step_list_reachable_included: forall (g1 g2 g3: Graph) x l y l',
  vvalid g1 x ->
  step_list g1 x (l ++ y :: l') ->
  mark1 g1 x g2 ->
  mark_list g2 l g3 ->
  Included (reachable g3 y) (reachable g3 x).
Proof.
  intros.
  hnf; unfold Ensembles.In; intros.
  assert ((marked g3) x /\ step g3 x y /\ vvalid g3 x);
    [| apply step_reachable with y; tauto].
  assert (step g2 x y).
  Focus 1. {
    destruct H1 as [? _].
    rewrite <- step_si by eassumption.
    specialize (H0 y);
    rewrite in_app_iff in H0; simpl in H0; tauto.
  } Unfocus.
  assert (vvalid g2 x) by (rewrite <- (proj1 (proj1 H1)); auto).
  destruct H1 as [_ [? _]].
  clear - H1 H2 H4 H5.
  induction H2.
  + split.
    - simpl.
      destruct H as [_ [? _]].
      rewrite <- H; auto.
    - destruct H as [? _].
      erewrite <- step_si by eassumption.
      rewrite <- (proj1 H).
      auto.
  + do 3 (spec IHrelation_list; [auto |]).
    clear H2 H4 H5 H1 x0.
    assert ((marked z) x) by (eapply mark_marked; eauto; tauto).
    split; [| split]; auto.
    - destruct H as [? [? ?]].
      assert (step (dualgraph y0) y x) by admit.
      pose proof partialgraph_step _ (unmarked z) _ _ H3.
      
SearchAbout edge.
Locate partialgraph_edge.
 rewrite !step_spec in IHrelation_list |- *.
      destruct IHrelation_list as [? [[e [? [? ?]]] ?]].
      exists e.
      
    destruct H as [? _].
    assert (marked g2 x) by destru
    Focus 1. {
      destruct H1.
SearchAbout reachable Proper.

Locate reachable_proper.
rewrite <- H1.
*)
End WeakMarkGraph.

End WeakMarkGraph.
