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
  (predicate_partialgraph g1 (unmarked g2)) ~=~
  (predicate_partialgraph g2 (unmarked g2)) /\
  (forall n, g1 |= root ~o~> n satisfying (unmarked g1) -> marked g2 n) /\
  (forall n, ~ g1 |= root ~o~> n satisfying (unmarked g1) -> (marked g1 n <-> marked g2 n)).

Definition mark_list g1 xs g2 := relation_list (fun x g1 g2 => mark g1 x g2) xs g1 g2.

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

End WeakMarkGraph.

End WeakMarkGraph.
