Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import RamifyCoq.Coqlib.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas. Import RamifyCoq.graph.path_lemmas.PathNotation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.

Definition relation_concat {A: Type} (P Q: Relation_Definitions.relation A): Relation_Definitions.relation A := fun x z => exists y, P x y /\ P y z.

Section PartialLabeledGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE: Type}.

Notation Graph := (LabeledGraph V E DV DE).

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
  vvalid g1 n /\
  marked g2 n /\
  forall n', n <> n' -> (marked g1 n' <-> marked g2 n').

Definition mark (g1 : Graph) (root : V) (g2 : Graph) : Prop :=
  (predicate_partialgraph g1 (Complement _ (reachable_by g1 root (unmarked g1)))) ~=~
  (predicate_partialgraph g2 (Complement _ (reachable_by g1 root (unmarked g1)))) /\
  (forall n, g1 |= root ~o~> n satisfying (unmarked g1) -> marked g2 n) /\
  (forall n, ~ g1 |= root ~o~> n satisfying (unmarked g1) -> (marked g1 n <-> marked g2 n)).

Inductive mark_list: Graph -> list V -> Graph -> Prop :=
| mark_list_nil: forall g g0, (g ~=~ g0)%LabeledGraph -> mark_list g nil g0
| mark_list_cons: forall g g0 g1 v vs, mark g v g0 -> mark_list g0 vs g1 -> mark_list g (v :: vs) g1
.

Lemma mark1_mark_list_mark: forall (g1: Graph) root l (g2 g3: Graph)
  (V_DEC: forall x, In x l -> Decidable (vvalid g1 x)),
  vvalid g1 root ->
  (unmarked g1) root ->
  step_list g1 root l ->
  mark1 g1 root g2 ->
  mark_list g2 l g3 ->
  mark g1 root g3.
Admitted.

Lemma vertex_update_mark1: forall (g1: Graph) x (g2: Graph),
  g1 ~=~ g2 ->
  vvalid g1 x ->
  unmarked g1 x ->
  marked g2 x ->
  (forall y, x <> y -> vlabel_lg g2 y = vlabel_lg g1 y) ->
  (forall e, elabel_lg g2 e = elabel_lg g1 e) ->
  mark1 g1 x g2.
Admitted.

End WeakMarkGraph.

End WeakMarkGraph.
