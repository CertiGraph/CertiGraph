Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Equivalence_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.

Section MathGraph.

Context {V E: Type} {EV: EqDec V eq} {EE: EqDec E eq}.

Class MathGraph (pg: PreGraph V E) (is_null: DecidablePred V): Prop := {
  weak_valid: V -> Prop := fun p => is_null p \/ vvalid pg p;
  valid_graph: forall e, evalid pg e -> vvalid pg (src pg e) /\ weak_valid (dst pg e);
  valid_not_null: forall x, vvalid pg x -> is_null x -> False
}.

Context {is_null: DecidablePred V}.

Lemma is_null_dec: forall x, {is_null x} + {~ is_null x}.
Proof.
  intros.
  destruct is_null as [P ?].
  simpl.
  auto.
Qed.

Arguments weak_valid _ {_} {_}  _.
Arguments valid_graph _ {_} {_} _ _.
Arguments valid_not_null _ {_} {_} _ _ _. 

Definition well_defined_list (pg: PreGraph V E) {ma: MathGraph pg is_null} (l : list V) := forall x, In x l -> weak_valid pg x.

Lemma valid_step: forall (pg: PreGraph V E) {ma: MathGraph pg is_null} x y, step pg x y -> vvalid pg x /\ weak_valid pg y.
Proof.
  intros.
  rewrite step_spec in H.
  destruct H as [? [? [? ?]]].
  subst.
  apply valid_graph; auto.
Qed.

Lemma null_or_valid: forall (pg: PreGraph V E) {ma: MathGraph pg is_null} x,
  weak_valid pg x -> {is_null x} + {vvalid pg x}.
Proof.
  intros.
  destruct (is_null_dec x); [left | right]; auto.
  unfold weak_valid in H.
  tauto.
Qed.

Lemma math_graph_si: forall (g1 g2: PreGraph V E),
  g1 ~=~ g2 ->
  MathGraph g1 is_null ->
  MathGraph g2 is_null.
Proof.
  intros.
  constructor.
  + intros.
    pose proof (proj2 (proj1 (proj2 H) _) H1).
    pose proof valid_graph g1 e H2.
    unfold weak_valid in H3.
    rewrite (si_src1 _ _ _ H) in H3 by auto.
    rewrite (si_dst1 _ _ _ H) in H3 by auto.
    rewrite !(proj1 H) in H3.
    auto.
  + intros.
    rewrite <- (proj1 H) in H1.
    apply (valid_not_null g1 x); auto.
Qed.

Lemma gen_dst_preserve_math: forall (g: PreGraph V E) e t (M: MathGraph g is_null),
    weak_valid g t -> MathGraph (pregraph_gen_dst g e t) is_null.
Proof.
  intros. refine (Build_MathGraph (pregraph_gen_dst g e t) is_null _ (valid_not_null g)).
  simpl. intros. apply (valid_graph g) in H0. destruct H0. split.
  + auto.
  + unfold updateEdgeFunc.
    destruct_eq_dec e e0.
    - apply H.
    - apply H1.
Defined.

Definition predicate_sub_mathgraph (g: PreGraph V E) (p: V -> Prop) (MA: MathGraph g is_null): MathGraph (predicate_subgraph g p) is_null.
Proof.
  refine (Build_MathGraph _ _ _ _).
  + unfold predicate_subgraph, predicate_vvalid, predicate_evalid; simpl; intros.
    pose proof valid_graph g e.
    unfold weak_valid in H0.
    tauto.
  + unfold predicate_subgraph, predicate_vvalid, predicate_evalid; simpl; intros.
    pose proof valid_not_null g x.
    tauto.
Defined.

Lemma math_graph_join: forall (g: PreGraph V E) (PV1 PV2 PV: V -> Prop) (PE1 PE2 PE: E -> Prop),
  Prop_join PV1 PV2 PV ->
  Prop_join PE1 PE2 PE ->
  MathGraph (gpredicate_subgraph PV1 PE1 g) is_null ->
  MathGraph (gpredicate_subgraph PV2 PE2 g) is_null ->
  MathGraph (gpredicate_subgraph PV PE g) is_null.
Proof.
  intros.
  constructor.
  + simpl; intro; rewrite !Intersection_spec; intros.
    destruct H, H0.
    rewrite H0 in H3; destruct H3 as [? [? | ?]].
    - pose proof valid_graph (gpredicate_subgraph PV1 PE1 g) e.
      simpl in H7; unfold weak_valid in H7; simpl in H7; rewrite !Intersection_spec in H7.
      specialize (H7 (conj H3 H6)).
      rewrite !H.
      tauto.
    - pose proof valid_graph (gpredicate_subgraph PV2 PE2 g) e.
      simpl in H7; unfold weak_valid in H7; simpl in H7; rewrite !Intersection_spec in H7.
      specialize (H7 (conj H3 H6)).
      rewrite !H.
      tauto.
  + simpl; intros.
    destruct H, H0.
    rewrite Intersection_spec, H in H3.
    destruct H3 as [? [? | ?]].
    - apply (valid_not_null (gpredicate_subgraph PV1 PE1 g) x); auto.
      simpl; rewrite Intersection_spec; auto.
    - apply (valid_not_null (gpredicate_subgraph PV2 PE2 g) x); auto.
      simpl; rewrite Intersection_spec; auto.
Qed.

End MathGraph.

Arguments weak_valid {_} {_} {_} {_} _ {_} {_} _.
Arguments valid_graph {_} {_} {_} {_} _ {_} {_} _ _.
Arguments valid_not_null {_} {_} {_} {_} _ {_} {_} _ _ _. 
