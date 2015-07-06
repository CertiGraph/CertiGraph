Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Lists.List.
Require Import RamifyCoq.Coqlib.

Lemma Union_iff: forall U A B x, Ensembles.In U (Union U A B) x <-> Ensembles.In U A x \/ Ensembles.In U B x.
Proof.
  intros; split; intros.
  + apply Constructive_sets.Union_inv; auto.
  + destruct H; [apply Union_introl | apply Union_intror]; auto.
Qed.

Lemma Empty_set_iff: forall U x, Ensembles.In U (Empty_set U) x <-> False.
Proof.
  intros; split; intro; inversion H.
Qed.

Lemma Singleton_iff: forall U x y, Ensembles.In U (Singleton U x) y <-> x = y.
Proof.
  intros; split; intro.
  + inversion H; auto.
  + subst; constructor.
Qed.

Lemma Finite_spec: forall A U, Finite A U <-> exists l, NoDup l /\ forall x, In x l <-> Ensembles.In A U x.
Proof.
  intros.
  split; intros.
  + induction H.
    - exists nil.
      split; [constructor |].
      intros.
      rewrite Empty_set_iff; simpl; tauto.
    - destruct IHFinite as [l [? ?]].
      exists (x :: l).
      split; [constructor; auto; rewrite H2; auto |]. 
      intros x0; specialize (H2 x0).
      simpl.
      unfold Add.
      rewrite Union_iff, Singleton_iff.
      tauto.
  + destruct H as [l [? ?]].
    revert U H0; induction l; intros.
    - replace U with (Empty_set A); [apply Empty_is_finite |].
      apply Extensionality_Ensembles.
      split; intros x ?; specialize (H0 x); simpl in *; repeat rewrite Empty_set_iff in *; tauto.
    - replace U with (Add A (Subtract A U a) a);
      [apply Union_is_finite | apply Extensionality_Ensembles].
      * inversion H; subst.
        apply IHl; [auto |].
        intros x; specialize (H0 x).
        unfold Subtract, Setminus; unfold Ensembles.In at 1.
        simpl in H0.
        rewrite Singleton_iff.
        assert (a = x -> ~ In x l) by (intro; subst; auto).
        tauto.
      * unfold Subtract, Setminus; unfold Ensembles.In at 1.
        rewrite Singleton_iff.
        tauto.
      * unfold Add, Subtract, Setminus.
        split; intros ?; rewrite Union_iff;
          [unfold Ensembles.In at 1 | unfold Ensembles.In at 2];
          rewrite  Singleton_iff; intro;
          specialize (H0 x); simpl in H0; [tauto |].
        inversion H; subst.
        assert (a = x -> ~ In x l) by (intro; subst; auto).
        tauto.
Qed.

Definition Enumerable U (A: Ensemble U) := {l: list U | NoDup l /\ forall x, In x l <-> Ensembles.In U A x}.

Definition EnumCovered U (A: Ensemble U) := {l: list U | NoDup l /\ forall x, Ensembles.In U A x -> In x l}.

Lemma EnumCovered_strengthen: forall U A B,
  Included A B -> EnumCovered U B -> EnumCovered U A.
Proof.
  intros.
  destruct X as [x ?H].
  exists x.
  split; [tauto |].
  intros.
  apply H in H1.
  firstorder.
Qed.

(******************************************

Graph Definitions

******************************************)

Class PreGraph (Vertex Edge: Type) := {
  EV: EqDec Vertex;
  EE: EqDec Edge;
  vvalid : Ensemble Vertex;
  evalid : Ensemble Edge;
  src : Edge -> Vertex;
  dst : Edge -> Vertex
}.

Global Existing Instances EV EE.

Inductive step {Vertex Edge: Type} (pg: PreGraph Vertex Edge): Vertex -> Vertex -> Prop :=
  | step_intro: forall e x y, evalid e -> src e = x -> dst e = y -> step pg x y.

Definition edge {V E : Type} (G : PreGraph V E) (n n' : V) : Prop :=
  vvalid n /\ vvalid n' /\ step G n n'.

Notation " g |= n1 ~> n2 " := (edge g n1 n2) (at level 1).

Definition edge_list {V E : Type} (G : PreGraph V E) n l : Prop := forall n', In n' l <-> edge G n n'.

Definition out_edges {Vertex Edge: Type} (pg: PreGraph Vertex Edge) x: Ensemble Edge := fun e => evalid e /\ src e = x.

Definition in_edges {Vertex Edge: Type} (pg: PreGraph Vertex Edge) x: Ensemble Edge := fun e => evalid e /\ dst e = x.

Class MathGraph {Vertex Edge: Type} (pg: PreGraph Vertex Edge) := {
  is_null: Ensemble Vertex;
  is_null_dec: forall p, {is_null p} + {~ is_null p};
  weak_valid: Vertex -> Prop := fun p => is_null p \/ vvalid p;
  valid_graph: forall e, evalid e -> vvalid (src e) /\ weak_valid (dst e);
  valid_not_null: forall x, vvalid x -> is_null x -> False
}.

Definition well_defined_list {Vertex Edge: Type} (pg: PreGraph Vertex Edge) {ma : MathGraph pg} (l : list Vertex) :=
  forall x, In x l -> weak_valid x.

Class FiniteGraph {Vertex Edge: Type} (pg: PreGraph Vertex Edge) :=
{
  finiteV: Enumerable Vertex vvalid;
  finiteE: Enumerable Edge evalid
}.

Class LocalFiniteGraph {Vertex Edge: Type} (pg: PreGraph Vertex Edge) :=
{
  local_enumerable: forall x, Enumerable Edge (out_edges pg x)
}.

Definition NodePred {Vertex Edge: Type} (pg: PreGraph Vertex Edge) := 
  {P : Vertex -> Prop & forall x, {P x} + {~ P x}}.

Definition app_node_pred {Vertex Edge: Type} {pg: PreGraph Vertex Edge} (P: NodePred pg) (x: Vertex) :=
  projT1 P x.

Coercion app_node_pred : NodePred >-> Funclass.

Definition node_pred_dec {Vertex Edge: Type} {pg: PreGraph Vertex Edge} (P: NodePred pg) (x: Vertex): {P x} + {~ P x} := projT2 P x.

Definition edge_func {Vertex Edge: Type} (pg: PreGraph Vertex Edge) {lfg: LocalFiniteGraph pg} x := projT1 (local_enumerable x).

Class BiGraph {Vertex Edge: Type} (pg: PreGraph Vertex Edge) :=
{
  left_out_edge: Vertex -> Edge;
  right_out_edge: Vertex -> Edge;
  left_sound: forall x, src (left_out_edge x) = x;
  right_sound: forall x, src (right_out_edge x) = x;
  left_valid: forall x, vvalid x -> evalid (left_out_edge x);
  right_valid: forall x, vvalid x -> evalid (right_out_edge x);
  bi_consist: forall x, left_out_edge x <> right_out_edge x;
  only_two_edges: forall x e, src e = x <-> e = left_out_edge x \/ e = right_out_edge x
(*  only_two_neighbours : forall (v : Vertex), edge_func pg v = left_out_edge v :: left_out_edge v :: nil *)
}.

Lemma left_or_right {Vertex Edge: Type} (pg: PreGraph Vertex Edge) (bi: BiGraph pg): forall x e, src e = x -> {e = left_out_edge x} + {e = right_out_edge x}.
Proof.
  intros.
  pose proof only_two_edges x e.
  destruct (t_eq_dec e (left_out_edge x)); [left | right]; tauto.
Qed.
  
(******************************************

Properties

******************************************)

Lemma step_spec: forall {Vertex Edge: Type} (pg: PreGraph Vertex Edge) x y, step pg x y <-> exists e, evalid e /\ src e = x /\ dst e = y.
Proof.
  intros; split; intro.
  + inversion H; eauto.
  + destruct H as [? [? [? ?]]]; econstructor; eauto.
Qed.

Lemma valid_step: forall {Vertex Edge: Type} (PG: PreGraph Vertex Edge) {MA: MathGraph PG} x y, step PG x y -> vvalid x /\ weak_valid y.
Proof.
  intros.
  rewrite step_spec in H.
  destruct H as [? [? [? ?]]].
  subst.
  apply valid_graph; auto.
Qed.

Lemma edge_func_spec: forall {Vertex Edge} {PG : PreGraph Vertex Edge} {LFG: LocalFiniteGraph PG} e x,
  In e (edge_func PG x) <-> evalid e /\ src e = x.
Proof.
  intros.
  unfold edge_func.
  destruct (local_enumerable x) as [? [?H ?H]]; simpl.
  specialize (H0 e).
  rewrite H0; unfold out_edges.
  unfold Ensembles.In; tauto.
Qed.

Lemma edge_func_step: forall {Vertex Edge} {PG : PreGraph Vertex Edge} {LFG: LocalFiniteGraph PG} x y,
  step PG x y <-> In y (map dst (edge_func PG x)).
Proof.
  intros.
  rewrite step_spec.
  rewrite in_map_iff.
  apply Morphisms_Prop.ex_iff_morphism.
  hnf; cbv beta; intro e.
  rewrite edge_func_spec.
  tauto.
Qed.

Lemma null_or_valid: forall {Vertex Edge: Type} (pg: PreGraph Vertex Edge) {mg: MathGraph pg} x,
  weak_valid x -> {is_null x} + {vvalid x}.
Proof.
  intros.
  destruct (is_null_dec x); [left | right]; auto.
  unfold weak_valid in H.
  tauto.
Qed.

Definition biEdge {Vertex Edge} {PG : PreGraph Vertex Edge} (BG: BiGraph PG) (v: Vertex) : Vertex * Vertex := (dst (left_out_edge v), dst (right_out_edge v)).

Lemma biEdge_only2 {Vertex Edge} {PG : PreGraph Vertex Edge} (BG: BiGraph PG) :
  forall v v1 v2 n, biEdge BG v = (v1 ,v2) -> step PG v n -> n = v1 \/ n = v2.
Proof.
  intros; unfold biEdge in H.
  inversion H0; subst.
  inversion H; subst.
  assert (e = left_out_edge (src e) \/ e = right_out_edge (src e)) by (apply only_two_edges; auto).
  destruct H2; rewrite <- H2; auto.
Qed.

Definition structurally_identical {V E: Type} (G1 G2: PreGraph V E): Prop :=
  (forall v : V, (@vvalid V E G1 v <-> @vvalid V E G2 v)) /\
  (forall e : E, (@evalid V E G1 e <-> @evalid V E G2 e)) /\
  (forall e : E, @src V E G1 e = @src V E G2 e) /\
  (forall e : E, @dst V E G1 e = @dst V E G2 e).

Notation "g1 '~=~' g2" := (structurally_identical g1 g2) (at level 1).

Lemma si_refl: forall {V E : Type} (G : PreGraph V E), G ~=~ G.
Proof. intros; repeat split; auto. Qed.

Lemma si_sym: forall {V E : Type} (G1 G2: PreGraph V E), G1 ~=~ G2 -> G2 ~=~ G1.
Proof. intros; destruct H as [? [? [? ?]]]; split; [| split; [| split]]; auto; firstorder. Qed.

Lemma si_trans: forall {V E : Type} (G1 G2 G3: PreGraph V E), G1 ~=~ G2 -> G2 ~=~ G3 -> G1 ~=~ G3.
Proof.
  intros; destruct H as [? [? [? ?]]], H0 as [? [? [? ?]]].
  split; [| split; [| split]]; auto; firstorder;
  specialize (H2 e); specialize (H3 e); specialize (H4 e); specialize (H5 e); congruence.
Qed.

Add Parametric Relation {V E : Type} : (PreGraph V E) structurally_identical
    reflexivity proved by si_refl
    symmetry proved by si_sym
    transitivity proved by si_trans as si_equal.

Lemma step_si {V E : Type}:
  forall (g1 g2 : PreGraph V E) (n n' : V), g1 ~=~ g2 -> (step g1 n n' <-> step g2 n n').
Proof.
  cut (forall (g1 g2 : PreGraph V E) (n n' : V), g1 ~=~ g2 -> step g1 n n' -> step g2 n n').
  1: intros; split; apply H; [eauto | symmetry; auto].
  intros.
  rewrite step_spec in H0 |- *.
  destruct H as [? [? [? ?]]].
  destruct H0 as [e [? [? ?]]]; exists e.
  rewrite <- H1, <- H2, <- H3.
  auto.
Qed.

Lemma edge_si {V E : Type}:
  forall (g1 g2 : PreGraph V E) (n n' : V), g1 ~=~ g2 -> (g1 |= n ~> n' <-> g2 |= n ~> n').
Proof.
  intros; unfold edge in *.
  pose proof proj1 H n.
  pose proof proj1 H n'.
  pose proof step_si _ _ n n' H.
  tauto.
Qed.

Definition negateP {V E} {g: PreGraph V E} (p : NodePred g) : NodePred g.
Proof.
  exists (Complement V (projT1 p)).
  intros. destruct p. simpl in *. unfold Complement.
  destruct (s x); [right | left]; auto.
Defined.

Lemma negateP_spec {V E} {g: PreGraph V E}: forall (p : NodePred g) (x : V), (negateP p) x <-> ~ p x.
Proof. intros; unfold negateP; simpl; unfold Complement; tauto. Qed.

Lemma negateP_spec_d {V E} {g: PreGraph V E}:
  forall (p: NodePred g) (x : V), ~ Ensembles.In V (projT1 (negateP p)) x <-> p x.
Proof.
  intros. unfold negateP. simpl. unfold Complement. 
  destruct p; simpl. split; intros; destruct (s x); try tauto.
  intro. hnf in H0. tauto.
Qed.


