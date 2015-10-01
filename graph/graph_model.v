Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
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

(******************************************

Graph Definitions

******************************************)

Section GRAPH_DEF.

Context {Vertex Edge: Type}.

Record PreGraph {EV: EqDec Vertex eq} {EE: EqDec Edge eq} := {
  vvalid : Ensemble Vertex;
  evalid : Ensemble Edge;
  src : Edge -> Vertex;
  dst : Edge -> Vertex
}.

Context {EV: EqDec Vertex eq}.
Context {EE: EqDec Edge eq}.

Record LabeledGraph {DV DE: Type} := {
  pg_lg: PreGraph;
  vlabel_lg: Vertex -> DV;
  elabel_lg: Edge -> DE
}.

Record GeneralGraph {DV DE: Type} {P: PreGraph -> (Vertex -> DV) -> (Edge -> DE) -> Type (* Should be Prop *)} := {
  pg_gg: PreGraph;
  vlabel: Vertex -> DV;
  elabel: Edge -> DE;
  sound_gg: P pg_gg vlabel elabel
}.

Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion pg_gg: GeneralGraph >-> PreGraph.

Definition strong_evalid (pg: PreGraph) (e: Edge) : Prop :=
  evalid pg e /\ vvalid pg (src pg e) /\ vvalid pg (dst pg e).

Inductive step (pg: PreGraph): Vertex -> Vertex -> Prop :=
  | step_intro: forall e x y, evalid pg e -> src pg e = x -> dst pg e = y -> step pg x y.

Definition edge (pg : PreGraph) (n n' : Vertex) : Prop :=
  vvalid pg n /\ vvalid pg n' /\ step pg n n'.

Notation " pg |= n1 ~> n2 " := (edge pg n1 n2) (at level 1).

Definition step_list (pg : PreGraph) n l : Prop := forall n', In n' l <-> step pg n n'.

Definition out_edges (pg : PreGraph) x: Ensemble Edge := fun e => evalid pg e /\ src pg e = x.

Definition in_edges (pg : PreGraph) x: Ensemble Edge := fun e => evalid pg e /\ dst pg e = x.

Definition NodePred := {P : Vertex -> Prop & forall x, {P x} + {~ P x}}.

Definition app_node_pred (P: NodePred) (x: Vertex) := projT1 P x.

Coercion app_node_pred : NodePred >-> Funclass.

Definition node_pred_dec (P: NodePred) (x: Vertex): {P x} + {~ P x} := projT2 P x.

Class MathGraph (pg: PreGraph) := {
  is_null: Vertex -> Prop;
  is_null_dec: forall x, {is_null x} + {~ is_null x};
  weak_valid: Vertex -> Prop := fun p => is_null p \/ vvalid pg p;
  valid_graph: forall e, evalid pg e -> vvalid pg (src pg e) /\ weak_valid (dst pg e);
  valid_not_null: forall x, vvalid pg x -> is_null x -> False
}.

Definition well_defined_list (pg: PreGraph) {ma: MathGraph pg} (l : list Vertex) := forall x, In x l -> weak_valid x.

Class FiniteGraph (pg: PreGraph) :=
{
  finiteV: Enumerable Vertex (vvalid pg);
  finiteE: Enumerable Edge (evalid pg)
}.

Class LocalFiniteGraph (pg: PreGraph) :=
{
  local_enumerable: forall x, Enumerable Edge (out_edges pg x)
}.

Definition edge_func (pg: PreGraph) {lfg: LocalFiniteGraph pg} x := projT1 (local_enumerable x).

Class BiGraph (pg: PreGraph) (left_out_edge right_out_edge: Vertex -> Edge) :=
{
  left_valid: forall x, vvalid pg x -> evalid pg (left_out_edge x);
  right_valid: forall x, vvalid pg x -> evalid pg (right_out_edge x);
  bi_consist: forall x, left_out_edge x <> right_out_edge x;
  only_two_edges: forall x e, src pg e = x <-> e = left_out_edge x \/ e = right_out_edge x
}.

End GRAPH_DEF.

Arguments PreGraph _ _ {_} {_}.
Arguments LabeledGraph _ _ {_} {_} _ _.
Arguments GeneralGraph _ _ {_} {_} _ _ _.
Arguments NodePred : clear implicits.
Arguments is_null {_} {_} {_} {_} _ {_} _.
Arguments is_null_dec {_} {_} {_} {_} _ {_} _.
Arguments weak_valid {_} {_} {_} {_} _ {_} _.
Arguments valid_graph {_} {_} {_} {_} _ {_} _ _.
Arguments valid_not_null {_} {_} {_} {_} _ {_} _ _ _. 
Arguments left_valid {_} {_} {_} {_} _ {_} {_} {_} _ _.
Arguments right_valid {_} {_} {_} {_} _ {_} {_} {_} _ _.
Arguments bi_consist {_} {_} {_} {_} _ {_} {_} {_} _ _.
Arguments only_two_edges {_} {_} {_} {_} _ {_} {_} {_} _ _.

Notation " pg |= n1 ~> n2 " := (edge pg n1 n2) (at level 1).

(******************************************

Properties

******************************************)

Section GRAPH_BASIC_LEM.

Context {Vertex Edge: Type}.
Context {EV: EqDec Vertex eq}.
Context {EE: EqDec Edge eq}.

Lemma step_spec: forall (pg: PreGraph Vertex Edge) x y, step pg x y <-> exists e, evalid pg e /\ src pg e = x /\ dst pg e = y.
Proof.
  intros; split; intro.
  + inversion H; eauto.
  + destruct H as [? [? [? ?]]]; econstructor; eauto.
Qed.

Lemma valid_step: forall (pg: PreGraph Vertex Edge) {ma: MathGraph pg} x y, step pg x y -> vvalid pg x /\ weak_valid pg y.
Proof.
  intros.
  rewrite step_spec in H.
  destruct H as [? [? [? ?]]].
  subst.
  apply valid_graph; auto.
Qed.

Lemma edge_func_spec: forall {pg : PreGraph Vertex Edge} {lfg: LocalFiniteGraph pg} e x,
  In e (edge_func pg x) <-> evalid pg e /\ src pg e = x.
Proof.
  intros.
  unfold edge_func.
  destruct (local_enumerable x) as [? [?H ?H]]; simpl.
  specialize (H0 e).
  rewrite H0; unfold out_edges.
  clear - H0.
  unfold Ensembles.In; tauto.
Qed.

Lemma edge_func_step: forall {pg : PreGraph Vertex Edge} {lfg: LocalFiniteGraph pg} x y,
  step pg x y <-> In y (map (dst pg) (edge_func pg x)).
Proof.
  intros.
  rewrite step_spec.
  rewrite in_map_iff.
  apply Morphisms_Prop.ex_iff_morphism.
  hnf; cbv beta; intro e.
  rewrite edge_func_spec.
  clear - e.
  tauto.
Qed.

Lemma null_or_valid: forall (pg: PreGraph Vertex Edge) {ma: MathGraph pg} x,
  weak_valid pg x -> {is_null pg x} + {vvalid pg x}.
Proof.
  intros.
  destruct (is_null_dec pg x); [left | right]; auto.
  unfold weak_valid in H.
  tauto.
Qed.

Definition negateP (p : NodePred Vertex) : NodePred Vertex.
Proof.
  exists (Complement Vertex (projT1 p)).
  intros. destruct p. simpl in *. unfold Complement.
  destruct (s x); [right | left]; auto.
Defined.

Lemma negateP_spec: forall (p : NodePred Vertex) (x : Vertex), (negateP p) x <-> ~ p x.
Proof. intros; unfold negateP; simpl; unfold Complement; tauto. Qed.

Lemma negateP_spec_d: forall (p: NodePred Vertex) (x : Vertex), ~ Ensembles.In Vertex (negateP p) x <-> p x.
Proof.
  intros. unfold negateP. simpl. unfold Complement. 
  destruct p; simpl. split; intros; destruct (s x); try tauto.
  intro. hnf in H0. tauto.
Qed.

Instance LocalFiniteGraph_FiniteGraph (g: PreGraph Vertex Edge) (fg: FiniteGraph g): LocalFiniteGraph g.
Proof.
  intros.
  destruct fg as [[vs [?H ?H]] [es [?H ?H]]].
  constructor.
  intros.
  exists (filter (fun e => if equiv_dec (src g e) x then true else false) es).
  split.
  + apply NoDup_filter; auto.
  + intro e.
    rewrite filter_In.
    rewrite H2.
    unfold Ensembles.In, out_edges.
    destruct_eq_dec (src g e) x; [tauto |].
    assert (~ false = true) by congruence; tauto.
Defined.

Definition node_pred_equiv (m1 m2: NodePred Vertex) := forall n, m1 n <-> m2 n.

Lemma npe_refl: forall (m: NodePred Vertex), node_pred_equiv m m.
Proof. unfold node_pred_equiv; intros. tauto. Qed.

Lemma npe_sym: forall (m1 m2: NodePred Vertex), node_pred_equiv m1 m2 -> node_pred_equiv m2 m1.
Proof. unfold node_pred_equiv; intros. specialize (H n); tauto. Qed.

Lemma npe_trans: forall (m1 m2 m3: NodePred Vertex), node_pred_equiv m1 m2 -> node_pred_equiv m2 m3 -> node_pred_equiv m1 m3.
Proof. unfold node_pred_equiv; intros. specialize (H n); specialize (H0 n); tauto. Qed.

Instance npe_Equiv: Equivalence (node_pred_equiv).
Proof.
  split.
  + intro; apply npe_refl.
  + intro; apply npe_sym.
  + intro; apply npe_trans.
Defined.

Definition vertex_prop_coincide (g1 g2: PreGraph Vertex Edge) (p1 p2: Vertex -> Prop) := forall x, vvalid g1 x -> vvalid g2 x -> (p1 x <-> p2 x).

Lemma vertex_prop_coincide_refl: forall (g: PreGraph Vertex Edge) (p: Vertex -> Prop), vertex_prop_coincide g g p p.
Proof.
  intros.
  hnf; intros.
  reflexivity.
Qed.

Lemma vertex_prop_coincide_sym: forall (g1 g2: PreGraph Vertex Edge) (p1 p2: Vertex -> Prop), vertex_prop_coincide g1 g2 p1 p2 -> vertex_prop_coincide g2 g1 p2 p1.
Proof.
  unfold vertex_prop_coincide.
  intros.
  symmetry.
  auto.
Qed.

Section BIGRAPH_LEM.

Context {left_out_edge right_out_edge: Vertex -> Edge}.

Lemma left_sound (pg: PreGraph Vertex Edge) {bi: BiGraph pg left_out_edge right_out_edge}: forall x, src pg (left_out_edge x) = x.
Proof.
  intros.
  pose proof only_two_edges pg x (left_out_edge x).
  tauto.
Qed.

Lemma right_sound (pg: PreGraph Vertex Edge) {bi: BiGraph pg left_out_edge right_out_edge}: forall x, src pg (right_out_edge x) = x.
Proof.
  intros.
  pose proof only_two_edges pg x (right_out_edge x).
  tauto.
Qed.

Lemma left_or_right (pg: PreGraph Vertex Edge) (bi: BiGraph pg left_out_edge right_out_edge): forall x e, src pg e = x -> {e = left_out_edge x} + {e = right_out_edge x}.
Proof.
  intros.
  pose proof only_two_edges pg x e.
  destruct_eq_dec e (left_out_edge x); [left | right]; tauto.
Qed.

Definition biEdge (pg : PreGraph Vertex Edge) {bi: BiGraph pg left_out_edge right_out_edge} (v: Vertex) : Vertex * Vertex := (dst pg (left_out_edge v), dst pg (right_out_edge v)).

Lemma biEdge_only2 (pg : PreGraph Vertex Edge) {bi: BiGraph pg left_out_edge right_out_edge} :
  forall v v1 v2 n, vvalid pg v -> biEdge pg v = (v1 ,v2) -> (step pg v n <-> n = v1 \/ n = v2).
Proof.
  intros; unfold biEdge in H.
  split; intros.
  + inversion H1; subst.
    inversion H0; subst.
    assert (e = left_out_edge (src pg e) \/ e = right_out_edge (src pg e)) by (rewrite <- only_two_edges; eauto).
    destruct H3; rewrite <- H3; auto.
  + rewrite step_spec; inversion H0; subst.
    destruct H1; [exists (left_out_edge v) | exists (right_out_edge v)]; subst.
    - split; [| split]; [eapply left_valid | rewrite left_sound |]; eauto.
    - split; [| split]; [eapply right_valid | rewrite right_sound |]; eauto.
Qed.

End BIGRAPH_LEM.

(******************************************

Lemmas about structurally identical

******************************************)

Definition structurally_identical (g1 g2: PreGraph Vertex Edge): Prop :=
  (forall v : Vertex, (vvalid g1 v <-> vvalid g2 v)) /\
  (forall e : Edge, (evalid g1 e <-> evalid g2 e)) /\
  (forall e : Edge, evalid g1 e -> evalid g2 e -> src g1 e = src g2 e) /\
  (forall e : Edge, evalid g1 e -> evalid g2 e -> dst g1 e = dst g2 e).

Notation "g1 '~=~' g2" := (structurally_identical g1 g2) (at level 1).

Lemma si_refl: forall (G : PreGraph Vertex Edge), G ~=~ G.
Proof. intros; repeat split; auto. Qed.

Lemma si_sym: forall (G1 G2: PreGraph Vertex Edge), G1 ~=~ G2 -> G2 ~=~ G1.
Proof. intros; destruct H as [? [? [? ?]]]; split; [| split; [| split]]; auto; firstorder. Qed.

Lemma si_trans: forall (G1 G2 G3: PreGraph Vertex Edge), G1 ~=~ G2 -> G2 ~=~ G3 -> G1 ~=~ G3.
Proof.
  intros; destruct H as [? [? [? ?]]], H0 as [? [? [? ?]]].
  split; [| split; [| split]]; intros; [firstorder | firstorder | |];
  specialize (H1 e); specialize (H2 e); specialize (H3 e);
  specialize (H4 e); specialize (H5 e); specialize (H6 e);
  assert (evalid G2 e) by (apply H1; auto); specialize (H2 H7 H9); specialize (H3 H7 H9);
  specialize (H5 H9 H8); specialize (H6 H9 H8); congruence.
Qed.

Instance si_Equiv: Equivalence (structurally_identical).
Proof.
  split.
  + intro; apply si_refl.
  + intro; apply si_sym.
  + intro; apply si_trans.
Defined.

Lemma step_si: forall (g1 g2 : PreGraph Vertex Edge) (n n' : Vertex), g1 ~=~ g2 -> (step g1 n n' <-> step g2 n n').
Proof.
  cut (forall (g1 g2 : PreGraph Vertex Edge) (n n' : Vertex), g1 ~=~ g2 -> step g1 n n' -> step g2 n n').
  1: intros; split; apply H; [eauto | symmetry; auto].
  intros.
  rewrite step_spec in H0 |- *.
  destruct H as [? [? [? ?]]].
  destruct H0 as [e [? [? ?]]]; exists e.
  specialize (H1 e).
  rewrite <- H1, <- H2, <- H3; tauto.
Qed.

Lemma edge_si:
  forall (g1 g2 : PreGraph Vertex Edge) (n n' : Vertex), g1 ~=~ g2 -> (g1 |= n ~> n' <-> g2 |= n ~> n').
Proof.
  intros; unfold edge in *.
  pose proof proj1 H n.
  pose proof proj1 H n'.
  pose proof step_si _ _ n n' H.
  clear - H0 H1 H2.
  tauto.
Qed.

Definition remove_edge (g1: PreGraph Vertex Edge) (e0: Edge) (g2: PreGraph Vertex Edge) :=
  (forall v : Vertex, (vvalid g1 v <-> vvalid g2 v)) /\
  (forall e : Edge, e <> e0 -> (evalid g1 e <-> evalid g2 e)) /\
  (forall e : Edge, e <> e0 -> src g1 e = src g2 e) /\
  (forall e : Edge, e <> e0 -> dst g1 e = dst g2 e) /\
  ~ evalid g2 e0.

Definition gremove_edge (g1: PreGraph Vertex Edge) (e0: Edge) (g2: PreGraph Vertex Edge) :=
  (forall v : Vertex, (vvalid g1 v <-> vvalid g2 v)) /\
  (forall e : Edge, e <> e0 -> (evalid g1 e <-> evalid g2 e)) /\
  (forall e : Edge, e <> e0 -> src g1 e = src g2 e) /\
  (forall e : Edge, e <> e0 -> dst g1 e = dst g2 e) /\
  ~ strong_evalid g2 e0.

Section GENERAL_GRAPH_EQUIV.

Context {DV DE: Type}.
Context {P: PreGraph Vertex Edge -> (Vertex -> DV) -> (Edge -> DE) -> Type}.
Notation Graph := (@GeneralGraph Vertex Edge EV EE DV DE P).

Definition general_graph_equiv (g1 g2: Graph) :=
  g1 ~=~ g2 /\
  (forall v, vlabel g1 v = vlabel g2 v) /\
  (forall e, elabel g1 e = elabel g2 e).

Lemma gge_refl: forall (G : Graph), general_graph_equiv G G.
Proof. intros; repeat split; auto. Qed.

Lemma gge_sym: forall (G1 G2: Graph), general_graph_equiv G1 G2 -> general_graph_equiv G2 G1.
Proof. intros; destruct H as [? [? ?]]; split; [| split]; auto. symmetry; auto. Qed.

Lemma gge_trans: forall (G1 G2 G3: Graph), general_graph_equiv G1 G2 -> general_graph_equiv G2 G3 -> general_graph_equiv G1 G3.
Proof.
  intros; destruct H as [? [? ?]], H0 as [? [? ?]].
  split; [| split].
  + transitivity G2; auto.
  + intros. specialize (H1 v); specialize (H3 v); congruence.
  + intros. specialize (H2 e); specialize (H4 e); congruence.
Qed.

Instance gge_Equiv: Equivalence (general_graph_equiv).
Proof.
  split.
  + intro; apply gge_refl.
  + intro; apply gge_sym.
  + intro; apply gge_trans.
Defined.

End GENERAL_GRAPH_EQUIV.

End GRAPH_BASIC_LEM.

Notation "g1 '~=~' g2" := (structurally_identical g1 g2) (at level 1): PreGraph.
Notation "m1 '~=~' m2" := (node_pred_equiv m1 m2) (at level 1) : NodePred.
Notation "g1 '~=~' g2" := (general_graph_equiv g1 g2) (at level 1) : LabeledGraph.
Delimit Scope PreGraph with PreGraph.
Delimit Scope NodePred with NodePred.
Delimit Scope LabeledGraph with LabeledGraph.

Open Scope PreGraph.
Global Existing Instance npe_Equiv.
Global Existing Instance si_Equiv.
Global Existing Instance gge_Equiv.
