Require Import Coq.Logic.ProofIrrelevance.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Equivalence_ext.

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

Record LabeledGraph {DV DE DG: Type} := {
  pg_lg: PreGraph;
  vlabel: Vertex -> DV;
  elabel: Edge -> DE;
  glabel: DG
}.

Record GeneralGraph {DV DE DG: Type} {P: @LabeledGraph DV DE DG -> Type} := {
  lg_gg: @LabeledGraph DV DE DG;
  sound_gg: P lg_gg
}.

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

End GRAPH_DEF.

Arguments PreGraph _ _ {_} {_}.
Arguments LabeledGraph _ _ {_} {_} _ _ _.
Arguments GeneralGraph _ _ {_} {_} _ _ _ _.
Arguments NodePred : clear implicits.

(* Require Import VST.veric.SeparationLogic. *)

(* Definition temp_spec := *)
(* NDmk_funspec (nil, Tvoid) cc_default (Ensemble nat) (fun x => TT) (fun x => TT). *)

(* Definition temp_spec := *)
(* NDmk_funspec (nil, Tvoid) cc_default (@PreGraph _ _ EquivDec.nat_eq_eqdec EquivDec.nat_eq_eqdec) (fun x => TT) (fun x => TT). *)

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

Lemma out_edges_step: forall (pg: PreGraph Vertex Edge) x e,
  out_edges pg x e -> step pg x (dst pg e).
Proof.
  unfold out_edges.
  intros.
  rewrite step_spec.
  firstorder.
Qed.

Lemma out_edges_step_list: forall (pg: PreGraph Vertex Edge) x es,
  (forall e, In e es <-> out_edges pg x e) ->
  (step_list pg x (map (dst pg) es)).
Proof.
  intros.
  unfold step_list.
  intros v.
  split.
  + intros.
    rewrite in_map_iff in H0.
    destruct H0 as [e [? ?]]; subst v.
    apply out_edges_step.
    apply H; auto.
  + intros.
    rewrite step_spec in H0.
    destruct H0 as [e [? [? ?]]].
    subst.
    apply in_map.
    rewrite H.
    split; auto.
Qed.
  
Definition negateP (p : NodePred Vertex) : NodePred Vertex.
Proof.
  exists (Complement Vertex (projT1 p)).
  intros. destruct p. simpl in *. unfold Complement.
  destruct (s x); [right | left]; auto.
Defined.

Lemma negateP_spec: forall (p : NodePred Vertex) (x : Vertex), (negateP p) x <-> ~ p x.
Proof. intros; unfold negateP; simpl; unfold Complement; tauto. Qed.

Lemma negateP_spec': forall (p : NodePred Vertex), Same_set (negateP p) (Complement _ p).
Proof. intros. rewrite Same_set_spec; intros ?. apply negateP_spec. Qed.

Lemma negateP_spec_d: forall (p: NodePred Vertex) (x : Vertex), ~ Ensembles.In Vertex (negateP p) x <-> p x.
Proof.
  intros. unfold negateP. simpl. unfold Complement. 
  destruct p; simpl. split; intros; destruct (s x); try tauto.
  intro. hnf in H0. tauto.
Qed.

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

Lemma si_src1: forall (g1 g2 : PreGraph Vertex Edge) (e: Edge), g1 ~=~ g2 -> evalid g1 e -> src g1 e = src g2 e.
Proof.
  intros.
  destruct H as [? [? [? ?]]].
  firstorder.
Qed.

Lemma si_src2: forall (g1 g2 : PreGraph Vertex Edge) (e: Edge), g1 ~=~ g2 -> evalid g2 e -> src g1 e = src g2 e.
Proof.
  intros.
  destruct H as [? [? [? ?]]].
  firstorder.
Qed.

Lemma si_dst1: forall (g1 g2 : PreGraph Vertex Edge) (e: Edge), g1 ~=~ g2 -> evalid g1 e -> dst g1 e = dst g2 e.
Proof.
  intros.
  destruct H as [? [? [? ?]]].
  firstorder.
Qed.

Lemma si_dst2: forall (g1 g2 : PreGraph Vertex Edge) (e: Edge), g1 ~=~ g2 -> evalid g2 e -> dst g1 e = dst g2 e.
Proof.
  intros.
  destruct H as [? [? [? ?]]].
  firstorder.
Qed.

Lemma out_edges_si: forall (g1 g2 : PreGraph Vertex Edge) (v: Vertex) (e : Edge),
    g1 ~=~ g2 -> (out_edges g1 v e <-> out_edges g2 v e).
Proof.
  cut (forall (g1 g2: PreGraph Vertex Edge) v e, g1 ~=~ g2 -> out_edges g1 v e -> out_edges g2 v e).
  + intros. split; intros; [apply (H g1) | apply (H g2)]; auto. symmetry; auto.
  + intros. destruct H0. destruct H as [_ [? [? _]]].
    specialize (H e). specialize (H2 e). split; [|rewrite <- H2]; intuition.
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
  (forall e : Edge, e <> e0 -> evalid g1 e -> evalid g2 e -> src g1 e = src g2 e) /\
  (forall e : Edge, e <> e0 -> evalid g1 e -> evalid g2 e -> dst g1 e = dst g2 e) /\
  ((~ evalid g2 e0) \/ (~ vvalid g2 (dst g2 e0) /\ src g1 e0 = src g2 e0 /\ evalid g2 e0)).

Section LABELED_GRAPH_EQUIV.

Context {DV DE DG: Type}.
Notation Graph := (@LabeledGraph Vertex Edge EV EE DV DE DG).

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition labeled_graph_equiv (g1 g2: Graph) :=
  g1 ~=~ g2 /\
  (forall v, vvalid g1 v -> vvalid g2 v -> vlabel g1 v = vlabel g2 v) /\
  (forall e, evalid g1 e -> evalid g2 e -> elabel g1 e = elabel g2 e).

Lemma lge_refl: forall (G : Graph), labeled_graph_equiv G G.
Proof. intros; repeat split; auto. Qed.

Lemma lge_sym: forall (G1 G2: Graph), labeled_graph_equiv G1 G2 -> labeled_graph_equiv G2 G1.
Proof. intros; destruct H as [? [? ?]]; split; [| split]; auto; intros; symmetry; auto. Qed.

Lemma lge_trans: forall (G1 G2 G3: Graph), labeled_graph_equiv G1 G2 -> labeled_graph_equiv G2 G3 -> labeled_graph_equiv G1 G3.
Proof.
  intros; destruct H as [? [? ?]], H0 as [? [? ?]].
  split; [| split].
  + transitivity G2; auto.
  + intros.
    assert (vvalid G2 v) by (pose proof (proj1 H v); tauto).
    specialize (H1 v H5 H7); specialize (H3 v H7 H6); congruence.
  + intros.
    assert (evalid G2 e) by (pose proof (proj1 (proj2 H) e); tauto).
    specialize (H2 e H5 H7); specialize (H4 e H7 H6); congruence.
Qed.

Instance lge_Equiv: Equivalence (labeled_graph_equiv).
Proof.
  split.
  + intro; apply lge_refl.
  + intro; apply lge_sym.
  + intro; apply lge_trans.
Defined.

Lemma si_list: forall {A} (l: list A) (G1 G2: Graph), relation_list (map (fun _ (G1 G2: Graph) => G1 ~=~ G2) l) G1 G2 -> G1 ~=~ G2.
Proof.
  intros until l.
  pose proof @resp_Equivalence Graph _ pg_lg structurally_identical.
  apply eq_relation_list.
Qed.

End LABELED_GRAPH_EQUIV.

End GRAPH_BASIC_LEM.

Notation "g1 '~=~' g2" := (structurally_identical g1 g2) (at level 1): PreGraph.
Notation "m1 '~=~' m2" := (node_pred_equiv m1 m2) (at level 1) : NodePred.
Notation "g1 '~=~' g2" := (labeled_graph_equiv g1 g2) (at level 1) : LabeledGraph.
Delimit Scope PreGraph with PreGraph.
Delimit Scope NodePred with NodePred.
Delimit Scope LabeledGraph with LabeledGraph.

Open Scope PreGraph.
Global Existing Instance npe_Equiv.
Global Existing Instance si_Equiv.
Global Existing Instance lge_Equiv.

