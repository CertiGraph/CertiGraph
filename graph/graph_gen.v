Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.Equivalence_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import VST.msl.Coqlib2.
Require Import Coq.Lists.List.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_ind.

Section AUXILIARY_COMPONENT_CONSTR.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE DG: Type}.

(******************)
(* Definitions    *)
(******************)

(* TODO: Maybe redefine these three using respectful_set. *)
(* TODO: rename them into edge_prop_11/10/01. *)
Definition strong_edge_prop (P: V -> Prop) (g: PreGraph V E): E -> Prop := fun e => P (src g e) /\ P (dst g e).

Definition weak_edge_prop (P: V -> Prop) (g: PreGraph V E): E -> Prop := fun e => P (src g e).

Definition weak'_edge_prop (P: V -> Prop) (g: PreGraph V E): E -> Prop := fun e => P (dst g e).

Instance weak_edge_prop_proper: Proper (Same_set ==> eq ==> Same_set) weak_edge_prop.
Proof.
  do 2 (hnf; intros); subst.
  rewrite Same_set_spec in *.
  intro e; unfold weak_edge_prop.
  auto.
Defined.
Global Existing Instance weak_edge_prop_proper.

Definition predicate_vvalid (g: PreGraph V E) (p: V -> Prop): Ensemble V :=
  fun n => vvalid g n /\ p n.

Definition predicate_evalid (g: PreGraph V E) (p: V -> Prop): Ensemble E :=
  fun e => evalid g e /\ p (src g e) /\ p (dst g e).

Definition predicate_weak_evalid (g: PreGraph V E) (p: V -> Prop): Ensemble E :=
  fun e => evalid g e /\ p (src g e).

Definition addValidFunc {T: Type} (v: T) (validFunc: Ensemble T) : Ensemble T :=
  fun n => validFunc n \/ n = v.

Definition removeValidFunc {T: Type} (v: T) (validFunc: Ensemble T) : Ensemble T :=
  fun n => validFunc n /\ n <> v.

Definition update_vlabel (vlabel: V -> DV) (x: V) (d: DV) :=
  fun v => if equiv_dec x v then d else vlabel v.

Definition update_elabel (elabel: E -> DE) (e0: E) (d: DE) :=
  fun e => if equiv_dec e0 e then d else elabel e.

Definition updateEdgeFunc (edgeFunc: E -> V) (e: E) (v: V) :
  E -> V := fun n => if equiv_dec e n then v else edgeFunc n.

(******************)
(* Properties     *)
(******************)

Lemma updateEdgeFunc_eq: forall edgeFunc e v, updateEdgeFunc edgeFunc e v e = v.
Proof.
  intros. unfold updateEdgeFunc. destruct_eq_dec e e; auto. exfalso; now apply H.
Qed.

Lemma updateEdgeFunc_neq: forall edgeFunc e v e',
    e <> e' -> updateEdgeFunc edgeFunc e v e' = edgeFunc e'.
Proof. intros. unfold updateEdgeFunc. destruct_eq_dec e e'; auto. easy. Qed.

Lemma weak_edge_prop_si: forall (P: V -> Prop) (g1 g2: PreGraph V E),
  g1 ~=~ g2 ->
  Same_set
   (Intersection _ (weak_edge_prop P g1) (evalid g1))
   (Intersection _ (weak_edge_prop P g2) (evalid g2)).
Proof.
  intros.
  rewrite Same_set_spec; intro e.
  rewrite !Intersection_spec.
  unfold weak_edge_prop.
  pose proof (proj1 (proj2 H) e).
  pose proof proj1 (proj2 (proj2 H)) e.
  split; intros [? ?]; do 2 (spec H1; [tauto |]); (split; [congruence | tauto]).
Qed.

Lemma weak_edge_prop_Empty: forall g, Same_set (weak_edge_prop (Empty_set _) g) (Empty_set _).
Proof.
  intros.
  unfold weak_edge_prop.
  rewrite Same_set_spec; intros x.
  rewrite !Empty_set_spec; reflexivity.
Qed.

Lemma weak_edge_prop_Disjoint: forall (P1 P2: V -> Prop) (g: PreGraph V E),
  Disjoint _ P1 P2 ->
  Disjoint _ (weak_edge_prop P1 g) (weak_edge_prop P2 g).
Proof.
  intros.
  unfold weak_edge_prop.
  rewrite Disjoint_spec in *.
  firstorder.
Qed.

Lemma weak_edge_prop_Complement: forall (P: V -> Prop) (g: PreGraph V E), Same_set (weak_edge_prop (Complement _ P) g) (Complement _ (weak_edge_prop P g)).
Proof.
  intros.
  unfold weak_edge_prop, Complement, Ensembles.In.
  rewrite Same_set_spec.
  hnf; intros; simpl.
  reflexivity.
Qed.

Lemma weak_edge_prop_Union: forall (P Q: V -> Prop) (g: PreGraph V E), Same_set (weak_edge_prop (Union _ P Q) g) (Union _ (weak_edge_prop P g) (weak_edge_prop Q g)).
Proof.
  intros.
  unfold weak_edge_prop.
  rewrite Same_set_spec; intros ?; rewrite !Union_spec.
  simpl.
  reflexivity.
Qed.

Lemma weak_edge_prop_Decidable: forall (P: V -> Prop) (g: PreGraph V E),
  (forall v, Decidable (P v)) ->
  (forall e, Decidable (weak_edge_prop P g e)).
Proof.
  intros.
  unfold weak_edge_prop.
  apply X.
Qed.

End AUXILIARY_COMPONENT_CONSTR.

Section PREGRAPH_GEN.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Notation Graph := (PreGraph V E).

Definition empty_pregraph (src0 dst0: E -> V): Graph :=
  @Build_PreGraph V E EV EE (fun v => False) (fun e => False) src0 dst0.

Definition single_vertex_pregraph (v0: V): Graph :=
  @Build_PreGraph V E EV EE (eq v0) (fun e => False) (fun e => v0) (fun e => v0).

Definition pregraph_add_vertex (g: Graph) (v: V) : Graph :=
  @Build_PreGraph V E EV EE (addValidFunc v (vvalid g)) (evalid g) (src g) (dst g).

Lemma addVertex_preserve_vvalid: forall g v v', vvalid g v -> vvalid (pregraph_add_vertex g v') v. Proof. intros; hnf; left; auto. Qed.

Lemma addVertex_add_vvalid: forall g v, vvalid (pregraph_add_vertex g v) v. Proof. intros. hnf. right; auto. Qed.

Lemma addVertex_preserve_evalid: forall g e v, evalid g e -> evalid (pregraph_add_vertex g v) e. Proof. intros; simpl; auto. Qed.

Definition pregraph_add_edge (g : Graph) (e : E) (o t : V) :=
  @Build_PreGraph V E EV EE (vvalid g) (addValidFunc e (evalid g)) (updateEdgeFunc (src g) e o) (updateEdgeFunc (dst g) e t).

Definition pregraph_add_whole_edge (g: Graph) (e: E) (s t: V) : Graph :=
  Build_PreGraph _ _ (addValidFunc t (vvalid g)) (addValidFunc e (evalid g)) (updateEdgeFunc (src g) e s) (updateEdgeFunc (dst g) e t).

Lemma addEdge_preserve_vvalid: forall g v e s t, vvalid g v -> vvalid (pregraph_add_whole_edge g e s t) v. Proof. intros. hnf; left; auto. Qed.

Lemma addEdge_preserve_evalid: forall g e e' s t, evalid g e -> evalid (pregraph_add_whole_edge g e' s t) e. Proof. intros. hnf; left; auto. Qed.

Lemma addEdge_add_vvalid: forall g e s t, vvalid (pregraph_add_whole_edge g e s t) t. Proof. intros. hnf. right; auto. Qed.

Lemma addEdge_add_evalid: forall g e s t, evalid (pregraph_add_whole_edge g e s t) e. Proof. intros. hnf. right; auto. Qed.

Lemma addEdge_src_iff: forall g e s t e' x, src (pregraph_add_whole_edge g e s t) e' = x <-> ((e <> e' /\ src g e' = x) \/ (e = e' /\ s = x)).
Proof. intros. simpl. unfold updateEdgeFunc. destruct (equiv_dec e e'); intuition. Qed.

Lemma addEdge_dst_iff: forall g e s t e' x, dst (pregraph_add_whole_edge g e s t) e' = x <-> ((e <> e' /\ dst g e' = x) \/ (e = e' /\ t = x)).
Proof. intros. simpl. unfold updateEdgeFunc. destruct (equiv_dec e e'); intuition. Qed.

Definition pregraph_remove_vertex (g: Graph) (v: V) : Graph :=
  @Build_PreGraph V E EV EE (removeValidFunc v (vvalid g)) (evalid g) (src g) (dst g).

Lemma remove_vertex_vvalid: forall g v v',
    vvalid (pregraph_remove_vertex g v') v <-> vvalid g v /\ v <> v'.
Proof. intros. unfold pregraph_remove_vertex, removeValidFunc. simpl. reflexivity. Qed.

Definition pregraph_remove_edge (g: Graph) (e: E): Graph :=
  @Build_PreGraph V E EV EE (vvalid g) (removeValidFunc e (evalid g)) (src g) (dst g).

Lemma remove_edge_evalid: forall g e e',
    evalid (pregraph_remove_edge g e') e <-> evalid g e /\ e <> e'.
Proof. intros. unfold pregraph_remove_edge, removeValidFunc. simpl. reflexivity. Qed.

Definition pregraph_gen_dst (g : Graph) (e : E) (t : V) :=
  @Build_PreGraph V E EV EE (vvalid g) (evalid g) (src g) (updateEdgeFunc (dst g) e t).

Definition union_pregraph (PV : V -> Prop) (PE: E -> Prop) (PVD: forall v, Decidable (PV v)) (PED: forall e, Decidable (PE e)) (g1 g2: Graph): Graph :=
  @Build_PreGraph V E EV EE
    (fun v => if PVD v then vvalid g1 v else vvalid g2 v)
    (fun e => if PED e then evalid g1 e else evalid g2 e)
    (fun e => if PED e then src g1 e else src g2 e)
    (fun e => if PED e then dst g1 e else dst g2 e).

(* TODO: rename them into sub_pregraph, v11_sub_pregraph, v10_sub_pregraph *)
Definition gpredicate_subgraph (PV: V -> Prop) (PE: E -> Prop) (g: Graph): Graph :=
  Build_PreGraph EV EE (Intersection _ (vvalid g) PV) (Intersection _ (evalid g) PE) (src g) (dst g).

Definition predicate_subgraph (g: Graph) (p: V -> Prop): Graph :=
  Build_PreGraph EV EE (predicate_vvalid g p) (predicate_evalid g p) (src g) (dst g).

Definition predicate_partialgraph (g: Graph) (p: V -> Prop): Graph :=
  Build_PreGraph EV EE (predicate_vvalid g p) (predicate_weak_evalid g p) (src g) (dst g).

Instance subgraph_proper: Proper (structurally_identical ==> @Same_set V ==> structurally_identical) predicate_subgraph.
Proof.
  do 2 (hnf; intros).
  destruct H as [? [? [? ?]]].
  rewrite Same_set_spec in H0; hnf in H0.
  split; [| split; [| split]]; intros; simpl.
  + unfold predicate_vvalid.
    rewrite H0, H.
    reflexivity.
  + unfold predicate_evalid. rewrite !H0, !H1. specialize (H1 e).
    split; intros; destruct H4 as [? [? ?]]; [rewrite <- H2, <- H3 | rewrite H2, H3]; tauto.
  + simpl in * |- . unfold predicate_evalid in * |- . apply H2; tauto.
  + simpl in * |- . unfold predicate_evalid in * |- . apply H3; tauto.
Defined.

Global Existing Instance subgraph_proper.

Instance partialgraph_proper: Proper (structurally_identical ==> @Same_set V ==> structurally_identical) predicate_partialgraph.
Proof.
  do 2 (hnf; intros).
  destruct H as [? [? [? ?]]].
  rewrite Same_set_spec in H0; hnf in H0.
  split; [| split; [| split]]; intros; simpl.
  + unfold predicate_vvalid.
    rewrite H0, H.
    reflexivity.
  + unfold predicate_weak_evalid. rewrite !H0, !H1. specialize (H1 e).
    split; intro; intuition; [rewrite <- H2 | rewrite H2]; auto.
  + simpl in * |- . unfold predicate_weak_evalid in * |- . apply H2; tauto.
  + simpl in * |- . unfold predicate_weak_evalid in * |- . apply H3; tauto.
Defined.

Global Existing Instance partialgraph_proper.

Instance gpredicate_subgraph_proper: Proper (@Same_set V ==> @Same_set E ==> structurally_identical ==> structurally_identical) gpredicate_subgraph.
Proof.
  do 3 (hnf; intros).
  destruct H1 as [? [? [? ?]]].
  rewrite Same_set_spec in H, H0; hnf in H, H0.
  split; [| split; [| split]]; intros; simpl.
  + rewrite !Intersection_spec.
    rewrite H1, H.
    reflexivity.
  + rewrite !Intersection_spec.
    rewrite H2, H0.
    reflexivity.
  + simpl in H5, H6.
    rewrite Intersection_spec in *.
    apply H3; tauto.
  + simpl in H5, H6.
    rewrite Intersection_spec in *.
    apply H4; tauto.
Defined.

Global Existing Instance gpredicate_subgraph_proper.

Lemma predicate_partialgraph_gpredicate_subgraph (g: Graph) (p: V -> Prop):
  (predicate_partialgraph g p) ~=~ (gpredicate_subgraph p (Intersection _ (weak_edge_prop p g) (evalid g)) g).
Proof.
  split; [| split; [| split]]; simpl; intros.
  + rewrite Intersection_spec.
    reflexivity.
  + rewrite !Intersection_spec.
    unfold predicate_weak_evalid.
    unfold weak_edge_prop.
    tauto.
  + auto.
  + auto.
Qed.

Lemma partial_partialgraph: forall p1 p2 (g: Graph),
  (predicate_partialgraph (predicate_partialgraph g p1) p2) ~=~
  (predicate_partialgraph g (Intersection _ p1 p2)).
Proof.
  intros.
  split; [| split; [| split]]; simpl; intros.
  + unfold predicate_vvalid; simpl; unfold predicate_vvalid.
    rewrite Intersection_spec.
    tauto.
  + unfold predicate_weak_evalid; simpl.
    unfold predicate_weak_evalid.
    rewrite Intersection_spec.
    tauto.
  + reflexivity.
  + reflexivity.
Qed.

Lemma si_stronger_partialgraph: forall (g1 g2: PreGraph V E) (p1 p2 p1' p2' p: V -> Prop),
  (forall v, p1' v <-> p1 v /\ p v) ->
  (forall v, p2' v <-> p2 v /\ p v) ->
  (predicate_partialgraph g1 p1) ~=~ (predicate_partialgraph g2 p2) ->
  (predicate_partialgraph g1 p1') ~=~ (predicate_partialgraph g2 p2').
Proof.
  intros.
  destruct H1 as [? [? [? ?]]].
  split; [| split; [| split]].
  + intro v; specialize (H1 v); specialize (H0 v); specialize (H v);
    simpl in H1 |- *.
    unfold predicate_vvalid in H1 |- *.
    tauto.
  + intro e; specialize (H2 e); specialize (H3 e); specialize (H (src g1 e)); specialize (H0 (src g2 e));
    simpl in H2, H3 |- *.
    unfold predicate_weak_evalid in H2, H3 |- *. clear H4. split; intros; destruct H4.
    - rewrite H in H5. destruct H5. assert (evalid g1 e /\ p1 (src g1 e)) by auto.
      specialize (H3 H7). rewrite H2 in H7. specialize (H3 H7). rewrite <- H3 in *. tauto.
    - rewrite H0 in H5. destruct H5. assert (evalid g2 e /\ p2 (src g2 e)) by auto.
      assert (evalid g1 e /\ p1 (src g1 e)) by tauto. specialize (H3 H8 H7).
      rewrite H3 in *. rewrite H. tauto.
  + simpl in *. unfold predicate_weak_evalid in *. intros.
    rewrite H in H5. rewrite H0 in H6. apply H3; tauto.
  + simpl in *. unfold predicate_weak_evalid in *. intros.
    rewrite H in H5. rewrite H0 in H6. apply H4; tauto.
Qed.

Lemma si_stronger_partialgraph': forall (g1 g2: PreGraph V E) (p1 p2 p1' p2' p: V -> Prop),
  Same_set p1' (Intersection _ p1 p) ->
  Same_set p2' (Intersection _ p2 p) ->
  (predicate_partialgraph g1 p1) ~=~ (predicate_partialgraph g2 p2) ->
  (predicate_partialgraph g1 p1') ~=~ (predicate_partialgraph g2 p2').
Proof.
  intros.
  apply si_stronger_partialgraph with (p := p) (p1 := p1) (p2 := p2); auto.
  - intros.
    rewrite Same_set_spec in H; specialize (H v).
    rewrite Intersection_spec in H; auto.
  - intros.
    rewrite Same_set_spec in H0; specialize (H0 v).
    rewrite Intersection_spec in H0; auto.
Qed.

Lemma si_stronger_partialgraph_simple: forall (g1 g2: PreGraph V E) (p p': V -> Prop),
  Included p' p ->
  (predicate_partialgraph g1 p) ~=~ (predicate_partialgraph g2 p) ->
  (predicate_partialgraph g1 p') ~=~ (predicate_partialgraph g2 p').
Proof.
  intros.
  eapply si_stronger_partialgraph with (p := p'); [| | exact H0].
  + intro v; specialize (H v); simpl in H; tauto.
  + intro v; specialize (H v); simpl in H; tauto.
Qed.

Lemma si_partialgraph_stronger_trans: forall (g1 g g2: PreGraph V E) (P1 P2 P: V -> Prop),
  Included P P1 ->
  Included P P2 ->
  (predicate_partialgraph g1 P1) ~=~ (predicate_partialgraph g P1) ->
  (predicate_partialgraph g P2) ~=~ (predicate_partialgraph g2 P2) ->
  (predicate_partialgraph g1 P) ~=~ (predicate_partialgraph g2 P).
Proof.
  intros.
  transitivity (predicate_partialgraph g P).
  + apply si_stronger_partialgraph_simple with P1; auto.
  + apply si_stronger_partialgraph_simple with P2; auto.
Qed.

Lemma sub_subgraph: forall p1 p2 (g: Graph),
  (predicate_subgraph (predicate_subgraph g p1) p2) ~=~
  (predicate_subgraph g (Intersection _ p1 p2)).
Proof.
  intros.
  split; [| split; [| split]]; simpl; intros.
  + unfold predicate_vvalid; simpl; unfold predicate_vvalid.
    rewrite Intersection_spec.
    tauto.
  + unfold predicate_evalid; simpl; unfold predicate_evalid; simpl.
    rewrite !Intersection_spec.
    tauto.
  + reflexivity.
  + reflexivity.
Qed.

Lemma subgraph_step: forall (g: Graph) (p: V -> Prop) x y,
  step g x y -> p x -> p y -> step (predicate_subgraph g p) x y.
Proof.
  intros.
  rewrite step_spec in H |- *.
  destruct H as [e [? [? ?]]].
  exists e.
  split; [| split; simpl; auto].
  simpl.
  unfold predicate_evalid.
  rewrite H2, H3.
  auto.
Qed.

Lemma subgraph_edge: forall (g: Graph) (p: V -> Prop) x y,
    edge g x y -> p x -> p y -> edge (predicate_subgraph g p) x y.
Proof.
  intros.
  destruct H as [? [? ?]].
  unfold edge.
  simpl.
  unfold predicate_vvalid.
  do 2 (split; [tauto |]).
  apply subgraph_step; auto.
Qed.

Lemma partialgraph_step: forall (g: Graph) (p: V -> Prop) x y,
  step g x y -> p x -> step (predicate_partialgraph g p) x y.
Proof.
  intros.
  rewrite step_spec in H |- *.
  destruct H as [e [? [? ?]]].
  exists e.
  split; [| split; simpl; auto].
  simpl.
  unfold predicate_weak_evalid.
  rewrite H1.
  auto.
Qed.

Lemma partialgraph_edge: forall (g: Graph) (p: V -> Prop) x y,
    edge g x y -> p x -> p y -> edge (predicate_partialgraph g p) x y.
Proof.
  intros.
  destruct H as [? [? ?]].
  unfold edge.
  simpl.
  unfold predicate_vvalid.
  do 2 (split; [tauto |]).
  apply partialgraph_step; auto.
Qed.

Lemma subgraph_step_iff: forall (g: Graph) (p: V -> Prop) x y,
  (step g x y /\ p x /\ p y) <-> step (predicate_subgraph g p) x y.
Proof.
  intros.
  split; [intros [? [? ?]]; apply subgraph_step; auto |].
  rewrite !step_spec.
  intros [e [? [? ?]]]; simpl in *.
  destruct H as [? [? ?]].
  subst.
  split; [| split]; auto.
  exists e.
  split; [| split]; auto.
Qed.

Lemma subgraph_edge_iff: forall (g: Graph) (p: V -> Prop) x y,
  (edge g x y /\ p x /\ p y) <-> edge (predicate_subgraph g p) x y.
Proof.
  intros.
  unfold edge.
  rewrite <- subgraph_step_iff.
  simpl.
  unfold predicate_vvalid.
  tauto.
Qed.

Lemma partialgraph_step_iff: forall (g: Graph) (p: V -> Prop) x y,
  (step g x y /\ p x) <-> step (predicate_partialgraph g p) x y.
Proof.
  intros.
  split; [intros [? ?]; apply partialgraph_step; auto |].
  rewrite !step_spec.
  intros [e [? [? ?]]]; simpl in *.
  destruct H as [? ?].
  subst.
  split; auto.
  exists e.
  split; [| split]; auto.
Qed.

Lemma partialgraph_edge_iff: forall (g: Graph) (p: V -> Prop) x y,
  (edge g x y /\ p x /\ p y) <-> edge (predicate_partialgraph g p) x y.
Proof.
  intros.
  unfold edge.
  rewrite <- partialgraph_step_iff.
  simpl.
  unfold predicate_vvalid.
  tauto.
Qed.

Lemma step_list_partialgraph: forall  (g: PreGraph V E) n l (P: Ensemble V),
  vvalid g n ->
  P n ->
  step_list g n l ->
  step_list (predicate_partialgraph g P) n l.
Proof.
  intros.
  intro m; specialize (H1 m).
  rewrite H1; clear H1.
  split.
  + intros; apply partialgraph_step; auto.
  + intro.
    inv H1; simpl in *.
    econstructor.
    - destruct H2; eauto.
    - reflexivity.
    - reflexivity.
Qed.

Lemma partialgraph_si_node_prop: forall n (g1 g2: PreGraph V E) p1 p2,
  (predicate_partialgraph g1 p1) ~=~ (predicate_partialgraph g2 p2) ->
  Included p1 (vvalid g1) ->
  Included p2 (vvalid g2) ->
  (p1 n <-> p2 n).
Proof.
  intros.
  destruct H as [? _].
  specialize (H n).
  specialize (H0 n).
  specialize (H1 n).
  simpl in *.
  unfold predicate_vvalid in H.
  tauto.
Qed.

Lemma subgraph_node_prop: forall n (g1 g2: PreGraph V E) p1 p2,
  (predicate_subgraph g1 p1) ~=~ (predicate_subgraph g2 p2) ->
  Included p1 (vvalid g1) ->
  Included p2 (vvalid g2) ->
  (p1 n <-> p2 n).
Proof.
  intros.
  destruct H as [? _].
  specialize (H n).
  specialize (H0 n).
  specialize (H1 n).
  simpl in *.
  unfold Ensembles.In in *.
  unfold predicate_vvalid in H.
  tauto.
Qed.

Lemma gpredicate_subgraph_self: forall (g: Graph),
  (gpredicate_subgraph (vvalid g) (evalid g) g) ~=~ g.
Proof.
  intros.
  split; [| split; [| split]].
  + simpl; intros.
    rewrite Intersection_spec; tauto.
  + simpl; intros.
    rewrite Intersection_spec; tauto.
  + simpl; intros.
    auto.
  + simpl; intros.
    auto.
Qed.

Lemma gpredicate_subgraph_equiv: forall (g: Graph) (PV1 PV2: V -> Prop) (PE1 PE2: E -> Prop),
  Same_set (Intersection _ (vvalid g) PV1) (Intersection _ (vvalid g) PV2) ->
  Same_set (Intersection _ (evalid g) PE1) (Intersection _ (evalid g) PE2) ->
  (gpredicate_subgraph PV1 PE1 g) ~=~ (gpredicate_subgraph PV2 PE2 g).
Proof.
  intros.
  split; [| split; [| split]].
  + simpl; intros.
    rewrite Same_set_spec in H.
    auto.
  + simpl; intros.
    rewrite Same_set_spec in H0.
    auto.
  + simpl; intros.
    auto.
  + simpl; intros.
    auto.
Qed.

Lemma stronger_gpredicate_subgraph_simple: forall (g g': PreGraph V E) (PV1 PV2: V -> Prop) (PE1 PE2: E -> Prop),
  Included PV2 PV1 ->
  Included PE2 PE1 ->
  (gpredicate_subgraph PV1 PE1 g) ~=~ (gpredicate_subgraph PV1 PE1 g') ->
  (gpredicate_subgraph PV2 PE2 g) ~=~ (gpredicate_subgraph PV2 PE2 g').
Proof.
  intros.
  destruct H1 as [? [? [? ?]]].
  unfold Included, Ensembles.In in H, H0.
  split; [| split; [| split]].
  + simpl in *; intros.
    specialize (H1 v); specialize (H v).
    rewrite !Intersection_spec in H1 |- *.
    tauto.
  + simpl in *; intros.
    specialize (H2 e); specialize (H0 e).
    rewrite !Intersection_spec in H2 |- *.
    tauto.
  + simpl; intros.
    specialize (H0 e).
    apply H3; simpl; rewrite !Intersection_spec in *; tauto.
  + simpl; intros.
    specialize (H0 e).
    apply H4; simpl; rewrite !Intersection_spec in *; tauto.
Qed.

Lemma no_edge_gen_dst_equiv: forall e p (g: Graph) pa x y,
    ~ In e (snd p) -> (pregraph_gen_dst g e pa) |= p is x ~o~> y satisfying (fun _ => True) <-> g |= p is x ~o~> y satisfying (fun _ => True).
Proof.
  intros. destruct p as [p l]. simpl in H. split; intro; destruct H0 as [[? ?] [? ?]]; split; split; auto; clear H0 H3.
  - clear H2. revert p H H1. induction l; intros. 1: simpl in *; auto. rewrite pfoot_cons in H1. remember (dst (pregraph_gen_dst g e pa) a) as w.
    simpl in Heqw. unfold updateEdgeFunc in Heqw. destruct (equiv_dec e a).
    + unfold Equivalence.equiv in e0; exfalso; apply H; left; auto.
    + rewrite pfoot_cons. apply IHl.
      * intro. apply H; right; auto.
      * subst w. auto.
  - clear H1. revert p H H2. induction l; intros. 1: simpl in *; auto. rewrite valid_path_cons_iff in H2 |-* . destruct H2 as [? [? ?]]. split; [|split].
    + simpl in H0. auto.
    + hnf in H1. simpl in H1. unfold updateEdgeFunc in H1. destruct (equiv_dec e a). 1: unfold Equivalence.equiv in e0; exfalso; apply H; left; auto. apply H1.
    + remember (dst (pregraph_gen_dst g e pa) a) as w. simpl in Heqw. unfold updateEdgeFunc in Heqw. destruct (equiv_dec e a). 1: exfalso; apply H; left; auto.
      subst w. apply IHl; auto. intro; apply H; right; auto.
  - clear H2. revert p H H1. induction l; intros. 1: simpl; auto. rewrite pfoot_cons. remember (dst (pregraph_gen_dst g e pa) a) as w. simpl in Heqw.
    unfold updateEdgeFunc in Heqw. destruct (equiv_dec e a). 1: exfalso; apply H; left; auto. subst w. apply IHl.
    + intro; apply H; right; auto.
    + rewrite pfoot_cons in H1. auto.
  - clear H1. revert p H H2. induction l; intros. 1: simpl in *; auto. rewrite valid_path_cons_iff in H2 |-* . destruct H2 as [? [? ?]]. split; [|split].
    + simpl; auto.
    + hnf. simpl. unfold updateEdgeFunc. destruct (equiv_dec e a). 1: unfold Equivalence.equiv in e0; exfalso; apply H; left; auto. apply H1.
    + remember (dst (pregraph_gen_dst g e pa) a) as w. simpl in Heqw. unfold updateEdgeFunc in Heqw. destruct (equiv_dec e a). 1: exfalso; apply H; left; auto.
      subst w. apply IHl; auto. intro; apply H; right; auto.
Qed.

Lemma not_reachable_gen_dst_equiv: forall (g: Graph) x e y z, ~ reachable g x (src g e) -> reachable (pregraph_gen_dst g e y) x z <-> reachable g x z.
Proof.
  intros. split; intro.
  - destruct H0 as [[p l] ?]. assert (~ In e l). {
      intro. apply (in_split_not_in_first EE) in H1. destruct H1 as [l1 [l2 [? ?]]]. subst l. apply reachable_by_path_app_cons in H0. destruct H0 as [? _].
      rewrite no_edge_gen_dst_equiv in H0. 2: simpl; auto. simpl src in H0. apply H. exists (p, l1). auto.
    } rewrite no_edge_gen_dst_equiv in H0. 2: simpl; auto. exists (p, l). auto.
  - destruct H0 as [[p l] ?]. assert (~ In e l). {
      intro. apply in_split in H1. destruct H1 as [l1 [l2 ?]]. subst l. apply reachable_by_path_app_cons in H0. destruct H0 as [? _]. apply H. exists (p, l1). auto.
    } exists (p, l). rewrite no_edge_gen_dst_equiv; auto.
Qed.

Lemma pgd_dst_changed: forall (g: Graph) e x, dst (pregraph_gen_dst g e x) e = x.
Proof. intros. simpl. unfold updateEdgeFunc. rewrite if_true; auto. easy. Qed.

Lemma pgd_dst_unchanged: forall (g: Graph) e1 e2 x,
    e1 <> e2 -> dst (pregraph_gen_dst g e1 x) e2 = dst g e2.
Proof. intros. simpl. unfold updateEdgeFunc. rewrite if_false; auto. Qed.

End PREGRAPH_GEN.

Section LABELED_GRAPH_GEN.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE DG: Type}.

Notation Graph := (LabeledGraph V E DV DE DG).

Local Coercion pg_lg : LabeledGraph >-> PreGraph.

Definition empty_labeledgraph (src0 dst0: E -> V) (v_default: DV) (e_default: DE) (g_default : DG) : Graph :=
  @Build_LabeledGraph V E EV EE DV DE DG (empty_pregraph src0 dst0) (fun v => v_default) (fun e => e_default) (g_default).

Definition single_vertex_labeledgraph (v0: V) (v_default: DV) (e_default: DE) (g_default : DG) : Graph :=
  @Build_LabeledGraph V E EV EE DV DE DG (single_vertex_pregraph v0) (fun v => v_default) (fun e => e_default) (g_default).

Definition labeledgraph_vgen (g: Graph) (x: V) (a: DV) : Graph := Build_LabeledGraph _ _ _ g (update_vlabel (vlabel g) x a) (elabel g) (glabel g).

Definition labeledgraph_egen (g: Graph) (e: E) (d: DE) : Graph := Build_LabeledGraph _ _ _ g (vlabel g) (update_elabel (elabel g) e d) (glabel g).

Definition labeledgraph_ggen (g: Graph) (m: DG) : Graph := Build_LabeledGraph _ _ _ g (vlabel g) (elabel g) m.

Definition labeledgraph_add_edge (g : Graph) (e : E) (o t : V) (d: DE) :=
  Build_LabeledGraph _ _ _ (pregraph_add_edge g e o t) (vlabel g) (update_elabel (elabel g) e d) (glabel g).

Definition labeledgraph_gen_dst (g : Graph) (e : E) (t : V) :=
  Build_LabeledGraph _ _ _ (pregraph_gen_dst g e t) (vlabel g) (elabel g) (glabel g).

Definition gpredicate_sub_labeledgraph (PV: V -> Prop) (PE: E -> Prop) (g: Graph): Graph :=
  Build_LabeledGraph _ _ _ (gpredicate_subgraph PV PE g) (vlabel g) (elabel g) (glabel g).

Definition predicate_sub_labeledgraph (g: Graph) (p: V -> Prop) :=
  Build_LabeledGraph _ _ _ (predicate_subgraph g p) (vlabel g) (elabel g) (glabel g).

Definition predicate_partial_labeledgraph (g: Graph) (p: V -> Prop) :=
  Build_LabeledGraph _ _ _ (predicate_partialgraph g p) (vlabel g) (elabel g) (glabel g).

Instance sub_labeledgraph_proper: Proper (labeled_graph_equiv ==> @Same_set V ==> labeled_graph_equiv) predicate_sub_labeledgraph.
Proof.
  do 2 (hnf; intros).
  destruct H as [? [? ?]].
  split; [| split].
  + apply subgraph_proper; auto.
  + simpl; intros.
    destruct H3, H4.
    apply H1; auto.
  + simpl; intros.
    destruct H3, H4.
    apply H2; auto.
Defined.

Global Existing Instance sub_labeledgraph_proper.

Instance partial_labeledgraph_proper: Proper (labeled_graph_equiv ==> @Same_set V ==> labeled_graph_equiv) predicate_partial_labeledgraph.
Proof.
  do 2 (hnf; intros).
  destruct H as [? [? ?]].
  split; [| split].
  + apply partialgraph_proper; auto.
  + simpl; intros.
    destruct H3, H4.
    apply H1; auto.
  + simpl; intros.
    destruct H3, H4.
    apply H2; auto.
Defined.

Global Existing Instance partial_labeledgraph_proper.

Instance gpredicate_sub_labeledgraph_proper: Proper (@Same_set V ==> @Same_set E ==> labeled_graph_equiv ==> labeled_graph_equiv) gpredicate_sub_labeledgraph.
Proof.
  do 3 (hnf; intros).
  split; [| split].
  + apply gpredicate_subgraph_proper; auto.
    destruct H1; auto.
  + simpl; intros.
    rewrite Intersection_spec in H2, H3.
    apply (proj1 (proj2 H1)); tauto.
  + simpl; intros.
    rewrite Intersection_spec in H2, H3.
    apply (proj2 (proj2 H1)); tauto.
Qed.

Global Existing Instance gpredicate_sub_labeledgraph_proper.

Lemma lg_vgen_stable: forall (g: Graph) (x: V) (d: DV),
  (predicate_partial_labeledgraph g (Complement V (eq x))) ~=~
   (predicate_partial_labeledgraph (labeledgraph_vgen g x d) (Complement V (eq x)))%LabeledGraph.
Proof.
  intros.
  split; [| split].
  + simpl.
    reflexivity.
  + intros; simpl.
    unfold update_vlabel.
    if_tac; auto.
    destruct H.
    exfalso; apply H2, H1.
  + intros; simpl.
    reflexivity.
Qed.

Lemma si_stronger_partial_labeledgraph: forall (g1 g2: Graph) (p1 p2 p1' p2' p: V -> Prop),
  (forall v, p1' v <-> p1 v /\ p v) ->
  (forall v, p2' v <-> p2 v /\ p v) ->
  (predicate_partial_labeledgraph g1 p1) ~=~ (predicate_partial_labeledgraph g2 p2)%LabeledGraph ->
  (predicate_partial_labeledgraph g1 p1') ~=~ (predicate_partial_labeledgraph g2 p2')%LabeledGraph.
Proof.
  intros.
  split; [| split].
  + eapply si_stronger_partialgraph; eauto.
    destruct H1 as [? _].
    auto.
  + simpl.
    intros ? [? ?] [? ?].
    destruct H1 as [_ [? _]].
    specialize (H1 v); simpl in H1.
    firstorder.
  + simpl.
    intros ? [? ?] [? ?].
    destruct H1 as [_ [_ ?]].
    specialize (H1 e); simpl in H1.
    firstorder.
Qed.

Lemma si_stronger_partial_labeledgraph_simple: forall (g1 g2: Graph) (p p': V -> Prop),
  Included p' p ->
  (predicate_partial_labeledgraph g1 p) ~=~ (predicate_partial_labeledgraph g2 p)%LabeledGraph ->
  (predicate_partial_labeledgraph g1 p') ~=~ (predicate_partial_labeledgraph g2 p')%LabeledGraph.
Proof.
  intros.
  eapply si_stronger_partial_labeledgraph with (p := p'); [| | exact H0].
  + intro v; specialize (H v); simpl in H; tauto.
  + intro v; specialize (H v); simpl in H; tauto.
Qed.

Lemma predicate_partial_labeledgraph_gpredicate_sub_labeledgraph (g: Graph) (p: V -> Prop):
  (predicate_partial_labeledgraph g p) ~=~ (gpredicate_sub_labeledgraph p (Intersection _ (weak_edge_prop p g) (evalid g)) g)%LabeledGraph.
Proof.
  split; [| split].
  + apply predicate_partialgraph_gpredicate_subgraph.
  + simpl; auto.
  + simpl; auto.
Qed.

Lemma gpredicate_sub_labeledgraph_self: forall (g: Graph),
  (gpredicate_sub_labeledgraph (vvalid g) (evalid g) g) ~=~ g%LabeledGraph.
Proof.
  intros.
  split; [| split].
  + apply gpredicate_subgraph_self; auto.
  + simpl; intros; auto.
  + simpl; intros; auto.
Qed.

Lemma gpredicate_sub_labeledgraph_equiv: forall (g: Graph) (PV1 PV2: V -> Prop) (PE1 PE2: E -> Prop),
  Same_set (Intersection _ (vvalid g) PV1) (Intersection _ (vvalid g) PV2) ->
  Same_set (Intersection _ (evalid g) PE1) (Intersection _ (evalid g) PE2) ->
  (gpredicate_sub_labeledgraph PV1 PE1 g) ~=~ (gpredicate_sub_labeledgraph PV2 PE2 g)%LabeledGraph.
Proof.
  intros.
  split; [| split].
  + apply gpredicate_subgraph_equiv; auto.
  + simpl; intros; auto.
  + simpl; intros; auto.
Qed.

Lemma stronger_gpredicate_sub_labeledgraph_simple: forall (g g': Graph) (PV1 PV2: V -> Prop) (PE1 PE2: E -> Prop),
  Included PV2 PV1 ->
  Included PE2 PE1 ->
  (gpredicate_sub_labeledgraph PV1 PE1 g) ~=~ (gpredicate_sub_labeledgraph PV1 PE1 g')%LabeledGraph ->
  (gpredicate_sub_labeledgraph PV2 PE2 g) ~=~ (gpredicate_sub_labeledgraph PV2 PE2 g')%LabeledGraph.
Proof.
  intros.
  destruct H1 as [? [? ?]].
  split; [| split].
  + eapply stronger_gpredicate_subgraph_simple; eauto.
  + simpl; intros.
    specialize (H v).
    apply H2; simpl; rewrite !Intersection_spec in *; tauto.
  + simpl; intros.
    specialize (H0 e).
    apply H3; simpl; rewrite !Intersection_spec in *; tauto.
Qed.

End LABELED_GRAPH_GEN.

Section GENERAL_GRAPH_GEN.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE DG: Type}.

Class NormalGeneralGraph (P: LabeledGraph V E DV DE DG -> Type): Type := {
  lge_preserved: forall g1 g2, labeled_graph_equiv g1 g2 -> P g1 -> P g2;
  join_preserved: forall g (PV1 PV2 PV: V -> Prop) (PE1 PE2 PE: E -> Prop),
    Prop_join PV1 PV2 PV ->
    Prop_join PE1 PE2 PE ->
    P (gpredicate_sub_labeledgraph PV1 PE1 g) ->
    P (gpredicate_sub_labeledgraph PV2 PE2 g) ->
    P (gpredicate_sub_labeledgraph PV PE g)
}.

Context {P: LabeledGraph V E DV DE DG -> Type}.

Notation Graph := (GeneralGraph V E DV DE DG P).

Local Coercion pg_lg : LabeledGraph >-> PreGraph.
Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.

Definition generalgraph_vgen (g: Graph) (x: V) (d: DV) (sound': P _): Graph := @Build_GeneralGraph V E EV EE DV DE DG P (labeledgraph_vgen g x d) sound'.

Definition generalgraph_egen (g: Graph) (e: E) (d: DE) (sound': P _): Graph := @Build_GeneralGraph V E EV EE DV DE DG P (labeledgraph_egen g e d) sound'.

Definition generalgraph_ggen (g: Graph) (m: DG) (sound': P _): Graph := @Build_GeneralGraph V E EV EE DV DE DG P (labeledgraph_ggen g m) sound'.

Definition generalgraph_gen_dst (g: Graph) (e : E) (t : V) (sound' : P _): Graph := @Build_GeneralGraph V E EV EE DV DE DG P (labeledgraph_gen_dst g e t) sound'.

End GENERAL_GRAPH_GEN.

Section ADD_GRAPH_GEN.

  Context {V E: Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.
  Context {DV DE: Type}.
  Notation Gph := (PreGraph V E).

  Variable g: Gph.

  Definition change_vvalid (v: V): Ensemble V :=
    fun n => vvalid g n \/ n = v.

  Definition change_node_pred (P: NodePred V) (v: V) (Pv: {Pv : Prop & {Pv} + {~ Pv}}) : NodePred V.
  Proof.
    intros.
    exists (fun n: V => (if equiv_dec n v then projT1 Pv else P n)).
    intros.
    destruct_eq_dec x v.
    + destruct Pv; auto.
    + destruct P; simpl; auto.
  Defined.

  Definition change_evalid v : Ensemble E := fun e => evalid g e \/ src g e = v.

(*
(*TODO: To resume *)
  Context {BI: BiGraph g left_out_edge right_out_edge}.

  Definition change_dst (v l r: V) : E -> V.
  Proof.
    intro e.
    refine (if equiv_dec (src g e) v then _ else dst g e).
    exact (if left_or_right _ _ v e _H then l else r).
  Defined.

  Definition update_PreGraph v l r : Gph :=
    Build_PreGraph EV EE (change_vvalid v) (change_evalid v) (src g) (change_dst v l r).

  Definition in_math (v l r: V) : Type :=
    forall y, In y (l :: r :: nil) -> {vvalid g y} + {y = v} + {is_null g y}.

  Definition update_MathGraph v l r (Hi: in_math v l r) (Hn: ~ is_null g v): MathGraph (update_PreGraph v l r).
  Proof.
    refine (Build_MathGraph _ (is_null g) (is_null_dec g) _ _).
    + unfold update_PreGraph, change_vvalid, change_evalid, change_dst; simpl.
      intros.
      destruct_eq_dec (src g e) v.
      - split; [right; auto |].
        destruct (left_or_right g BI v e H0); [destruct (Hi l) | destruct (Hi r)]; simpl; tauto.
      - assert (evalid g e) by tauto.
        apply (valid_graph g) in H1.
        unfold weak_valid in H1.
        tauto.
    + unfold update_PreGraph, change_vvalid; simpl.
      intros.
      destruct H; [| subst]; auto.
      apply (valid_not_null g) with x; tauto.
  Defined.

  Definition update_BiGraph v l r: BiGraph (update_PreGraph v l r) left_out_edge right_out_edge.
  Proof.
    refine (Build_BiGraph _ _ _ _ _ _ _).
    + unfold update_PreGraph; simpl.
      unfold change_vvalid, change_evalid.
      intros.
      rewrite (left_sound g).
      pose proof left_valid g x.
      tauto.
    + unfold update_PreGraph; simpl.
      unfold change_vvalid, change_evalid.
      intros.
      rewrite (right_sound g).
      pose proof right_valid g x.
      tauto.
    + unfold update_PreGraph; simpl; apply (bi_consist g).
    + unfold update_PreGraph; simpl; apply (only_two_edges g).
  Defined.

  Definition update_FiniteGraph v l r: FiniteGraph (update_PreGraph v l r).
  Proof.
    refine (Build_FiniteGraph _ _ _); unfold update_PreGraph, change_vvalid, change_evalid, change_dst; simpl.
    + destruct FA as [? _]. unfold EnumEnsembles.Enumerable, Ensembles.In in *.
      destruct finiteV as [l0 [? ?]]. destruct (in_dec equiv_dec v l0).
      - exists l0. split; auto. intro. split; intros.
        * left. apply H0 in H1. auto.
        * destruct H1; [rewrite H0 | subst]; auto.
      - exists (v :: l0). split. constructor; auto. intros. split; intro.
        * destruct H1; [right | left]. auto. specialize (H0 x); intuition.
        * simpl. destruct H1; [right | left]; auto. specialize (H0 x); intuition.
    + destruct FA as [_ ?]. unfold EnumEnsembles.Enumerable, Ensembles.In in *.
      destruct finiteE as [l0 [? ?]].
      destruct (in_dec equiv_dec (left_out_edge v) l0); destruct (in_dec equiv_dec (right_out_edge v) l0).
      - exists l0. split; auto. intros; split; intros.
        left; specialize (H0 x); intuition. destruct H1.
        * specialize (H0 x); intuition.
        * destruct BI. specialize (only_two_edges v x). rewrite only_two_edges in H1.
          destruct H1; subst; auto.
      - remember (left_out_edge v) as e1. remember (right_out_edge v) as e2. exists (e2 :: l0).
        split. constructor; auto. intro; split; intro.
        * destruct H1; [right | left]. subst x. subst e2. destruct BI.
          rewrite only_two_edges. right; auto. specialize (H0 x); intuition.
        * simpl. destruct H1. right; specialize (H0 x); intuition. destruct BI.
          rewrite only_two_edges in H1. destruct H1.
          1: { right. subst e1. subst x. auto. }
          1: { left. subst e2. subst x. auto. }
      - remember (left_out_edge v) as e1. remember (right_out_edge v) as e2. exists (e1 :: l0).
        split. constructor; auto. intro; split; intro.
        * destruct H1; [right | left]. subst x. subst e1. destruct BI.
          rewrite only_two_edges. left; auto. specialize (H0 x); intuition.
        * simpl. destruct H1. right; specialize (H0 x); intuition. destruct BI.
          rewrite only_two_edges in H1. destruct H1.
          1: { left. subst e1. subst x. auto. }
          1: { right. subst e2. subst x. auto. }
      - remember (left_out_edge v) as e1. remember (right_out_edge v) as e2. exists (e1 :: e2 :: l0). split.
        * constructor. intro. destruct H1; auto. destruct BI.
          specialize (bi_consist v). subst. auto. constructor; auto.
        * intro. split; intro.
          1: {
            simpl in H1. destruct H1; [|destruct H1].
            + right. subst x. subst e1. destruct BI. rewrite only_two_edges. left; auto.
            + right. subst x. subst e2. destruct BI. rewrite only_two_edges. right; auto.
            + left. specialize (H0 x). intuition.
          }
          1: {
            destruct H1.
            + simpl. right; right. specialize (H0 x). intuition.
            + destruct BI. rewrite only_two_edges in H1. simpl. destruct H1.
              - left. subst x. subst e1. auto.
              - right; left. subst x. subst e2. auto.
          }
  Qed.
*)
End ADD_GRAPH_GEN.
(*
(* TODO: to resume *)
Section ADD_LABELED_GRAPH_GEN.

  Context {V E: Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.
  Context {DV DE: Type}.

  Notation Graph := (LabeledGraph V E DV DE).

  Local Coercion pg_lg: LabeledGraph >-> PreGraph.

  Variable g: Graph.

  Definition update_LabeledGraph (x l r: V) :=
    Build_LabeledGraph _ _ (update_PreGraph g left_out_edge right_out_edge x l r) (vlabel g) (elabel g).

End ADD_LABELED_GRAPH_GEN.

Section ADD_GENERAL_GRAPH_GEN.

  Context {V E: Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.
  Context {DV DE: Type}.
  Context {P: LabeledGraph V E DV DE -> Type}.

  Notation Graph := (GeneralGraph V E DV DE P).

  Local Coercion pg_lg: LabeledGraph >-> PreGraph.
  Local Coercion lg_gg: GeneralGraph >-> LabeledGraph.

  Variable g: Graph.

  Definition update_GeneralGraph (x l r: V) (sound': P _): Graph :=
    @Build_GeneralGraph V E EV EE DV DE P (update_LabeledGraph g left_out_edge right_out_edge x l r) sound'.

End ADD_GENERAL_GRAPH_GEN.
*)