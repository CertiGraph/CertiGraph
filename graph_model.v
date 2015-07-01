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

Definition out_edges {Vertex Edge: Type} (pg: PreGraph Vertex Edge) x: Ensemble Edge := fun e => evalid e /\ src e = x.

Definition in_edges {Vertex Edge: Type} (pg: PreGraph Vertex Edge) x: Ensemble Edge := fun e => evalid e /\ dst e = x.

Class MathGraph {Vertex Edge: Type} (pg: PreGraph Vertex Edge) := {
  is_null: Ensemble Vertex;
  is_null_dec: forall p, {is_null p} + {~ is_null p};
  weak_valid: Vertex -> Prop := fun p => is_null p \/ vvalid p;
  valid_graph: forall e, evalid e -> vvalid (src e) /\ weak_valid (dst e);
  valid_not_null: forall x, vvalid x -> is_null x -> False
}.

Class FiniteGraph {Vertex Edge: Type} (pg: PreGraph Vertex Edge) :=
{
  finiteV: Enumerable Vertex vvalid;
  finiteE: Enumerable Edge evalid
}.

Class LocalFiniteGraph {Vertex Edge: Type} (pg: PreGraph Vertex Edge) :=
{
  local_enumerable: forall x, Enumerable Edge (out_edges pg x)
}.

Definition GraphMark {Vertex Edge: Type} (pg: PreGraph Vertex Edge) := 
  sigT (fun marked : Vertex -> Prop => forall x, vvalid x -> {marked x} + {~ marked x}).

Definition app_graph_mark {Vertex Edge: Type} {pg: PreGraph Vertex Edge} (marked: GraphMark pg) (x: Vertex) :=
  projT1 marked x.

Coercion app_graph_mark : GraphMark >-> Funclass.

Definition edge_func {Vertex Edge: Type} (pg: PreGraph Vertex Edge) {lfg: LocalFiniteGraph pg} x := projT1 (local_enumerable x).

Class BiGraph {Vertex Edge: Type} (pg: PreGraph Vertex Edge) {lfg: LocalFiniteGraph pg} :=
{
  only_two_neighbours : forall (v : Vertex), {e1 : Edge & {e2 : Edge | edge_func pg v = e1 :: e2 :: nil}}
}.

(******************************************

Properties

******************************************)

Lemma step_spec: forall {Vertex Edge: Type} (pg: PreGraph Vertex Edge) x y, step pg x y <-> exists e, evalid e /\ src e = x /\ dst e = y.
Proof.
  intros; split; intro.
  + inversion H; eauto.
  + destruct H as [? [? [? ?]]]; econstructor; eauto.
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

Definition biEdge {Vertex Edge} {PG : PreGraph Vertex Edge} {LFG: LocalFiniteGraph PG} (BG: BiGraph PG) (v: Vertex) : Vertex * Vertex.
  specialize (only_two_neighbours v); intro.
  destruct X as [e1 [e2 ?]].
  exact (dst e1, dst e2).
Defined.

Lemma biEdge_only2 {Vertex Edge} {PG : PreGraph Vertex Edge} {LFG: LocalFiniteGraph PG} (BG: BiGraph PG) :
  forall v v1 v2 n, biEdge BG v = (v1 ,v2) -> step PG v n -> n = v1 \/ n = v2.
Proof.
  intros; unfold biEdge in H.
  revert H; case_eq (only_two_neighbours v); intro x1; intros.
  revert H1; case_eq s; intro x2; intros. inversion H2. subst.
  rewrite edge_func_step in H0; rewrite e in H0.
  simpl in H0.
  destruct H0 as [? | [? | ?]]; [left | right | right]; symmetry; tauto.
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

Definition edge {V E : Type} (G : PreGraph V E) (n n' : V) : Prop :=
  vvalid n /\ vvalid n' /\ step G n n'.

Notation " g |= n1 ~> n2 " := (edge g n1 n2) (at level 1).

Lemma step_si {V E : Type}:
  forall (g1 g2 : PreGraph V E) (n n' : V), g1 ~=~ g2 -> step g1 n n' -> step g2 n n'.
Proof.
  intros.
  rewrite step_spec in H0 |- *.
  destruct H as [? [? [? ?]]].
  destruct H0 as [e [? [? ?]]]; exists e.
  rewrite <- H1, <- H2, <- H3.
  auto.
Qed.

Lemma edge_si {V E : Type}:
  forall (g1 g2 : PreGraph V E) (n n' : V), g1 ~=~ g2 -> g1 |= n ~> n' -> g2 |= n ~> n'.
Proof.
  intros; unfold edge in *.
  pose proof H.
  destruct H as [? [? [? ?]]].
  rewrite <- !H.
  split; [| split]; try tauto.
  apply (step_si g1 g2); auto.
  tauto.
Qed.

(******************************************

Paths

******************************************)

Fixpoint valid_path {V E : Type} (g: PreGraph V E) (p : list V) : Prop :=
  match p with
    | nil => True
    | n :: nil => vvalid n
    | n1 :: ((n2 :: _) as p') => g |= n1 ~> n2 /\ valid_path g p'
  end.

Definition graph_is_acyclic {V E : Type} (g: PreGraph V E) : Prop :=
  forall p : list V, valid_path g p -> NoDup p.

Definition path_prop {V E : Type} (g: PreGraph V E) (P : Ensemble V) : (list V -> Prop) :=
  Forall P.

Definition good_path {V E : Type} (g: PreGraph V E) (P : Ensemble V) : (list V -> Prop) :=
    fun p => valid_path g p /\ path_prop g P p.

Definition path_endpoints {N} (p : list N) (n1 n2 : N) : Prop := head p = Some n1 /\ foot p = Some n2.

(******************************************

Reachable

******************************************)

Definition reachable_by_path {V E : Type} (g: PreGraph V E) (p : list V)
           (n : V) (P : Ensemble V) : Ensemble V := fun n' => path_endpoints p n n' /\ good_path g P p.
Notation " g '|=' p 'is' n1 '~o~>' n2 'satisfying' P" := (reachable_by_path g p n1 P n2) (at level 1).

Definition reachable_by {V E : Type} (g: PreGraph V E) (n : V) (P : Ensemble V) : Ensemble V :=
  fun n' => exists p, g |= p is n ~o~> n' satisfying P.
Notation " g '|=' n1 '~o~>' n2 'satisfying' P " := (reachable_by g n1 P n2) (at level 1).

Definition reachable_by_acyclic {V E : Type} (g: PreGraph V E) (n : V) (P : Ensemble V) : Ensemble V :=
  fun n' => exists p, NoDup p /\ g |= p is n ~o~> n' satisfying P.
Notation " g '|=' n1 '~~>' n2 'satisfying' P " := (reachable_by_acyclic g n1 P n2) (at level 1).

Definition reachable {V E : Type} (g: PreGraph V E) (n : V): Ensemble V:=
  reachable_by g n (fun _ => True).

Definition reachable_through_set {V E : Type} (g: PreGraph V E) (S : list V) : Ensemble V:=
  fun n => exists s, In s S /\ reachable g s n.

Lemma reachable_Same_set  {V E : Type} (g: PreGraph V E) (S1 S2 : list V):
  S1 ~= S2 -> Same_set (reachable_through_set g S1) (reachable_through_set g S2).
Proof. intros; destruct H; split; repeat intro; destruct H1 as [y [HIn Hrch]]; exists y; split; auto. Qed.

Definition reachable_valid {V E : Type} (g: PreGraph V E) (S : list V) : V -> Prop :=
  fun n => @vvalid _ _ _ n /\ reachable_through_set g S n.

Definition reachable_subgraph {V E : Type} (g: PreGraph V E) (S : list V) :=
  Build_PreGraph V E EV EE (reachable_valid g S) evalid.

Definition unreachable_valid {V E : Type} (g: PreGraph V E) (S : list V) : V -> Prop :=
  fun n => @vvalid _ _ _ n /\ ~ reachable_through_set g S n.

Definition unreachable_subgraph {V E : Type} (g: PreGraph V E) (S : list V) :=
  Build_PreGraph  V E EV EE (unreachable_valid g S) evalid.

(******************************************

Marked Graph

******************************************)

Module MARKED_GRAPH.

Definition marked_coincide {V E : Type} {g1 g2: PreGraph V E} (m1: GraphMark g1) (m2: GraphMark g2) :=
  forall x, @vvalid _ _ g1 x -> @vvalid _ _ g2 x -> (m1 x <-> m2 x).

Class MarkedGraph (Vertex Edge: Type) := {
  pg: PreGraph Vertex Edge;
  marked: GraphMark pg
}.

Local Coercion pg : MarkedGraph >-> PreGraph.
Local Coercion marked : MarkedGraph >-> GraphMark.

Definition validly_identical {V E: Type} (g1 g2: MarkedGraph V E) : Prop :=
  g1 ~=~ g2 /\ marked_coincide g1 g2.

Notation "g1 '-=-' g2" := (validly_identical g1 g2) (at level 1).

Lemma vi_refl: forall {V E : Type} (G : MarkedGraph V E), G -=- G.
Proof. intros; split; [reflexivity |]. repeat intro. reflexivity. Qed.

Lemma vi_sym: forall {V E : Type} (G1 G2 : MarkedGraph V E), G1 -=- G2 -> G2 -=- G1.
Proof.
  intros; destruct H; split; [symmetry; auto |].
  repeat intro.
  symmetry; apply H0; auto.
Qed.

Lemma vi_trans: forall {V E : Type} (G1 G2 G3 : MarkedGraph V E), G1 -=- G2 -> G2 -=- G3 -> G1 -=- G3.
Proof.
Arguments vvalid {_} {_} _ _.
  intros; destruct H, H0; split; [rewrite H; auto |].
  repeat intro.
  assert (vvalid G2 x) by (rewrite (proj1 H) in H3; auto).
  rewrite (H1 _ H3 H5).
  auto.
Qed.

Add Parametric Relation {V E : Type} : (MarkedGraph V E) validly_identical
    reflexivity proved by vi_refl
    symmetry proved by vi_sym
    transitivity proved by vi_trans as vi_equal.

End MARKED_GRAPH.

Print MARKED_GRAPH.

Section GraphPath.
  Variable V : Type.
  Variable E : Type.
  Notation Gph := (PreGraph V E).

  Definition path : Type := list V.
  Definition paths_meet_at (p1 p2 : path) := fun n => foot p1 = Some n /\ head p2 = Some n.
  Definition paths_meet (p1 p2 : path) : Prop := exists n, paths_meet_at p1 p2 n.

  Lemma path_endpoints_meet: forall p1 p2 n1 n2 n3,
    path_endpoints p1 n1 n2 ->
    path_endpoints p2 n2 n3 ->
    paths_meet p1 p2.
  Proof.
    unfold path_endpoints, paths_meet; intros.
    destruct H, H0. exists n2. red. tauto.
  Qed.

  Lemma paths_foot_head_meet: forall p1 p2 n, paths_meet (p1 +:: n) (n :: p2).
  Proof. intros. exists n. split. apply foot_last. trivial. Qed.

  Definition path_glue (p1 p2 : path) : path := p1 ++ (tail p2).
  Notation "p1 '+++' p2" := (path_glue p1 p2) (at level 20, left associativity).

  Lemma path_glue_nil_l: forall p, nil +++ p = tail p.
  Proof.
    unfold path_glue.  trivial.
  Qed.

  Lemma path_glue_nil_r: forall p, p +++ nil = p.
  Proof.
    unfold path_glue. simpl. intro. rewrite app_nil_r. trivial.
  Qed.

  Lemma path_glue_assoc: forall p1 p2 p3 : path,
    paths_meet p1 p2 -> paths_meet p2 p3 -> (p1 +++ p2) +++ p3 = p1 +++ (p2 +++ p3).
  Proof.
    unfold path_glue.
    induction p1; simpl; intros. icase H. icase H.
    icase p2. icase H. icase H. icase p3.
    do 2 rewrite app_nil_r. trivial.
    icase p2. simpl. rewrite app_nil_r. trivial. simpl.
    rewrite <- app_assoc. f_equal.
  Qed.

  Lemma path_glue_comm_cons: forall n p1 p2, (n :: p1 +++ p2) = ((n :: p1) +++ p2).
  Proof.
    unfold path_glue. intros. rewrite app_comm_cons. trivial.
  Qed.

  Lemma path_endpoints_glue: forall n1 n2 n3 p1 p2,
    path_endpoints p1 n1 n2 -> path_endpoints p2 n2 n3 -> path_endpoints (p1 +++ p2) n1 n3.
  Proof.
    split; destruct H, H0.
    icase p1. unfold path_glue.
    icase p2. icase p2. inv H0. inv H2. simpl. rewrite app_nil_r. trivial.
    rewrite foot_app; disc. apply H2.
  Qed.

  Lemma valid_path_tail: forall (g : Gph) p, valid_path g p -> valid_path g (tail p).
  Proof.
    destruct p; auto. simpl. destruct p; auto.
    intro; simpl; auto. intros [? ?]; auto.
  Qed.

  Lemma valid_path_split: forall (g : Gph) p1 p2, valid_path g (p1 ++ p2) -> valid_path g p1 /\ valid_path g p2.
  Proof.
    induction p1. simpl. tauto.
    intros. rewrite <- app_comm_cons in H.
    simpl in H. revert H. case_eq (p1 ++ p2); intros.
    apply app_eq_nil in H. destruct H. subst. simpl. tauto.
    destruct H0. rewrite <- H in H1.
    apply IHp1 in H1. destruct H1.
    split; trivial.
    simpl. destruct p1; auto.
    destruct H0; auto.
    rewrite <- app_comm_cons in H. inv H. tauto.
  Qed.

  Lemma valid_path_merge: forall (g : Gph) p1 p2,
                            paths_meet p1 p2 -> valid_path g p1 -> valid_path g p2 -> valid_path g (p1 +++ p2).
  Proof.
    induction p1. simpl. intros. apply valid_path_tail. trivial.
    intros. rewrite <- path_glue_comm_cons.
    simpl.
    case_eq (p1 +++ p2); auto.
    intros. simpl in H0. destruct p1; auto; destruct H0; destruct H0; auto.
    intros. rewrite <- H2.
    split.
    icase p1. unfold path_glue in H2. simpl in H2.
    icase p2. inv H. simpl in H2. subst p2.
    simpl in H1. destruct H3. rewrite <- H in H2. simpl in H2. inv H2. tauto.
    rewrite <- path_glue_comm_cons in H2. inv H2.
    simpl in H0. tauto.
    icase p1.
    rewrite path_glue_nil_l. apply valid_path_tail; auto.
    apply IHp1; auto.
    change (v0 :: p1) with (tail (a :: v0 :: p1)). apply valid_path_tail; auto.
  Qed.

  Lemma valid_path_si: forall (g1 g2: Gph),
      structurally_identical g1 g2 -> forall p, valid_path g1 p -> valid_path g2 p.
  Proof.
    induction p; simpl; auto.
    icase p.
    + pose proof (proj1 H a); tauto.
    + intros [? ?]. split; auto.
      apply (edge_si g1 g2 a v H H0).
  Qed.

  Lemma valid_path_acyclic:
    forall (g : Gph) (p : path) n1 n2,
      path_endpoints p n1 n2 -> valid_path g p ->
      exists p', Sublist p' p /\ path_endpoints p' n1 n2 /\ NoDup p' /\ valid_path g p'.
  Proof.
    intros until p. remember (length p). assert (length p <= n) by omega. clear Heqn. revert p H. induction n; intros.
    icase p; icase H0. inv H0. inv H.
    destruct (nodup_dec p) as [? | H2]. exists p. split. reflexivity. tauto.
    apply Dup_cyclic in H2. destruct H2 as [a [L1 [L2 [L3 ?]]]]. subst p. specialize (IHn (L1 ++ a :: L3)).
    spec IHn. do 2 rewrite app_length in H. rewrite app_length. simpl in *. omega. specialize (IHn n1 n2).
    spec IHn. destruct H0. split. icase L1. repeat (rewrite foot_app in *; disc). trivial.
    spec IHn. change (L1 ++ a :: L3) with (L1 ++ (a :: nil) ++ tail (a :: L3)).
    rewrite app_assoc. change (a :: L2) with ((a :: nil) ++ L2) in H1.
    do 2 rewrite app_assoc in H1. apply valid_path_split in H1. destruct H1.
    apply valid_path_merge; auto. apply paths_foot_head_meet. apply valid_path_split in H1. tauto.
    destruct IHn as [p' [? [? [? ?]]]]. exists p'. split. 2: tauto. transitivity (L1 ++ a :: L3); auto.
    apply Sublist_app. reflexivity. pattern (a :: L3) at 1. rewrite <- (app_nil_l (a :: L3)).
    apply Sublist_app. apply Sublist_nil. reflexivity.
  Qed.

(*
  Lemma node_prop_label_eq: forall g1 g2 n P,
    @node_label _ D _ g1 n = @node_label _ _ _ g2 n -> node_prop g1 P n -> node_prop g2 P n.
  Proof. intros; hnf in *; rewrite <- H; trivial.  Qed.

  Lemma node_prop_weaken: forall g (P1 P2 : Ensemble D) n, (forall d, P1 d -> P2 d) -> node_prop g P1 n -> node_prop g P2 n.
  Proof. intros; hnf in *; auto. Qed.
*)

  Lemma path_prop_weaken: forall (g: Gph) (P1 P2 : Ensemble V) p,
    (forall d, P1 d -> P2 d) -> path_prop g P1 p -> path_prop g P2 p.
  Proof. intros; hnf in *; intros; hnf in *; eapply Forall_impl; eauto. Qed.

  Lemma path_prop_sublist: forall (g: Gph) P p1 p2, Sublist p1 p2 -> path_prop g P p2 -> path_prop g P p1.
  Proof. repeat intro. eapply Forall_sublist; eauto. Qed.

  Lemma path_prop_tail: forall (g: Gph) P n p, path_prop g P (n :: p) -> path_prop g P p.
  Proof. repeat intro. inversion H; auto. Qed.

  Lemma good_path_split: forall (g: Gph) p1 p2 P, good_path g P (p1 ++ p2) -> (good_path g P p1) /\ (good_path g P p2).
  Proof.
    intros. destruct H. apply valid_path_split in H; destruct H. unfold good_path. unfold path_prop in *.
    rewrite !Forall_forall in *.
    intuition.
  Qed.

  Lemma good_path_merge: forall (g: Gph) p1 p2 P,
                           paths_meet p1 p2 -> good_path g P p1 -> good_path g P p2 -> good_path g P (p1 +++ p2).
  Proof.
    intros. destruct H0. destruct H1. split. apply valid_path_merge; auto. unfold path_prop in *. intros.
    rewrite Forall_forall in *; intros.
    unfold path_glue in H4. apply in_app_or in H4. destruct H4. auto. apply H3. apply In_tail; auto.
  Qed.

  Lemma good_path_weaken: forall (g: Gph) p (P1 P2 : Ensemble V),
                            (forall d, P1 d -> P2 d) -> good_path g P1 p -> good_path g P2 p.
  Proof.
    split; destruct H0; auto.
    apply path_prop_weaken with P1; auto.
  Qed.

  Lemma good_path_acyclic:
    forall (g: Gph) P p n1 n2,
      path_endpoints p n1 n2 -> good_path g P p -> exists p', path_endpoints p' n1 n2 /\ NoDup p' /\ good_path g P p'.
  Proof.
    intros. destruct H0. apply valid_path_acyclic with (n1 := n1) (n2 := n2) in H0; trivial.
    destruct H0 as [p' [? [? [? ?]]]]. exists p'. split; trivial. split; trivial.
    split; trivial. apply path_prop_sublist with p; trivial.
  Qed.

  Lemma reachable_by_path_nil: forall (g : Gph) n1 n2 P, ~ g |= nil is n1 ~o~> n2 satisfying P.
  Proof. repeat intro. destruct H as [[? _] _]. disc. Qed.

  Lemma reachable_by_path_head: forall (g: Gph) p n1 n2 P, g |= p is n1 ~o~> n2 satisfying P -> head p = Some n1.
  Proof. intros. destruct H as [[? _] _]. trivial. Qed.

  Lemma reachable_by_path_foot: forall (g: Gph) p n1 n2 P, g |= p is n1 ~o~> n2 satisfying P -> foot p = Some n2.
  Proof. intros. destruct H as [[_ ?] _]. trivial. Qed.

  Lemma reachable_by_path_merge: forall (g: Gph) p1 n1 n2 p2 n3 P,
                                   g |= p1 is n1 ~o~> n2 satisfying P ->
                                   g |= p2 is n2 ~o~> n3 satisfying P ->
                                   g |= (p1 +++ p2) is n1 ~o~> n3 satisfying P.
  Proof.
    intros. destruct H. destruct H0.
    split. apply path_endpoints_glue with n2; auto.
    apply good_path_merge; auto.
    eapply path_endpoints_meet; eauto.
  Qed.

  Lemma reachable_by_path_split_glue:
    forall (g: Gph) P p1 p2 n1 n2 n, paths_meet_at p1 p2 n ->
                                     g |= (p1 +++ p2) is n1 ~o~> n2 satisfying P ->
                                     g |= p1 is n1 ~o~> n satisfying P /\
                                     g |= p2 is n ~o~> n2 satisfying P.
  Proof.
    intros. unfold path_glue in H0. destruct H0.
    destruct H.
    destruct (foot_explicit _ _ H) as [L' ?]. subst p1.
    icase p2. inv H2.
    copy H1. apply good_path_split in H1. destruct H1 as [? _].
    rewrite <- app_assoc in H2, H0. simpl in H2, H0.
    apply good_path_split in H2. destruct H2 as [_ ?].
    destruct H0. rewrite foot_app in H3; disc.
    repeat (split; trivial). icase L'.
  Qed.

  Lemma reachable_by_path_split_in: forall (g : Gph) P p n n1 n2,
    g |= p is n1 ~o~> n2 satisfying P ->
    In n p -> exists p1 p2,
                p = p1 +++ p2 /\
                g |= p1 is n1 ~o~> n satisfying P /\
                g |= p2 is n ~o~> n2 satisfying P.
  Proof.
    intros. destruct (in_split _ _ H0) as [p1 [p2 ?]]. subst p. clear H0.
    replace (p1 ++ n :: p2) with ((p1 ++ (n :: nil)) +++ (n :: p2)) in H.
    2: unfold path_glue; rewrite <- app_assoc; auto.
    apply reachable_by_path_split_glue with (n := n) in H.
    exists (p1 ++ n :: nil). exists (n :: p2).
    split; trivial.
    unfold path_glue. rewrite <- app_assoc. trivial.
    split; trivial. rewrite foot_app; disc. trivial.
  Qed.

  Lemma reachable_by_path_Forall: forall (g: Gph) p n1 n2 P,
    g |= p is n1 ~o~> n2 satisfying P -> Forall P p.
  Proof. intros. destruct H as [_ [_ ?]]. apply H. Qed.

  Lemma reachable_by_path_In: forall (g: Gph) p n1 n2 P n,
    g |= p is n1 ~o~> n2 satisfying P -> In n p -> P n.
  Proof. intros. pose proof reachable_by_path_Forall _ _ _ _ _ H. rewrite Forall_forall in H1; auto. Qed.

  Lemma reachable_by_reflexive: forall (g : Gph) n P, @vvalid _ _ g n /\ P n -> g |= n ~o~> n satisfying P.
  Proof.
    intros.
    exists (n :: nil). split. compute. auto.
    split. simpl. trivial. destruct H; auto.
    repeat constructor; tauto.
  Qed.

  Lemma reachable_by_merge: forall (g: Gph) n1 n2 n3 P,
    g |= n1 ~o~> n2 satisfying P ->
    g |= n2 ~o~> n3 satisfying P ->
    g |= n1 ~o~> n3 satisfying P.
  Proof. do 2 destruct 1. exists (x +++ x0). apply reachable_by_path_merge with n2; auto. Qed.

  Lemma reachable_by_head_prop: forall (g: Gph) n1 n2 P, g |= n1 ~o~> n2 satisfying P -> P n1.
  Proof.
    intros. destruct H as [p ?]. eapply reachable_by_path_In; eauto.
    apply reachable_by_path_head in H. icase p. inv H. simpl. auto.
  Qed.

  Lemma reachable_by_foot_prop: forall (g: Gph) n1 n2 P, g |= n1 ~o~> n2 satisfying P -> P n2.
  Proof.
    intros. destruct H as [p ?]. eapply reachable_by_path_In; eauto.
    apply reachable_by_path_foot in H. apply foot_in. trivial.
  Qed.

  Lemma reachable_by_cons:
    forall (g: Gph) n1 n2 n3 (P: Ensemble V),
       g |= n1 ~> n2 ->
       P n1 ->
       g |= n2 ~o~> n3 satisfying P ->
       g |= n1 ~o~> n3 satisfying P.
  Proof.
    intros. apply reachable_by_merge with n2; auto.
    apply reachable_by_head_prop in H1.
    exists (n1 :: n2 :: nil). split. split; auto.
    split. simpl. split; auto. destruct H as [? [? ?]]. auto.
    repeat constructor; auto.
  Qed.

  Lemma reachable_acyclic: forall (g: Gph) n1 P n2,
    g |= n1 ~o~> n2 satisfying P <->
    g |= n1 ~~> n2 satisfying P.
  Proof.
    split; intros.
    destruct H as [p [? ?]].
    apply (good_path_acyclic g P p n1 n2 H) in H0.
    destruct H0 as [p' [? ?]].
    exists p'. destruct H1. split; auto. split; auto.
    destruct H as [p [? ?]].
    exists p. trivial.
  Qed.

  Lemma reachable_by_subset_reachable: forall (g: Gph) n P,
    Included (reachable_by g n P) (reachable g n).
  Proof.
    repeat intro. unfold reachable.
    destruct H as [p [? [? ?]]]. exists p.
    split; trivial.
    split; trivial. apply path_prop_weaken with P; auto.
  Qed.

  Lemma valid_path_valid: forall (g : Gph) p, valid_path g p -> Forall (@vvalid _ _ g) p.
  Proof.
    induction p; intros; simpl in *. apply Forall_nil.
    destruct p; constructor; auto; destruct H as [[? ?] ?]; [| apply IHp]; auto.
  Qed.

  Lemma reachable_foot_valid: forall (g : Gph) n1 n2, reachable g n1 n2 -> @vvalid _ _ g n2.
  Proof.
    repeat intro. destruct H as [l [[? ?] [? ?]]]. apply foot_in in H0. apply valid_path_valid in H1.
    rewrite Forall_forall in H1. apply H1. auto.
  Qed.

  Lemma reachable_head_valid: forall (g : Gph) n1 n2, reachable g n1 n2 -> @vvalid _ _ g n1.
  Proof.
    repeat intro. destruct H as [l [[? ?] [? ?]]]. destruct l. inversion H. simpl in H. inversion H. subst. simpl in H1.
    destruct l. auto. destruct H1 as [[? _] _]. auto.
  Qed.

End GraphPath.