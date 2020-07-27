Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Logic.ProofIrrelevance.
Require Import CertiGraph.Coqlib.

Class PreGraph (Vertex: Type) Data {EV: EqDec Vertex} :=
  {
    valid : Vertex -> Prop;
    node_label : Vertex -> Data;
    edge_func : Vertex -> list Vertex
  }.

Class MathGraph {Vertex : Type} {Data} {EV: EqDec Vertex} (pg: PreGraph Vertex Data) (nV : Vertex):=
  {
    weak_valid: Vertex -> Prop := fun p => if t_eq_dec p nV then True else valid p;
    valid_graph: forall x, valid x -> forall y, In y (edge_func x) -> weak_valid y;
    valid_not_null: forall x, valid x -> x <> nV
  }.

Class BiGraph {Vertex Data: Type} {EV: EqDec Vertex} (pg : PreGraph Vertex Data):=
  {
    only_two_neighbours : forall v : Vertex, {v1 : Vertex & {v2 : Vertex | edge_func v = v1 :: v2 :: nil}}
  }.

Lemma weak_valid_spec: forall {Vertex Data EV Null} {pg: @PreGraph Vertex Data EV} {mag: MathGraph pg Null} p,
  {p = Null} + {valid p} -> weak_valid p.
Proof.
  intros.
  unfold weak_valid.
  destruct (t_eq_dec p Null); tauto.
Qed.

Lemma weak_valid_complete: forall {Vertex Data EV Null} {pg: @PreGraph Vertex Data EV} {mag: MathGraph pg Null} p,
  weak_valid p -> {p = Null} + {valid p}.
Proof.
  intros.
  unfold weak_valid in H.
  destruct (t_eq_dec p Null); tauto.
Qed.

(*
Class BiMathGraph {Vertex Data : Type} {EV: EqDec Vertex} (pg : PreGraph Vertex Data)(nV : Vertex):=
  {
    bm_bi :> BiGraph pg;
    bm_ma :> MathGraph pg nV
  }.

Coercion bm_bi : BiMathGraph >-> BiGraph.

Coercion bm_ma : BiMathGraph >-> MathGraph.
*)

Definition biEdge {Vertex Data} {EV: EqDec Vertex} {PG : PreGraph Vertex Data} (BG: BiGraph PG) (v: Vertex) : Vertex * Vertex.
  specialize (only_two_neighbours v); intro.
  destruct X as [v1 [v2 ?]].
  apply (v1, v2).
Defined.

Lemma biEdge_only2 {Vertex Data} {EV: EqDec Vertex} {PG : PreGraph Vertex Data} (BG: BiGraph PG) :
  forall v v1 v2 n, biEdge BG v = (v1 ,v2) -> In n (edge_func v) -> n = v1 \/ n = v2.
Proof.
  intros; unfold biEdge in H.
  revert H; case_eq (only_two_neighbours v); intro x1; intros.
  revert H1; case_eq s; intro x2; intros. inversion H2. subst.
  rewrite e in *. clear -H0. apply in_inv in H0. destruct H0. left; auto.
  right. apply in_inv in H. destruct H; auto. apply in_nil in H. exfalso; trivial.
Qed.

Definition structurally_identical {V D1 D2 : Type} {EV: EqDec V}
           (G1 : @PreGraph V D1 EV) (G2 : @PreGraph V D2 EV) : Prop :=
  forall v : V, (@valid V D1 EV G1 v <-> @valid V D2 EV G2 v) /\
                (@edge_func V D1 EV G1 v) = (@edge_func V D2 EV G2 v).

Notation "g1 '~=~' g2" := (structurally_identical g1 g2) (at level 1).

Lemma si_refl: forall (V D : Type) (EV : EqDec V) (G : PreGraph V D), G ~=~ G.
Proof. intros; intro; split; reflexivity. Qed.

Lemma si_sym: forall (V D1 D2 : Type) (EV: EqDec V) (G1 : @PreGraph V D1 EV)
                     (G2 : @PreGraph V D2 EV), G1 ~=~ G2 -> G2 ~=~ G1.
Proof. intros; intro; specialize (H v); destruct H; split; [split; intuition | destruct H0; split; auto]. Qed.

Lemma si_trans: forall {V D1 D2 D3 : Type} {EV : EqDec V} {G1 : @PreGraph V D1 EV}
                       {G2 : @PreGraph V D2 EV} {G3 : @PreGraph V D3 EV}, G1 ~=~ G2 -> G2 ~=~ G3 -> G1 ~=~ G3.
Proof.
  intros; intro; specialize (H v); specialize (H0 v); destruct H, H0; split;
  [intuition | transitivity (@edge_func V D2 EV G2 v); trivial].
Qed.

Add Parametric Relation {V D : Type} {EV : EqDec V} : (PreGraph V D) structurally_identical
    reflexivity proved by (si_refl V D EV)
    symmetry proved by (si_sym V D D EV)
    transitivity proved by (@si_trans V D D D EV) as si_equal.

Definition edge {V D : Type} {EV : EqDec V} (G : PreGraph V D) (n n' : V) : Prop :=
  valid n /\ valid n' /\ In n' (edge_func n).

Notation " g |= n1 ~> n2 " := (edge g n1 n2) (at level 1).

Lemma edge_si {V D1 D2 : Type} {EV: EqDec V} :
  forall (g1 : @PreGraph V D1 EV) (g2 : @PreGraph V D2 EV) (n n' : V), g1 ~=~ g2 -> g1 |= n ~> n' -> g2 |= n ~> n'.
Proof.
  intros; hnf in *; generalize (H n); intro; specialize (H n'); destruct H, H1; clear H2; destruct H0 as [? [? ?]];
  destruct H3; split; intuition.
Qed.

Fixpoint valid_path {A D : Type} {EV: EqDec A} (g: PreGraph A D) (p : list A) : Prop :=
  match p with
    | nil => True
    | n :: nil => valid n
    | n1 :: ((n2 :: _) as p') => g |= n1 ~> n2 /\ valid_path g p'
  end.

Definition graph_is_acyclic {A D : Type} {EV: EqDec A} (g: PreGraph A D) : Prop :=
  forall p : list A, valid_path g p -> NoDup p.

Definition node_prop {A D : Type} {EV: EqDec A} (g: PreGraph A D) (P : Ensemble D) : Ensemble A :=
  fun n => P (node_label n).

Definition path_prop {A D : Type} {EV: EqDec A} (g: PreGraph A D) (P : Ensemble D) : (list A -> Prop) :=
  fun p => forall n, In n p -> node_prop g P n.

Definition good_path {A D : Type} {EV: EqDec A} (g: PreGraph A D) (P : Ensemble D) : (list A -> Prop) :=
    fun p => valid_path g p /\ path_prop g P p.

Definition path_endpoints {N} (p : list N) (n1 n2 : N) : Prop := head p = Some n1 /\ foot p = Some n2.

Definition reachable_by_path {A D : Type} {EV: EqDec A} (g: PreGraph A D) (p : list A)
           (n : A) (P : Ensemble D) : Ensemble A := fun n' => path_endpoints p n n' /\ good_path g P p.
Notation " g '|=' p 'is' n1 '~o~>' n2 'satisfying' P" := (reachable_by_path g p n1 P n2) (at level 1).

Definition reachable_by {A D : Type} {EV: EqDec A} (g: PreGraph A D) (n : A) (P : Ensemble D) : Ensemble A :=
  fun n' => exists p, g |= p is n ~o~> n' satisfying P.
Notation " g '|=' n1 '~o~>' n2 'satisfying' P " := (reachable_by g n1 P n2) (at level 1).

Definition reachable_by_acyclic {A D : Type} {EV: EqDec A}
           (g: PreGraph A D) (n : A) (P : Ensemble D) : Ensemble A :=
  fun n' => exists p, NoDup p /\ g |= p is n ~o~> n' satisfying P.
Notation " g '|=' n1 '~~>' n2 'satisfying' P " := (reachable_by_acyclic g n1 P n2) (at level 1).

Definition reachable {A D : Type} {EV: EqDec A} (g: PreGraph A D) (n : A) : Ensemble A:=
  reachable_by g n (fun _ => True).

Lemma reachable_by_is_reachable {A D : Type} {EV: EqDec A} (g: PreGraph A D):
  forall n1 n2 P, g |= n1 ~o~> n2 satisfying P -> reachable g n1 n2.
Proof.
  intros. unfold reachable. destruct H as [l [? [? ?]]]. exists l.
  split; auto. split. auto. hnf. intros. hnf. auto.
Qed.

Lemma reachable_by_path_is_reachable_by {A D : Type} {EV: EqDec A} (g: PreGraph A D):
  forall p n1 n2 P, g |= p is n1 ~o~> n2 satisfying P -> g |= n1 ~o~> n2 satisfying P.
Proof. intros. exists p; auto. Qed.

Lemma reachable_by_path_is_reachable {A D : Type} {EV: EqDec A} (g: PreGraph A D):
  forall p n1 n2 P, g |= p is n1 ~o~> n2 satisfying P -> reachable g n1 n2.
Proof. intros. apply reachable_by_path_is_reachable_by in H. apply reachable_by_is_reachable with P. auto. Qed.

Definition reachable_through_set {A D : Type} {EV: EqDec A} (g: PreGraph A D) (S : list A) : Ensemble A:=
  fun n => exists s, In s S /\ reachable g s n.

Lemma reachable_Same_set {A D : Type} {EV: EqDec A} (g: PreGraph A D) (S1 S2 : list A):
  S1 ~= S2 -> Same_set (reachable_through_set g S1) (reachable_through_set g S2).
Proof. intros; destruct H; split; repeat intro; destruct H1 as [y [HIn Hrch]]; exists y; split; auto. Qed.

Definition reachable_valid {A D : Type} {EV: EqDec A} (g: PreGraph A D) (S : list A) : A -> Prop :=
  fun n => @valid _ _ _ _ n /\ reachable_through_set g S n.

Definition reachable_subgraph {A D : Type} {EV: EqDec A} (g: PreGraph A D) (S : list A) :=
  Build_PreGraph A D EV (reachable_valid g S) node_label edge_func.

Definition unreachable_valid {A D : Type} {EV: EqDec A} (g: PreGraph A D) (S : list A) : A -> Prop :=
  fun n => @valid _ _ _ _ n /\ ~ reachable_through_set g S n.

Definition unreachable_subgraph {A D : Type} {EV: EqDec A} (g: PreGraph A D) (S : list A) :=
  Build_PreGraph A D EV (unreachable_valid g S) node_label edge_func.

Definition validly_identical {V D: Type} {EV: EqDec V} (G1 G2: @PreGraph V D EV) : Prop :=
  (forall v : V, @valid V D EV G1 v <-> @valid V D EV G2 v) /\
  (forall v : V, @valid V D EV G1 v -> @node_label V D EV G1 v = @node_label V D EV G2 v) /\
  (forall v : V, @valid V D EV G1 v -> @edge_func V D EV G1 v = @edge_func V D EV G2 v).

Notation "g1 '-=-' g2" := (validly_identical g1 g2) (at level 1).

Lemma vi_refl: forall {V D : Type} {EV : EqDec V} (G : PreGraph V D), G -=- G.
Proof. intros; split; [| split]; intros; intuition. Qed.

Lemma vi_sym: forall {V D : Type} {EV: EqDec V} (G1 G2 : PreGraph V D), G1 -=- G2 -> G2 -=- G1.
Proof.
  intros; split; [| split]; intros; destruct H as [? [? ?]];
  [rewrite <- H  | rewrite <- H in H0; rewrite <- (H1 v H0) | rewrite <- H in H0; rewrite <- (H2 v H0)]; intuition.
Qed.

Lemma vi_trans: forall {V D : Type} {EV : EqDec V} (G1 G2 G3 : PreGraph V D), G1 -=- G2 -> G2 -=- G3 -> G1 -=- G3.
Proof.
  intros; split; [| split]; intros; destruct H as [? [? ?]]; destruct H0 as [? [? ?]]. rewrite H; rewrite <- H0. intuition.
  rewrite (H2 v H1); rewrite H in H1; apply H4; auto. rewrite (H3 v H1); rewrite H in H1; apply H5; auto.
Qed.

Add Parametric Relation {V D : Type} {EV : EqDec V} : (PreGraph V D) validly_identical
    reflexivity proved by vi_refl
    symmetry proved by vi_sym
    transitivity proved by vi_trans as vi_equal.

Section GraphPath.
  Variable N : Type.
  Variable D : Type.
  Variable EDN : EqDec N.
  Let Gph := @PreGraph N D EDN.

  Definition path : Type := list N.
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
    change (n0 :: p1) with (tail (a :: n0 :: p1)). apply valid_path_tail; auto.
  Qed.

  Lemma valid_path_si {V D1 D2 : Type} {EV: EqDec V}:
    forall (g1 : @PreGraph V D1 EV) (g2 : @PreGraph V D2 EV),
      structurally_identical g1 g2 -> forall p, valid_path g1 p -> valid_path g2 p.
  Proof.
    induction p; simpl; auto.
    icase p.
    intro; destruct (H a); rewrite <- H1; auto.
    intros [? ?]. split; auto.
    apply (edge_si g1 g2 a v H H0).
  Qed.

  Lemma valid_path_acyclic:
    forall (g : Gph) (p : path) n1 n2,
      path_endpoints p n1 n2 -> valid_path g p ->
      exists p', Sublist p' p /\ path_endpoints p' n1 n2 /\ NoDup p' /\ valid_path g p'.
  Proof.
    intros until p. remember (length p). assert (length p <= n) by omega. clear Heqn. revert p H. induction n; intros.
    icase p; icase H0. inv H0. inv H. destruct (nodup_dec p) as [? | H2]. exists p. split. reflexivity. tauto.
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

  Lemma node_prop_label_eq: forall g1 g2 n P,
    @node_label _ D _ g1 n = @node_label _ _ _ g2 n -> node_prop g1 P n -> node_prop g2 P n.
  Proof. intros; hnf in *; rewrite <- H; trivial.  Qed.

  Lemma node_prop_weaken: forall g (P1 P2 : Ensemble D) n, (forall d, P1 d -> P2 d) -> node_prop g P1 n -> node_prop g P2 n.
  Proof. intros; hnf in *; auto. Qed.

  Lemma path_prop_weaken: forall g (P1 P2 : Ensemble D) p,
    (forall d, P1 d -> P2 d) -> path_prop g P1 p -> path_prop g P2 p.
  Proof. intros; hnf in *; intros; hnf in *; apply H; apply H0; auto. Qed.

  Lemma path_prop_sublist: forall (g: Gph) P p1 p2, Sublist p1 p2 -> path_prop g P p2 -> path_prop g P p1.
  Proof. repeat intro; apply H0; apply H; trivial. Qed.

  Lemma path_prop_tail: forall (g: Gph) P n p, path_prop g P (n :: p) -> path_prop g P p.
  Proof. repeat intro; specialize (H n0); apply H; apply in_cons; trivial. Qed.

  Lemma good_path_split: forall (g: Gph) p1 p2 P, good_path g P (p1 ++ p2) -> (good_path g P p1) /\ (good_path g P p2).
  Proof.
    intros. destruct H. apply valid_path_split in H. destruct H. unfold good_path. unfold path_prop in *. intuition.
  Qed.

  Lemma good_path_merge: forall (g: Gph) p1 p2 P,
                           paths_meet p1 p2 -> good_path g P p1 -> good_path g P p2 -> good_path g P (p1 +++ p2).
  Proof.
    intros. destruct H0. destruct H1. split. apply valid_path_merge; auto. unfold path_prop in *. intros.
    unfold path_glue in H4. apply in_app_or in H4. destruct H4. auto. apply H3. apply In_tail; auto.
  Qed.

  Lemma good_path_weaken: forall (g: Gph) p (P1 P2 : Ensemble D),
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

  Lemma reachable_by_path_In_prop: forall (g: Gph) p n1 n2 P n,
    g |= p is n1 ~o~> n2 satisfying P -> In n p -> node_prop g P n.
  Proof. intros. destruct H as [_ [_ ?]]. apply H. trivial. Qed.

  Lemma reachable_by_reflexive: forall (g : Gph) n P, @valid _ _ _ g n /\ node_prop g P n -> g |= n ~o~> n satisfying P.
  Proof.
    intros.
    exists (n :: nil). split. compute. auto.
    split. simpl. trivial. destruct H; auto.
    intros ? ?. icase H0. subst n0. destruct H; trivial.
  Qed.

  Lemma reachable_by_merge: forall (g: Gph) n1 n2 n3 P,
    g |= n1 ~o~> n2 satisfying P ->
    g |= n2 ~o~> n3 satisfying P ->
    g |= n1 ~o~> n3 satisfying P.
  Proof. do 2 destruct 1. exists (x +++ x0). apply reachable_by_path_merge with n2; auto. Qed.

  Lemma reachable_by_head_prop: forall (g: Gph) n1 n2 P, g |= n1 ~o~> n2 satisfying P -> node_prop g P n1.
  Proof.
    intros. destruct H as [p ?]. eapply reachable_by_path_In_prop; eauto.
    apply reachable_by_path_head in H. icase p. inv H. simpl. auto.
  Qed.

  Lemma reachable_by_foot_prop: forall (g: Gph) n1 n2 P, g |= n1 ~o~> n2 satisfying P -> node_prop g P n2.
  Proof.
    intros. destruct H as [p ?]. eapply reachable_by_path_In_prop; eauto.
    apply reachable_by_path_foot in H. apply foot_in. trivial.
  Qed.

  Lemma reachable_by_cons:
    forall (g: Gph) n1 n2 n3 P, g |= n1 ~> n2 -> node_prop g P n1 ->
                                g |= n2 ~o~> n3 satisfying P ->
                                g |= n1 ~o~> n3 satisfying P.
  Proof.
    intros. apply reachable_by_merge with n2; auto.
    apply reachable_by_head_prop in H1.
    exists (n1 :: n2 :: nil). split. split; auto.
    split. simpl. split; auto. destruct H as [? [? ?]]. auto.
    intros n ?. simpl in H2.
    icase H2. subst; trivial.
    icase H2. subst; trivial.
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

  Lemma valid_path_valid: forall (g : Gph) p, valid_path g p -> Forall (@valid _ _ _ g) p.
  Proof.
    induction p; intros; simpl in *. apply Forall_nil.
    destruct p; constructor; auto; destruct H as [[? ?] ?]; [| apply IHp]; auto.
  Qed.

  Lemma reachable_foot_valid: forall (g : Gph) n1 n2, reachable g n1 n2 -> @valid _ _ _ g n2.
  Proof.
    repeat intro. destruct H as [l [[? ?] [? ?]]]. apply foot_in in H0. apply valid_path_valid in H1.
    rewrite Forall_forall in H1. apply H1. auto.
  Qed.

  Lemma reachable_head_valid: forall (g : Gph) n1 n2, reachable g n1 n2 -> @valid _ _ _ g n1.
  Proof.
    repeat intro. destruct H as [l [[? ?] [? ?]]]. destruct l. inversion H. simpl in H. inversion H. subst. simpl in H1.
    destruct l. auto. destruct H1 as [[? _] _]. auto.
  Qed.

  (* START OF MARK *)
  Variable marked : Ensemble D.
  Definition unmarked (d : D) : Prop := ~ marked d.

  Definition mark1 (g1 : Gph) (n : N) (g2 : Gph) : Prop :=
    structurally_identical g1 g2 /\ @valid _ _ _ g1 n /\ node_prop g2 marked n /\
    forall n', n <> n' -> @node_label _ _ _ g1 n' = @node_label _ _ _ g2 n'.

  Lemma mark1_marked: forall g1 root g2,
                        mark1 g1 root g2 ->
                        forall n, node_prop g1 marked n-> node_prop g2 marked n.
  Proof.
    intros. destruct H as [? [? [? ?]]].
    destruct (t_eq_dec root n).
    subst. auto. specialize (H3 n n0). hnf in *. rewrite <- H3. auto.
  Qed.

  (* The first subtle lemma *)
  Lemma mark1_unmarked : forall g1 root g2 n,
    mark1 g1 root g2 ->
    g1 |= root ~o~> n satisfying unmarked -> n = root \/ exists child, edge g1 root child /\
                                                                       g2 |= child ~o~> n satisfying unmarked.
  Proof.
    intros.
    (* Captain Hammer *)
    rewrite reachable_acyclic in H0.
    destruct H0 as [p [? ?]].
    icase p. exfalso. eapply reachable_by_path_nil; eauto.
    assert (n0 = root) by (apply reachable_by_path_head in H1; inv H1; trivial). subst n0.
    icase p. apply reachable_by_path_foot in H1. inv H1; auto.
    right. exists n0.
    change (root :: n0 :: p) with ((root :: n0 :: nil) +++ (n0 :: p)) in H1.
    apply reachable_by_path_split_glue with (n := n0) in H1. 2: red; auto. destruct H1.
    split. destruct H1 as [_ [? _]]. apply valid_path_si with (g4 := g2) in H1. 2: destruct H; trivial.
    simpl in H1. destruct H. apply si_sym in H. apply edge_si with g2; tauto.
    exists (n0 :: p). destruct H2 as [? [? ?]].
    split; trivial.
    destruct H as [? [_ ?]]. split. eapply valid_path_si; eauto.
    intros ? ?. specialize (H4 n1 H6).
    (* Hammertime! *)
    assert (root <> n1). intro. inversion H0. subst. contr.
    destruct H5.
    specialize (H8 n1 H7). eapply node_prop_label_eq; eauto.
  Qed.

  (* Not the best name in the world... *)
  Lemma mark1_reverse_unmark: forall g1 root g2,
    mark1 g1 root g2 ->
    forall n1 n2,
      g2 |= n1 ~o~> n2 satisfying unmarked ->
      g1 |= n1 ~o~> n2 satisfying unmarked.
  Proof.
    intros. destruct H0 as [p [? ?]]. exists p. split; trivial.
    destruct H1. destruct H as [? [? ?]].
    split. eapply valid_path_si; eauto. apply si_sym; trivial. (* clear -H3 H0 H2. *)
    intros ? ?. specialize (H2 n H5). destruct H4. specialize (H6 n).
    spec H6. intro. subst n. hnf in H3. hnf in H2. specialize (H2 H4). inv H2.
    apply node_prop_label_eq with g2; auto.
  Qed.

  Definition mark (g1 : Gph) (root : N) (g2 : Gph) : Prop :=
    structurally_identical g1 g2 /\
    (forall n,  g1 |= root ~o~> n satisfying unmarked -> node_prop g2 marked n) /\
    (forall n, ~g1 |= root ~o~> n satisfying unmarked -> @node_label _ _ _ g1 n = @node_label _ _ _ g2 n).

  (* Sanity condition 1 *)
  Lemma mark_reachable: forall g1 root g2, mark g1 root g2 -> Included (reachable g1 root) (reachable g2 root).
  Proof.
    repeat intro. destruct H as [? [? ?]].
    hnf in H0 |- *.
    destruct H0 as [p [? [? ?]]]; exists p. split; auto. split; auto. eapply valid_path_si; eauto.
  Qed.

  Require Import Classical.
  Tactic Notation "LEM" constr(v) := (destruct (classic v); auto).

  (* The second subtle lemma.  Maybe needs a better name? *)
  Lemma mark_unmarked: forall g1 root g2 n1 n2,
                         mark g1 root g2 -> g1 |= n1 ~o~> n2 satisfying unmarked ->
                         (g2 |= n1 ~o~> n2 satisfying unmarked) \/ (node_prop g2 marked n2).
  Proof.
    intros. destruct H0 as [p ?].
    (* This is a very handy LEM. *)
    LEM (exists n, In n p /\ g1 |= root ~o~> n satisfying unmarked).
    right. destruct H as [_ [? _]]. apply H.
    destruct H1 as [n [? ?]]. apply reachable_by_merge with n; trivial.
    destruct (reachable_by_path_split_in _ _ _ _ _ _ H0 H1) as [p1 [p2 [? [? ?]]]].
    exists p2. trivial.
    left. exists p. destruct H0. split; trivial. clear H0.
    destruct H2. destruct H as [? [_ ?]]. split. eapply valid_path_si; eauto.
    intros ? ?. specialize (H2 n H4). specialize (H3 n).
    spec H3. intro. apply H1. exists n. tauto.
    eapply node_prop_label_eq; eauto.
  Qed.

  Lemma mark_marked: forall g1 root g2,
                       mark g1 root g2 ->
                       forall n, node_prop g1 marked n-> node_prop g2 marked n.
  Proof.
    intros. destruct H as [_ [? ?]]. LEM (g1 |= root ~o~> n satisfying unmarked).
    specialize (H1 n H2). eapply node_prop_label_eq; eauto.
  Qed.

  (* Maybe a better name? *)
  Lemma mark_reverse_unmarked: forall g1 root g2,
                                 mark g1 root g2 ->
                                 forall n1 n2, g2 |= n1 ~o~> n2 satisfying unmarked -> g1 |= n1 ~o~> n2 satisfying unmarked.
  Proof.
    intros. destruct H0 as [p [? ?]]. exists p. split; trivial. clear H0.
    destruct H as [? [? ?]]. destruct H1.
    split. eapply valid_path_si; eauto. apply si_sym; trivial. clear -H3 H0 H2.
    intros ? ?. specialize (H3 n H). specialize (H0 n). specialize (H2 n).
    LEM (g1 |= root ~o~> n satisfying unmarked).
    specialize (H0 H1). clear H2 H1. exfalso.
    hnf in H3. hnf in H0. apply H3. auto.
    specialize (H2 H1). apply node_prop_label_eq with g2; auto.
  Qed.

  (* Here is where we specialize to bigraphs, at least at root *)
  Definition node_connected_two (g : Gph) (root left right : N) : Prop :=
    edge g root left /\ edge g root right /\ forall n', edge g root n' -> n' = left \/ n' = right.

  Lemma node_connected_two_eq:
    forall (g1 g2 : Gph) root l r, g1 ~=~ g2 -> node_connected_two g1 root l r -> node_connected_two g2 root l r.
  Proof.
    intros. destruct (H root). destruct H0 as [[? [? ?]] [[? [? ?]] ?]]. split. split. tauto. split. destruct (H l); tauto.
    rewrite <- H2. auto. split. split. tauto. split. destruct (H r); tauto. rewrite <- H2; auto. intros.
    destruct H9 as [? [? ?]]. assert (g1 |= root ~> n'). split. tauto. split. destruct (H n'). tauto. rewrite H2. auto.
    specialize (H8 n' H12). auto.
  Qed.

  Ltac break_unmark := match goal with
                              | [H1: mark1 ?g1 ?root _, H2: ?g1 |= ?root ~o~> _ satisfying unmarked |- _] =>
                                destruct (mark1_unmarked _ _ _ _ H1 H2)
                              | [H1: mark ?g1 _ _, H2: ?g1 |= _ ~o~> _ satisfying unmarked |- _] =>
                                destruct (mark_unmarked _ _ _ _ _ H1 H2)
                       end.

  Lemma root_neq: forall g1 g2 root n, mark1 g1 root g2 -> node_prop g1 unmarked root ->
                                       (~ g1 |= root ~o~> n satisfying unmarked) -> root <> n.
  Proof. repeat intro; subst; apply H1. apply reachable_by_reflexive; split; auto. destruct H as [? [? [? ?]]]; auto. Qed.

  Ltac structure_id_3 :=
    match goal with
      | [H1 : mark1 ?g1 _ ?g2, H2 : mark ?g2 _ ?g3, H3 : mark ?g3 _ ?g4 |- ?g1 ~=~ ?g4]
        => destruct H1, H2, H3; apply (si_trans H1); apply (si_trans H2); auto
      | [H1 : mark ?g1 _ ?g2, H2 : mark1 ?g2 _ ?g3, H3 : mark ?g3 _ ?g4 |- ?g1 ~=~ ?g4]
        => destruct H1, H2, H3; apply (si_trans H1); apply (si_trans H2); auto
      | [H1 : mark ?g1 _ ?g2, H2 : mark ?g2 _ ?g3, H3 : mark1 ?g3 _ ?g4 |- ?g1 ~=~ ?g4]
        => destruct H1, H2, H3; apply (si_trans H1); apply (si_trans H2); auto
    end.

  Ltac reverse_unmark :=
    match goal with
      | [H1 : mark1 ?g1 ?root ?g2, H2 : ?g2 |= _ ~o~> _ satisfying unmarked |- _]
        => apply (mark1_reverse_unmark g1 root _ H1) in H2
      | [H1 : mark ?g1 ?root ?g2, H2 : ?g2 |= _ ~o~> _ satisfying unmarked |- _]
        => apply (mark_reverse_unmarked g1 root _ H1) in H2
    end.

  Ltac node_mark :=
    match goal with
      | [H : mark1 _ _ ?g |- node_prop ?g marked _] => eapply mark1_marked; eauto
      | [H : mark _ _ ?g |- node_prop ?g marked _] => eapply mark_marked; eauto
    end.

  Lemma mark_root_left_right: forall g1 g2 g3 g4 root left right,
                                node_prop g1 unmarked root -> node_connected_two g1 root left right ->
                                mark1 g1 root g2 -> mark g2 left g3 -> mark g3 right g4 -> mark g1 root g4.
  Proof.
    split. structure_id_3. split; intros.
    break_unmark. subst. do 2 node_mark. hnf in H1. tauto. destruct H5 as [x [? ?]]. destruct H0 as [? [? ?]].
    apply H8 in H5. destruct H5; subst. node_mark. destruct H2 as [? [? ?]]. auto. clear H4; break_unmark.
    destruct H3 as [? [? ?]]. auto. node_mark. assert (root <> n) by (apply (root_neq g1 g2); auto).
    assert (~ g2 |= left ~o~> n satisfying unmarked). intro; apply H4. destruct H0. reverse_unmark.
    apply reachable_by_cons with left; auto. assert (~ g3 |= right ~o~> n satisfying unmarked). intro. apply H4.
    destruct H0 as [? [? ?]]. do 2 reverse_unmark. apply reachable_by_cons with right; auto. destruct H1 as [_ [_ [_ ?]]].
    rewrite H1; auto. destruct H2 as [_ [_ ?]]. rewrite H2; auto. destruct H3 as [_ [_ ?]]. rewrite H3; auto.
  Qed.

  Lemma mark_root_right_left: forall g1 g2 g3 g4 root left right,
                                node_prop g1 unmarked root -> node_connected_two g1 root left right ->
                                mark1 g1 root g2 -> mark g2 right g3 -> mark g3 left g4 -> mark g1 root g4.
  Proof.
    split. structure_id_3. split; intros.
    break_unmark. subst. do 2 node_mark. hnf in H1. tauto. destruct H5 as [x [? ?]]. destruct H0 as [? [? ?]].
    apply H8 in H5. destruct H5; subst. clear H4; break_unmark. destruct H3 as [? [? ?]]. auto. node_mark. node_mark.
    destruct H2 as [? [? ?]]. auto. assert (root <> n) by (apply (root_neq g1 g2); auto).
    assert (~ g2 |= right ~o~> n satisfying unmarked). intro; apply H4. destruct H0 as [? [? ?]]. reverse_unmark.
    apply reachable_by_cons with right; auto. assert (~ g3 |= left ~o~> n satisfying unmarked). intro. apply H4.
    destruct H0 as [? [? ?]]. do 2 reverse_unmark. apply reachable_by_cons with left; auto. destruct H1 as [_ [_ [_ ?]]].
    rewrite H1; auto. destruct H2 as [_ [_ ?]]. rewrite H2; auto. destruct H3 as [_ [_ ?]]. rewrite H3; auto.
  Qed.

  Lemma mark_left_right_root: forall g1 g2 g3 g4 root left right,
                                node_prop g1 unmarked root -> node_connected_two g1 root left right ->
                                mark g1 left g2 -> mark g2 right g3 -> mark1 g3 root g4 -> mark g1 root g4.
  Proof.
    intros. assert (g1 ~=~ g3). destruct H1, H2 as [? [? ?]]. apply (si_trans H1). auto.
    split. structure_id_3.
    split; intros. break_unmark. break_unmark. break_unmark. subst. destruct H3. tauto. destruct H8 as [? [? ?]].
    generalize (node_connected_two_eq _ _ _ _ _ H4 H0); intro. destruct H10 as [_ [_ ?]]. specialize (H10 x H8).
    destruct H10; subst. clear H5 H6 H7. do 3 reverse_unmark. destruct H1 as [? [? ?]]. specialize (H5 n H9).
    do 2 node_mark. do 2 reverse_unmark. destruct H2 as [? [? ?]]. specialize (H10 n H9). node_mark. node_mark. do 2 node_mark.
    assert (root <> n). intro. apply H5. subst. exists (n :: nil). split. split; simpl; auto. split. simpl. destruct (H4 n).
    rewrite H6. destruct H3. tauto. hnf. intros. apply in_inv in H6. destruct H6. subst; auto. apply in_nil in H6. tauto.
    destruct H3 as [_ [_ [_ ?]]]. rewrite <- H3; auto. clear H3 H6. assert (~ g2 |= right ~o~> n satisfying unmarked). intro.
    apply H5. reverse_unmark. apply reachable_by_cons with right; auto. destruct H0. tauto.
    destruct H2 as [_ [_ ?]]. rewrite <- H2; auto. clear H2 H3. assert (~ g1 |= left ~o~> n satisfying unmarked). intro.
    apply H5. apply reachable_by_cons with left; auto. destruct H0; auto. destruct H1 as [_ [_ ?]]. apply H1; auto.
  Qed.

  Lemma mark_right_left_root: forall g1 g2 g3 g4 root left right,
                                node_prop g1 unmarked root -> node_connected_two g1 root left right ->
                                mark g1 right g2 -> mark g2 left g3 -> mark1 g3 root g4 -> mark g1 root g4.
  Proof.
    intros. assert (g1 ~=~ g3). destruct H1, H2 as [? [? ?]]. apply (si_trans H1). auto.
    split. structure_id_3.
    split; intros. break_unmark. break_unmark. break_unmark. subst. destruct H3. tauto. destruct H8 as [? [? ?]].
    generalize (node_connected_two_eq _ _ _ _ _ H4 H0); intro. destruct H10 as [_ [_ ?]]. specialize (H10 x H8).
    destruct H10; subst. clear H5 H6 H7. reverse_unmark. reverse_unmark. destruct H2 as [? [? ?]]. specialize (H5 n H9).
    node_mark. do 3 reverse_unmark. destruct H1 as [? [? ?]]. specialize (H10 n H9). do 2 node_mark. node_mark. do 2 node_mark.
    assert (root <> n). intro. apply H5. subst. exists (n :: nil). split. split; simpl; auto. split. simpl. destruct (H4 n).
    rewrite H6. destruct H3. tauto. hnf. intros. apply in_inv in H6. destruct H6. subst; auto. apply in_nil in H6. tauto.
    destruct H3 as [_ [_ [_ ?]]]. rewrite <- H3; auto. clear H3 H6. assert (~ g2 |= left ~o~> n satisfying unmarked). intro.
    apply H5. reverse_unmark. apply reachable_by_cons with left; auto. destruct H0. auto.
    destruct H2 as [_ [_ ?]]. rewrite <- H2; auto. clear H2 H3. assert (~ g1 |= right ~o~> n satisfying unmarked). intro.
    apply H5. apply reachable_by_cons with right; auto. destruct H0; tauto. destruct H1 as [_ [_ ?]]. apply H1; auto.
  Qed.

  Lemma mark_left_root_right: forall g1 g2 g3 g4 root left right,
                                node_prop g1 unmarked root -> node_connected_two g1 root left right ->
                                mark g1 left g2 -> mark1 g2 root g3 -> mark g3 right g4 -> mark g1 root g4.
  Proof.
    intros. split. structure_id_3.
    split; intros. break_unmark. break_unmark. subst. destruct H2 as [_ [_ [? _]]]. apply (mark_marked g3 right); auto.
    destruct H6 as [? [? ?]]. assert (g1 ~=~ g2). destruct H1; auto. generalize (node_connected_two_eq _ _ _ _ _ H8 H0); intro.
    destruct H9 as [_ [_ ?]]. specialize (H9 x H6). destruct H9; subst. do 2 reverse_unmark. destruct H1 as [? [? ?]].
    specialize (H9 n H7). do 2 node_mark. destruct H3 as [? [? ?]]. specialize (H9 n H7). auto. do 2 node_mark.

    assert (~ g3 |= right ~o~> n satisfying unmarked). intro. apply H4. do 2 reverse_unmark.
    apply reachable_by_cons with right; auto. destruct H0. tauto. destruct H3 as [_ [_ ?]]. rewrite <- H3; auto. clear H3 H5.

    assert (root <> n). intro. apply H4. subst. exists (n :: nil). split. split; simpl; auto. split. simpl.
    destruct H1. destruct (H1 n). rewrite H5. destruct H2. tauto. hnf. intros. apply in_inv in H3. destruct H3. subst; auto.
    apply in_nil in H3. tauto. destruct H2 as [_ [_ [_ ?]]]. rewrite <- H2; auto. clear H2 H3.

    assert (~ g1 |= left ~o~> n satisfying unmarked). intro. apply H4. apply reachable_by_cons with left; auto.
    destruct H0; auto. destruct H1 as [_ [_ ?]]. apply H1; auto.
  Qed.

  Lemma mark_right_root_left: forall g1 g2 g3 g4 root left right,
                                node_prop g1 unmarked root -> node_connected_two g1 root left right ->
                                mark g1 right g2 -> mark1 g2 root g3 -> mark g3 left g4 -> mark g1 root g4.
  Proof.
    intros. split. structure_id_3.
    split; intros. break_unmark. break_unmark. subst. destruct H2 as [_ [_ [? _]]]. apply (mark_marked g3 left); auto.
    destruct H6 as [? [? ?]]. assert (g1 ~=~ g2). destruct H1; auto. generalize (node_connected_two_eq _ _ _ _ _ H8 H0); intro.
    destruct H9 as [_ [_ ?]]. specialize (H9 x H6). destruct H9; subst. destruct H3 as [? [? ?]]. apply H9; auto.
    do 2 reverse_unmark. destruct H1 as [? [? ?]]. specialize (H9 n H7). do 2 node_mark. do 2 node_mark.

    assert (~ g3 |= left ~o~> n satisfying unmarked). intro. apply H4. do 2 reverse_unmark.
    apply reachable_by_cons with left; auto. destruct H0. tauto. destruct H3 as [_ [_ ?]]. rewrite <- H3; auto. clear H3 H5.

    assert (root <> n). intro. apply H4. subst. exists (n :: nil). split. split; simpl; auto. split. simpl.
    destruct H1. destruct (H1 n). rewrite H5. destruct H2. tauto. hnf. intros. apply in_inv in H3. destruct H3. subst; auto.
    apply in_nil in H3. tauto. destruct H2 as [_ [_ [_ ?]]]. rewrite <- H2; auto. clear H2 H3.

    assert (~ g1 |= right ~o~> n satisfying unmarked). intro. apply H4. apply reachable_by_cons with right; auto.
    destruct H0 as [? [? ?]]; auto. destruct H1 as [_ [_ ?]]. apply H1; auto.
  Qed.

  Lemma mark_unreachable: forall g1 root g2,
    mark g1 root g2 ->
    forall n, ~ (reachable g1 root n) -> @node_label _ _ _ g1 n = @node_label _ _ _ g2 n.
  Proof.
    intros. destruct H as [? [? ?]].
    apply H2.
    intro. apply H0.
    generalize (reachable_by_subset_reachable g1 root unmarked n); intro.
    intuition.
  Qed.

  Lemma si_reachable: forall (g1 g2: Gph) n,  g1 ~=~ g2 -> Included (reachable g1 n) (reachable g2 n).
  Proof.
    intros. intro t. intros. destruct H0 as [p ?]. destruct H0. exists p. split. auto. destruct H1. split. clear - H H1.
    induction p. simpl. auto. simpl. simpl in H1. destruct p. destruct (H a). rewrite <- H0. auto. destruct H1. split.
    destruct H0 as [? [? ?]]. split. destruct (H a). rewrite <- H4. auto. split. destruct (H n). rewrite <- H4. auto.
    destruct (H a). rewrite <- H5. auto. apply IHp. auto. repeat intro; hnf; auto.
  Qed.

  Lemma mark_unreachable_subgraph:
    forall g1 root g2, mark g1 root g2 -> (unreachable_subgraph g1 (root :: nil)) -=- (unreachable_subgraph g2 (root :: nil)).
  Proof.
    intros. generalize H; intro. split; [|split]; intros; destruct H as [? [? ?]]; specialize (H v); destruct H. simpl.
    unfold unreachable_valid. split; intros; destruct H4; split. rewrite <- H. apply H4. intro; apply H5; clear H5.
    unfold reachable_through_set in *. destruct H6 as [s [? ?]]. exists s. split; auto. apply in_inv in H5. destruct H5. subst.
    destruct H0 as [? _]. apply si_sym in H0. apply (si_reachable _ _ s H0). auto. inversion H5. rewrite H. auto.
    intro; apply H5; clear H5. destruct H6 as [s [? ?]]. exists s. split; auto. apply in_inv in H5. destruct H5. subst.
    destruct H0 as [? _]. apply (si_reachable _ _ s H0). auto. inversion H5. simpl in H1. hnf in H1. destruct H1.
    assert (~ (reachable g1 root v)). intro; apply H5; clear H5. exists root. split. apply in_eq. auto.
    apply (mark_unreachable _ _ _ H0 v H6). auto.
  Qed.

End GraphPath.

Lemma reachable_through_empty {A D : Type} {EV: EqDec A} (g: PreGraph A D):
  Same_set (reachable_through_set g nil) (Empty_set A).
Proof.
  split; repeat intro.
  destruct H; destruct H; apply in_nil in H; tauto.
  hnf in H; tauto.
Qed.

Lemma reachable_is_valid {A D : Type} {EV: EqDec A} (g: PreGraph A D):
  forall a x, reachable g x a -> valid x.
Proof.
  intros. destruct H as [l [? [? ?]]].
  destruct l. destruct H; discriminate H.
  destruct H; inversion H; rewrite H4 in *; clear H4 H2 a0;
  simpl in H0; destruct l; trivial; destruct H0 as [[? _] _]; trivial.
Qed.

Definition well_defined_list {A D} {EV : EqDec A} {null : A} {PG : PreGraph A D} (mg : MathGraph PG null) (l : list A) :=
  forall x, In x l -> x = null \/ valid x.

Tactic Notation "LEM" constr(v) := (destruct (classic v); auto).

Lemma reachable_through_empty_eq {A D : Type} {EV: EqDec A} (g: PreGraph A D):
  forall S, Same_set (reachable_through_set g S) (Empty_set A) <-> S = nil \/ forall y, In y S -> ~ valid y.
Proof.
  intros; split.
  induction S; intros. left; trivial. right; intros; LEM (valid a).
  destruct H. specialize (H a). spec H. unfold Ensembles.In . exists a; split; [apply in_eq | apply reachable_by_reflexive; split;[|hnf]; trivial]; inversion H.
  inversion H.
  destruct (in_inv H0). rewrite H2 in H1; trivial.
  assert (Same_set (reachable_through_set g (a :: S)) (reachable_through_set g S)).
  split; intro x; intro; destruct H3 as [s [? ?]]. destruct (in_inv H3). rewrite H5 in *; clear H5 a.
  apply reachable_is_valid in H4; tauto. exists s; split; trivial.
  exists s; split; trivial; apply in_cons; trivial. rewrite <- H3 in IHS. destruct (IHS H).
  rewrite H4 in *; inversion H0. rewrite H5 in H1. trivial. inversion H5. apply H4; trivial.

  intros; destruct H. rewrite H. apply reachable_through_empty. split; repeat intro.
  destruct H0 as [y [? ?]]. apply H in H0. apply reachable_is_valid in H1; tauto. hnf in H0; tauto.
Qed.

Definition change_valid {A D: Type} {EV: EqDec A} (g: PreGraph A D) (v: A): A -> Prop :=
  fun n => valid n \/ n = v.

Definition change_node_label {A D: Type} {EV: EqDec A} (g: PreGraph A D) (v: A) (d: D): A -> D :=
  fun n => if t_eq_dec n v then d else node_label n.

Definition change_edge_func {A D: Type} {EV: EqDec A} (g: PreGraph A D) (v l r: A): A -> list A :=
  fun n => if t_eq_dec n v then (l:: r:: nil) else edge_func n.

Definition update_PreGraph {A D: Type} {EV: EqDec A} (g: PreGraph A D) v d l r :=
  Build_PreGraph A D EV (change_valid g v) (change_node_label g v d) (change_edge_func g v l r).

Definition update_BiGraph {A D: Type} {EV: EqDec A} {PG : PreGraph A D} (g: BiGraph PG) (v: A) (d: D) (l r: A): BiGraph (update_PreGraph PG v d l r).
  refine (Build_BiGraph A D EV _ _).
  intro n. destruct (t_eq_dec n v). exists l, r. subst. simpl. unfold change_edge_func. destruct (t_eq_dec v v).
  auto. exfalso. auto. destruct (only_two_neighbours n) as [vv1 [vv2 ?]]. exists vv1, vv2. simpl. unfold change_edge_func.
  destruct (t_eq_dec n v). exfalso; auto. auto.
Defined.

Definition in_math {A D: Type} {nV: A} {EV: EqDec A} {PG : PreGraph A D} (g: MathGraph PG nV) (v: A) (l r: A) : Type :=
  forall e, In e (l :: r :: nil) -> {valid e} + {e = v} + {e = nV}.

Definition update_MathGraph {A D: Type} {nV: A} {EV: EqDec A} {PG : PreGraph A D} (g: MathGraph PG nV)
           (v: A) (d: D) (l r: A) (Hi: in_math g v l r) (Hn: v <> nV): MathGraph (update_PreGraph PG v d l r) nV.
  refine (Build_MathGraph A D EV _ nV _ _).
  intros. simpl in H0. unfold change_edge_func in H0. simpl in H; simpl. unfold change_valid in *. destruct (t_eq_dec x v).
  subst. specialize (Hi y H0). destruct Hi as [[? | ?] | ?]; destruct (t_eq_dec y nV); tauto.
  destruct H. apply (valid_graph x H y) in H0. apply weak_valid_complete in H0. destruct H0; destruct (t_eq_dec y nV); tauto.  destruct (t_eq_dec y nV); tauto.
  intros. simpl in H. unfold change_valid in H. destruct H; [apply valid_not_null | subst]; auto.
Defined.

(*
Definition update_graph {A D: Type} {nV: A} {EV: EqDec A} {PG : PreGraph A D} (g: BiMathGraph PG nV)
           (v: A) (d: D) (l r: A) (Hi: in_math bm_ma v l r) (Hn: v <> nV): BiMathGraph (update_PreGraph PG v d l r) nV
  := Build_BiMathGraph A D EV _ nV (update_BiGraph bm_bi v d l r) (update_MathGraph bm_ma v d l r Hi Hn).
*)

Definition single_PreGraph {A D: Type} (EV: EqDec A) (v : A) (d : D) (l r : A) : PreGraph A D :=
  Build_PreGraph A D EV (fun n => n = v) (fun n => d) (fun n => (l :: r :: nil)).

Definition single_BiGraph {A D: Type} (EV: EqDec A) (v: A) (d: D) (l r : A) : BiGraph (single_PreGraph EV v d l r).
  refine (Build_BiGraph A D EV _ _).
  intros. exists l, r. simpl. auto.
Defined.

Definition single_MathGraph_double {A D: Type} (nV: A) (EV: EqDec A) (v: A) (d: D) (Hn: v <> nV): MathGraph (single_PreGraph EV v d v v) nV.
  refine (Build_MathGraph A D EV _ nV _ _).
  intros. simpl in H. subst. simpl in H0. simpl.
  destruct (t_eq_dec y nV); [auto |]. destruct H0 as [? | [? | ?]]; try congruence; tauto.
  intros. simpl in H. subst. auto.
Defined.

Definition single_MathGraph_left {A D: Type} (nV: A) (EV: EqDec A) (v: A) (d: D) (Hn: v <> nV): MathGraph (single_PreGraph EV v d v nV) nV.
  refine (Build_MathGraph A D EV _ nV _ _).
  intros. simpl in H. subst. simpl in H0. simpl.
  destruct (t_eq_dec y nV); [auto | ].
  destruct H0 as [? | [? | ?]]; try congruence; tauto.
  intros. simpl in H. subst. auto.
Defined.

Definition single_MathGraph_right {A D: Type} (nV: A) (EV: EqDec A) (v: A) (d: D) (Hn: v <> nV): MathGraph (single_PreGraph EV v d nV v) nV.
  refine (Build_MathGraph A D EV _ nV _ _).
  intros. simpl in H. subst. simpl in H0. simpl.
  destruct (t_eq_dec y nV); [auto |].
  destruct H0 as [? | [? | ?]]; try congruence; tauto.
  intros. simpl in H. subst. auto.
Defined.
(*
Definition single_graph_double {A D: Type} (nV: A) (EV: EqDec A) (v: A) (d: D) (Hn: v <> nV): BiMathGraph (single_PreGraph EV v d v v) nV := Build_BiMathGraph A D EV _ nV (single_BiGraph EV v d v v) (single_MathGraph_double nV EV v d Hn).

Definition single_graph_left {A D: Type} (nV: A) (EV: EqDec A) (v: A) (d: D) (Hn: v <> nV): BiMathGraph (single_PreGraph EV v d v nV) nV := Build_BiMathGraph A D EV _ nV (single_BiGraph EV v d v nV) (single_MathGraph_left nV EV v d Hn).

Definition single_graph_right {A D: Type} (nV: A) (EV: EqDec A) (v: A) (d: D) (Hn: v <> nV): BiMathGraph (single_PreGraph EV v d nV v) nV := Build_BiMathGraph A D EV _ nV (single_BiGraph EV v d nV v) (single_MathGraph_right nV EV v d Hn).
*)

Definition gamma {Vertex Data} {EV: EqDec Vertex} {PG : PreGraph Vertex Data} (BG: BiGraph PG) (v: Vertex) : Data * Vertex * Vertex := let (v1, v2) := biEdge BG v in (node_label v, v1, v2).

Lemma update_bigraph_gamma {A D: Type} {EV: EqDec A} {PG : PreGraph A D}:
  forall (g: BiGraph PG) (v: A) (d: D) (l r: A), gamma (update_BiGraph g v d l r) v = (d, l, r).
Proof.
  intros. unfold gamma, biEdge. destruct (@only_two_neighbours A D EV _ (@update_BiGraph A D EV PG g v d l r) v) as [v1 [v2 ?]].
  simpl in *. unfold change_edge_func, change_node_label in *. destruct (t_eq_dec v v).
  + inversion e. subst; auto.
  + exfalso; auto.
Qed.

