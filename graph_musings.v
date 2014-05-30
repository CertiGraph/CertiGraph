(* Axioms *)

Require Import FunctionalExtensionality.
Require Import Classical.
Require Import Omega.
(** For compatibility with earlier developments, [extensionality]
  is an alias for [functional_extensionality]. *)

Lemma extensionality:
  forall (A B: Type) (f g : A -> B),  (forall x, f x = g x) -> f = g.
Proof. intros; apply functional_extensionality. auto. Qed.

Implicit Arguments extensionality.
Tactic Notation "extensionality" :=
 let x := fresh "x" in extensionality x.

Tactic Notation "extensionality" ident(x) ident(y) :=
    extensionality x; extensionality y.

Tactic Notation "extensionality" ident(x) ident(y) ident(z):=
    extensionality x; extensionality y z.
(* end Axioms *)

(* Tactics *)
(** Perform inversion on a hypothesis, removing it from the context, and
    perform substitutions
  *)
Tactic Notation "inv" hyp(H) := inversion H; clear H; subst.

Ltac detach H :=
  match goal with [ H : (?X -> ?Y) |- _ ] =>
    cut Y; [ clear H; intro H | apply H; clear H ]
  end.

(** Specialize a hypothesis with respect to specific terms or proofs. *)
Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ =>
    let H1 := fresh in (assert (H1: a); [|generalize (H H1); clear H H1; intro H]) end.

Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) :=
  (generalize (H a b); clear H; intro H).

 Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) :=
  (generalize (H a b c); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) :=
  (generalize (H a b c d); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) :=
  (generalize (H a b c d e); clear H; intro H).

(* Some further tactics, from Barrier Project *)

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) :=
  (generalize (H a b c d e f); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) :=
  (generalize (H a b c d e f g); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) :=
  (generalize (H a b c d e f g h); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) :=
  (generalize (H a b c d e f g h i); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) constr(m) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) constr(m) constr(n) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) constr(m) constr(n) constr(o) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) constr(m) constr(n) constr(o) constr(p) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "disc" := (try discriminate).

Tactic Notation "contr" := (try contradiction).

Tactic Notation "congr" := (try congruence).

Tactic Notation  "icase" constr(v) := (destruct v; disc; contr; auto).

Tactic Notation "omegac" := (elimtype False; omega).

Tactic Notation "copy" hyp(H) := (generalize H; intro).

Tactic Notation "LEM" constr(v) := (destruct (classic v); auto).
(* end Tactics *)

Set Implicit Arguments.

Require Import List.
Require Import Setoid.
Require Import Omega.

  Definition set (A : Type) : Type := A -> Prop.
  Definition subset {A} (S1 S2 : set A) : Prop :=
    forall a, S1 a -> S2 a.

  Notation "a '+::' b" := (a ++ (b :: nil)) (at level 19).
  Fixpoint foot {A} (L : list A) : option A :=
    match L with
     | nil => None
     | a :: nil => Some a
     | a :: L' => foot L'
    end.
  Lemma foot_simpl: forall A (a1 a2 : A) (L : list A),
    foot (a1 :: a2 :: L) = foot (a2 :: L).
  Proof. intros. simpl. destruct L; auto. Qed.
  Lemma foot_last: forall A (L : list A) (a : A),
    foot (L +:: a) = Some a.
  Proof. induction L; auto. icase L. Qed.
  Lemma foot_app: forall A (L1 L2 : list A),
    L2 <> nil ->
    foot (L1 ++ L2) = foot L2.
  Proof.
    induction L1. auto.
    intros.
    rewrite <- app_comm_cons. simpl.
    case_eq (L1 ++ L2). intro.
    apply app_eq_nil in H0. destruct H0. contradiction.
    intros. rewrite <- H0.
    apply IHL1. trivial.
  Qed.
  Lemma foot_explicit {A}: forall L (a : A),
    foot L = Some a ->
    exists L', L = L' +:: a.
  Proof.
    induction L. inversion 1.
    intros. simpl in H. icase L. inv H. exists nil. trivial.
    spec IHL a0 H. destruct IHL. exists (a :: x). rewrite <- app_comm_cons. congr.
  Qed.
  Lemma foot_in {A}: forall (a : A) L,
    foot L = Some a ->
    In a L.
  Proof.
    induction L. inversion 1.
    icase L. simpl. inversion 1. auto.
    rewrite foot_simpl. right. auto.
  Qed.

  Definition Dup {A} (L : list A) : Prop :=
    ~ NoDup L.
  Lemma Dup_unfold: forall A (a : A) (L : list A),
    Dup (a :: L) ->
    In a L \/ Dup L.
  Proof.
    intros.
    LEM (In a L).
    right.
    intro. apply H.
    constructor; auto.
  Qed.
  Lemma Dup_cyclic : forall A (L : list A),
    Dup L ->
    exists a, exists L1, exists L2, exists L3,
    L = L1 ++ (a :: L2) ++ (a :: L3).
  Proof.
    induction L.
    destruct 1. constructor.
    intros.
    apply Dup_unfold in H.
    destruct H.
    apply in_split in H.
    destruct H as [L1 [L2 ?]].
    exists a. exists nil. exists L1. exists L2.
    rewrite H. simpl. trivial.
    destruct (IHL H) as [a' [L1 [L2 [L3 ?]]]].
    rewrite H0.
    exists a'. exists (a :: L1). exists L2. exists L3. trivial.
  Qed.
  Definition sublist {A} (L1 L2 : list A) : Prop :=
    forall a, In a L1 -> In a L2.
  Lemma sublist_refl: forall A (L : list A),
    sublist L L.
  Proof.
    repeat intro; auto.
  Qed.
  Lemma sublist_trans: forall A (L1 L2 L3 : list A),
    sublist L1 L2 -> sublist L2 L3 -> sublist L1 L3.
  Proof.
    repeat intro.
    apply H0. apply H. trivial.
  Qed.
  Add Parametric Relation {A} : (list A) sublist
    reflexivity proved by (@sublist_refl A)
    transitivity proved by (@sublist_trans A)
    as sublist_rel.
  Lemma sublist_nil: forall A (L : list A),
    sublist nil L.
  Proof.
    repeat intro. inversion H.
  Qed.
  Lemma sublist_cons: forall A (a : A) L,
    sublist L (a :: L).
  Proof.
    repeat intro. simpl.
    auto.
  Qed.
  Lemma sublist_app: forall A (L1 L2 L3 L4: list A),
    sublist L1 L2 ->
    sublist L3 L4 ->
    sublist (L1 ++ L3) (L2 ++ L4).
  Proof.
    repeat intro.
    apply in_app_or in H1.
    apply in_or_app.
    destruct H1.
    left. apply H. trivial.
    right. apply H0. trivial.
  Qed.
  Lemma In_tail: forall A (a : A) L,
    In a (tl L) ->
    In a L.
  Proof.
    induction L; simpl; auto.
  Qed.

Record pregraph N E D L :=
  Pregraph
  { node_label : N -> option D
  ; edge_label : E -> option L
  ; edge_source : E -> N
  ; edge_dest : E -> N
  }.

Section mark.
  Variables N E D L:Type.

  Let gph := pregraph N E D L.

(* Rob: some, but by no means all, of what follows is similar to what you did. *)
  Definition structurally_identical (g g':gph) :=
    (edge_label g = edge_label g') /\
    (edge_source g = edge_source g') /\
    (edge_dest g = edge_dest g').
  Lemma structurally_identical_refl: reflexive _ structurally_identical.
  Proof.
    split; trivial. split; trivial.
  Qed.
  Lemma structurally_identical_sym: symmetric _ structurally_identical.
  Proof.
    split; destruct H as [? [? ?]]. congruence. split; congruence.
  Qed.
  Lemma structurally_identical_trans: transitive _ structurally_identical.
  Proof.
    split; destruct H as [? [? ?]]; destruct H0 as [? [? ?]]. congruence.
    split; congruence.
  Qed.
  Add Parametric Relation : gph structurally_identical
    reflexivity proved by structurally_identical_refl
    symmetry proved by structurally_identical_sym
    transitivity proved by structurally_identical_trans
    as structurally_identical_rel.

  Definition edge (g : gph) (n n' : N) : Prop :=
    exists l,
      edge_label g l <> None /\
      edge_source g l = n /\
      edge_dest g l = n'.
  Notation " g |= n1 ~> n2 " := (edge g n1 n2) (at level 1).
  Lemma edge_si: forall g1 g2 n n',
    structurally_identical g1 g2 ->
    edge g1 n n' ->
    edge g2 n n'.
  Proof.
    intros. destruct H0 as [l ?]. exists l.
    destruct H as [? [? ?]]. rewrite H, H1, H2 in H0.
    trivial.
  Qed.

  Definition path : Type := list N.
  Definition path_endpoints (p : path) (n1 n2 : N) : Prop :=
    head p = Some n1 /\ foot p = Some n2.
  Definition paths_meet_at (p1 p2 : path) : set N :=
    fun n => foot p1 = Some n /\ head p2 = Some n.
  Definition paths_meet (p1 p2 : path) : Prop :=
    exists n, paths_meet_at p1 p2 n.
  Lemma path_endpoints_meet: forall p1 p2 n1 n2 n3,
    path_endpoints p1 n1 n2 ->
    path_endpoints p2 n2 n3 ->
    paths_meet p1 p2.
  Proof.
    unfold path_endpoints, paths_meet; intros.
    destruct H, H0. exists n2. red. tauto.
  Qed.
  Lemma paths_foot_head_meet: forall p1 p2 n,
    paths_meet (p1 +:: n) (n :: p2).
  Proof. intros. exists n. split. apply foot_last. trivial. Qed.
  Definition path_glue (p1 p2 : path) : path :=
    p1 ++ (tail p2).
  Notation "p1 '+++' p2" := (path_glue p1 p2) (at level 20, left associativity).
  Lemma path_glue_nil_l: forall p,
    nil +++ p = tail p.
  Proof.
    unfold path_glue.  trivial.
  Qed.
  Lemma path_glue_nil_r: forall p,
    p +++ nil = p.
  Proof.
    unfold path_glue. simpl. intro. rewrite app_nil_r. trivial.
  Qed.
  Lemma path_glue_assoc: forall p1 p2 p3 : path,
    paths_meet p1 p2 ->
    paths_meet p2 p3 ->
    (p1 +++ p2) +++ p3 = p1 +++ (p2 +++ p3).
  Proof.
    unfold path_glue.
    induction p1; simpl; intros. icase H. icase H.
    icase p2. icase H. icase H. icase p3.
    do 2 rewrite app_nil_r. trivial.
    icase p2. simpl. rewrite app_nil_r. trivial. simpl.
    rewrite <- app_assoc. f_equal.
  Qed.
  Lemma path_glue_comm_cons: forall n p1 p2,
    (n :: p1 +++ p2) = ((n :: p1) +++ p2).
  Proof.
    unfold path_glue. intros. rewrite app_comm_cons. trivial.
  Qed.
  Lemma path_endpoints_glue: forall n1 n2 n3 p1 p2,
    path_endpoints p1 n1 n2 ->
    path_endpoints p2 n2 n3 ->
    path_endpoints (p1 +++ p2) n1 n3.
  Proof.
    split; destruct H, H0.
    icase p1. unfold path_glue.
    icase p2. icase p2. inv H0. inv H2. simpl. rewrite app_nil_r. trivial.
    rewrite foot_app; disc. apply H2.
  Qed.
(*
  Definition subpath (p1 p2 : path) : Prop :=
    sublist p1 p2 /\ exists n1, exists n2
*)

  (* A path is valid when there are edges going from one node to the next.
     This property is entirely about the edges: paths are allowed to go through
     invalid labels.  Empty and singleton paths are always valid. *)
  Fixpoint valid_path (g : gph) (p : path) {struct p} : Prop :=
    match p with
     | nil => True
     | n :: nil => True
     | n1 :: ((n2 :: _) as p') => g |= n1 ~> n2 /\ valid_path g p'
    end.
  Lemma valid_path_tail: forall g p,
    valid_path g p ->
    valid_path g (tail p).
  Proof.
    destruct p; auto.
    simpl. destruct p; auto.
    intros [? ?]; auto.
  Qed.
  Lemma valid_path_split: forall g p1 p2,
    valid_path g (p1 ++ p2) ->
    valid_path g p1 /\ valid_path g p2.
  Proof.
    induction p1. simpl. tauto.
    intros. rewrite <- app_comm_cons in H.
    simpl in H. revert H. case_eq (p1 ++ p2); intros.
    apply app_eq_nil in H. destruct H. subst. simpl. tauto.
    destruct H0. rewrite <- H in H1.
    apply IHp1 in H1. destruct H1.
    split; trivial.
    simpl. destruct p1; auto.
    rewrite <- app_comm_cons in H. inv H. tauto.
  Qed.
  Lemma valid_path_merge: forall g p1 p2,
    paths_meet p1 p2 ->
    valid_path g p1 ->
    valid_path g p2 ->
    valid_path g (p1 +++ p2).
  Proof.
    induction p1. simpl. intros. apply valid_path_tail. trivial.
    intros. rewrite <- path_glue_comm_cons.
    simpl.
    case_eq (p1 +++ p2); auto.
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
  (* There is probaby some fancy morphism way to register this... *)
  Lemma valid_path_si: forall g1 g2,
    structurally_identical g1 g2 ->
    forall p,
      valid_path g1 p ->
      valid_path g2 p.
  Proof.
    induction p; simpl; auto.
    icase p.
    intros [? ?]. split; auto.
    eapply edge_si; eauto.
  Qed.
  (* A big hammer... *)
  Lemma valid_path_acyclic: forall g p n1 n2,
    path_endpoints p n1 n2 ->
    valid_path g p ->
    exists p',
      sublist p' p /\
      path_endpoints p' n1 n2 /\
      NoDup p' /\
      valid_path g p'.
  Proof.
    intros until p.
    remember (length p).
    assert (length p <= n) by omega. clear Heqn.
    revert p H. induction n; intros.
    icase p; icase H0. inv H0. inv H.
    LEM (NoDup p).
    exists p. split. reflexivity. tauto.
    apply Dup_cyclic in H2.
    destruct H2 as [a [L1 [L2 [L3 ?]]]]. subst p.
    spec IHn (L1 ++ a :: L3).
    spec IHn.
      do 2 rewrite app_length in H.
      rewrite app_length. simpl in *. omega.
    spec IHn n1 n2.
    spec IHn.
      destruct H0.
      split. icase L1.
      repeat (rewrite foot_app in *; disc). trivial.
    spec IHn.
      change (L1 ++ a :: L3) with (L1 ++ (a :: nil) ++ tail (a :: L3)).
      rewrite app_assoc. change (a :: L2) with ((a :: nil) ++ L2) in H1.
      do 2 rewrite app_assoc in H1. apply valid_path_split in H1. destruct H1.
      apply valid_path_merge; auto. apply paths_foot_head_meet.
      apply valid_path_split in H1. tauto.
    destruct IHn as [p' [? [? [? ?]]]].
    exists p'. split. 2: tauto.
    transitivity (L1 ++ a :: L3); auto.
    apply sublist_app. reflexivity.
    pattern (a :: L3) at 1. rewrite <- (app_nil_l (a :: L3)).
    apply sublist_app. apply sublist_nil. reflexivity.
  Qed.

  (* If we have a path, we can assert that a certain property is true of
     each node on the path.  Note that here we assume every node on the
     path exists; this may or may not be the right choice.  We also only
     allow P to look at D, instead of N * D.  Again, this may not be the
     right choice. *)
  Definition node_prop (g : gph) (P : set D) : set N :=
    fun n => exists d, node_label g n = Some d /\ P d.
  Lemma node_prop_label_eq: forall g1 g2 n P,
    node_label g1 n = node_label g2 n ->
    node_prop g1 P n ->
    node_prop g2 P n.
  Proof. intros. destruct H0 as [l ?]. exists l. rewrite <- H. trivial. Qed.
  Lemma node_prop_weaken: forall g (P1 P2 : set D) n,
    (forall d, P1 d -> P2 d) ->
    node_prop g P1 n ->
    node_prop g P2 n.
  Proof. destruct 2 as [d [? ?]]. exists d. split; auto. Qed.

  Definition path_prop (g : gph) (P : set D) : set path :=
    fun p => forall n, In n p -> node_prop g P n.
  Lemma path_prop_weaken: forall g (P1 P2 : set D) p,
    (forall d, P1 d -> P2 d) ->
    path_prop g P1 p ->
    path_prop g P2 p.
  Proof. repeat intro. spec H0 n H1. eapply node_prop_weaken; eauto. Qed.
  Lemma path_prop_sublist: forall g P p1 p2,
    sublist p1 p2 ->
    path_prop g P p2 ->
    path_prop g P p1.
  Proof. repeat intro. apply H0. apply H. trivial. Qed.
  Lemma path_prop_tail: forall g P n p,
    path_prop g P (n :: p) ->
    path_prop g P p.
  Proof. repeat intro. spec H n0. apply H. apply In_tail. trivial. Qed.

  Definition good_path (g : gph) (P : set D) : set path :=
    fun p => valid_path g p /\ path_prop g P p.
  Lemma good_path_split: forall g p1 p2 P,
    good_path g P (p1 ++ p2) ->
    (good_path g P p1) /\ (good_path g P p2).
  Proof.
    intros. destruct H.
    apply valid_path_split in H. destruct H.
    unfold good_path. unfold path_prop in *. intuition.
  Qed.
  Lemma good_path_merge: forall g p1 p2 P,
    paths_meet p1 p2 ->
    good_path g P p1 ->
    good_path g P p2 ->
    good_path g P (p1 +++ p2).
  Proof.
    intros. destruct H0. destruct H1.
    split. apply valid_path_merge; auto.
    unfold path_prop in *. intros.
    unfold path_glue in H4. apply in_app_or in H4.
    destruct H4. auto.
    apply H3. apply In_tail; auto.
  Qed.
  Lemma good_path_weaken: forall g p (P1 P2 : set D),
    (forall d, P1 d -> P2 d) ->
    good_path g P1 p ->
    good_path g P2 p.
  Proof.
    split; destruct H0; auto.
    apply path_prop_weaken with P1; auto.
  Qed.
  Lemma good_path_acyclic: forall g P p n1 n2,
    path_endpoints p n1 n2 ->
    good_path g P p ->
    exists p',
      path_endpoints p' n1 n2 /\
      NoDup p' /\
      good_path g P p'.
  Proof.
    intros.
    destruct H0.
    apply valid_path_acyclic with (n1 := n1) (n2 := n2) in H0; trivial.
    destruct H0 as [p' [? [? [? ?]]]].
    exists p'. split; trivial. split; trivial.
    split; trivial.
    apply path_prop_sublist with p; trivial.
  Qed.


  Definition reachable_by_path (g : gph) (p : path) (n : N) (P : set D) : set N :=
    fun n' => path_endpoints p n n' /\ good_path g P p.
  Notation " g '|=' p 'is' n1 '~o~>' n2 'satisfying' P" := (reachable_by_path g p n1 P n2) (at level 1).

  Lemma reachable_by_path_nil: forall g n1 n2 P,
    ~ g |= nil is n1 ~o~> n2 satisfying P.
  Proof. repeat intro. destruct H as [[? _] _]. disc. Qed.
  Lemma reachable_by_path_head: forall g p n1 n2 P,
    g |= p is n1 ~o~> n2 satisfying P ->
    head p = Some n1.
  Proof. intros. destruct H as [[? _] _]. trivial. Qed.
  Lemma reachable_by_path_foot: forall g p n1 n2 P,
    g |= p is n1 ~o~> n2 satisfying P ->
    foot p = Some n2.
  Proof. intros. destruct H as [[_ ?] _]. trivial. Qed.
  Lemma reachable_by_path_merge: forall g p1 n1 n2 p2 n3 P,
    g |= p1 is n1 ~o~> n2 satisfying P ->
    g |= p2 is n2 ~o~> n3 satisfying P ->
    g |= (p1 +++ p2) is n1 ~o~> n3 satisfying P.
  Proof.
    intros. destruct H. destruct H0.
    split. apply path_endpoints_glue with n2; auto.
    apply good_path_merge; auto.
    eapply path_endpoints_meet; eauto.
  Qed.
  Lemma reachable_by_path_split_glue: forall g P p1 p2 n1 n2 n,
    paths_meet_at p1 p2 n ->
    g |= (p1 +++ p2) is n1 ~o~> n2 satisfying P ->
    g |= p1 is n1 ~o~> n satisfying P /\ g |= p2 is n ~o~> n2 satisfying P.
  Proof.
    intros. unfold path_glue in H0. destruct H0.
    destruct H.
    destruct (foot_explicit _ H) as [L' ?]. subst p1.
    icase p2. inv H2.
    copy H1. apply good_path_split in H1. destruct H1 as [? _].
    rewrite <- app_assoc in H2, H0. simpl in H2, H0.
    apply good_path_split in H2. destruct H2 as [_ ?].
    destruct H0. rewrite foot_app in H3; disc.
    repeat (split; trivial). icase L'.
  Qed.
  Lemma reachable_by_path_split_in: forall g P p n n1 n2,
    g |= p is n1 ~o~> n2 satisfying P ->
    In n p ->
    exists p1, exists p2,
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
  Lemma reachable_by_path_In_prop: forall g p n1 n2 P n,
    g |= p is n1 ~o~> n2 satisfying P ->
    In n p ->
    node_prop g P n.
  Proof. intros. destruct H as [_ [_ ?]]. apply H. trivial. Qed.


  Definition reachable_by (g : gph) (n : N) (P : set D) : set N :=
    fun n' => exists p, g |= p is n ~o~> n' satisfying P.
  Notation " g '|=' n1 '~o~>' n2 'satisfying' P " := (reachable_by g n1 P n2) (at level 1).

  Lemma reachable_by_reflexive: forall g n P,
    node_prop g P n ->
    g |= n ~o~> n satisfying P.
  Proof.
    intros.
    exists (n :: nil). split. compute. auto.
    split. simpl. trivial.
    intros ? ?. icase H0. subst n0. trivial.
  Qed.
  Lemma reachable_by_merge: forall g n1 n2 n3 P,
    g |= n1 ~o~> n2 satisfying P ->
    g |= n2 ~o~> n3 satisfying P ->
    g |= n1 ~o~> n3 satisfying P.
  Proof. do 2 destruct 1. exists (x +++ x0). apply reachable_by_path_merge with n2; auto. Qed.
  Lemma reachable_by_head_prop: forall g n1 n2 P,
    g |= n1 ~o~> n2 satisfying P ->
    node_prop g P n1.
  Proof.
    intros. destruct H as [p ?].
    eapply reachable_by_path_In_prop; eauto.
    apply reachable_by_path_head in H. icase p. inv H. simpl. auto.
  Qed.
  Lemma reachable_by_foot_prop: forall g n1 n2 P,
    g |= n1 ~o~> n2 satisfying P ->
    node_prop g P n2.
  Proof.
    intros. destruct H as [p ?].
    eapply reachable_by_path_In_prop; eauto.
    apply reachable_by_path_foot in H. apply foot_in. trivial.
  Qed.
  Lemma reachable_by_cons: forall g n1 n2 n3 P,
    g |= n1 ~> n2 ->
    node_prop g P n1 ->
    g |= n2 ~o~> n3 satisfying P ->
    g |= n1 ~o~> n3 satisfying P.
  Proof.
    intros. apply reachable_by_merge with n2; auto.
    apply reachable_by_head_prop in H1.
    exists (n1 :: n2 :: nil). split. split; auto.
    split. simpl. tauto.
    intros n ?. simpl in H2.
    icase H2. subst; trivial.
    icase H2. subst; trivial.
  Qed.

  Definition reachable_by_acyclic (g : gph) (n : N) (P : set D) : set N :=
    fun n' => exists p, NoDup p /\ g |= p is n ~o~> n' satisfying P.
  Notation " g '|=' n1 '~~>' n2 'satisfying' P " := (reachable_by_acyclic g n1 P n2) (at level 1).

  Lemma reachable_acyclic: forall g n1 P n2,
    g |= n1 ~o~> n2 satisfying P <->
    g |= n1 ~~> n2 satisfying P.
  Proof.
    split; intros.
    destruct H as [p [? ?]].
    apply (good_path_acyclic H) in H0.
    destruct H0 as [p' [? ?]].
    exists p'. compute. tauto.
    destruct H as [p [? ?]].
    exists p. trivial.
  Qed.

  Definition reachable (g : gph) (n : N) : set N :=
    reachable_by g n (fun _ => True).

  Lemma reachable_by_subset_reachable: forall g n P,
    subset (reachable_by g n P) (reachable g n).
  Proof.
    repeat intro. unfold reachable.
    destruct H as [p [? [? ?]]]. exists p.
    split; trivial.
    split; trivial. apply path_prop_weaken with P; auto.
  Qed.

(*
  Definition local_change (g1 : gph) (n : N) (g2 : gph) : Prop :=
    forall n',
      ~reachable g1 n n' ->
      node_label g1 n = node_label g2 n /\
      (forall e, edge_source g1 e = n -> edge_source g2 e = n)

Record pregraph N E D L :=
  Pregraph
  { node_label : N -> option D
  ; edge_label : E -> option L
  ; edge_source : E -> N
  ; edge_dest : E -> N
  }.

  Lemma mark_local: forall g1 root g2,
    mark g1 root g2 ->
*)

(* START OF MARK *)

  Variable marked : D -> Prop.
  Definition unmarked (d : D) : Prop := ~ marked d.

  Definition mark1 (g1 : gph) (n : N) (g2 : gph) : Prop :=
    structurally_identical g1 g2 /\
    node_prop g2 marked n /\
    forall n', n <> n' -> node_label g1 n' = node_label g2 n'.

  (* The first subtle lemma *)
  Lemma mark1_unmarked : forall g1 root g2 n,
    mark1 g1 root g2 ->
    g1 |= root ~o~> n satisfying unmarked ->
      n = root \/
      exists child,
        edge g1 root child /\
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
    split. destruct H1 as [_ [? _]]. apply valid_path_si with (g2 := g2) in H1. 2: destruct H; trivial.
    simpl in H1. destruct H. symmetry in H. apply edge_si with g2; tauto.
    exists (n0 :: p). destruct H2 as [? [? ?]].
    split; trivial.
    destruct H as [? [_ ?]]. split. eapply valid_path_si; eauto.
    intros ? ?. spec H4 n1 H6.
    (* Hammertime! *)
    assert (root <> n1). intro. inversion H0. subst. contr.
    spec H5 n1 H7. eapply node_prop_label_eq; eauto.
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
    split. eapply valid_path_si; eauto. symmetry; trivial. (* clear -H3 H0 H2. *)
    intros ? ?. spec H2 n H5. spec H4 n.
    spec H4. intro. subst n. destruct H3 as [? [? ?]]. destruct H2 as [? [? ?]]. rewrite H3 in H2. inv H2. contr.
    apply node_prop_label_eq with g2; auto.
  Qed.

  Definition mark (g1 : gph) (root : N) (g2 : gph) : Prop :=
    structurally_identical g1 g2 /\
    (forall n,  g1 |= root ~o~> n satisfying unmarked -> node_prop g2 marked n) /\
    (forall n, ~g1 |= root ~o~> n satisfying unmarked -> node_label g1 n = node_label g2 n).

  (* Sanity condition 1 *)
  Lemma mark_reachable: forall g1 root g2,
    mark g1 root g2 ->
    subset (reachable g1 root) (reachable g2 root).
  Proof.
    repeat intro. destruct H as [? [? ?]].
    destruct H0 as [p ?]. destruct H0.
    exists p. split. tauto.
    destruct H3. split. eapply valid_path_si; eauto.
    clear -H1 H2 H4. induction p; repeat intro. inv H. simpl in H. destruct H. subst a.
    LEM (g1 |= root ~o~> n satisfying unmarked).
    spec H1 n H. apply node_prop_weaken with marked; auto.
    spec H2 n H. eapply node_prop_label_eq; eauto. apply H4. left. trivial.
    apply IHp; auto. intros ? ?. apply H4. right. trivial.
  Qed.

  (* The second subtle lemma.  Maybe needs a better name? *)
  Lemma mark_unmarked: forall g1 root g2 n1 n2,
    mark g1 root g2 ->
    g1 |= n1 ~o~> n2 satisfying unmarked ->
    (g2 |= n1 ~o~> n2 satisfying unmarked) \/ (node_prop g2 marked n2).
  Proof.
    intros. destruct H0 as [p ?].
    (* This is a very handy LEM. *)
    LEM (exists n, In n p /\ g1 |= root ~o~> n satisfying unmarked).
    right. destruct H as [_ [? _]]. apply H.
    destruct H1 as [n [? ?]]. apply reachable_by_merge with n; trivial.
    destruct (reachable_by_path_split_in _ H0 H1) as [p1 [p2 [? [? ?]]]].
    exists p2. trivial.
    left. exists p. destruct H0. split; trivial. clear H0.
    destruct H2. destruct H as [? [_ ?]]. split. eapply valid_path_si; eauto.
    intros ? ?. spec H2 n H4. spec H3 n.
    spec H3. intro. apply H1. exists n. tauto.
    eapply node_prop_label_eq; eauto.
  Qed.

  Lemma mark_marked: forall g1 root g2,
    mark g1 root g2 ->
    forall n,
      node_prop g1 marked n->
      node_prop g2 marked n.
  Proof.
    intros. destruct H as [_ [? ?]].
    LEM (g1 |= root ~o~> n satisfying unmarked).
    spec H1 n H2. eapply node_prop_label_eq; eauto.
  Qed.

  (* Maybe a better name? *)
  Lemma mark_reverse_unmarked: forall g1 root g2,
    mark g1 root g2 ->
    forall n1 n2,
      g2 |= n1 ~o~> n2 satisfying unmarked ->
      g1 |= n1 ~o~> n2 satisfying unmarked.
  Proof.
    intros. destruct H0 as [p [? ?]]. exists p. split; trivial. clear H0.
    destruct H as [? [? ?]]. destruct H1.
    split. eapply valid_path_si; eauto. symmetry; trivial. clear -H3 H0 H2.
    intros ? ?. spec H3 n H. spec H0 n. spec H2 n.
    LEM (g1 |= root ~o~> n satisfying unmarked).
    spec H0 H1. clear H2 H1. exfalso.
    destruct H3 as [? [? ?]]. destruct H0 as [? [? ?]]. rewrite H1 in H0. inv H0. auto.
    spec H2 H1. apply node_prop_label_eq with g2; auto.
  Qed.

  (* Here is where we specialize to bigraphs, at least at root *)
  Definition node_connected_two (g : gph) (root left right : N) : Prop :=
    edge g root left /\
    edge g root right /\
    forall n', edge g root n' -> n' = left \/ n' = right.

  (* The main lemma *)
  Lemma mark_mark_mark1: forall g1 g2 g3 g4 root left right,
    node_prop g1 unmarked root -> (* Oh no!  We forgot this precondition in the paper!! *)
    node_connected_two g1 root left right ->
    mark1 g1 root g2 ->
    mark g2 left g3 ->
    mark g3 right g4 ->
    mark g1 root g4.
  Proof.
    split. destruct H1. rewrite H1. destruct H2. rewrite H2. destruct H3. trivial.
    split; intros.
    (* Need subtle lemma 1 *)
    destruct (mark1_unmarked H1 H4); clear H4.
    subst n. eapply mark_marked; eauto. eapply mark_marked; eauto. red in H1; tauto.
    destruct H5 as [child [? ?]]. destruct H0 as [_ [_ ?]]. apply H0 in H4. clear H0.
    destruct H4; subst child.
    eapply mark_marked; eauto.
    destruct H2 as [_ [? _]]. auto.
    (* Need subtle lemma 2 *)
    destruct (mark_unmarked H2 H5).
    destruct H3 as [_ [? _]]. auto.
    eapply mark_marked; eauto.
    (* *** *)
    assert (root <> n). intro. subst n. apply H4. apply reachable_by_reflexive; auto.
    assert (~ g2 |= left ~o~> n satisfying unmarked).
      intro. apply H4. apply reachable_by_cons with left; auto. red in H0; tauto.
      eapply mark1_reverse_unmark; eauto.
    assert (~ g3 |= right ~o~> n satisfying unmarked).
      intro. apply H4. apply mark_reverse_unmarked with (root := left) (g1 := g2) in H7; auto.
      apply reachable_by_cons with right; auto. red in H0; tauto.
      eapply mark1_reverse_unmark; eauto.
    destruct H1 as [? [_ ?]]. rewrite H8; auto.
    destruct H2 as [? [_ ?]]. rewrite H9; auto.
    destruct H3 as [? [_ ?]]. rewrite H10; auto.
  Qed.

End mark.

