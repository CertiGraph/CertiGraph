Require Import FunctionalExtensionality.
Require Import List.
Require Import Omega.
Require Import Setoid.

Class EqDec (T: Type) := {t_eq_dec: forall t1 t2 : T, {t1 = t2} + {t1 <> t2}}.

Class Valid (T: Type) {EDT: EqDec T} := valid: T -> bool.

Definition sameValid (T : Type) (b: bool) {EDT: EqDec T} : Valid T := fun _ => b.

Definition modifyValid (T : Type) (t : T) (b : bool) {EDT: EqDec T} {V : Valid T} : Valid T :=
  fun (x : T) => if (t_eq_dec x t) then b else V x.

Class PreGraph (Vertex: Type) Data {EV: EqDec Vertex} {VV : Valid Vertex}:=
  {
    node_label : Vertex -> Data;
    edge_func : Vertex -> list Vertex
  }.

Class BiGraph (Vertex: Type) Data {EV: EqDec Vertex} {VV: Valid Vertex} {PG: PreGraph Vertex Data} :=
  {
    length_limit: forall v : Vertex, length (edge_func v) >= 2
  }.

Definition biEdge (Vertex : Type) Data (v: Vertex) {EV: EqDec Vertex} {VV: Valid Vertex}
           {PG: PreGraph Vertex Data} {BG: BiGraph Vertex Data} : Vertex * Vertex.
  specialize (length_limit v); intro Hlen;
  destruct (edge_func v); [simpl in Hlen; exfalso; intuition |
                           destruct l; [simpl in Hlen; exfalso; intuition | apply (v0, v1)]].
Defined.

Definition gamma (Vertex : Type) Data (v: Vertex) {EV: EqDec Vertex} {VV: Valid Vertex}
           {PG: PreGraph Vertex Data} {BG: BiGraph Vertex Data} : Data * Vertex * Vertex :=
  let (v1, v2) := biEdge Vertex Data v in (node_label v, v1, v2).

Definition sublist {A} (L1 L2 : list A) : Prop := forall a, In a L1 -> In a L2.

Lemma sublist_refl: forall A (L : list A), sublist L L. Proof. repeat intro; auto. Qed.

Lemma sublist_trans: forall A (L1 L2 L3 : list A), sublist L1 L2 -> sublist L2 L3 -> sublist L1 L3.
Proof. repeat intro; apply H0; apply H; trivial. Qed.

Add Parametric Relation {A} : (list A) sublist
    reflexivity proved by (@sublist_refl A)
    transitivity proved by (@sublist_trans A) as sublist_rel.

Lemma sublist_nil: forall A (L : list A), sublist nil L. Proof. repeat intro; inversion H. Qed.

Lemma sublist_cons: forall A (a : A) L, sublist L (a :: L). Proof. repeat intro; simpl; auto. Qed.

Lemma sublist_app: forall A (L1 L2 L3 L4: list A), sublist L1 L2 -> sublist L3 L4 -> sublist (L1 ++ L3) (L2 ++ L4).
Proof. repeat intro; apply in_app_or in H1; apply in_or_app; destruct H1; [left; apply H | right; apply H0]; trivial. Qed.

Definition eq_as_set {A} (L1 L2 : list A) : Prop := sublist L1 L2 /\ sublist L2 L1.

Notation "a '~=' b" := (eq_as_set a b) (at level 1).

Lemma eq_as_set_refl: forall A (L : list A), L ~= L. Proof. intros; split; apply sublist_refl. Qed.

Lemma eq_as_set_sym: forall A (L1 L2 : list A), L1 ~= L2 -> L2 ~= L1. Proof. intros; hnf in *; firstorder. Qed.

Lemma eq_as_set_trans: forall A (L1 L2 L3 : list A), L1 ~= L2 -> L2 ~= L3 -> L1 ~= L3.
Proof. intros; hnf in *; intuition; transitivity L2; trivial. Qed.

Add Parametric Relation {A} : (list A) eq_as_set
    reflexivity proved by (eq_as_set_refl A)
    symmetry proved by (eq_as_set_sym A)
    transitivity proved by (eq_as_set_trans A) as eq_as_set_rel.

Lemma eq_as_set_app: forall A (L1 L2 L3 L4: list A), L1 ~= L2 -> L3 ~= L4 -> (L1 ++ L3) ~= (L2 ++ L4).
Proof. intros; hnf in *; intuition; apply sublist_app; trivial. Qed.

Definition removeInvalid {A} {EDT: EqDec A} (VT: Valid A) := filter valid.

Definition structurally_identical {V D1 D2 : Type} {EV: EqDec V} {VV1 VV2 : Valid V}
           (G1 : @PreGraph V D1 EV VV1) (G2 : @PreGraph V D2 EV VV2) : Prop :=
  forall v : V, (@valid V EV VV1 v) = (@valid V EV VV2 v) /\
                (((@valid V EV VV1 v) = true /\ (@edge_func V D1 EV VV1 G1 v) ~= (@edge_func V D2 EV VV2 G2 v)) \/
                 ((@valid V EV VV1 v) = false /\ (removeInvalid VV1 (@edge_func V D1 EV VV1 G1 v)) ~=
                                                (removeInvalid VV2 (@edge_func V D2 EV VV2 G2 v)))).

Notation "g1 '~=~' g2" := (structurally_identical g1 g2) (at level 1).

Lemma si_refl: forall (V D : Type) (EV : EqDec V) (VV : Valid V) (G : PreGraph V D), G ~=~ G.
Proof. intros; hnf; intros; split; [reflexivity | destruct (valid v); [left | right]; split; reflexivity]. Qed.

Lemma si_sym: forall (V D1 D2 : Type) (EV: EqDec V) (VV1 VV2 : Valid V) (G1 : @PreGraph V D1 EV VV1)
                     (G2 : @PreGraph V D2 EV VV2), G1 ~=~ G2 -> G2 ~=~ G1.
Proof.
  intros; hnf in *; intros; specialize (H v); destruct H; split; auto; destruct H0;
  [left; intuition; rewrite <- H; assumption | right; intuition; rewrite <- H; assumption].
Qed.

Lemma si_trans: forall (V D1 D2 D3 : Type) (EV : EqDec V) (VV1 VV2 VV3 : Valid V) (G1 : @PreGraph V D1 EV VV1)
                       (G2 : @PreGraph V D2 EV VV2) (G3 : @PreGraph V D3 EV VV3), G1 ~=~ G2 -> G2 ~=~ G3 -> G1 ~=~ G3.
Proof.
  intros; hnf in *; intros; specialize (H v); specialize (H0 v); destruct H, H0; split;
  [transitivity (@valid V EV VV2 v); auto |
   destruct H1, H2; destruct H1, H2;
   [left; split; auto; transitivity (@edge_func V D2 EV VV2 G2 v); trivial |
    rewrite H in H1; rewrite H2 in H1; discriminate H1 |
    rewrite H in H1; rewrite H2 in H1; discriminate H1 |
    right; split; auto; transitivity (@removeInvalid V EV VV2 (@edge_func V D2 EV VV2 G2 v)); trivial]].
Qed.

Definition edge {V D : Type} {EV : EqDec V} {VV : Valid V} (G : PreGraph V D) (n n' : V) : Prop :=
  valid n = true /\ valid n' = true /\ In n' (edge_func n).

Notation " g |= n1 ~> n2 " := (edge g n1 n2) (at level 1).

Lemma edge_si {V D1 D2 : Type} {EV: EqDec V} {VV1 VV2 : Valid V}:
  forall (g1 : @PreGraph V D1 EV VV1) (g2 : @PreGraph V D2 EV VV2) (n n' : V), g1 ~=~ g2 -> g1 |= n ~> n' -> g2 |= n ~> n'.
Proof.
  intros; hnf in *; generalize (H n); intro; specialize (H n'); destruct H, H1; clear H2; destruct H0 as [? [? ?]];
  destruct H3; destruct H3;
  [split; auto; [rewrite H1 in H3; assumption |
                 split; [rewrite H in H2; assumption | destruct H5; specialize (H5 n'); apply H5; assumption]] |
   rewrite H0 in H3; discriminate H3].
Qed.

Notation "a '+::' b" := (a ++ (b :: nil)) (at level 19).
Fixpoint foot {A} (L : list A) : option A :=
  match L with
    | nil => None
    | a :: nil => Some a
    | a :: L' => foot L'
  end.

Lemma foot_simpl: forall A (a1 a2 : A) (L : list A), foot (a1 :: a2 :: L) = foot (a2 :: L).
Proof. intros. simpl. destruct L; auto. Qed.

Lemma foot_last: forall A (L : list A) (a : A), foot (L +:: a) = Some a.
Proof.
  induction L; auto; intros; destruct L; auto; rewrite <- (IHL a0); simpl; destruct (L +:: a0); simpl; auto.
Qed.

Lemma foot_app: forall A (L1 L2 : list A), L2 <> nil -> foot (L1 ++ L2) = foot L2.
Proof.
  induction L1. auto. intros. rewrite <- app_comm_cons. simpl. case_eq (L1 ++ L2).
  intro. apply app_eq_nil in H0. destruct H0. contradiction. intros. rewrite <- H0. apply IHL1. trivial.
Qed.

Tactic Notation "disc" := (try discriminate).
Tactic Notation "contr" := (try contradiction).
Tactic Notation "congr" := (try congruence).
Tactic Notation "inv" hyp(H) := inversion H; clear H; subst.
Tactic Notation  "icase" constr(v) := (destruct v; disc; contr; auto).

Lemma foot_explicit {A}: forall L (a : A), foot L = Some a -> exists L', L = L' +:: a.
Proof.
  induction L. inversion 1. intros. simpl in H. icase L. inv H. exists nil. trivial.
  specialize (IHL a0 H). destruct IHL. exists (a :: x). rewrite <- app_comm_cons. congr.
Qed.

Lemma foot_in {A}: forall (a : A) L, foot L = Some a -> In a L.
Proof. induction L. inversion 1. icase L. simpl. inversion 1. auto. rewrite foot_simpl. right. auto. Qed.

Section GraphPath.
  Variable N : Type.
  Variable D : Type.
  Variable EDN : EqDec N.
  Variable VN : Valid N.
  Let Gph := @PreGraph N D EDN VN.

  Definition path : Type := list N.
  Definition path_endpoints (p : path) (n1 n2 : N) : Prop := head p = Some n1 /\ foot p = Some n2.
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

  Fixpoint valid_path (g : Gph) (p : path) : Prop :=
    match p with
     | nil => True
     | n :: nil => valid n = true
     | n1 :: ((n2 :: _) as p') => g |= n1 ~> n2 /\ valid_path g p'
    end.

  Lemma valid_path_tail: forall g p, valid_path g p -> valid_path g (tail p).
  Proof.
    destruct p; auto. simpl. destruct p; auto.
    intro; simpl; auto. intros [? ?]; auto.
  Qed.

  Lemma valid_path_split: forall g p1 p2, valid_path g (p1 ++ p2) -> valid_path g p1 /\ valid_path g p2.
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

  Lemma valid_path_merge: forall g p1 p2, paths_meet p1 p2 -> valid_path g p1 -> valid_path g p2 -> valid_path g (p1 +++ p2).
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

End GraphPath.

Lemma valid_path_si {V D1 D2 : Type} {EV: EqDec V} {VV1 VV2 : Valid V}:
  forall (g1 : @PreGraph V D1 EV VV1) (g2 : @PreGraph V D2 EV VV2),
    structurally_identical g1 g2 -> forall p, valid_path V D1 EV VV1 g1 p -> valid_path V D2 EV VV2 g2 p.
Proof.
  Set Printing Implicit.
  induction p; simpl; auto.
  icase p.
  intro; destruct (H a); rewrite <- H1; auto.
  intros [? ?]. split; auto.
  apply (edge_si g1 g2 a v H H0).
Qed.
