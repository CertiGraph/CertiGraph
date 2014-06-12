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

Definition structurally_identical {V D1 D2 : Type} {EV: EqDec V} {VV1 VV2 : Valid V}
           (G1 : @PreGraph V D1 EV VV1) (G2 : @PreGraph V D2 EV VV2) : Prop :=
  forall v : V, (@edge_func V D1 EV VV1 G1 v) ~= (@edge_func V D2 EV VV2 G2 v) /\
                (@valid V EV VV1 v) = (@valid V EV VV2 v).

Notation "g1 '~=~' g2" := (structurally_identical g1 g2) (at level 1).

Lemma si_refl: forall (V D : Type) (EV : EqDec V) (VV : Valid V) (G : PreGraph V D), G ~=~ G.
Proof. repeat (intros; hnf); split; reflexivity. Qed.

Lemma si_sym: forall (V D1 D2 : Type) (EV: EqDec V) (VV1 VV2 : Valid V) (G1 : @PreGraph V D1 EV VV1)
                     (G2 : @PreGraph V D2 EV VV2), G1 ~=~ G2 -> G2 ~=~ G1.
Proof. intros; hnf in *; intros; specialize (H v); intuition. Qed.

Lemma si_trans: forall (V D1 D2 D3 : Type) (EV : EqDec V) (VV1 VV2 VV3 : Valid V) (G1 : @PreGraph V D1 EV VV1)
                       (G2 : @PreGraph V D2 EV VV2) (G3 : @PreGraph V D3 EV VV3), G1 ~=~ G2 -> G2 ~=~ G3 -> G1 ~=~ G3.
Proof. 
  intros; hnf in *; intros; specialize (H v); specialize (H0 v); intuition;
  [transitivity (@edge_func V D2 EV VV2 G2 v) | transitivity (@valid V EV VV2 v)]; trivial.
Qed.
