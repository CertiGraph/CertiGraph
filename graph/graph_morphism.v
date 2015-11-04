Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Morphisms_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas. Import RamifyCoq.graph.path_lemmas.PathNotation.
Require Import RamifyCoq.graph.subgraph2.

Module GraphMophism.

Section GraphMophism.

Context {V V' E E': Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {EV': EqDec V' eq}.
Context {EE': EqDec E' eq}.

Variables (PV: V -> Prop) (PE: E -> Prop) (PV': V' -> Prop) (PE': E' -> Prop).

Definition guarded_morphism (vmap: V -> V') (emap: E -> E') (G1: PreGraph V E) (G2: PreGraph V' E'): Prop :=
  (forall v, PV v -> PV' (vmap v)) /\
  (forall e, PE e -> PE' (emap e)) /\
  (forall v, PV v -> (vvalid G1 v <-> vvalid G2 (vmap v))) /\
  (forall e, PE e -> (evalid G1 e <-> evalid G2 (emap e))) /\
  (forall e, PE e -> PV (src G1 e) -> evalid G1 e -> vmap (src G1 e) = src G2 (emap e)) /\
  (forall e, PE e -> PV (dst G1 e) -> evalid G1 e -> vmap (dst G1 e) = dst G2 (emap e)).

Definition guarded_inj (vmap: V -> V') (emap: E -> E') (G1: PreGraph V E) (G2: PreGraph V' E'): Prop :=
  (forall v1 v2, PV v1 -> PV v2 -> v1 <> v2 -> vmap v1 <> vmap v2) /\
  (forall e1 e2, PE e1 -> PE e2 -> e1 <> e2 -> emap e1 <> emap e2) /\
  guarded_morphism vmap emap G1 G2.

Definition guarded_surj (vmap: V -> V') (emap: E -> E') (G1: PreGraph V E) (G2: PreGraph V' E'): Prop :=
  (forall v', PV' v' -> exists v, PV v /\ vmap v = v') /\
  (forall e', PE' e' -> exists e, PE e /\ emap e = e') /\
  guarded_morphism vmap emap G1 G2.

Definition guarded_bij (vmap: V -> V') (emap: E -> E') (G1: PreGraph V E) (G2: PreGraph V' E'): Prop :=
  (forall v1 v2, PV v1 -> PV v2 -> v1 <> v2 -> vmap v1 <> vmap v2) /\
  (forall e1 e2, PE e1 -> PE e2 -> e1 <> e2 -> emap e1 <> emap e2) /\
  (forall v', PV' v' -> exists v, PV v /\ vmap v = v') /\
  (forall e', PE' e' -> exists e, PE e /\ emap e = e') /\
  guarded_morphism vmap emap G1 G2.

Lemma guarded_morphism_proper_aux: forall vmap1 vmap2 emap1 emap2 G1 G2 G1' G2',
  guarded_pointwise_relation PV eq vmap1 vmap2 ->
  guarded_pointwise_relation PE eq emap1 emap2 ->
  guarded_structurally_identical PV PE G1 G2 ->
  guarded_structurally_identical PV' PE' G1' G2' ->
  guarded_morphism vmap1 emap1 G1 G1' ->
  guarded_morphism vmap2 emap2 G2 G2'.
Proof.
  unfold guarded_morphism.
  intros.
  rewrite guarded_pointwise_relation_spec in H.
  rewrite guarded_pointwise_relation_spec in H0.
  destruct H3 as [? [? [? [? [? ?]]]]].
  destruct (proj1 (guarded_si_spec _ _ _ _) H1) as [? [? [? ?]]].
  destruct (proj1 (guarded_si_spec _ _ _ _) H2) as [? [? [? ?]]].
  assert (forall v : V, PV v -> PV' (vmap2 v))
    by (intros; rewrite <- H by auto; apply H3; auto).
  assert (forall e : E, PE e -> PE' (emap2 e))
    by (intros; rewrite <- H0 by auto; apply H4; auto).
  assert (forall v : V, PV v -> (vvalid G2 v <-> vvalid G2' (vmap2 v))).
  Focus 1. {
    intros.
    rewrite <- H9 by auto.
    rewrite <- H by auto.
    rewrite <- H13 by auto.
    apply H5; auto.
  } Unfocus.
  assert (forall e : E, PE e -> (evalid G2 e <-> evalid G2' (emap2 e))).
  Focus 1. {
    intros.
    rewrite <- H10 by auto.
    rewrite <- H0 by auto.
    rewrite <- H14 by auto.
    apply H6; auto.
  } Unfocus.
  split; [| split; [| split; [| split; [| split]]]]; auto; intros.
  + assert (evalid G1 e) by (rewrite H10 by auto; auto).
    rewrite <- H15.
    2: apply H18; auto.
    2: rewrite <- H0, <- H6, H10 by auto; auto.
    2: rewrite <- H20 by auto; auto.
    rewrite <- H0 by auto.
    rewrite <- H by auto.
    rewrite <- H11 by auto.
    apply H7; auto.
    rewrite H11 by auto; auto.
  + assert (evalid G1 e) by (rewrite H10 by auto; auto).
    rewrite <- H16.
    2: apply H18; auto.
    2: rewrite <- H0, <- H6, H10 by auto; auto.
    2: rewrite <- H20 by auto; auto.
    rewrite <- H0 by auto.
    rewrite <- H by auto.
    rewrite <- H12 by auto.
    apply H8; auto.
    rewrite H12 by auto; auto.
Qed.

Lemma guarded_bij_proper_aux: forall vmap1 vmap2 emap1 emap2 G1 G2 G1' G2',
  guarded_pointwise_relation PV eq vmap1 vmap2 ->
  guarded_pointwise_relation PE eq emap1 emap2 ->
  guarded_structurally_identical PV PE G1 G2 ->
  guarded_structurally_identical PV' PE' G1' G2' ->
  guarded_bij vmap1 emap1 G1 G1' ->
  guarded_bij vmap2 emap2 G2 G2'.
Proof.
  unfold guarded_bij.
  intros.
  assert (guarded_morphism vmap2 emap2 G2 G2') by (eapply guarded_morphism_proper_aux; eauto; tauto).
  rewrite guarded_pointwise_relation_spec in H.
  rewrite guarded_pointwise_relation_spec in H0.
  destruct H3 as [? [? [? [? _]]]].
  split; [| split; [| split; [| split]]]; intros.
  + rewrite <- !H by auto.
    apply H3; auto.
  + rewrite <- !H0 by auto.
    apply H5; auto.
  + apply H6 in H8.
    destruct H8 as [v [? ?]]; exists v.
    rewrite <- H by auto; auto.
  + apply H7 in H8.
    destruct H8 as [e [? ?]]; exists e.
    rewrite <- H0 by auto; auto.
  + auto.
Qed.

Instance guarded_morphism_proper: Proper (guarded_pointwise_relation PV eq ==> guarded_pointwise_relation PE eq ==> guarded_structurally_identical PV PE ==> guarded_structurally_identical PV' PE' ==> iff) guarded_morphism.
Proof.
  hnf; intros vmap1 vmap2 ?H.
  hnf; intros emap1 emap2 ?H.
  hnf; intros G1 G2 ?H.
  hnf; intros G1' G2' ?H.
  split; apply guarded_morphism_proper_aux; auto; symmetry; auto.
Defined.

Instance guarded_bij_proper: Proper (guarded_pointwise_relation PV eq ==> guarded_pointwise_relation PE eq ==> guarded_structurally_identical PV PE ==> guarded_structurally_identical PV' PE' ==> iff) guarded_bij.
Proof.
  hnf; intros vmap1 vmap2 ?H.
  hnf; intros emap1 emap2 ?H.
  hnf; intros G1 G2 ?H.
  hnf; intros G1' G2' ?H.
  split; apply guarded_bij_proper_aux; auto; symmetry; auto.
Defined.

End GraphMophism.

Class GraphMorphismSetting (DV DE V' E': Type): Type := {
  co_vertex: DV -> V';
  co_edge: DE -> E'
}.

End GraphMophism.

Module CopyGraph.

Section CopyGraph.

Import GraphMophism.

Context {V E V' E': Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {EV': EqDec V' eq}.
Context {EE': EqDec E' eq}.
Context {DV DE: Type}.
Context {GMS: GraphMorphismSetting DV DE V' E'}.

Notation Graph := (LabeledGraph V E DV DE).

Notation Graph' := (PreGraph V' E').

Definition vmap (g: Graph): V -> V' := fun v => co_vertex (vlabel g v).

Definition emap (g: Graph): E -> E' := fun e => co_edge (elabel g e).

Definition nothing (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  pointwise_relation V eq (vmap g1) (vmap g2) /\
  pointwise_relation E eq (emap g1) (emap g2) /\
  g1' ~=~ g2'.

Definition vcopy1 x (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  exists y,
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ (eq x)) eq (vmap g1) (vmap g2) /\
  pointwise_relation E eq (emap g1) (emap g2) /\
  y = vmap g2 x /\
  vertex_join (eq y) g1' g2'.

Definition ecopy1 e (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  exists e',
  g1 ~=~ g2 /\
  pointwise_relation V eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ (eq e)) eq (emap g1) (emap g2) /\
  emap g2 e = e' /\
  edge_union (eq e') g1' g2' /\
  vmap g2 (src g2 e) = src g2' e' /\
  vmap g2 (dst g2 e) = dst g2' e'.

Definition copy P (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ P) eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ (weak_edge_prop P g1)) eq (emap g1) (emap g2) /\
  (exists P', forall PV PE PV' PE',
     guarded_inj PV PE PV' PE' (vmap g1) (emap g1) g1 g1' ->
     guarded_inj (Union _ PV P) (Union _ PE (weak_edge_prop P g2))
      (Union _ PV' P') (Union _ PE' (weak_edge_prop P' g2')) (vmap g2) (emap g2) g2 g2').

Definition gcopy (PV: V -> Prop) (PE: E -> Prop) (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  guarded_pointwise_relation (Complement _ PV) eq (vmap g1) (vmap g2) /\
  guarded_pointwise_relation (Complement _ PE) eq (emap g1) (emap g2) /\
  (exists PV' PE', forall fPV fPE fPV' fPE',
     guarded_inj fPV fPE fPV' fPE' (vmap g1) (emap g1) g1 g1' ->
     guarded_inj (Union _ fPV PV) (Union _ fPE PE)
      (Union _ fPV' PV') (Union _ fPE' PE') (vmap g2) (emap g2) g2 g2').

Definition edge_copy (g: Graph) (P: V -> Prop) (l: list E * E) :=
  let (es, e) := l in
  let P0 := Intersection _ (reachable_by g (dst g e) P)
               (Complement _ (reachable_by_through_set g (map (dst g) es) P)) in
  relation_list (nothing :: copy P0 :: nothing :: ecopy1 e :: nothing :: nil).

Definition edge_copy_list (g: Graph) es (P: V -> Prop) :=
  relation_list (map (edge_copy g P) (combine (prefixes es) es)).

Lemma eq_do_nothing: inclusion _ eq nothing.
Proof.
  intros; hnf; intros.
  hnf; destruct x as [g1 g1'], y as [g2 g2'].
  inversion H; subst.
  split; [| split; [| split]].
  + reflexivity.
  + intro; reflexivity.
  + intro; reflexivity.
  + reflexivity.
Qed.

(*
Require Import Coq.Classes.Morphisms.
Definition respectful {A B : Type}
  (R : relation A) (R' : relation B) : relation (A -> B) :=
  Eval compute in @respectful_hetero A A (fun _ => B) (fun _ => B) R (fun _ _ => R').

PRETTY SURPRISING THAT THIS SYNTAX IS LEGAL!!!!!!!!!!!!!!!!!!!!!!!!!!

*)

Lemma vcopy1_is_gcopy: forall x (p1 p2: Graph * Graph'),
  let (g1, _) := p1 in
  vcopy1 x p1 p2 ->
  gcopy (eq x) (weak_edge_prop (eq x) g1) p1 p2.
Proof.
  intros.
  destruct p1 as [g1 g1'], p2 as [g2 g2'].
  intros.
  destruct H as [y [? [? [? [? ?]]]]].
  split; [| split; [| split]].
  1: auto.
  1: auto.
  1: apply guarded_pointwise_relation_pointwise_relation; auto.
  intros.
  exists (eq y), (Empty_set _).
  intros.
(*
SearchAbout Ensemble.

  destruct H4 as [? [? [? [? [? ?]]]]].
  destruct H as [? [? [? ?]]].
  destruct H3 as [[? ?] [? [? ?]]].
  split; [| split; [| split; [| split; [| split]]]]; intros.
  + rewrite <- H, H3.
    rewrite Union_spec in H17.
    subst y.
    destruct H17.
    - rewrite H4 by auto.
    subst y; tauto.
*)

Lemma vcopy1_edge_copy_list_copy: forall root es (p1 p2: Graph * Graph') (P: V -> Prop),
  let (g1, _) := p1 in
  vvalid g1 root ->
  P root ->
  (forall e, In e es <-> out_edges g1 root e) ->
  relation_list (nothing :: vcopy1 root :: nothing :: edge_copy_list g1 es (Intersection _ P (Complement _ (eq root))) :: nothing :: nil) p1 p2 ->
  copy (reachable_by g1 root P) p1 p2.
Proof.
  intros.
  destruct p1 as [g1 g1'], p2 as [g2 g2'].
  intros.
  destruct_relation_list p3 p4 p5 p6 in H2.
Admitted.

End CopyGraph.

End CopyGraph.

