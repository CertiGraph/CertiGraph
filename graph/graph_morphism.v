Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas. Import RamifyCoq.graph.path_lemmas.PathNotation.
Require Import RamifyCoq.graph.subgraph2.

Definition guarded_same_morphism {A B} (P: A -> Prop) (f g: A -> B) :=
  forall a, P a -> f a = g a.

Definition same_morphism {A B} (f g: A -> B) := forall a, f a = g a.

Lemma same_morphism_guarded_same_morphism: forall {A B} P (f g: A -> B), same_morphism f g -> guarded_same_morphism P f g.
Proof.
  intros; hnf; intros.
  apply H.
Qed.

Section GraphMophism0.

Context {V1 V2 E1 E2: Type}.
Context {EV1: EqDec V1 eq}.
Context {EE1: EqDec E1 eq}.
Context {EV2: EqDec V2 eq}.
Context {EE2: EqDec E2 eq}.

Definition is_homo (vmap: V1 -> V2) (emap: E1 -> E2) (G1: PreGraph V1 E1) (G2: PreGraph V2 E2): Prop :=
  (forall v, vvalid G1 v <-> vvalid G2 (vmap v)) /\
  (forall e, evalid G1 e <-> evalid G2 (emap e)) /\
  (forall e, vmap (src G1 e) = src G2 (emap e)) /\
  (forall e, vmap (dst G1 e) = dst G2 (emap e)).

Definition guarded_inj (vmap: V1 -> V2) (emap: E1 -> E2) (PV: V1 -> Prop) (PE: E1 -> Prop) (G1: PreGraph V1 E1) (G2: PreGraph V2 E2): Prop :=
  (forall v, PV v -> (vvalid G1 v <-> vvalid G2 (vmap v))) /\
  (forall v v', PV v -> PV v' -> v <> v' -> vmap v <> vmap v') /\
  (forall e, PE e -> (evalid G1 e <-> evalid G2 (emap e))) /\
  (forall e e', PE e -> PE e' -> e <> e' -> emap e <> emap e') /\
  (forall e, PE e -> vmap (src G1 e) = src G2 (emap e)) /\
  (forall e, PE e -> vmap (dst G1 e) = dst G2 (emap e)).

Definition Homo G1 G2: Type := {f: (V1 -> V2) * (E1 -> E2) | is_homo (fst f) (snd f) G1 G2}.

End GraphMophism0.

Section GraphMophism1.

Context {V1 V2 E1 E2: Type}.
Context {EV1: EqDec V1 eq}.
Context {EE1: EqDec E1 eq}.
Context {EV2: EqDec V2 eq}.
Context {EE2: EqDec E2 eq}.

Definition Iso G1 G2: Type := (Homo G1 G2 * Homo G2 G1)%type.

End GraphMophism1.

Module CopyGraph.

Section CopyGraph.

Class GraphMorphismSetting (DV DE V' E': Type): Type := {
  co_vertex: DV -> V';
  co_edge: DE -> E'
}.

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
  same_morphism (vmap g1) (vmap g2) /\
  same_morphism (emap g1) (emap g2) /\
  g1' ~=~ g2'.

Definition vcopy1 x (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  exists y,
  g1 ~=~ g2 /\
  guarded_same_morphism (Complement _ (eq x)) (vmap g1) (vmap g2) /\
  same_morphism (emap g1) (emap g2) /\
  y = vmap g2 x /\
  vertex_join (eq y) g1' g2'.

Definition ecopy1 e (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  exists e',
  g1 ~=~ g2 /\
  same_morphism (vmap g1) (vmap g2) /\
  guarded_same_morphism (Complement _ (eq e)) (emap g1) (emap g2) /\
  emap g2 e = e' /\
  edge_union (eq e') g1' g2' /\
  vmap g2 (src g2 e) = src g2' e' /\
  vmap g2 (dst g2 e) = dst g2' e'.

Definition copy P (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  guarded_same_morphism (Complement _ P) (vmap g1) (vmap g2) /\
  guarded_same_morphism (Complement _ (std_edge_prop g1 P)) (emap g1) (emap g2) /\
  (forall PV PE,
     guarded_inj (vmap g1) (emap g1) PV PE g1 g1' ->
     guarded_inj (vmap g2) (emap g2) (Union _ PV P) (Union _ PE (std_edge_prop g1 P)) g2 g2').

Definition gcopy (PV: V -> Prop) (PE: E -> Prop) (p1 p2: Graph * Graph') :=
  let (g1, g1') := p1 in
  let (g2, g2') := p2 in
  g1 ~=~ g2 /\
  guarded_same_morphism (Complement _ PV) (vmap g1) (vmap g2) /\
  guarded_same_morphism (Complement _ PE) (emap g1) (emap g2) /\
  (forall PV' PE',
     guarded_inj (vmap g1) (emap g1) PV' PE' g1 g1' ->
     guarded_inj (vmap g2) (emap g2) (Union _ PV' PV) (Union _ PE' PE) g2 g2').

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

Lemma vcopy1_is_gcopy: forall x (p1 p2: Graph * Graph'),
  let (g1, _) := p1 in
  vcopy1 x p1 p2 ->
  gcopy (eq x) (std_edge_prop g1 (eq x)) p1 p2.
Proof.
  intros.
  destruct p1 as [g1 g1'], p2 as [g2 g2'].
  intros.
  destruct H as [y [? [? [? [? ?]]]]].
  split; [| split; [| split]].
  1: auto.
  1: auto.
  1: apply same_morphism_guarded_same_morphism; auto.
  intros.
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

