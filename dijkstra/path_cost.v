Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.path_lemmas.
(* Require Import CertiGraph.graph.AdjMatGraph_new. *)
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Import CertiGraph.dijkstra.SpaceDijkGraph.

Local Open Scope logic.
Local Open Scope Z_scope.

Definition path_cost inf size (g : (DijkGG inf size)) (path : @path V E) : DE :=
  fold_left Z.add (map (elabel g) (snd path)) 0.

Lemma one_step_path_Znth:
  forall inf size (g: (DijkGG inf size)) s e,
    path_cost inf size g (s, e :: nil) =
    elabel g e.
Proof.
  intros. unfold path_cost; simpl.
  apply Z.add_0_l.
Qed.

Lemma acc_pos: forall inf size (g : (DijkGG inf size)) l z,
    (forall e : E, In e l -> 0 <= elabel g e) ->
    0 <= z ->
    0 <= fold_left Z.add (map (elabel g) l) z.
Proof.
  intro. induction l; intros; simpl; auto. apply IHl.
  - intros. apply H. now apply in_cons.
  - assert (In a (a :: l)) by apply in_eq.
    specialize (H _ H1). lia.
Qed.

Lemma path_cost_pos:
  forall inf size (g: (DijkGG inf size)) p,
    valid_path g p ->
    0 <= path_cost inf size g p.
Proof.
  intros. apply acc_pos; [|lia].
  intros. apply edge_cost_pos.
Qed.

Lemma path_cost_init:
  forall l init s,
    fold_left Z.add l (init + s) =
    init + (fold_left Z.add l s).
Proof.
  intros.
  generalize dependent s.
  induction l.
  - intros; simpl. trivial. 
  - intros; simpl.
    rewrite <- Z.add_assoc.
    rewrite IHl. lia.
Qed.

Lemma path_cost_path_glue:
  forall inf size (g: (DijkGG inf size)) p1 p2,
    path_cost inf size g (path_glue p1 p2) =
    path_cost inf size g p1 + path_cost inf size g p2.
Proof.
  intros.
  unfold path_cost at 1, path_glue at 1.
  simpl. rewrite map_app.
  rewrite fold_left_app.
  assert ((fold_left Z.add (map (elabel g) (snd p1)) 0) = (path_cost inf size g p1))
    by now unfold path_cost.
  unfold DE in *.
  rewrite H. 
  unfold path_cost at 3.
  remember (map (elabel g) (snd p2)) as l2.
  unfold DE in *.
  rewrite <- Heql2.
  remember (path_cost inf size g p1) as c1.
  replace c1 with (c1 + 0) at 1 by lia.
  rewrite path_cost_init; trivial.
Qed.

Lemma path_cost_app_cons:
  forall inf size (g: (DijkGG inf size)) path e,
    path_cost inf size g (fst path, snd path +:: e) =
    path_cost inf size g path + elabel g e.
Proof.
  intros.
  replace (fst path, snd path +:: e) with
      (path_glue path (fst e, [e])).
  rewrite path_cost_path_glue.
  rewrite one_step_path_Znth; trivial.
  unfold path_glue. simpl. trivial.
Qed.

Lemma path_cost_path_glue_lt:
  forall inf size (g: (DijkGG inf size)) p1 p2 limit,
    valid_path g p1 ->
    valid_path g p2 ->
    path_cost inf size g (path_glue p1 p2) < limit ->
    path_cost inf size g p1 < limit /\ path_cost inf size g p2 < limit.
Proof.
  intros.
  rewrite path_cost_path_glue in H1.
  pose proof (path_cost_pos _ _ _ _ H).
  pose proof (path_cost_pos _ _ _ _ H0).
  split; lia.
Qed.
