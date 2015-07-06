Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Lists.List.
Require Import RamifyCoq.Coqlib.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas. Import RamifyCoq.graph.path_lemmas.PathNotation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.

(******************************************

Marked Graph

******************************************)

Class MarkedGraph (Vertex Edge: Type) := {
  pg: PreGraph Vertex Edge;
  marked: NodePred pg
}.

Local Coercion pg : MarkedGraph >-> PreGraph.

Existing Instances pg.
Arguments marked {_} {_} _.


Section MARKED_GRAPH.

  Context {V : Type}.
  Context {E : Type}.
  Notation Gph := (MarkedGraph V E).

  Definition marked_coincide {g1 g2: PreGraph V E} (m1: NodePred g1) (m2: NodePred g2) :=
    forall x, @vvalid _ _ g1 x -> @vvalid _ _ g2 x -> (m1 x <-> m2 x).

  Definition validly_identical (g1 g2: Gph) : Prop :=
    g1 ~=~ g2 /\ marked_coincide (marked g1) (marked g2).
   
  Notation "g1 '-=-' g2" := (validly_identical g1 g2) (at level 1).
   
  Lemma vi_refl: forall (G : Gph), G -=- G.
  Proof. intros; split; [reflexivity |]. repeat intro. reflexivity. Qed.
   
  Lemma vi_sym: forall (G1 G2 : Gph), G1 -=- G2 -> G2 -=- G1.
  Proof.
    intros; destruct H; split; [symmetry; auto |].
    repeat intro.
    symmetry; apply H0; auto.
  Qed.
   
  Lemma vi_trans: forall (G1 G2 G3 : Gph), G1 -=- G2 -> G2 -=- G3 -> G1 -=- G3.
  Proof.
  Arguments vvalid {_} {_} _ _.
    intros; destruct H, H0; split; [rewrite H; auto |].
    repeat intro.
    assert (vvalid G2 x) by (rewrite (proj1 H) in H3; auto).
    rewrite (H1 _ H3 H5).
    auto.
  Arguments vvalid {_} {_} {_} _.
  Qed.
   
  Add Parametric Relation : Gph validly_identical
      reflexivity proved by vi_refl
      symmetry proved by vi_sym
      transitivity proved by vi_trans as vi_equal.

  Definition reachable_sub_markedgraph (G: Gph) x: Gph :=
    Build_MarkedGraph _ _ (reachable_subgraph G x) (marked G).

  Definition unmarked (g: Gph): NodePred g := negateP (marked g).

  Lemma unmarked_spec (g: Gph): forall x, (unmarked g) x <-> ~ (marked g) x.
  Proof. apply negateP_spec. Qed.

  Definition mark1 (g1 : Gph) (n : V) (g2 : Gph) : Prop :=
    structurally_identical g1 g2 /\ @vvalid _ _ g1 n /\ marked g2 n /\
    forall n', n <> n' -> (marked g1 n' <-> marked g2 n').

  Lemma mark1_marked: forall g1 root g2,
                        mark1 g1 root g2 ->
                        forall n, marked g1 n-> marked g2 n.
  Proof.
    intros. destruct H as [? [? [? ?]]].
    destruct (t_eq_dec root n).
    subst. auto. specialize (H3 n n0). tauto.
  Qed.

  (* The first subtle lemma *)
  Lemma mark1_unmarked : forall g1 root g2 n,
    mark1 g1 root g2 ->
    g1 |= root ~o~> n satisfying (unmarked g1) ->
    n = root \/ exists child, edge g1 root child /\ g2 |= child ~o~> n satisfying (unmarked g2).
  Proof.
    intros.
    (* Captain Hammer *)
    rewrite reachable_acyclic in H0.
    destruct H0 as [p [? ?]].
    icase p. exfalso. eapply reachable_by_path_nil; eauto.
    assert (v = root) by (apply reachable_by_path_head in H1; inv H1; trivial). subst v.
    icase p. apply reachable_by_path_foot in H1. inv H1; auto.
    right. exists v.
    change (root :: v :: p) with (path_glue (root :: v :: nil) (v :: p)) in H1.
    apply reachable_by_path_split_glue with (n := v) in H1. 2: red; auto. destruct H1.
    split. destruct H1 as [_ [? _]]. apply valid_path_si with (g2 := g2) in H1. 2: destruct H; trivial.
    simpl in H1. destruct H. rewrite (edge_si g1 g2); tauto.
    exists (v :: p). destruct H2 as [? [? ?]].
    split; trivial.
    destruct H as [? [_ ?]]. split. apply (valid_path_si _ _ g1 g2); auto.
    unfold path_prop in H4 |- *.
    rewrite Forall_forall in H4 |- *.
    intros ? ?. specialize (H4 x H6).
    (* Hammertime! *)
    assert (root <> x). intro. inversion H0. subst. contr.
    destruct H5.
    specialize (H8 x H7). rewrite unmarked_spec in *. tauto.
  Qed.

  (* Not the best name in the world... *)
  Lemma mark1_reverse_unmark: forall g1 root g2,
    mark1 g1 root g2 ->
    forall n1 n2,
      g2 |= n1 ~o~> n2 satisfying (unmarked g2) ->
      g1 |= n1 ~o~> n2 satisfying (unmarked g1).
  Proof.
    intros. destruct H0 as [p [? ?]]. exists p. split; trivial.
    destruct H1. destruct H as [? [? ?]].
    split. rewrite (valid_path_si _ _ g1 g2) by eauto. auto.
    unfold path_prop in H2 |- *.
    rewrite Forall_forall in H2 |- *.
    intros ? ?. specialize (H2 x H5). destruct H4. specialize (H6 x).
    spec H6. intro. subst x. hnf in H3. hnf in H2. apply H2; auto.
    rewrite unmarked_spec in *; tauto.
  Qed.

  Definition mark (g1 : Gph) (root : V) (g2 : Gph) : Prop :=
    structurally_identical g1 g2 /\
    (forall n,  g1 |= root ~o~> n satisfying (unmarked g1) -> marked g2 n) /\
    (forall n, ~g1 |= root ~o~> n satisfying (unmarked g1) -> (marked g1 n <-> marked g2 n)).

  (* Sanity condition 1 *)
  Lemma mark_reachable: forall g1 root g2, mark g1 root g2 -> Included (reachable g1 root) (reachable g2 root).
  Proof.
    repeat intro. destruct H as [? [? ?]].
    hnf in H0 |- *.
    destruct H0 as [p [? [? ?]]]; exists p. split; auto. split; auto. eapply (valid_path_si _ _ g1 g2); eauto.
  Qed.

  Lemma mark_exists: forall (g: Gph) x,
    vvalid x ->
    (forall y, {g |= x ~o~> y satisfying (unmarked g) \/ marked g y} +
               {~ (g |= x ~o~> y satisfying (unmarked g) \/ marked g y)}) ->
    {g': Gph | mark g x g'}.
  Proof.
    intros. destruct ((node_pred_dec (unmarked g)) x).
    + exists (Build_MarkedGraph _ _ g (existT _ (fun y => g |= x ~o~> y satisfying (unmarked g) \/ (marked g) y) X)). split; [| split].
      - simpl. reflexivity.
      - intros; subst; hnf. auto.
      - split; intros; subst; simpl in *; tauto.
    + exists g. split. reflexivity. split; intros.
      - destruct H0 as [path ?]. apply (reachable_by_path_In _ _ _ _ _ _ _ x) in H0.
        hnf in H0. tauto. destruct H0 as [[? _] _]. destruct path; simpl in H0; inversion H0. apply in_eq.
      - reflexivity.
  Qed.
   
  Lemma mark1_exists: forall (g: Gph) x,
                       vvalid x -> {g': Gph | mark1 g x g'}.
  Proof.
    intros. destruct ((node_pred_dec (marked g)) x).
    + exists g. split. reflexivity. split; auto. split; [exact a |]. intros; reflexivity.
    + assert (forall y, {y = x \/ marked g y} + {~ (y = x \/ marked g y)}).
      Focus 1. {
        intros.
        apply sumbool_dec_or.
        + apply t_eq_dec.
        + apply node_pred_dec.
      } Unfocus.
      exists (Build_MarkedGraph _ _ g (existT _ (fun y => y = x \/ marked g y) X)). split; [| split].
      * simpl; reflexivity.
      * auto.
      * split; [simpl; auto |].
        intros; simpl.
        assert (n' <> x) by congruence. tauto.
  Qed.

  Lemma reachable_mark1: forall (g g': Gph) x y z,
                           mark1 g x g' -> (reachable g y z <-> reachable g' y z).
  Proof. intros. destruct H as [? _]. apply (si_reachable _ _ y) in H. destruct H. specialize (H z). specialize (H0 z). tauto. Qed.
   
  Lemma reachable_mark: forall (g g': Gph) x y z,
                          mark g x g' -> (reachable g y z <-> reachable g' y z).
  Proof. intros. destruct H as [? _]. apply (si_reachable _ _ y) in H. destruct H. specialize (H z). specialize (H0 z). tauto. Qed.

  (* The second subtle lemma.  Maybe needs a better name? *)
  Lemma mark_unmarked: forall (g1: Gph) root g2 n1 n2,
                         @vvalid _ _ g1 root ->
                         (forall y, {g1 |= root ~o~> y satisfying (unmarked g1)} +
                                    {~ g1 |= root ~o~> y satisfying (unmarked g1)}) ->
                         mark g1 root g2 ->
                         g1 |= n1 ~o~> n2 satisfying (unmarked g1) ->
                         (g2 |= n1 ~o~> n2 satisfying (unmarked g1)) \/ (marked g2 n2).
  Proof.
    intros until n2. intros HH ENUMC; intros; destruct H0 as [p ?].
    (* This was a very handy LEM. *)
    destruct (exists_list_dec _ p (fun n => g1 |= root ~o~> n satisfying (unmarked g1))) as [?H | ?H].
    1: apply ENUMC.
    + right. destruct H as [_ [? _]]. apply H.
      destruct H1 as [n [? ?]]. apply reachable_by_merge with n; trivial.
      destruct (reachable_by_path_split_in _ _ _ _ _ _ _ _ H0 H1) as [p1 [p2 [? [? ?]]]].
      exists p2. trivial.
    + left. exists p. destruct H0. split; trivial. clear H0.
      destruct H2. destruct H as [? [_ ?]]. split.
      rewrite <- (valid_path_si _ _ g1 g2); auto.
      unfold path_prop in *; rewrite Forall_forall in *.
      intros ? ?. specialize (H2 x H4). specialize (H3 x).
      spec H3. intro. apply H1. exists x. tauto.
      rewrite unmarked_spec in *; tauto.
  Qed.

  Lemma mark_invalid: forall (g1: Gph) root g2,
                         ~ @vvalid _ _ g1 root ->
                         mark g1 root g2 ->
                         g1 -=- g2.
  Proof.
    intros.
    destruct H0 as [? [? ?]].
    split; [auto |].
    intro; intros.
    apply H2.
    intro.
    apply reachable_by_is_reachable in H5.
    apply reachable_head_valid in H5.
    tauto.
  Qed.

  Lemma mark_marked_root: forall (g1: Gph) root g2,
                         marked g1 root ->
                         mark g1 root g2 ->
                         g1 -=- g2.
  Proof.
    intros.
    destruct H0 as [? [? ?]].
    split; [auto |].
    intro; intros.
    apply H2.
    intro.
    rewrite reachable_by_eq_subgraph_reachable in H5.
    apply reachable_head_valid in H5.
    simpl in H5.
    unfold predicate_vvalid in H5.
    rewrite unmarked_spec in H5.
    tauto.
  Qed.

  Require Import Classical.
  Tactic Notation "LEM" constr(v) := (destruct (classic v); auto).

  Lemma mark_marked: forall g1 root g2,
                       mark g1 root g2 ->
                       forall n, marked g1 n-> marked g2 n.
  Proof.
    intros. destruct H as [_ [? ?]]. LEM (g1 |= root ~o~> n satisfying (unmarked g1)).
    specialize (H1 n H2). tauto.
  Qed.

  (* Maybe a better name? *)
  Lemma mark_reverse_unmarked: forall g1 root g2,
                                 mark g1 root g2 ->
                                 forall n1 n2, g2 |= n1 ~o~> n2 satisfying (unmarked g2) -> g1 |= n1 ~o~> n2 satisfying (unmarked g1).
  Proof.
    intros. destruct H0 as [p [? ?]]. exists p. split; trivial. clear H0.
    destruct H as [? [? ?]]. destruct H1.
    split. rewrite (valid_path_si _ _ g1 g2); eauto. clear -H3 H0 H2.
    unfold path_prop in *; rewrite Forall_forall in *.
    intros ? ?. specialize (H3 x H). specialize (H0 x). specialize (H2 x).
    LEM (g1 |= root ~o~> x satisfying (unmarked g1)).
    specialize (H0 H1). clear H2 H1. exfalso.
    hnf in H3. hnf in H0. apply H3. auto.
    specialize (H2 H1).
    rewrite unmarked_spec in *; tauto.
  Qed.

  Inductive mark_list: Gph -> list V -> Gph -> Prop :=
  | mark_list_nil: forall g, mark_list g nil g
  | mark_list_cons: forall g g0 g1 v vs, mark g v g0 -> mark_list g0 vs g1 -> mark_list g (v :: vs) g1
  .

  Lemma mark_mark1_mark: forall (g1: Gph) root l g2 g3
                           (R_DEC: forall x, In x l -> forall y, {g1 |= x ~o~> y satisfying (unmarked g1)} +
                                                                 {~ g1 |= x ~o~> y satisfying (unmarked g1)}),
                           vvalid root -> (unmarked g1) root ->
                           edge_list g1 root l ->
                           mark1 g1 root g2 ->
                           mark_list g2 l g3 ->
                           mark g1 root g3.
  Proof.
    intros. split; [|split]; intros.
    + transitivity g2.
      - destruct H2; auto.
      - clear H0 H1 R_DEC H H2. induction H3. reflexivity. rewrite <- IHmark_list. destruct H. auto.
    + admit.
    + assert ((marked g1) n <-> (marked g2) n). {
        destruct H2 as [? [? [? ?]]].
        apply H7. intro. apply H4. subst. exists (n :: nil).
        split; split; simpl; auto.
        hnf. apply Forall_cons. auto. apply Forall_nil.
      } rewrite H5.
      clear R_DEC H H1 H2 H5. induction H3. tauto. rewrite <- IHmark_list.
      destruct H as [? [? ?]]. apply H2.
  Admitted.

  Lemma mark_func: forall g root g1 g2,
    vvalid root ->
    mark g root g1 ->
    mark g root g2 ->
    g1 -=- g2.
  Proof.
    intros.
    split.
    + destruct H0, H1.
      rewrite <- H0; auto.
    + intro; intros.
  Abort.

(*
  (* Here is where we specialize to bigraphs, at least at root *)
  Definition node_connected_two (g : Gph) (root left right : V) : Prop :=
    edge g root left /\ edge g root right /\ forall n', edge g root n' -> n' = left \/ n' = right.

  Lemma node_connected_two_eq:
    forall (g1 g2 : Gph) root l r, g1 ~=~ g2 -> node_connected_two g1 root l r -> node_connected_two g2 root l r.
  Proof.
    intros. pose proof H; destruct H. pose proof (H root); pose proof (H l); pose proof (H r).
    destruct H0 as [? [? ?]].
    split; [| split].
    + rewrite <- (edge_si g1 g2) by auto; auto.
    + rewrite <- (edge_si g1 g2) by auto; auto.
    + intros.
      rewrite <- (edge_si g1 g2) in H8; auto.
  Qed.

  Ltac break_unmark :=
    match goal with
    | [H1: mark1 ?g1 ?root _, H2: (@pg _ _ ?g1) |= ?root ~o~> _ satisfying (app_node_pred (unmarked _)) |- _] =>
      destruct (mark1_unmarked _ _ _ _ H1 H2)
    | [H1: mark ?g1 _ _, H2: (@pg _ _ ?g1) |= _ ~o~> _ satisfying (app_node_pred (unmarked _)) |- _] =>
      destruct (mark_unmarked _ _ _ _ _ H1 H2)
    end.


  Lemma root_neq: forall g1 g2 root n, mark1 g1 root g2 -> unmarked g1 root ->
                                       (~ g1 |= root ~o~> n satisfying (unmarked g1)) -> root <> n.
  Proof. repeat intro; subst; apply H1. apply reachable_by_reflexive; split; auto. destruct H as [? [? [? ?]]]; auto. Qed.

  Ltac structure_id_3 :=
    match goal with
      | [H1 : mark1 ?g1 _ ?g2, H2 : mark ?g2 _ ?g3, H3 : mark ?g3 _ ?g4 |- (@pg _ _ ?g1) ~=~ (@pg _ _ ?g4)]
        => destruct H1, H2, H3; apply (si_trans _ _ _ H1); apply (si_trans _ _ _ H2); auto
      | [H1 : mark ?g1 _ ?g2, H2 : mark1 ?g2 _ ?g3, H3 : mark ?g3 _ ?g4 |- @pg _ _ ?g1 ~=~ @pg _ _ ?g4]
        => destruct H1, H2, H3; apply (si_trans _ _ _ H1); apply (si_trans _ _ _ H2); auto
      | [H1 : mark ?g1 _ ?g2, H2 : mark ?g2 _ ?g3, H3 : mark1 ?g3 _ ?g4 |- @pg _ _ ?g1 ~=~ @pg _ _ ?g4]
        => destruct H1, H2, H3; apply (si_trans _ _ _ H1); apply (si_trans _ _ _ H2); auto
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
      | [H : mark1 ?g' _ ?g |- app_node_pred (marked ?g) _] => eapply (mark1_marked g' _ g H); eauto
      | [H : mark ?g' _ ?g |- app_node_pred (marked ?g) _] => apply (mark_marked g' _ g H); eauto
    end.

  Lemma mark_root_left_right: forall g1 g2 g3 g4 root left right,
                                unmarked g1 root -> node_connected_two g1 root left right ->
                                mark1 g1 root g2 -> mark g2 left g3 -> mark g3 right g4 -> mark g1 root g4.
  Proof.
    split; [structure_id_3 |].
    split; intros.
    + break_unmark.
      - subst. do 2 node_mark. hnf in H1. tauto.
      - destruct H5 as [x [? ?]]. destruct H0 as [? [? ?]].
        apply H8 in H5. destruct H5; subst.
        * node_mark. destruct H2 as [? [? ?]]. auto.
        * clear H4.
Print mark_unmarked.
match goal with
   | [H1: mark ?g1 _ _, H2: (@pg _ _ ?g1) |= _ ~o~> _ satisfying (app_node_pred (unmarked _)) |- _] =>
      destruct (mark_unmarked _ _ _ _ _ H1 H2)
end.

 break_unmark.
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
*)
End MARKED_GRAPH.

Notation "g1 '-=-' g2" := (validly_identical g1 g2) (at level 1).