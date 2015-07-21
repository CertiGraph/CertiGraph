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

Section SIMPLE_MARK_GRAPH.

  Context {V : Type}.
  Context {E : Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.
  Context (g: PreGraph V E).

(*
  Definition reachable_sub_markedgraph (G: Gph) x: Gph :=
    Build_MarkedGraph _ _ (reachable_subgraph G x) (marked G).

  Definition unmarked (g: Gph): NodePred g := negateP (marked g).

  Lemma unmarked_spec (g: Gph): forall x, (unmarked g) x <-> ~ (marked g) x.
  Proof. apply negateP_spec. Qed.
*)
  Definition mark1 (m1 : NodePred V) (n : V) (m2 : NodePred V) : Prop :=
    vvalid g n /\ m2 n /\ forall n', n <> n' -> (m1 n' <-> m2 n').

  Lemma mark1_marked: forall m1 root m2,
                        mark1 m1 root m2 ->
                        forall n, m1 n-> m2 n.
  Proof.
    intros. destruct H as [? [? ?]].
    destruct_eq_dec root n.
    subst. auto. specialize (H2 n H3). tauto.
  Qed.

  (* The first subtle lemma *)
  Lemma mark1_unmarked : forall m1 root m2 n,
    mark1 m1 root m2 ->
    g |= root ~o~> n satisfying (negateP m1) ->
    n = root \/ exists child, edge g root child /\ g |= child ~o~> n satisfying (negateP m2).
  Proof.
    intros.
    (* Captain Hammer *)
    rewrite reachable_acyclic in H0.
    destruct H0 as [p [? ?]].
    icase p. exfalso. eapply (reachable_by_path_nil g); eauto.
    assert (v = root) by (apply reachable_by_path_head in H1; inv H1; trivial). subst v.
    icase p. apply reachable_by_path_foot in H1. inv H1; auto.
    right. exists v.
    change (root :: v :: p) with (path_glue (root :: v :: nil) (v :: p)) in H1.
    apply (reachable_by_path_split_glue g) with (n := v) in H1. 2: red; auto. destruct H1.
    split. destruct H1 as [_ [? _]]. apply valid_path_si with (g2 := g) in H1. 2: destruct H; trivial.
    simpl in H1. destruct H. tauto. reflexivity.
    exists (v :: p). destruct H2 as [? [? ?]].
    split; trivial.
    destruct H as [? [_ ?]]. split. auto.
    unfold path_prop in H4 |- *.
    rewrite Forall_forall in H4 |- *.
    intros ? ?. specialize (H4 x H6).
    (* Hammertime! *)
    assert (root <> x). intro. inversion H0. subst. contr.
    specialize (H5 x H7). rewrite negateP_spec in H4 |- *. tauto.
  Qed.

  (* Not the best name in the world... *)
  Lemma mark1_reverse_unmark: forall m1 root m2,
    mark1 m1 root m2 ->
    forall n1 n2,
      g |= n1 ~o~> n2 satisfying (negateP m2) ->
      g |= n1 ~o~> n2 satisfying (negateP m1).
  Proof.
    intros. destruct H0 as [p [? ?]]. exists p. split; trivial.
    destruct H1. destruct H as [? [? ?]].
    split. auto.
    unfold path_prop in H2 |- *.
    rewrite Forall_forall in H2 |- *.
    intros ? ?. specialize (H2 x H5). specialize (H4 x).
    spec H4. intro. subst x. hnf in H3. hnf in H2. apply H2; auto.
    rewrite negateP_spec in H2 |- *; tauto.
  Qed.

  Definition mark (m1 : NodePred V) (root : V) (m2 : NodePred V) : Prop :=
    (forall n,  g |= root ~o~> n satisfying (negateP m1) -> m2 n) /\
    (forall n, ~g |= root ~o~> n satisfying (negateP m1) -> (m1 n <-> m2 n)).

  Lemma mark_exists: forall m x,
    vvalid g x ->
    (forall y, {g |= x ~o~> y satisfying (negateP m)} +
               {~ (g |= x ~o~> y satisfying (negateP m))}) ->
    {m': NodePred V | mark m x m'}.
  Proof.
    intros. destruct ((node_pred_dec (negateP m)) x).
    + exists (existT (fun P => forall x, {P x} + {~ P x})
                     (fun y => g |= x ~o~> y satisfying (negateP m) \/ (m) y)
                     (fun y => sumbool_dec_or (X y) (node_pred_dec (m) y))).
      split.
      - intros; subst; hnf. auto.
      - split; intros; subst; simpl in *; tauto.
    + exists (m). split; intros.
      - destruct H0 as [path ?].
        apply (reachable_by_path_In g _ _ _ _ x) in H0.
        hnf in H0. tauto. destruct H0 as [[? _] _]. destruct path; simpl in H0; inversion H0. apply in_eq.
      - reflexivity.
  Qed.
   
  Lemma mark1_exists: forall m x, vvalid g x -> {m': NodePred V | mark1 m x m'}.
  Proof.
    intros. destruct ((node_pred_dec m) x).
    + exists m. split; auto. split; [exact a |]. intros; reflexivity.
    + assert (forall y, {y = x \/ m y} + {~ (y = x \/ m y)}).
      Focus 1. {
        intros.
        apply sumbool_dec_or.
        + apply equiv_dec.
        + apply node_pred_dec.
      } Unfocus.
      exists (existT _ (fun y => y = x \/ m y) X). split.
      * auto.
      * split; [simpl; auto |].
        intros; simpl.
        assert (n' <> x) by congruence. tauto.
  Qed.

  (* The second subtle lemma.  Maybe needs a better name? *)
  Lemma mark_unmarked: forall m1 root m2 n1 n2,
                         vvalid g root ->
                         (forall y, {g |= root ~o~> y satisfying (negateP m1)} +
                                    {~ g |= root ~o~> y satisfying (negateP m1)}) ->
                         mark m1 root m2 ->
                         g |= n1 ~o~> n2 satisfying (negateP m1) ->
                         (g |= n1 ~o~> n2 satisfying (negateP m2)) \/ (m2 n2).
  Proof.
    intros until n2. intros HH ENUMC; intros. destruct H0 as [p ?].
    (* This was a very handy LEM. *)
    destruct (exists_list_dec _ p (fun n => g |= root ~o~> n satisfying (negateP m1))) as [?H | ?H].
    1: apply ENUMC.
    + right. destruct H as [? _]. apply H.
      destruct H1 as [n [? ?]]. apply reachable_by_merge with n; trivial.
      destruct (reachable_by_path_split_in g _ _ _ _ _ H0 H1) as [p1 [p2 [? [? ?]]]].
      exists p2. trivial.
    + left. exists p. destruct H0. split; trivial. clear H0.
      destruct H2. destruct H as [_ ?]. split; auto.
      unfold path_prop in *; rewrite Forall_forall in *.
      intros ? ?. specialize (H2 x H3). specialize (H x).
      spec H. intro. apply H1. exists x. tauto.
      rewrite negateP_spec in H2 |- *; tauto.
  Qed.

  Lemma mark_unmarked_strong: forall m1 root m2 n1 n2,
                                vvalid g root ->
                                ReachDecidable g root (negateP m1) ->
                                mark m1 root m2 ->
                                g |= n1 ~o~> n2 satisfying (negateP m1) ->
                                Decidable (g |= n1 ~o~> n2 satisfying (negateP m2)).
  Proof.
    intros.
    pose proof mark_unmarked _ _ _ _ _ H X H0 H1.
    destruct (node_pred_dec (m2) n2); [| left; tauto].
    right.
    intro.
    rewrite reachable_by_eq_subgraph_reachable in H3.
    apply reachable_foot_valid in H3.
    simpl in H3.
    destruct H3.
    rewrite negateP_spec in H4; tauto.
  Qed.

  Lemma mark_invalid: forall m1 root m2,
                         ~ vvalid g root ->
                         mark m1 root m2 ->
                         vertex_prop_coincide g g m1 m2.
  Proof.
    intros.
    destruct H0 as [? ?].
    intro; intros.
    apply H1.
    intro.
    apply reachable_by_is_reachable in H4.
    apply reachable_head_valid in H4.
    tauto.
  Qed.

  Lemma mark_invalid_refl: forall m root,
                         ~ vvalid g root ->
                         mark m root m.
  Proof.
    intros.
    split.
    + intros.
      apply reachable_by_is_reachable in H0.
      apply reachable_head_valid in H0.
      tauto.
    + intros.
      reflexivity.
  Qed.

  Lemma mark_marked_root: forall (m1: NodePred V) root m2,
                         m1 root ->
                         mark m1 root m2 ->
                         vertex_prop_coincide g g m1 m2.
  Proof.
    intros.
    destruct H0 as [? ?].
    intro; intros.
    apply H1.
    intro.
    rewrite reachable_by_eq_subgraph_reachable in H4.
    apply reachable_head_valid in H4.
    simpl in H4.
    unfold predicate_vvalid in H4.
    rewrite negateP_spec in H4.
    tauto.
  Qed.

  Lemma mark_marked: forall m1 root m2,
                       mark m1 root m2 ->
                       ReachDecidable g root (negateP m1) ->
                       forall n, m1 n -> m2 n.
  Proof.
    intros. destruct H as [? ?].
    destruct (X n). auto. specialize (H1 n n0). tauto.
  Qed.

  (* Maybe a better name? *)
  Lemma mark_reverse_unmarked: forall m1 root m2,
                                 mark m1 root m2 ->
                                 forall n1 n2,
                                 ReachDecidable g root (negateP m1) ->
                                 g |= n1 ~o~> n2 satisfying (negateP m2) ->
                                 g |= n1 ~o~> n2 satisfying (negateP m1).
  Proof.
    intros.
    destruct H as [? ?].
    destruct H0 as [p [? ?]]; exists p.
    split; [auto |].
    destruct H2; split; [auto |].
    unfold path_prop in *; rewrite Forall_forall in *.
    intros ? ?.
    destruct (X x) as [?H | ?H].
    + clear - H5.
      destruct H5 as [p [? [? ?]]].
      unfold path_prop in H1.
      rewrite Forall_forall in H1.
      apply H1.
      inversion H.
      apply foot_in; auto.
    + specialize (H1 _ H5).
      specialize (H3 x). spec H3; [auto |].
      rewrite negateP_spec in H3 |- *; tauto.
  Qed.

  Inductive mark_list: NodePred V -> list V -> NodePred V -> Prop :=
  | mark_list_nil: forall m, mark_list m nil m
  | mark_list_cons: forall m m0 m1 v vs, mark m v m0 -> mark_list m0 vs m1 -> mark_list m (v :: vs) m1
  .

  Lemma mark_preserved_reach_decidable: forall m1 root m2 x,
    vvalid g root ->
    ReachDecidable g x (negateP m1) ->
    ReachDecidable g root (negateP m1) ->
    mark m1 root m2 ->
    ReachDecidable g x (negateP m2).
  Proof.
    intros. intro. destruct (X y).
    + apply (mark_unmarked_strong m1 root); auto.
    + right. intro. apply n. apply (mark_reverse_unmarked _ root m2); auto.
  Qed.

  Lemma ind_RV_DEC: forall (P: NodePred V -> list V -> NodePred V -> Prop),
    (forall m, P m nil m) ->
    (forall m v m' l m'',
      P m' l m'' ->
      forall 
        (R_DEC: forall x, In x (v :: l) -> ReachDecidable g x (negateP m))
        (V_DEC: forall x, In x (v :: l) -> Decidable (vvalid g x)),
      mark m v m' ->
      mark_list m' l m'' ->
      P m (v :: l) m'') ->
    (forall m l m',
      (forall x, In x l -> ReachDecidable g x (negateP m)) ->
      (forall x, In x l -> Decidable (vvalid g x)) ->
      mark_list m l m' ->
      P m l m').
  Proof.
    intros P H_nil IH m l m' R_DEC V_DEC ?.
    induction H.
    + apply H_nil.
    + apply (IH m v m0 vs m1); auto.
      apply IHmark_list.
      - destruct (V_DEC v (or_introl eq_refl)) as [?H | ?H].
        * intros.
          apply (mark_preserved_reach_decidable m v); auto.
          1: apply R_DEC; right; auto.
          1: apply R_DEC; left; auto.
        * pose proof mark_invalid m v m0 H1 H.
          intros.
          apply (ReachDecidable_si g g (negateP m)); [reflexivity | | apply R_DEC; right; auto].
          unfold vertex_prop_coincide in *; clear - H2.
          intros; specialize (H2 x); do 2 (spec H2; [auto |]).
          rewrite !negateP_spec; tauto.
      - intros; apply V_DEC; right; auto.
  Qed.

  Lemma mark_list_marked: forall m1 l m2
    (R_DEC: forall x, In x l -> ReachDecidable g x (negateP m1))
    (V_DEC: forall x, In x l -> Decidable (vvalid g x)),
    mark_list m1 l m2 ->
    forall n : V, m1 n -> m2 n.
  Proof.
    apply (ind_RV_DEC (fun m1 l m2 => forall n : V, m1 n -> m2 n)).
    + intros; auto.
    + intros.
      apply H.
      apply (mark_marked m v m'); auto.
      apply R_DEC; left; auto.
  Qed.
  
  Lemma mark_list_get_marked: forall m1 l m2
    (R_DEC: forall x, In x l -> ReachDecidable g x (negateP m1))
    (V_DEC: forall x, In x l -> Decidable (vvalid g x)),
    mark_list m1 l m2 ->
    forall z n,
    In z l ->
    g |= z ~o~> n satisfying (negateP m1) ->
    m2 n.
  Proof.
    apply (ind_RV_DEC (fun m1 l m2 =>
            forall z n : V, In z l -> g |= z ~o~> n satisfying (negateP m1) -> m2 n)).
    + intros.
      inversion H.
    + intros.
      destruct H2.
      - subst z. apply (mark_list_marked m' l m''); auto.
        * intros.
          apply (mark_preserved_reach_decidable m v m'); auto.
          1: apply reachable_by_is_reachable in H3; apply reachable_head_valid in H3; auto.
          1: apply R_DEC; right; auto.
          1: apply R_DEC; left; auto.
        * intros; apply V_DEC; right; auto.
        * destruct H0 as [? _]; auto.
      - destruct (V_DEC v (or_introl eq_refl)).
        Focus 1. {
          apply (mark_unmarked m v m') in H3; auto; [| apply R_DEC; left; auto].
          destruct H3.
          + apply (H z); auto.
          + apply (mark_list_marked m' l); auto.
            - intros.
              apply (mark_preserved_reach_decidable m v m'); auto.
              * apply R_DEC; right; auto.
              * apply R_DEC; left; auto.
            - intros; apply V_DEC; right; auto.
        } Unfocus.
        Focus 1. {
          pose proof (mark_invalid m v m' n0 H0).
          apply (H z); auto.
          erewrite si_reachable_by in H3; [exact H3 | reflexivity |].
          unfold vertex_prop_coincide in *; clear - H4.
          intros.
          specialize (H4 x); do 2 (spec H4; [auto |]).
          rewrite !negateP_spec.
          tauto.
        } Unfocus.
  Qed.

  Lemma mark_list_preserve_marked: forall m1 l m2
    (R_DEC: forall x, In x l -> ReachDecidable g x (negateP m1))
    (V_DEC: forall x, In x l -> Decidable (vvalid g x)),
    mark_list m1 l m2 ->
    forall n,
    (forall x, In x l -> ~ g |= x ~o~> n satisfying (negateP m1)) ->
    (m1 n <-> m2 n).
  Proof.
    apply (ind_RV_DEC (fun m1 l m2 =>
            forall n,
           (forall x, In x l -> ~ g |= x ~o~> n satisfying (negateP m1)) ->
           (m1 n <-> m2 n))).
    + intros; reflexivity.
    + intros.
      rewrite <- H.
      - destruct H0 as [_ ?].
        apply H0, H2.
        left; auto.
      - intros.
        intro.
        apply (mark_reverse_unmarked m v m') in H4; [| auto | apply R_DEC; left; auto].
        apply (H2 x); auto.
        right; auto.
  Qed.

  Lemma mark_mark1_mark: forall m1 root l m2 m3
    (R_DEC: forall x, In x l -> ReachDecidable g x (negateP m2))
    (V_DEC: forall x, In x l -> Decidable (vvalid g x)),
    vvalid g root -> (negateP m1) root ->
    step_list g root l ->
    mark1 m1 root m2 ->
    mark_list m2 l m3 ->
    mark m1 root m3.
  Proof.
    intros. split; intros.
    + apply (mark1_unmarked _ _ _ _ H2) in H4. destruct H4.
      - subst n. destruct H2 as [_ [? _]].
        eapply mark_list_marked; eauto.
      - destruct H4 as [z [? ?]]. unfold edge in H4; rewrite <- (H1 z) in H4. destruct H4 as [_ [_ ?]].
        eapply mark_list_get_marked; eauto.
    + assert (m1 n <-> m2 n). {
        destruct H2 as [? [? ?]].
        apply H6. intro. apply H4. subst. exists (n :: nil).
        split; split; simpl; auto.
        hnf. apply Forall_cons. auto. apply Forall_nil.
      } rewrite H5.
      assert (forall x, In x l -> ~ g |= x ~o~> n satisfying (negateP m2)). {
        intros. intro.
        destruct (V_DEC x H6).
        + apply (mark1_reverse_unmark m1 root) in H7; auto.
          apply H4. apply H1 in H6.
          apply reachable_by_cons with x; auto.
          unfold edge; auto.
        + apply reachable_by_is_reachable in H7.
          apply reachable_head_valid in H7; tauto.
      }
      eapply mark_list_preserve_marked; eauto.
  Qed.

  Lemma mark_func: forall m root m1 m2 (R_DEC: ReachDecidable g root (negateP m)),
                     mark m root m1 ->
                     mark m root m2 ->
                     vertex_prop_coincide g g m1 m2.
  Proof.
    intros.
    intro; intros.
    destruct H as [? ?].
    destruct H0 as [? ?].
    destruct (R_DEC x).
    - specialize (H x r). specialize (H0 x r). tauto.
    - specialize (H3 x n). specialize (H4 x n). tauto.
  Qed.

  Lemma mark1_mark_list_vi: forall m1 root l m2 m3 m4
                                   (R_DEC: forall x, In x l -> ReachDecidable g x (negateP m2))
                                   (V_DEC: forall x, In x l -> Decidable (vvalid g x))
                                   (R_DEC': ReachDecidable g root (negateP m1)),
                              vvalid g root -> (negateP m1) root ->
                              step_list g root l ->
                              mark1 m1 root m2 ->
                              mark_list m2 l m3 ->
                              mark m1 root m4 ->
                              vertex_prop_coincide g g m3 m4.
  Proof.
    intros. assert (mark m1 root m3).
    apply (mark_mark1_mark _ _ l m2); auto.
    apply (mark_func m1 root); auto.
  Qed.

(*

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
End SIMPLE_MARK_GRAPH.

Module MarkGraph.

Section MarkGraph.

Context {V : Type}.
Context {E : Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Class MarkGraphSetting 

Class MarkedGraph (Vertex Edge: Type) := {
  pg: PreGraph Vertex Edge;
  marked: NodePred pg
}.

Local Coercion pg : MarkedGraph >-> PreGraph.

Existing Instances pg.
Arguments marked {_} {_} _.


