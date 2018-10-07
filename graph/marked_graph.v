Require Import Coq.Logic.ProofIrrelevance.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas. Import RamifyCoq.graph.path_lemmas.PathNotation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.

Module SIMPLE_MARK_GRAPH.
Section SIMPLE_MARK_GRAPH.

  Context {V : Type}.
  Context {E : Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.

  Section SINGLE_GRAPH_LEM.

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

  Definition mark (m1 : NodePred V) (root : V) (m2 : NodePred V) : Prop :=
    (forall n,  g |= root ~o~> n satisfying (negateP m1) -> m2 n) /\
    (forall n, ~g |= root ~o~> n satisfying (negateP m1) -> (m1 n <-> m2 n)).

  Inductive mark_list: NodePred V -> list V -> NodePred V -> Prop :=
  | mark_list_nil: forall m m0, (m ~=~ m0)%NodePred -> mark_list m nil m0
  | mark_list_cons: forall m m0 m1 v vs, mark m v m0 -> mark_list m0 vs m1 -> mark_list m (v :: vs) m1
  .

  Lemma mark1_marked: forall m1 root m2,
                        mark1 m1 root m2 ->
                        forall n, m1 n -> m2 n.
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
    intros. rewrite reachable_acyclic in H0. destruct H0 as [p [? ?]]. destruct p as [v p].
    assert (v = root) by (destruct H1 as [[? _] _]; simpl in H1; auto). subst v. destruct p.
    + left. destruct H1 as [[? ?] _]. simpl in H2. auto.
    + right. exists (dst g e). change (root, e :: p) with (path_glue (root, e :: nil) (dst g e, p)) in H1.
      apply (reachable_by_path_split_glue g) with (n := dst g e) in H1. 2: red; simpl; auto.
      destruct H1. split.
      - destruct H1 as [_ [[? [? [? ?]]] _]]. hnf. subst root. rewrite step_spec. do 2 (split; auto). exists e; auto.
      - exists (dst g e, p). destruct H2 as [? [? ?]]. split; [|split]; auto.
        rewrite path_prop_equiv in H4 |-* ; auto. rewrite epath_to_vpath_cons_eq in H0. 2: destruct H1 as [_ [[? _] _]]; auto.
        apply NoDup_cons_2 in H0. rewrite in_path_eq_epath_to_vpath in H0; auto. intros. specialize (H4 _ H5).
        destruct H as [? [? ?]]. rewrite negateP_spec in H4 |- *. rewrite <- H7; auto.
        intro. apply H0. subst; auto.
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
    rewrite path_prop_equiv in H2 |- *; auto.
    intros. specialize (H2 _ H5). specialize (H4 n).
    spec H4. intro. subst n. hnf in H3. hnf in H2. apply H2; auto.
    rewrite negateP_spec in H2 |- *; tauto.
  Qed.

  Lemma mark_exists: forall m x,
    vvalid g x ->
    ReachDecidable g x (negateP m) ->
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
        hnf in H0. tauto. destruct H0 as [[? _] _]. destruct path; simpl in H0; inversion H0. hnf; left; auto.
      - reflexivity.
  Qed.

  Lemma mark1_exists: forall m x, vvalid g x -> {m': NodePred V | mark1 m x m'}.
  Proof.
    intros. destruct ((node_pred_dec m) x).
    + exists m. split; auto. split; [exact a |]. intros; reflexivity.
    + assert (forall y, {y = x \/ m y} + {~ (y = x \/ m y)}).
      1: {
        intros.
        apply sumbool_dec_or.
        + apply equiv_dec.
        + apply node_pred_dec.
      }
      exists (existT _ (fun y => y = x \/ m y) X). split.
      * auto.
      * split; [simpl; auto |].
        intros; simpl.
        assert (n' <> x) by congruence. tauto.
  Qed.

  (* The second subtle lemma.  Maybe needs a better name? *)
  Lemma mark_unmarked: forall m1 root m2 n1 n2,
                         vvalid g root ->
                         ReachDecidable g root (negateP m1)->
                         mark m1 root m2 ->
                         g |= n1 ~o~> n2 satisfying (negateP m1) ->
                         (g |= n1 ~o~> n2 satisfying (negateP m2)) \/ (m2 n2).
  Proof.
    intros until n2. intros HH ENUMC; intros. destruct H0 as [p ?].
    (* This was a very handy LEM. *)
    destruct (exists_list_dec _ (epath_to_vpath g p) (fun n => g |= root ~o~> n satisfying (negateP m1))) as [?H | ?H].
    1: apply ENUMC.
    + right. destruct H as [? _]. apply H.
      destruct H1 as [n [? ?]]. apply reachable_by_trans with n; trivial.
      rewrite in_path_eq_epath_to_vpath in H1. 2: destruct H0 as [_ [? _]]; auto.
      destruct (reachable_by_path_split_in g _ _ _ _ _ H0 H1) as [p1 [p2 [? [? ?]]]].
      exists p2. trivial.
    + left. exists p. destruct H0. split; trivial. clear H0.
      destruct H2. destruct H as [_ ?]. split; auto.
      rewrite path_prop_equiv in H2 |-* ; auto.
      intros x ?. specialize (H2 x H3). specialize (H x).
      spec H. intro. apply H1. exists x. rewrite in_path_eq_epath_to_vpath; auto.
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
                         (m1 ~=~ m2)%NodePred.
  Proof.
    intros.
    destruct H0 as [? ?].
    intro; intros.
    apply H1.
    intro.
    apply reachable_by_head_valid in H2.
    tauto.
  Qed.

  Lemma mark_invalid_refl: forall m root,
                         ~ vvalid g root ->
                         mark m root m.
  Proof.
    intros.
    split.
    + intros.
      apply reachable_by_head_valid in H0.
      tauto.
    + intros.
      reflexivity.
  Qed.

  Lemma mark_marked_root: forall (m1: NodePred V) root m2,
                         m1 root ->
                         mark m1 root m2 ->
                         (m1 ~=~ m2)%NodePred.
  Proof.
    intros.
    destruct H0 as [? ?].
    intro; intros.
    apply H1.
    intro.
    rewrite reachable_by_eq_subgraph_reachable in H2.
    apply reachable_head_valid in H2.
    simpl in H2.
    unfold predicate_vvalid in H2.
    rewrite negateP_spec in H2.
    tauto.
  Qed.

  Lemma mark_marked_root_refl: forall (m: NodePred V) root,
                         m root ->
                         mark m root m.
  Proof.
    intros.
    split.
    + intros.
      apply reachable_by_head_prop in H0.
      rewrite negateP_spec in H0.
      tauto.
    + intros.
      reflexivity.
  Qed.

  Lemma mark_marked: forall m1 root m2,
                       mark m1 root m2 ->
                       ReachDecidable g root (negateP m1) ->
                       forall n, m1 n -> m2 n.
  Proof.
    intros. destruct H as [? ?].
    destruct (X n). auto. specialize (H1 n n0). tauto.
  Qed.

  Lemma mark_marked_strong:
    forall m1 root m2 n,
      mark m1 root m2 ->
      ReachDecidable g root (negateP m1) ->
      g |= root ~o~> n satisfying (negateP m1) \/ m1 n ->
      m2 n.
  Proof.
    intros.
    destruct H0; [| eapply mark_marked; eauto].
    destruct H.
    eapply H; eauto.
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
    eapply reachable_by_weaken; [| eauto].
    change (@app_node_pred _ (negateP m2)) with (Complement _ (projT1 m2)).
    change (@app_node_pred _ (negateP m1)) with (Complement _ (projT1 m1)).
    apply Complement_Included_rev.
    intro; apply mark_marked with (root := root); auto.
  Qed.

  Lemma mark_reverse_unmarked_strong:
    forall m1 root m2,
      mark m1 root m2 ->
      forall n1 n2,
      ReachDecidable g root (negateP m1) ->
      g |= n1 ~o~> n2 satisfying (negateP m2) ->
      (predicate_partialgraph g (Complement _ (reachable_by g root (negateP m1)))) |= n1 ~o~> n2 satisfying (negateP m1).
  Proof.
    intros.
    rewrite reachable_by_eq_partialgraph_reachable.
    rewrite partial_partialgraph.
    rewrite <- reachable_by_eq_partialgraph_reachable.
    eapply reachable_by_weaken; [| eauto].
    change (@app_node_pred _ (negateP m2)) with (Complement _ (projT1 m2)).
    change (@app_node_pred _ (negateP m1)) with (Complement _ (projT1 m1)).
    rewrite Intersection_Complement.
    apply Complement_Included_rev.
    intro x; unfold Ensembles.In.
    rewrite Union_spec.
    apply mark_marked_strong; auto.
  Qed.

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
    (forall m m', (m ~=~ m')%NodePred -> P m nil m') ->
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
    + apply H_nil; auto.
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
          hnf in H2 |- *; clear - H2.
          intros; specialize (H2 x).
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
    + intros.
      rewrite <- (H n).
      auto.
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
      inversion H0.
    + intros.
      destruct H2.
      - subst z. apply (mark_list_marked m' l m''); auto.
        * intros.
          apply (mark_preserved_reach_decidable m v m'); auto.
          1: apply reachable_by_head_valid in H3; auto.
          1: apply R_DEC; right; auto.
          1: apply R_DEC; left; auto.
        * intros; apply V_DEC; right; auto.
        * destruct H0 as [? _]; auto.
      - destruct (V_DEC v (or_introl eq_refl)).
        1: {
          apply (mark_unmarked m v m') in H3; auto; [| apply R_DEC; left; auto].
          destruct H3.
          + apply (H z); auto.
          + apply (mark_list_marked m' l); auto.
            - intros.
              apply (mark_preserved_reach_decidable m v m'); auto.
              * apply R_DEC; right; auto.
              * apply R_DEC; left; auto.
            - intros; apply V_DEC; right; auto.
        }
        1: {
          pose proof (mark_invalid m v m' n0 H0).
          apply (H z); auto.
          erewrite si_reachable_by in H3; [exact H3 | reflexivity |].
          hnf in H4 |- *; clear - H4.
          intros.
          specialize (H4 x).
          rewrite !negateP_spec.
          tauto.
        }
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
    + intros. apply H.
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
        apply H6. intro. apply H4. subst. apply reachable_by_refl; auto.
      } rewrite H5.
      assert (forall x, In x l -> ~ g |= x ~o~> n satisfying (negateP m2)). {
        intros. intro.
        destruct (V_DEC x H6).
        + apply (mark1_reverse_unmark m1 root) in H7; auto.
          apply H4. apply H1 in H6.
          apply edge_reachable_by with x; auto.
          unfold edge; auto.
        + apply reachable_by_head_valid in H7; tauto.
      }
      eapply mark_list_preserve_marked; eauto.
  Qed.

  Lemma mark_func: forall m root m1 m2 (R_DEC: ReachDecidable g root (negateP m)),
                     mark m root m1 ->
                     mark m root m2 ->
                     (m1 ~=~ m2)%NodePred.
  Proof.
    intros.
    intro; intros.
    destruct H as [? ?].
    destruct H0 as [? ?].
    destruct (R_DEC n).
    - specialize (H n r). specialize (H0 n r). tauto.
    - specialize (H2 n n0). specialize (H1 n n0). tauto.
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
                              (m3 ~=~ m4)%NodePred.
  Proof.
    intros. assert (mark m1 root m3).
    apply (mark_mark1_mark _ _ l m2); auto.
    apply (mark_func m1 root); auto.
  Qed.

  Lemma mark_marked_reachable_conflict: forall m1 root m2 n
    (R_DEC: ReachDecidable g root (negateP m1)),
    mark m1 root m2 ->
    Included (reachable_by g n (negateP m2)) (Complement _ (reachable_by g root (negateP m1))).
  Proof.
    intros.
    intro n'; unfold Ensembles.In; intros.
    eapply mark_reverse_unmarked_strong in H0; [| eauto | eauto].
    apply reachable_by_is_reachable in H0.
    rewrite <- reachable_by_eq_partialgraph_reachable in H0.
    apply reachable_by_foot_prop in H0.
    auto.
  Qed.

  Lemma mark_list_marked_reachable_conflict: forall m1 l m2
    (R_DEC: forall x, In x l -> ReachDecidable g x (negateP m1))
    (V_DEC: forall x, In x l -> Decidable (vvalid g x)),
    mark_list m1 l m2 ->
    forall n,
    Included (reachable_by g n (negateP m2)) (Complement _ (reachable_by_through_set g l (negateP m1))).
  Proof.
    intros.
    intro n'; unfold Complement, Ensembles.In; intros.
    intros [? [? ?]].
    pose proof mark_list_get_marked _ _ _ R_DEC V_DEC H x n' H1.
    apply reachable_by_foot_prop in H0.
    change ((negateP m2) n') with (~ (m2 n')) in H0.
    tauto.
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

  End SINGLE_GRAPH_LEM.

  Instance mark1_proper: Proper (structurally_identical ==> node_pred_equiv ==> eq ==> node_pred_equiv ==> iff) mark1.
  Proof.
    hnf; intros g1 g2 Hg.
    do 3 (hnf; intros).
    subst.
    revert g1 g2 x y x1 y1 Hg H H1.
    assert (forall g1 g2 x y x1 y1, g1 ~=~ g2 -> x ~=~ y%NodePred -> x1 ~=~ y1%NodePred -> mark1 g1 x y0 x1 -> mark1 g2 y y0 y1);
      [| intros; split; apply H; auto; symmetry; auto].
    unfold mark1.
    intros.
    rewrite (H1 y0) in H2.
    rewrite (proj1 H) in H2.
    split; [| split]; try tauto.
    destruct H2 as [_ [_ ?]].
    intros; specialize (H2 n').
    rewrite (H0 n'), (H1 n') in H2.
    tauto.
  Qed.

  Lemma mark_proper_strong: forall (g g': PreGraph V E) m1 root m2,
    ((predicate_partialgraph g (reachable_by g root (negateP m1))) ~=~
    (predicate_partialgraph g' (reachable_by g' root (negateP m1)))) ->
    (mark g m1 root m2 <-> mark g' m1 root m2).
  Proof.
    assert (forall (g g': PreGraph V E) m1 root m2,
    ((predicate_partialgraph g (reachable_by g root (negateP m1))) ~=~
    (predicate_partialgraph g' (reachable_by g' root (negateP m1)))) ->
    mark g m1 root m2 -> mark g' m1 root m2).
    2: intros; split; apply H; auto; symmetry; auto.
    unfold mark; intros.
    split; intros; destruct H0.
    + apply H0.
      pose proof partialgraph_si_node_prop n g g' _ _ H.
      spec H3.
      1: {
        intros ? ?.
        apply reachable_by_foot_valid in H4.
        auto.
      }
      spec H3.
      1: {
        intros ? ?.
        apply reachable_by_foot_valid in H4.
        auto.
      }
      tauto.
    + apply H2.
      pose proof partialgraph_si_node_prop n g g' _ _ H.
      spec H3.
      1: {
        intros ? ?.
        apply reachable_by_foot_valid in H4.
        auto.
      }
      spec H3.
      1: {
        intros ? ?.
        apply reachable_by_foot_valid in H4.
        auto.
      }
      tauto.
  Qed.

  Lemma mark_list_proper_strong: forall (g g': PreGraph V E) m1 l m2
    (R_DEC: forall x, In x l -> ReachDecidable g x (negateP m1))
    (V_DEC: forall x, In x l -> Decidable (vvalid g x))
    (R_DEC': forall x, In x l -> ReachDecidable g' x (negateP m1))
    (V_DEC': forall x, In x l -> Decidable (vvalid g' x)),
    ((predicate_partialgraph g (reachable_by_through_set g l (negateP m1))) ~=~
    (predicate_partialgraph g' (reachable_by_through_set g' l (negateP m1)))) ->
    (mark_list g m1 l m2 <-> mark_list g' m1 l m2).
  Proof.
    intros.
    assert (forall (g: PreGraph V E) m1 l m2
    (R_DEC: forall x, In x l -> ReachDecidable g x (negateP m1))
    (V_DEC: forall x, In x l -> Decidable (vvalid g x)),
    mark_list g m1 l m2 ->
    forall (g': PreGraph V E),
    ((predicate_partialgraph g (reachable_by_through_set g l (negateP m1))) ~=~
    (predicate_partialgraph g' (reachable_by_through_set g' l (negateP m1)))) ->
    mark_list g' m1 l m2).
    2: intros; split; intros; eapply H0; eauto; symmetry; eauto; reflexivity.
    intro.
    apply (ind_RV_DEC g0 (fun m l m' => forall g'0 : PreGraph V E,
   (predicate_partialgraph g0 (reachable_by_through_set g0 l (negateP m))) ~=~
   (predicate_partialgraph g'0 (reachable_by_through_set g'0 l (negateP m))) ->
   mark_list g'0 m l m')); intros.
    + constructor.
      auto.
    + econstructor.
      - pose proof mark_proper_strong g0 g'0 m v m'.
        spec H4; [| rewrite <- H4; auto].
        eapply si_stronger_partialgraph with (p := (reachable_by g0 v (negateP m))); [| | exact H3]; intros.
        * assert (g0 |= v ~o~> v0 satisfying (negateP m) ->
            reachable_by_through_set g0 (v :: l0) (negateP m) v0); [intro | tauto].
          exists v; split; [simpl |]; auto.
        * pose proof reachable_by_partialgraph_reachable_by_equiv g0 (reachable_by_through_set g0 (v :: l0) (negateP m)) (negateP m) v.
          spec H5; [intro; intros; exists v; split; [simpl |]; auto |].
          pose proof reachable_by_partialgraph_reachable_by_equiv g'0 (reachable_by_through_set g'0 (v :: l0) (negateP m)) (negateP m) v.
          spec H6; [intro; intros; exists v; split; [simpl |]; auto |].
          rewrite H3 in H5.
          rewrite <- H5 in H6.
          clear H5.
          rewrite Same_set_spec in H6.
          specialize (H6 v0).
          assert (g'0 |= v ~o~> v0 satisfying (negateP m) ->
            reachable_by_through_set g'0 (v :: l0) (negateP m) v0); [intro | tauto].
          exists v; split; [simpl |]; auto.
      - apply H0.
        eapply si_stronger_partialgraph with (p := (reachable_by_through_set g0 l0 (negateP m'))); [| | eauto]; intros.
        * assert (reachable_by_through_set g0 l0 (negateP m') v0 ->
            reachable_by_through_set g0 (v :: l0) (negateP m) v0); [intro | tauto].
          destruct H4 as [vv [? ?]]; exists vv; split; [simpl |]; auto.
          eapply reachable_by_weaken; [| eauto].
          apply Complement_Included_rev; intro; eapply mark_marked; [eauto |].
          apply R_DEC0; simpl; auto.
        * assert (reachable_by_through_set g'0 l0 (negateP m') v0 <->
            reachable_by_through_set g0 l0 (negateP m') v0).
          1: {
            apply ex_iff; intro.
            apply and_iff_compat_l_weak; intro.
            pose proof reachable_by_partialgraph_reachable_by_equiv g0 (reachable_by_through_set g0 (v :: l0) (negateP m)) (negateP m') x.
            spec H5.
            1: {
              intro; intros; exists x.
              split; [simpl; auto |].
              eapply reachable_by_weaken; eauto.
              apply Complement_Included_rev; intro; eapply mark_marked; [eauto |].
              apply R_DEC0; simpl; auto.
            }
            pose proof reachable_by_partialgraph_reachable_by_equiv g'0 (reachable_by_through_set g'0 (v :: l0) (negateP m)) (negateP m') x.
            spec H6.
            1: {
              intro; intros; exists x.
              split; [simpl; auto |].
              eapply reachable_by_weaken; eauto.
              apply Complement_Included_rev; intro; eapply mark_marked; [eauto |].
              apply R_DEC0; simpl; auto.
            }
            rewrite H3 in H5.
            rewrite <- H5 in H6.
            rewrite Same_set_spec in H6.
            clear H5; apply H6.
          }
          assert (reachable_by_through_set g'0 l0 (negateP m') v0 ->
            reachable_by_through_set g'0 (v :: l0) (negateP m) v0); [clear H4; intro | tauto].
          destruct H4 as [vv [? ?]]; exists vv; split; [simpl |]; auto.
          eapply reachable_by_weaken; [| eauto].
          apply Complement_Included_rev; intro; eapply mark_marked; [eauto |].
          apply R_DEC0; simpl; auto.
  Qed.

  Instance mark_proper: Proper (structurally_identical ==> node_pred_equiv ==> eq ==> node_pred_equiv ==> iff) mark.
  Proof.
    hnf; intros g1 g2 Hg.
    do 3 (hnf; intros).
    subst.
    revert g1 g2 x y x1 y1 Hg H H1.
    assert (forall g1 g2 x y x1 y1, g1 ~=~ g2 -> x ~=~ y%NodePred -> x1 ~=~ y1%NodePred -> mark g1 x y0 x1 -> mark g2 y y0 y1);
      [| intros; split; apply H; auto; symmetry; auto].
    unfold mark.
    intros; destruct H2.
    split.
    + intros.
      rewrite <- (H1 n); apply H2; auto.
      rewrite si_reachable_by; [exact H4 | auto |].
      hnf; intros.
      rewrite !negateP_spec; specialize (H0 x0); tauto.
    + intros.
      rewrite <- (H0 n), <- (H1 n); apply H3; auto.
      rewrite si_reachable_by; [exact H4 | auto |].
      hnf; intros.
      rewrite !negateP_spec; specialize (H0 x0); tauto.
  Qed.

  Instance mark_list_proper: Proper (structurally_identical ==> node_pred_equiv ==> eq ==> node_pred_equiv ==> iff) mark_list.
  Proof.
    hnf; intros g1 g2 Hg.
    do 3 (hnf; intros).
    subst.
    revert g1 g2 x y x1 y1 Hg H H1.
    assert (forall g1 g2 x y x1 y1, g1 ~=~ g2 -> x ~=~ y%NodePred -> x1 ~=~ y1%NodePred -> mark_list g1 x y0 x1 -> mark_list g2 y y0 y1);
      [| intros; split; apply H; auto; symmetry; auto].
    intros; subst.
    revert g2 y y1 H H0 H1; induction H2; intros.
    + apply mark_list_nil.
      rewrite <- H1, <- H2, H; reflexivity.
    + apply mark_list_cons with m0.
      - rewrite <- H0, <- H1; auto.
      - apply IHmark_list; [auto | reflexivity | auto].
  Qed.

End SIMPLE_MARK_GRAPH.
End SIMPLE_MARK_GRAPH.

Existing Instances SIMPLE_MARK_GRAPH.mark1_proper SIMPLE_MARK_GRAPH.mark_proper SIMPLE_MARK_GRAPH.mark_list_proper.

Module MarkGraph.

Class MarkGraphSetting (DV: Type) := {
  label_marked: DV -> Prop;
  label_mark: DV -> DV;
  label_unmark: DV -> DV;
  marked_dec: forall x, {label_marked x} + {~ label_marked x};
  label_mark_sound: forall x, ~ label_marked x -> label_marked (label_mark x);
  label_unmark_sound: forall x, label_marked x -> ~ label_marked (label_unmark x)
}.

Section MarkGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE DG: Type}.
Context {MGS: MarkGraphSetting DV}.
Context {P: LabeledGraph V E DV DE DG -> Type}.

Notation Graph := (GeneralGraph V E DV DE DG P).
Local Coercion pg_lg : LabeledGraph >-> PreGraph.
Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.

Definition marked (g: Graph) : NodePred V.
  refine (existT _ (fun v => label_marked (vlabel g v)) _).
  intros.
  apply marked_dec.
Defined.

Definition unmarked (g: Graph) (v: V) : Prop := negateP (marked g) v.

Definition mark1 (g1 : Graph) (n : V) (g2 : Graph) : Prop :=
  g1 ~=~ g2 /\
  vvalid g1 n /\
  marked g2 n /\
  forall n', n <> n' -> (marked g1 n' <-> marked g2 n').

Definition mark (g1 : Graph) (root : V) (g2 : Graph) : Prop :=
  g1 ~=~ g2 /\
  (forall n, g1 |= root ~o~> n satisfying (unmarked g1) -> marked g2 n) /\
  (forall n, ~ g1 |= root ~o~> n satisfying (unmarked g1) -> (marked g1 n <-> marked g2 n)).

Inductive mark_list: Graph -> list V -> Graph -> Prop :=
| mark_list_nil: forall g, mark_list g nil g
| mark_list_cons: forall (g g0 g1: Graph) v vs, mark g v g0 -> mark_list g0 vs g1 -> mark_list g (v :: vs) g1
.

Definition inj (g: Graph): NodePred V.
  exists (fun v => label_marked (vlabel g v)).
  intros; apply marked_dec.
Defined.
(*
Instance inj_proper: Proper ((fun (g1 g2: Graph) => (g1 ~=~ g2)%LabeledGraph) ==> node_pred_equiv) inj.
Proof.
  hnf; intros.
  intro; simpl.
  destruct H as [_ [? _]].
  rewrite H.
  tauto.
Defined.
*)
Lemma mark1_inj: forall (g1 g2: Graph) (v: V), mark1 g1 v g2 <-> (g1 ~=~ g2 /\ SIMPLE_MARK_GRAPH.mark1 g1 (inj g1) v (inj g2)).
Proof.
  intros.
  unfold mark1, SIMPLE_MARK_GRAPH.mark1.
  simpl.
  unfold marked.
  tauto.
Qed.

Lemma mark_inj: forall (g1 g2: Graph) (v: V), mark g1 v g2 <-> (g1 ~=~ g2 /\ SIMPLE_MARK_GRAPH.mark g1 (inj g1) v (inj g2)).
Proof.
  intros.
  unfold mark, SIMPLE_MARK_GRAPH.mark.
  simpl.
  unfold marked.
  tauto.
Qed.

Lemma mark_list_inj: forall (g1 g2: Graph) (vs: list V), mark_list g1 vs g2 -> (g1 ~=~ g2 /\ SIMPLE_MARK_GRAPH.mark_list g1 (inj g1) vs (inj g2)).
Proof.
  intros.
  induction H.
  - split; [reflexivity |].
    constructor.
    reflexivity.
  - rewrite mark_inj in H.
    split; [transitivity g0; tauto |].
    apply SIMPLE_MARK_GRAPH.mark_list_cons with (inj g0); [tauto |].
    rewrite (proj1 H); tauto.
Qed.

Lemma vertex_update_mark1: forall (g1: Graph) x (g2: Graph),
  g1 ~=~ g2 ->
  vvalid g1 x ->
  unmarked g1 x ->
  vlabel g2 x = label_mark (vlabel g1 x) ->
  (forall y, x <> y -> vlabel g2 y = vlabel g1 y) ->
  (forall e, elabel g2 e = elabel g1 e) ->
  mark1 g1 x g2.
Proof.
  intros.
  split; [| split; [| split]]; auto.
  + simpl.
    rewrite H2.
    apply label_mark_sound.
    apply H1.
  + intros y HH; specialize (H3 y HH). clear - H3.
    simpl.
    rewrite H3.
    reflexivity.
Qed.

Lemma mark_invalid_refl: forall (g: Graph) root, ~ vvalid g root -> mark g root g.
Proof.
  intros.
  pose proof SIMPLE_MARK_GRAPH.mark_invalid_refl g (inj g) root H.
  rewrite -> mark_inj.
  split; [reflexivity | auto].
Qed.

Lemma mark_marked_root_refl: forall (g: Graph) root, marked g root -> mark g root g.
Proof.
  intros.
  pose proof SIMPLE_MARK_GRAPH.mark_marked_root_refl g (inj g) root H.
  rewrite -> mark_inj.
  split; [reflexivity | auto].
Qed.

Lemma mark_marked: forall (g1: Graph) root (g2: Graph),
  mark g1 root g2 ->
  ReachDecidable g1 root (unmarked g1) ->
  forall n, marked g1 n -> marked g2 n.
Proof.
  intros.
  rewrite mark_inj in H.
  destruct H.
  apply SIMPLE_MARK_GRAPH.mark_marked with (n0 := n) in H1; auto.
Qed.

Lemma mark1_mark_list_mark: forall (g1: Graph) root l (g2 g3: Graph)
  (R_DEC: forall x, In x l -> ReachDecidable g2 x (unmarked g2))
  (V_DEC: forall x, In x l -> Decidable (vvalid g1 x))
  (R_DEC': ReachDecidable g1 root (unmarked g1)),
  vvalid g1 root ->
  (unmarked g1) root ->
  step_list g1 root l ->
  mark1 g1 root g2 ->
  mark_list g2 l g3 ->
  mark g1 root g3.
Proof.
  intros.
  rewrite mark1_inj in H2.
  apply mark_list_inj in H3.
  rewrite mark_inj.
  split; [transitivity g2; tauto |].
  apply SIMPLE_MARK_GRAPH.mark_mark1_mark with l (inj g2); auto.
  + intros.
    eapply ReachDecidable_si; [symmetry; exact (proj1 H2) | | eauto].
    intro; intros.
    unfold unmarked; rewrite negateP_spec; simpl.
    reflexivity.
  + tauto.
  + rewrite <- (proj1 H2) in H3 at 2; tauto.
Qed.

End MarkGraph.
End MarkGraph.

(*
Module WeakMarkGraph.

Class MarkGraphSetting (DV: Type) := {
  label_marked: DV -> Prop;
  label_mark: DV -> DV;
  label_unmark: DV -> DV;
  marked_dec: forall x, {label_marked x} + {~ label_marked x};
  label_mark_sound: forall x, ~ label_marked x -> label_marked (label_mark x);
  label_unmark_sound: forall x, label_marked x -> ~ label_marked (label_unmark x)
}.

Section WeakMarkGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE: Type}.
Context {MGS: MarkGraphSetting DV}.
Context {P: LabeledGraph V E DV DE -> Type}.

Notation Graph := (GeneralGraph V E DV DE P).

Definition marked (g: Graph) : NodePred V.
  refine (existT _ (fun v => label_marked (vlabel g v)) _).
  intros.
  apply marked_dec.
Defined.

Definition unmarked (g: Graph) : NodePred V := negateP (marked g).

Hypothesis R_DEC: forall (g: Graph) x, vvalid g x -> ReachDecidable g x (unmarked g).

Lemma R_DEC': forall (g: Graph) x, Decidable (vvalid g x /\ unmarked g x) -> ReachDecidable g x (unmarked g).
Proof.
  intros.
  destruct H.
  + apply R_DEC; tauto.
  + right.
    intro.
    apply n; split.
    - apply reachable_by_head_valid in H; auto.
    - apply reachable_by_head_prop in H.
      auto.
Qed.

Definition mark1 (g1 : Graph) (n : V) (g2 : Graph) : Prop :=
  g1 ~=~ g2 /\
  vvalid g1 n /\
  marked g2 n /\
  forall n', n <> n' -> (marked g1 n' <-> marked g2 n').

Definition mark (g1 : Graph) (root : V) (g2 : Graph) : Prop :=
  (predicate_partialgraph g1 (Complement _ (reachable_by g1 root (unmarked g1)))) ~=~
  (predicate_partialgraph g2 (Complement _ (reachable_by g1 root (unmarked g1)))) /\
  (forall n, g1 |= root ~o~> n satisfying (unmarked g1) -> marked g2 n) /\
  (forall n, ~ g1 |= root ~o~> n satisfying (unmarked g1) -> (marked g1 n <-> marked g2 n)).

Inductive mark_list: Graph -> list V -> Graph -> Prop :=
| mark_list_nil: forall (g g0: Graph), (g ~=~ g0)%LabeledGraph -> mark_list g nil g0
| mark_list_cons: forall (g g0: Graph) g1 v vs, mark g v g0 -> mark_list g0 vs g1 -> mark_list g (v :: vs) g1
.

Definition inj (g: Graph): NodePred V.
  exists (fun v => label_marked (vlabel g v)).
  intros; apply marked_dec.
Defined.

Instance inj_proper: Proper ((fun (g1 g2: Graph) => (g1 ~=~ g2)%LabeledGraph) ==> node_pred_equiv) inj.
Proof.
  hnf; intros.
  intro; simpl.
  destruct H as [_ [? _]].
  rewrite H.
  tauto.
Defined.

Lemma V_DEC_mark: forall (g1 g2: Graph) (root: V) n,
  mark g1 root g2 ->
  Decidable (vvalid g1 root /\ unmarked g1 root) ->
  Decidable (vvalid g1 n /\ unmarked g1 n) ->
  Decidable (vvalid g2 n /\ unmarked g2 n).
Proof.
  intros.
  apply R_DEC' in H0.
  destruct (H0 n); [right |].
  + destruct H as [_ [? _]].
    apply H in r.
    unfold unmarked; rewrite negateP_spec.
    tauto.
  + destruct H as [? [_ ?]].
    destruct H as [H _]; specialize (H n); specialize (H2 _ n0).
    simpl in H; unfold predicate_vvalid, Complement, Ensembles.In in H.
    destruct H1 as [H1 | H1]; [left | right];
    unfold unmarked in *; rewrite negateP_spec in H1 |- *;
    tauto.
Qed.

Lemma mark1_inj: forall (g1 g2: Graph) (v: V), mark1 g1 v g2 <-> (g1 ~=~ g2 /\ SIMPLE_MARK_GRAPH.mark1 g1 (inj g1) v (inj g2)).
Proof.
  intros.
  unfold mark1, SIMPLE_MARK_GRAPH.mark1.
  simpl.
  unfold marked.
  tauto.
Qed.

Lemma mark_inj: forall (g1 g2: Graph) (v: V),
  mark g1 v g2 <->
  ((predicate_partialgraph g1 (Complement _ (reachable_by g1 v (unmarked g1)))) ~=~
   (predicate_partialgraph g2 (Complement _ (reachable_by g1 v (unmarked g1)))) /\
   SIMPLE_MARK_GRAPH.mark g1 (inj g1) v (inj g2)).
Proof.
  intros.
  unfold mark, SIMPLE_MARK_GRAPH.mark.
  simpl.
  unfold marked.
  tauto.
Qed.

Lemma mark_reverse_unmarked_strong: forall (g1 g2: Graph) n1 n2 root,
  mark g1 root g2 ->
  ReachDecidable g1 root (unmarked g1) ->
  g2 |= n1 ~o~> n2 satisfying (unmarked g2) ->
  (predicate_partialgraph g1 (Complement _ (reachable_by g1 root (unmarked g1)))) |= n1 ~o~> n2 satisfying (unmarked g1).
Proof.
  intros.
  eapply reachable_by_weaken with (Q := Complement _ (Union _ (reachable_by g1 root (unmarked g1)) (marked g1))) in H0.
  + rewrite <- Intersection_Complement in H0.
    rewrite reachable_by_eq_partialgraph_reachable in H0.
    rewrite <- partial_partialgraph in H0.
    destruct H.
    rewrite <- H in H0.
    rewrite <- reachable_by_eq_partialgraph_reachable in H0.
    auto.
  + apply Complement_Included_rev.
    intro; unfold Ensembles.In.
    rewrite Union_spec.
    apply SIMPLE_MARK_GRAPH.mark_marked_strong; auto.
    rewrite mark_inj in H.
    destruct H; auto.
Qed.

Lemma mark_reverse_unmarked: forall (g1 g2: Graph) n1 n2 root,
  mark g1 root g2 ->
  ReachDecidable g1 root (unmarked g1) ->
  g2 |= n1 ~o~> n2 satisfying (unmarked g2) ->
  g1 |= n1 ~o~> n2 satisfying (unmarked g1).
Proof.
  intros.
  eapply mark_reverse_unmarked_strong in H0; eauto.
  rewrite reachable_by_eq_partialgraph_reachable in H0.
  rewrite partial_partialgraph in H0.
  rewrite <- reachable_by_eq_partialgraph_reachable in H0.
  eapply reachable_by_weaken; [| exact H0].
  intro; unfold Ensembles.In; rewrite Intersection_spec.
  tauto.
Qed.

Lemma mark_list_inj: forall (g1 g2: Graph) (vs: list V)
  (V_DEC: forall x, In x vs -> Decidable (vvalid g1 x)),
  mark_list g1 vs g2 ->
  ((predicate_partialgraph g1 (Complement _ (reachable_by_through_set g1 vs (unmarked g1)))) ~=~
   (predicate_partialgraph g2 (Complement _ (reachable_by_through_set g1 vs (unmarked g1))))) /\
  SIMPLE_MARK_GRAPH.mark_list g1 (inj g1) vs (inj g2).
Proof.
  intros.
  assert (forall x : V, In x vs -> Decidable (vvalid g1 x /\ unmarked g1 x)).
  1: {
    intros.
    apply sumbool_dec_and; [apply V_DEC; auto |].
    apply node_pred_dec.
  }
  clear V_DEC; rename X into V_DEC.
  induction H.
  - split; [destruct H; rewrite <- H; reflexivity |].
    constructor.
    apply inj_proper; auto.
  - spec IHmark_list.
    1: {
      intros.
      eapply V_DEC_mark; [exact H | |]; apply V_DEC; simpl; auto.
    }
    rewrite mark_inj in H.
    split;
    [transitivity (predicate_partialgraph g0 (Complement _ (reachable_by_through_set g (v :: vs) (unmarked g)))) |].
    * eapply si_stronger_partialgraph_simple; [| destruct H; eassumption].
      apply Complement_Included_rev.
      hnf; intros.
      exists v; split; [simpl; tauto |].
      auto.
    * eapply si_stronger_partialgraph_simple.
      2: destruct IHmark_list; exact H1.
      apply Complement_Included_rev.
      hnf; intros.
      destruct H1 as [v0 [? ?]].
      exists v0; split; [simpl; auto |].
      eapply mark_reverse_unmarked; eauto.
      apply R_DEC', V_DEC.
      simpl; auto.
    * destruct IHmark_list.
      econstructor.
      1: destruct H as [_ H]; exact H.
      erewrite SIMPLE_MARK_GRAPH.mark_list_proper_strong; [exact H2 | | | | |].
Abort.

(*
Lemma vertex_update_mark1: forall (g1: Graph) x (g2: Graph),
  g1 ~=~ g2 ->
  vvalid g1 x ->
  unmarked g1 x ->
  vlabel g2 x = label_mark (vlabel g1 x) ->
  (forall y, x <> y -> vlabel g2 y = vlabel g1 y) ->
  (forall e, elabel g2 e = elabel g1 e) ->
  mark1 g1 x g2.
Proof.
  intros.
  split; [| split; [| split]]; auto.
  + simpl.
    rewrite H2.
    apply label_mark_sound.
    apply H1.
  + intros y HH; specialize (H3 y HH). clear - H3.
    simpl.
    rewrite H3.
    reflexivity.
Qed.

Lemma mark_invalid_refl: forall (g: Graph) root, ~ vvalid g root -> mark g root g.
Proof.
  intros.
  pose proof SIMPLE_MARK_GRAPH.mark_invalid_refl g (inj g) root H.
  rewrite -> mark_inj.
  split; [reflexivity | auto].
Qed.

Lemma mark_marked_root_refl: forall (g: Graph) root, marked g root -> mark g root g.
Proof.
  intros.
  pose proof SIMPLE_MARK_GRAPH.mark_marked_root_refl g (inj g) root H.
  rewrite -> mark_inj.
  split; [reflexivity | auto].
Qed.

Lemma mark_marked: forall (g1: Graph) root (g2: Graph),
  mark g1 root g2 ->
  ReachDecidable g1 root (unmarked g1) ->
  forall n, marked g1 n -> marked g2 n.
Proof.
  intros.
  rewrite mark_inj in H.
  destruct H.
  apply SIMPLE_MARK_GRAPH.mark_marked with (n0 := n) in H1; auto.
Qed.

Lemma mark1_mark_list_mark: forall (g1: Graph) root l (g2 g3: Graph)
  (R_DEC: forall x, In x l -> ReachDecidable g2 x (unmarked g2))
  (V_DEC: forall x, In x l -> Decidable (vvalid g1 x))
  (R_DEC': ReachDecidable g1 root (unmarked g1)),
  vvalid g1 root ->
  (unmarked g1) root ->
  step_list g1 root l ->
  mark1 g1 root g2 ->
  mark_list g2 l g3 ->
  mark g1 root g3.
Proof.
  intros.
  rewrite mark1_inj in H2.
  apply mark_list_inj in H3.
  rewrite mark_inj.
  split; [transitivity g2; tauto |].
  apply SIMPLE_MARK_GRAPH.mark_mark1_mark with l (inj g2); auto.
  + intros.
    eapply ReachDecidable_si; [symmetry; exact (proj1 H2) | | eauto].
    intro; intros.
    unfold unmarked; rewrite negateP_spec; simpl.
    reflexivity.
  + tauto.
  + rewrite <- (proj1 H2) in H3 at 2; tauto.
Qed.
*)
End WeakMarkGraph.
End WeakMarkGraph.
*)