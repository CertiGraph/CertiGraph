Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Classes.Morphisms.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas. Import RamifyCoq.graph.path_lemmas.PathNotation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.dual_graph.

(*
Definition DFS_acc {V E} {EV: EqDec V eq} {EE: EqDec E eq} (g: PreGraph V E) (P: V -> Prop) (x y: V) :=
  vvalid g x /\ x = y \/
  reachable_by g x P y \/
  exists z, reachable_by g x P z /\ edge g z y.

Lemma DFS_acc_self: forall {V E} {EV: EqDec V eq} {EE: EqDec E eq} (g: PreGraph V E) (P: V -> Prop) x,
  vvalid g x -> 
  DFS_acc g P x x.
Proof.
  intros.
  left.
  tauto.
Qed.

Lemma DFS_acc_vvalid: forall {V E} {EV: EqDec V eq} {EE: EqDec E eq} (g: PreGraph V E) (P: V -> Prop) x,
  Included (DFS_acc g P x) (vvalid g).
Proof.
  intros; hnf; unfold Ensembles.In; intros.
  destruct H as [? | [? | ?]].
  + destruct H; subst; auto.
  + apply reachable_by_foot_valid in H; auto.
  + destruct H as [? [_ [? [? ?]]]]; auto.
Qed.

*)

Module WeakMarkGraph.

Class MarkGraphSetting (DV: Type) := {
  label_marked: DV -> Prop;
  marked_dec: forall x, {label_marked x} + {~ label_marked x}
}.

Section WeakMarkGraph.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE: Type}.
Context {MGS: MarkGraphSetting DV}.

Notation Graph := (LabeledGraph V E DV DE).

Definition marked (g: Graph) : NodePred V.
  refine (existT _ (fun v => label_marked (vlabel g v)) _).
  intros.
  apply marked_dec.
Defined.

Definition unmarked (g: Graph) : NodePred V := negateP (marked g).

Hypothesis R_DEC: forall (g: Graph) x, vvalid g x -> ReachDecidable g x (unmarked g).

Definition nothing (n : V) (g1 : Graph) (g2 : Graph) : Prop :=
  (predicate_partialgraph g1 (eq n)) ~=~
  (predicate_partialgraph g2 (eq n)) /\
  (forall v, marked g1 v <-> marked g2 v).

Definition mark1 (n : V) (g1 : Graph) (g2 : Graph) : Prop :=
  g1 ~=~ g2 /\
  marked g2 n /\
  (forall n', n <> n' -> (marked g1 n' <-> marked g2 n')).

Definition mark (root : V) (g1 : Graph) (g2 : Graph) : Prop :=
  let PV := reachable_by g1 root (unmarked g1) in
  (predicate_partialgraph g1 (Complement _ PV)) ~=~ (predicate_partialgraph g2 (Complement _ PV)) /\
  (forall n, PV n -> marked g2 n) /\
  (forall n, ~ PV n -> (marked g1 n <-> marked g2 n)).

Definition componded root R :=
  compond_relation (compond_relation (nothing root) R) (nothing root).

Definition componded_mark_list root xs := relation_list (map (fun x => componded root (mark x)) xs).

Definition mark_list xs := relation_list (map mark xs).

Lemma mark_marked: forall (g1: Graph) root (g2: Graph),
  mark root g1 g2 ->
  forall n, marked g1 n -> marked g2 n.
Proof.
  intros.
  destruct H as [_ [_ ?]].
  rewrite <- H; [auto |].
  intro.
  apply reachable_by_foot_prop in H1.
  unfold unmarked in H1; rewrite negateP_spec in H1; auto.
Qed.

Lemma mark_unmarked: forall (g1: Graph) root (g2: Graph),
  mark root g1 g2 ->
  Same_set (unmarked g2) (Intersection _ (unmarked g1) (Complement _ (reachable_by g1 root (unmarked g1)))).
Proof.
  intros.
  rewrite Same_set_spec; intro n.
  rewrite Intersection_spec; unfold Complement, Ensembles.In.
  pose proof H.
  destruct H as [_ [? ?]].
  specialize (H n); specialize (H1 n).
  unfold unmarked at 1 2; rewrite !negateP_spec.
  split; intros; [split |].
  + intro; apply H2; clear H2.
    eapply mark_marked; eauto.
  + intro; apply H2; clear H2.
    apply H; auto.
  + destruct H2.
    apply H1 in H3.
    tauto.
Qed.

Lemma mark_invalid_refl: forall (g: Graph) root, ~ vvalid g root -> mark root g g.
Proof.
  intros.
  split; [| split].
  + reflexivity.
  + intros.
    apply reachable_by_head_valid in H0.
    tauto.
  + intros.
    reflexivity.
Qed.

Lemma mark_marked_root_refl: forall (g: Graph) root, marked g root -> mark root g g.
Proof.
  intros.
  split; [| split].
  + reflexivity.
  + intros.
    apply reachable_by_head_prop in H0.
    unfold unmarked in H0; rewrite negateP_spec in H0.
    tauto.
  + intros.
    reflexivity.
Qed.

Lemma lge_do_nothing: forall n, inclusion _ labeled_graph_equiv (nothing n).
Proof.
  intros; hnf; intros.
  destruct H as [? [? ?]].
  split.
  + rewrite H.
    reflexivity.
  + intros.
    simpl.
    rewrite H0.
    reflexivity.
Qed.

Lemma eq_do_nothing: forall n, inclusion _ eq (nothing n).
Proof.
  intros; hnf; intros.
  destruct H as [? [? ?]].
  split.
  + reflexivity.
  + intros.
    reflexivity.
Qed.

Lemma mark_is_componded_mark: forall root x,
  inclusion Graph (mark x) (componded root (mark x)).
Proof.
  intros.
  unfold componded.
  rewrite <- (compond_eq_right (mark x)) at 1.
  rewrite <- (compond_eq_left (mark x)) at 1.
  repeat apply compond_relation_inclusion.
  + apply eq_do_nothing.
  + hnf; auto.
  + apply eq_do_nothing.
Qed.

Lemma mark1_componded_mark_list_mark: forall root l (g1 g2: Graph)
  (V_DEC: forall x, In x l -> Decidable (vvalid g1 x)),
  vvalid g1 root ->
  (unmarked g1) root ->
  step_list g1 root l ->
  relation_list (nothing root :: mark1 root :: nothing root :: componded_mark_list root l :: nothing root :: nil) g1 g2 ->
  mark root g1 g2.
Abort.

Lemma triple1_mark: forall (g g1 g2: Graph) root l l_done son l_later,
  vvalid g root ->
  (unmarked g) root ->
  let unmarked' := Intersection _ (unmarked g) (Complement _ (eq root)) in
  step_list g root l ->
  l = l_done ++ son :: l_later ->
  let PV1 := reachable_by_through_set g l_done unmarked' in
  (predicate_partialgraph g (Complement _ PV1)) ~=~ (predicate_partialgraph g1 (Complement _ PV1)) /\
  Same_set (unmarked g1) (Intersection _ unmarked' (Complement _ PV1)) ->
  mark son g1 g2 ->
  let PV2 := reachable_by_through_set g (l_done ++ son :: nil) unmarked' in
  (predicate_partialgraph g (Complement _ PV2)) ~=~ (predicate_partialgraph g2 (Complement _ PV2)).
Proof.
  intros.
  destruct H3 as [PRE_psi PRE_unm].
  destruct H4 as [? _].
  transitivity (predicate_partialgraph g1 (Complement _ PV2)).
  + eapply si_stronger_partialgraph_simple; [| exact PRE_psi].
    apply Complement_Included_rev.
    unfold PV2; rewrite reachable_by_through_app'.
    apply left_Included_Union.
  + eapply si_stronger_partialgraph_simple; [| exact H3].
    unfold PV2; rewrite Complement_reachable_by_through_app_strong.
    rewrite PRE_unm.
    rewrite reachable_by_eq_partialgraph_reachable'.
    rewrite (Intersection_comm _ unmarked'), <- partial_partialgraph, <- PRE_psi.
    rewrite <- reachable_by_eq_partialgraph_reachable'.
    rewrite reachable_by_through_singleton'.
    apply Intersection2_Included.
    apply Included_refl.
Qed.

Lemma triple2_mark: forall (g g1 g2: Graph) root l l_done son l_later,
  vvalid g root ->
  (unmarked g) root ->
  let unmarked' := Intersection _ (unmarked g) (Complement _ (eq root)) in
  step_list g root l ->
  l = l_done ++ son :: l_later ->
  let PV1 := reachable_by_through_set g l_done unmarked' in
  (predicate_partialgraph g (Complement _ PV1)) ~=~ (predicate_partialgraph g1 (Complement _ PV1)) /\
  Same_set (unmarked g1) (Intersection _ unmarked' (Complement _ PV1)) ->
  mark son g1 g2 ->
  let PV2 := reachable_by_through_set g (l_done ++ son :: nil) unmarked' in
  Same_set (unmarked g2) (Intersection _ unmarked' (Complement _ PV2)).
Proof.
  intros.
  destruct H3 as [PRE_psi PRE_unm].
  apply mark_unmarked in H4.
  rewrite H4, PRE_unm.
  rewrite (Intersection_comm _ unmarked') at 2.
  rewrite reachable_by_eq_partialgraph_reachable', <- partial_partialgraph, <- PRE_psi, <- reachable_by_eq_partialgraph_reachable'.
  unfold PV2.
  rewrite Complement_reachable_by_through_app_strong, reachable_by_through_singleton'.
  rewrite Intersection_assoc.
  reflexivity.
Qed.  

Lemma triple_mark1: forall root (g g1: Graph),
  mark1 root g g1 ->
  let unmarked' := Intersection _ (unmarked g) (Complement _ (eq root)) in
  let PV1 := reachable_by_through_set g nil unmarked' in
  (predicate_partialgraph g (Complement _ PV1)) ~=~ (predicate_partialgraph g1 (Complement _ PV1)) /\
  Same_set (unmarked g1) (Intersection _ unmarked' (Complement _ PV1)).
Proof.
  intros.
  split.
  + destruct H.
    rewrite H; reflexivity.
  + unfold PV1, unmarked'.
    rewrite Same_set_spec; intro n; rewrite !Intersection_spec.
    unfold Complement, Ensembles.In.
    rewrite reachable_by_through_nil.
    destruct H as [_ [? ?]].
    unfold unmarked; rewrite !negateP_spec.
    destruct_eq_dec root n.
    - subst n; tauto.
    - specialize (H0 n).
      tauto.
Qed.

Lemma triple_final: forall root l (g g1: Graph),
  vvalid g root ->
  (unmarked g) root ->
  step_list g root l ->
  let unmarked' := Intersection _ (unmarked g) (Complement _ (eq root)) in
  let PV1 := reachable_by_through_set g l unmarked' in
  (predicate_partialgraph g (Complement _ PV1)) ~=~ (predicate_partialgraph g1 (Complement _ PV1)) /\
  Same_set (unmarked g1) (Intersection _ unmarked' (Complement _ PV1)) ->
  mark root g g1.
Proof.
  intros.
  destruct H2.
  assert (Same_set (reachable_by g root (unmarked g)) (Union _ (eq root) PV1)).
  Focus 1. {
    rewrite Same_set_spec.
    intro. rewrite Union_spec.
    apply reachable_by_step_equiv; auto.
  } Unfocus.
  split; [| split].
  + eapply si_stronger_partialgraph_simple; [| exact H2].
    apply Complement_Included_rev.
    rewrite H4.
    apply right_Included_Union.
  + intros.
    rewrite Same_set_spec in H4; rewrite (H4 n), Union_spec in H5.
    rewrite Same_set_spec in H3; specialize (H3 n).
    rewrite Intersection_spec in H3.
    unfold unmarked', unmarked, Complement, Ensembles.In in H3.
    rewrite Intersection_spec, !negateP_spec in H3.
    destruct (node_pred_dec (marked g1) n); auto.
    tauto.
  + intros.
    rewrite Same_set_spec in H4; rewrite (H4 n), Union_spec in H5.
    rewrite Same_set_spec in H3; specialize (H3 n).
    rewrite Intersection_spec in H3.
    unfold unmarked', unmarked, Complement, Ensembles.In in H3.
    rewrite Intersection_spec, !negateP_spec in H3.
    destruct (node_pred_dec (marked g1) n), (node_pred_dec (marked g) n); destruct_eq_dec root n; tauto.
Qed.

Lemma mark1_mark_list_mark: forall root l (g1 g2: Graph),
  vvalid g1 root ->
  (unmarked g1) root ->
  step_list g1 root l ->
  relation_list (mark1 root :: mark_list l :: nil) g1 g2 ->
  mark root g1 g2.
Proof.
  intros.
  rename g1 into g.
  destruct_relation_list g0 in H2.
  pose proof triple_mark1 root g g0 H3.
  cbv zeta in H4.
  set (unmarked' := Intersection _ (unmarked g) (Complement _ (eq root))) in H4.
  set (PV1 := reachable_by_through_set g nil unmarked') in H4.
  set (PV2 := reachable_by_through_set g l unmarked').
  assert ((predicate_partialgraph g (Complement V PV2)) ~=~
          (predicate_partialgraph g2 (Complement V PV2)) /\
          Same_set (unmarked g2) (Intersection V unmarked' (Complement V PV2)));
  [| eapply triple_final; eauto].
  clear H3.

  set (l_done := l).
  set (l_later := @nil V).
  assert (l = l_done ++ l_later) by (unfold l_later; rewrite app_nil_r; auto).
  revert PV2 H2; change l with l_done; intros.
  clearbody l_done l_later.
  revert  g2 H2 l_later H3; rev_induction l_done; intros.
  + unfold mark_list, relation_list in H2.
    simpl in H2; subst g2.
    auto.
  + clear PV1 H4.
    rename l0 into l_done.
    rewrite <- app_assoc in H5; simpl in H5.
    unfold mark_list in H3; rewrite map_app in H3; simpl in H3.
    apply (proj1 ((proj1 (same_relation_spec _ _) (relation_list_tail _ _)) _ _)) in H3.
    apply compond_relation_spec in H3; destruct H3 as [g1 [? ?]].

    cbv zeta in H2.
    specialize (H2 g1 H3 (a :: l_later) H5).
    set (PV1 := reachable_by_through_set g l_done unmarked') in H2.
    split.
    - eapply triple1_mark; eauto.
    - eapply triple2_mark; eauto.
Qed.

Lemma vertex_update_mark1: forall (g: Graph) x lx,
  label_marked lx ->
  mark1 x g (labeledgraph_vgen g x lx).
Proof.
  intros.
  split; [| split; [| split]].
  + reflexivity.
  + simpl.
    unfold update_vlabel.
    destruct_eq_dec x x; [auto | congruence].
  + simpl; intros.
    unfold update_vlabel.
    destruct_eq_dec x n'; [tauto | auto].
  + simpl; intros.
    unfold update_vlabel in H1.
    destruct_eq_dec x n'; [tauto | auto].
Qed.

(*
Lemma step_list_reachable_included: forall (g1 g2 g3: Graph) x l y l',
  vvalid g1 x ->
  step_list g1 x (l ++ y :: l') ->
  mark1 g1 x g2 ->
  mark_list g2 l g3 ->
  Included (reachable g3 y) (reachable g1 x).
Proof.
  intros.
  hnf; unfold Ensembles.In; intros.
  assert ((marked g3) x /\ step g3 x y /\ vvalid g3 x);
    [| apply step_reachable with y; tauto].
  assert (step g2 x y).
  Focus 1. {
    destruct H1 as [? _].
    rewrite <- step_si by eassumption.
    specialize (H0 y);
    rewrite in_app_iff in H0; simpl in H0; tauto.
  } Unfocus.
  assert (vvalid g2 x) by (rewrite <- (proj1 (proj1 H1)); auto).
  destruct H1 as [_ [? _]].
  clear - H1 H2 H4 H5.
  induction H2.
  + split.
    - simpl.
      destruct H as [_ [? _]].
      rewrite <- H; auto.
    - destruct H as [? _].
      erewrite <- step_si by eassumption.
      rewrite <- (proj1 H).
      auto.
  + do 3 (spec IHrelation_list; [auto |]).
    clear H2 H4 H5 H1 x0.
    assert ((marked z) x) by (eapply mark_marked; eauto; tauto).
    split; [| split]; auto.
    - destruct H as [? [? ?]].
      assert (step (dualgraph y0) y x) by admit.
      pose proof partialgraph_step _ (unmarked z) _ _ H3.
      
SearchAbout edge.
Locate partialgraph_edge.
 rewrite !step_spec in IHrelation_list |- *.
      destruct IHrelation_list as [? [[e [? [? ?]]] ?]].
      exists e.
      
    destruct H as [? _].
    assert (marked g2 x) by destru
    Focus 1. {
      destruct H1.
SearchAbout reachable Proper.

Locate reachable_proper.
rewrite <- H1.
*)

End WeakMarkGraph.

End WeakMarkGraph.
