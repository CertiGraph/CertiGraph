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
Context {DV DE DG: Type}.
Context {MGS: MarkGraphSetting DV}.

Notation Graph := (LabeledGraph V E DV DE DG).
Local Coercion pg_lg : LabeledGraph >-> PreGraph.

Definition marked (g: Graph) : NodePred V.
  refine (existT _ (fun v => label_marked (vlabel g v)) _).
  intros.
  apply marked_dec.
Defined.

Definition unmarked (g: Graph) : NodePred V := negateP (marked g).

Definition totally_unmarked (g: Graph) (x: V) :=
  forall y, reachable g x y -> g |= x ~o~> y satisfying (unmarked g).

Hypothesis R_DEC: forall (g: Graph) x, vvalid g x -> ReachDecidable g x (unmarked g).

Definition nothing (n : V) (g1 : Graph) (g2 : Graph) : Prop :=
  (predicate_partialgraph g1 (Complement _ (eq n))) ~=~
  (predicate_partialgraph g2 (Complement _ (eq n))) /\
  (forall v, marked g1 v <-> marked g2 v).

Definition mark1 (n : V) (g1 : Graph) (g2 : Graph) : Prop :=
  g1 ~=~ g2 /\
  marked g2 n /\
  (forall n', n <> n' -> (marked g1 n' <-> marked g2 n')).

Definition mark (root : V) (g1 : Graph) (g2 : Graph) : Prop :=
  let PV := reachable_by g1 root (unmarked g1) in
  (predicate_partialgraph g1 (Complement _ PV)) ~=~ (predicate_partialgraph g2 (Complement _ PV)) /\
  (forall n, marked g2 n <-> (marked g1 n \/ PV n)).

Definition componded root R :=
  compond_relation (compond_relation (nothing root) R) (nothing root).

Definition componded_mark_list root xs := relation_list (map (fun x => componded root (mark x)) xs).

Lemma mark_marked: forall (g1: Graph) root (g2: Graph),
  mark root g1 g2 ->
  forall n, marked g1 n -> marked g2 n.
Proof.
  intros.
  destruct H as [_ ?].
  rewrite H.
  auto.
Qed.

Lemma mark_marked': forall (g1: Graph) root (g2: Graph),
  mark root g1 g2 ->
  Same_set (marked g2) (Union _ (marked g1) (reachable_by g1 root (unmarked g1))).
Proof.
  intros.
  rewrite Same_set_spec; intro n.
  rewrite Union_spec.
  destruct H; auto.
Qed.

Lemma mark_unmarked: forall (g1: Graph) root (g2: Graph),
  mark root g1 g2 ->
  Same_set (unmarked g2) (Intersection _ (unmarked g1) (Complement _ (reachable_by g1 root (unmarked g1)))).
Proof.
  intros.
  unfold unmarked at 1 2.
  rewrite !negateP_spec'.
  rewrite Intersection_Complement.
  apply complement_proper.
  apply mark_marked'; auto.
Qed.

Lemma mark_invalid_refl: forall (g: Graph) root, ~ vvalid g root -> mark root g g.
Proof.
  intros.
  split.
  + reflexivity.
  + intros.
    pose proof reachable_by_head_valid g root n (unmarked g).
    tauto.
Qed.

Lemma mark_marked_root_refl: forall (g: Graph) root, marked g root -> mark root g g.
Proof.
  intros.
  split.
  + reflexivity.
  + intros.
    pose proof reachable_by_head_prop g root n (unmarked g).
    unfold unmarked at 2 in H0; rewrite negateP_spec in H0.
    tauto.
Qed.

Lemma eq_do_nothing: forall n, inclusion _ eq (nothing n).
Proof.
  intros; hnf; intros.
  destruct H.
  split.
  + reflexivity.
  + intros.
    reflexivity.
Qed.

Lemma labeledgraph_egen_do_nothing: forall (g: Graph) e d n, nothing n g (labeledgraph_egen g e d).
Proof.
  split; [reflexivity |].
  intros; reflexivity.
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

Lemma triple_nothing: forall (g g1 g2: Graph) root l l_done l_later,
  vvalid g root ->
  (unmarked g) root ->
  let marked' := Union _ (marked g) (eq root) in
  step_list g root l ->
  l = l_done ++ l_later ->
  let PV1 := reachable_by_through_set g l_done (Complement _ marked') in
  (predicate_partialgraph g (Complement _ (Union _ PV1 (eq root)))) ~=~
  (predicate_partialgraph g1 (Complement _ (Union _ PV1 (eq root)))) /\
  Same_set (marked g1) (Union _ marked' PV1) ->
  nothing root g1 g2 ->
  (predicate_partialgraph g (Complement _ (Union _ PV1 (eq root)))) ~=~
  (predicate_partialgraph g2 (Complement _ (Union _ PV1 (eq root)))) /\
  Same_set (marked g2) (Union _ marked' PV1).
Proof.
  intros.
  destruct H3.
  destruct H4.
  split.
  + etransitivity; [eauto |].
    eapply si_stronger_partialgraph_simple; [| eauto].
    apply Complement_Included_rev.
    apply right_Included_Union.
  + assert (Same_set (marked g1) (marked g2)) by (rewrite Same_set_spec; auto).
    rewrite <- H7.
    auto.
Qed.

Lemma triple_mark_aux1': forall g PV1 root marked',
  marked' = Union _ (marked g) (eq root) ->
  Same_set
   (Union V PV1 marked')
   (Union V (Union _ PV1 (eq root)) marked').
Proof.
  intros.
  subst.
  rewrite Same_set_spec; intro v.
  rewrite !Union_spec.
  tauto.
Qed.
(*
Lemma triple_mark_aux1: forall g PV1 root unmarked',
  unmarked' = Intersection _ (unmarked g) (Complement _ (eq root)) ->
  Same_set
   (Intersection V (Complement V PV1) unmarked')
   (Intersection V (Complement V (Union _ PV1 (eq root))) unmarked').
Proof.
  intros.
  subst.
  rewrite Same_set_spec; intro v.
  rewrite !Intersection_spec; unfold Complement, Ensembles.In.
  rewrite !Union_spec.
  tauto.
Qed.
*)
Lemma triple1_mark: forall (g g1 g2: Graph) root l l_done son l_later,
  vvalid g root ->
  (unmarked g) root ->
  let marked' := Union _ (marked g) (eq root) in
  step_list g root l ->
  l = l_done ++ son :: l_later ->
  let PV1 := reachable_by_through_set g l_done (Complement _ marked') in
  (predicate_partialgraph g (Complement _ (Union _ PV1 (eq root)))) ~=~
  (predicate_partialgraph g1 (Complement _ (Union _ PV1 (eq root)))) /\
  Same_set (marked g1) (Union _ marked' PV1) ->
  mark son g1 g2 ->
  let PV2 := reachable_by_through_set g (l_done ++ son :: nil) (Complement _ marked') in
  (predicate_partialgraph g (Complement _ (Union _ PV2 (eq root)))) ~=~
  (predicate_partialgraph g2 (Complement _ (Union _ PV2 (eq root)))).
Proof.
  intros.
  destruct H3 as [PRE_psi PRE_unm].
  destruct H4 as [? _].
  transitivity (predicate_partialgraph g1 (Complement _ (Union _ PV2 (eq root)))).
  + eapply si_stronger_partialgraph_simple; [| exact PRE_psi].
    apply Complement_Included_rev.
    unfold PV2; rewrite reachable_by_through_app'.
    rewrite !(Union_comm _ _ (eq root)), <- Union_assoc.
    apply left_Included_Union.
  + eapply si_stronger_partialgraph_simple; [| exact H3].
    unfold PV2.
    eapply Included_trans.
    - apply Complement_Included_rev.
      apply left_Included_Union.
    - rewrite Complement_reachable_by_through_app_strong.
      unfold unmarked. rewrite negateP_spec'. rewrite PRE_unm.
      rewrite (Union_comm _ marked').
      rewrite (triple_mark_aux1' g PV1 root marked') by auto.
      rewrite reachable_by_eq_partialgraph_reachable'.
      rewrite <- Intersection_Complement.
      rewrite <- partial_partialgraph, <- PRE_psi.
      rewrite <- reachable_by_eq_partialgraph_reachable'.
      rewrite reachable_by_through_singleton'.
      apply Intersection2_Included.
      rewrite !reachable_by_eq_partialgraph_reachable', !partial_partialgraph.
      rewrite Intersection_Complement.
      rewrite (triple_mark_aux1' g _ root marked') by auto.
      rewrite Intersection_Complement.
      apply Included_refl.
Qed.

Lemma triple2_mark: forall (g g1 g2: Graph) root l l_done son l_later,
  vvalid g root ->
  (unmarked g) root ->
  let marked' := Union _ (marked g) (eq root) in
  step_list g root l ->
  l = l_done ++ son :: l_later ->
  let PV1 := reachable_by_through_set g l_done (Complement _ marked') in
  (predicate_partialgraph g (Complement _ (Union _ PV1 (eq root)))) ~=~
  (predicate_partialgraph g1 (Complement _ (Union _ PV1 (eq root)))) /\
  Same_set (marked g1) (Union _ marked' PV1) ->
  mark son g1 g2 ->
  let PV2 := reachable_by_through_set g (l_done ++ son :: nil) (Complement _ marked') in
  Same_set (marked g2) (Union _ marked' PV2).
Proof.
  intros.
  destruct H3 as [PRE_psi PRE_unm].
  apply mark_marked' in H4.
  rewrite H4, PRE_unm.
  rewrite Union_assoc.
  apply Union_proper; [reflexivity |].
  unfold unmarked.
  rewrite negateP_spec'.
  rewrite PRE_unm.
  unfold PV2.
  rewrite reachable_by_eq_partialgraph_reachable'.
  rewrite (Union_comm _ marked' PV1).
  rewrite (triple_mark_aux1' g PV1 root marked') by auto.
  rewrite <- Intersection_Complement.
  rewrite <- partial_partialgraph, <- PRE_psi.
  rewrite partial_partialgraph.
  rewrite Intersection_Complement.
  rewrite <- (triple_mark_aux1' g PV1 root marked') by auto.
  rewrite <- Intersection_Complement.
  rewrite <- partial_partialgraph, <- reachable_by_eq_partialgraph_reachable'.
  unfold PV2.
  fold PV1.
  rewrite reachable_by_through_app_strong', reachable_by_through_singleton'.
  + rewrite !reachable_by_eq_partialgraph_reachable'.
    rewrite partial_partialgraph.
    rewrite Intersection_comm. 
    reflexivity.
  + rewrite Same_set_spec in PRE_unm |- *.
    intro v; specialize (PRE_unm v).
    rewrite Union_spec in PRE_unm |- *.
    unfold PV1 in PRE_unm.
    unfold Complement at 2; unfold Ensembles.In.
    pose proof reachable_by_through_set_foot_prop g l_done v (Complement V marked').
    unfold Complement at 2 in H3; unfold Ensembles.In in H3.
    assert ((marked g1) v \/ ~ (marked g1) v) by (destruct (node_pred_dec (marked g1) v); auto).
    assert (marked' v \/ ~ marked' v).
    1: {
      unfold marked'.
      rewrite Union_spec.
      destruct (node_pred_dec (marked g) v); destruct_eq_dec root v; auto.
      tauto.
    }
    pose proof Full_intro _ v.
    unfold Ensembles.In in H.
    tauto.
Qed.

Lemma triple_mark1: forall root (g g1 g2: Graph),
  nothing root g g1 ->
  mark1 root g1 g2 ->
  let marked' := Union _ (marked g) (eq root) in
  let PV1 := reachable_by_through_set g nil (Complement _ marked') in
  (predicate_partialgraph g (Complement _ (Union _ PV1 (eq root)))) ~=~
  (predicate_partialgraph g2 (Complement _ (Union _ PV1 (eq root)))) /\
  Same_set (marked g2) (Union _ marked' PV1).
Proof.
  intros.
  split.
  + destruct H, H0.
    rewrite <- H0.
    eapply si_stronger_partialgraph_simple; [| eauto].
    apply Complement_Included_rev.
    apply right_Included_Union.
  + unfold PV1, marked'.
    rewrite Same_set_spec; intro n; rewrite !Union_spec.
    rewrite reachable_by_through_nil.
    destruct H0 as [_ [? ?]].
    destruct_eq_dec root n.
    - subst n; tauto.
    - specialize (H1 n).
      destruct H.
      specialize (H3 n).
      tauto.
Qed.

Lemma triple_final: forall root l (g g1: Graph),
  vvalid g root ->
  (unmarked g) root ->
  step_list g root l ->
  let marked' := Union _ (marked g) (eq root) in
  let PV1 := reachable_by_through_set g l (Complement _ marked') in
  (predicate_partialgraph g (Complement _ (Union _ PV1 (eq root)))) ~=~
  (predicate_partialgraph g1 (Complement _ (Union _ PV1 (eq root)))) /\
  Same_set (marked g1) (Union _ marked' PV1) ->
  mark root g g1.
Proof.
  intros.
  destruct H2.
  assert (Same_set (reachable_by g root (unmarked g)) (Union _ (eq root) PV1)).
  1: {
    rewrite Same_set_spec.
    intro. rewrite Union_spec.
    unfold PV1, marked'.
    rewrite <- Intersection_Complement.
    apply reachable_by_ind_equiv; auto.
  }
  split.
  + eapply si_stronger_partialgraph_simple; [| exact H2].
    apply Complement_Included_rev.
    rewrite H4.
    rewrite Union_comm.
    apply Included_refl.
  + intros.
    rewrite Same_set_spec in H3; rewrite (H3 n).
    rewrite Same_set_spec in H4; rewrite (H4 n).
    unfold marked'.
    rewrite !Union_spec.
    tauto.
Qed.

Lemma triple_mark1_componded_mark_list: forall root l_done l_later l (g1 g2: Graph),
  vvalid g1 root ->
  (unmarked g1) root ->
  step_list g1 root l ->
  l = l_done ++ l_later ->
  relation_list (nothing root :: mark1 root :: nothing root :: componded_mark_list root l_done :: nil) g1 g2 ->
  let marked' := Union _ (marked g1) (eq root) in
  let PV1 := reachable_by_through_set g1 l_done (Complement _ marked') in
  (predicate_partialgraph g1 (Complement _ (Union _ PV1 (eq root)))) ~=~
  (predicate_partialgraph g2 (Complement _ (Union _ PV1 (eq root)))) /\
  Same_set (marked g2) (Union _ marked' PV1).
Proof.
  intros root ? ? ? g g4.
  intros.
  destruct_relation_list g1 g2 g3 in H3.
  pose proof triple_mark1 root g g1 g2 H4 H5 as PRE.
  cbv zeta in PRE.
  apply (triple_nothing _ g2 g3 root l nil l H H0 H1 eq_refl) in PRE; [| auto].
  clear g1 g2 H4 H5 H6.
  revert g4 l_later H2 H3; rev_induction l_done; intros.
  + unfold componded_mark_list, relation_list in H3.
    simpl in H3. subst g3.
    auto.
  + clear PRE.
    rename l0 into l_done.
    rewrite <- app_assoc in H3; simpl in H3.
    unfold componded_mark_list in H4; rewrite map_app in H4; simpl in H4.
    apply (proj1 ((proj1 (same_relation_spec _ _) (relation_list_tail _ _)) _ _)) in H4.

    rename g3 into g1, g4 into g5.
    apply compond_relation_spec in H4; destruct H4 as [g2 [? ?]].
    cbv zeta in H2.
    specialize (H2 g2 (x :: l_later) H3 H4).
    rename H2 into PRE; clear H4.

    unfold componded in H5.
    apply compond_relation_spec in H5.
    destruct H5 as [g4 [? ?]].
    apply compond_relation_spec in H2.
    destruct H2 as [g3 [? ?]].
    apply (triple_nothing _ g2 g3 root _ _ _ H H0 H1 H3) in PRE; [| auto].
    apply (triple_nothing _ g4 g5 root l (l_done ++ x :: nil) l_later H H0 H1); [rewrite <- app_assoc; exact H3 | | auto].
    
    split.
    - eapply triple1_mark; eauto.
    - eapply triple2_mark; eauto.
Qed.

Lemma mark1_componded_mark_list_mark: forall root l (g1 g2: Graph),
  vvalid g1 root ->
  (unmarked g1) root ->
  step_list g1 root l ->
  relation_list (nothing root :: mark1 root :: nothing root :: componded_mark_list root l :: nothing root :: nil) g1 g2 ->
  mark root g1 g2.
Proof.
  intros root l g g2.
  intros.
  change (nothing root
          :: mark1 root
             :: nothing root
                :: componded_mark_list root l :: nothing root :: nil)
    with ((nothing root
          :: mark1 root
             :: nothing root
                :: componded_mark_list root l :: nil) +:: nothing root)
    in H2.
  erewrite app_same_relation in H2 by (rewrite @relation_list_tail; reflexivity).
  inversion H2; subst; rename y into g1.
  pose proof triple_mark1_componded_mark_list root l nil l g g1 H H0 H1 (eq_sym (app_nil_r _)) H3.
  cbv zeta in H5.
  apply (triple_nothing _ g1 g2 root l l nil H H0 H1 (eq_sym (app_nil_r _))) in H5.
  apply (triple_final root l g g2 H H0 H1 H5).
  auto.
Qed.

(* TODO: rename it into labeledgraph_vgen? or rename labeledgraph_vgen itself? *)
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
  1: {
    destruct H1 as [? _].
    rewrite <- step_si by eassumption.
    specialize (H0 y);
    rewrite in_app_iff in H0; simpl in H0; tauto.
  }
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
    1: {
      destruct H1.
SearchAbout reachable Proper.

Locate reachable_proper.
rewrite <- H1.
*)

End WeakMarkGraph.

End WeakMarkGraph.
