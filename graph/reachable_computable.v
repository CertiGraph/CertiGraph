Require Import Coq.Sets.Finite_sets.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.
Require Import Coq.omega.Omega.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import Coq.Lists.List.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.MathGraph.
Require Import RamifyCoq.graph.FiniteGraph.

Section REACHABLE_COMPUTABLE.

  Context {V E : Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.

  Definition reach_input := (nat * list V * list V)%type.
  (* an input is (length, working list, visited list). Working list are to be visited. *)

  Definition lengthInput (i : reach_input) :=
    match i with | (len, _, re) => len - length re end.

  Definition inputOrder (i1 i2 : reach_input) := lengthInput i1 < lengthInput i2.

  Lemma inputOrder_wf': forall len i, lengthInput i <= len -> Acc inputOrder i.
  Proof.
    induction len; intros; constructor; intros; unfold inputOrder in * |-; [exfalso | apply IHlen]; intuition.
  Qed.

  Lemma inputOrder_wf : well_founded inputOrder.
  Proof. red; intro; eapply inputOrder_wf'; eauto. Defined.

  (******************************************
   
  Definition and lemmas of remove_list. The
  core step in BFS.
   
  ******************************************)

  Section UniquePreGraph.

  Variable G: PreGraph V E.
  Context {is_null: DecidablePred V}.
  Context {MA: MathGraph G is_null}.
  Context {LF: LocalFiniteGraph G}.
  
  Lemma weak_In_dec: forall l x, {In x l \/ is_null x} + {~ (In x l \/ is_null x)}.
  Proof.
    intros.
    apply sumbool_dec_or; [| apply is_null_dec].
    apply in_dec; intros.
    apply equiv_dec.
  Qed.

  Definition new_working_list (l1 l2 l3 : list V) : list V :=
    filter (fun x => if weak_In_dec l3 x then false else true) (l1 ++ l2).
  (* l1 is the tail of original working list,
     l2 is all hop-1 neighbor of the head of original working list,
     l3 is visited list. *)

  Lemma new_working_list_sublist: forall l1 l2 l3, incl (new_working_list l1 l2 l3) (l1 ++ l2). Proof. intros; apply filter_incl; auto. Qed.

  Lemma in_new_working_list: forall l1 l2 l3 x,
    In x (new_working_list l1 l2 l3) <->
    In x (l1 ++ l2) /\ ~ In x l3 /\ ~ is_null x.
  Proof.
    intros.
    unfold new_working_list; rewrite filter_In.
    assert (false = true <-> False) by (split; [congruence | tauto]).
    destruct (weak_In_dec l3 x); tauto.
  Qed.

  Lemma construct_omega: forall len (r : list V),  (~ len <= length r) -> len - S (length r) < len - length r.
  Proof. intros; omega. Qed.

  Definition construct_reachable : reach_input -> list V.
    refine (
        Fix inputOrder_wf (fun _ => list V)
            (fun (inp : reach_input) =>
               match inp return ((forall inp2, inputOrder inp2 inp -> list V) -> list V) with
                 | (_, nil, r) => fun _ => r
                 | (len, g :: l, r) => fun f =>
                                         if le_dec len (length r)
                                         then r
                                         else let newL := new_working_list l (map (dst G) (edge_func G g)) (g :: r) in f (len, newL, g :: r) _
               end)).
    unfold inputOrder, lengthInput. simpl. apply construct_omega; auto.
  Defined.

  Lemma construct_reachable_unfold:
    forall i,
      construct_reachable i = match i with
                                | (_, nil, r) => r
                                | (len, g :: l, r) =>
                                  if le_dec len (length r)
                                  then r
                                  else let newL := new_working_list l (map (dst G) (edge_func G g)) (g :: r) in
                                       construct_reachable (len, newL, g :: r)
                              end.
  Proof.
    intros. destruct i as [[n pr] rslt]. unfold construct_reachable at 1; rewrite Fix_eq.
    destruct pr; simpl. auto. destruct (le_dec n (length rslt)). auto. unfold construct_reachable; auto.
    intros; assert (f = g) by (extensionality y; extensionality p; auto); subst; auto.
  Qed.

  Section Soundness.

  Definition rch1 (i : reach_input) := match i with (n, _, _) => n end.

  Definition rch2 (i : reach_input) := match i with (_, l, _) => l end.

  Definition rch3 (i: reach_input) := match i with (_, _, result) => result end.

  Definition invariant (P: reach_input -> Prop): Prop :=
    forall len g l r, ~ (len <= length r) -> P (len, g :: l, r) ->
      let newL := new_working_list l (map (dst G) (edge_func G g)) (g :: r) in P (len, newL, g :: r).

  Definition sound1 (P: reach_input -> Prop) (Q: list V -> Prop): Prop :=
    forall len r, P (len, nil, r) -> Q r.

  Definition sound2 (P: reach_input -> Prop) (Q: list V -> Prop): Prop :=
    forall len g l r, len <= length r -> P (len, g :: l, r) -> Q r.

  Lemma sound_by_invariance: forall (P: reach_input -> Prop) (Q: list V -> Prop) i, P i -> invariant P -> sound1 P Q -> sound2 P Q -> Q (construct_reachable i).
  Proof.
    intros.
    remember (lengthInput i).
    assert (lengthInput i <= n) by omega; clear Heqn.
    revert i H H3; induction n; intros; remember (construct_reachable i) as r; destruct i as [[len pr] rslt]; simpl in *;
    rewrite construct_reachable_unfold in Heqr; destruct pr; simpl in Heqr.
    + subst. apply H1 in H; auto.
    + destruct (le_dec len (length rslt)).
      - subst; apply H2 in H; auto.
      - exfalso; omega.
    + subst. apply H1 in H; auto.
    + destruct (le_dec len (length rslt)).
      - subst; apply H2 in H; auto.
      - subst.
        apply IHn; [apply H0; auto |].
        simpl.
        omega.
  Qed.

  Definition rch1_is_bound i: Prop := rch1 i <= length (rch3 i) -> rch2 i = nil.

  Lemma sound_by_invariance': forall (P: reach_input -> Prop) (Q: list V -> Prop) i, 
    P i ->
    (forall i, P i -> rch1_is_bound i) ->
    invariant P ->
    sound1 P Q ->
    Q (construct_reachable i).
  Proof.
    intros.
    apply sound_by_invariance with P; auto.
    intros ? ? ? ? ? ?.
    specialize (H0 _ H4 H3).
    inversion H0.
  Qed.    

  Lemma invariant_and: forall P1 P2, invariant P1 -> invariant P2 -> invariant (fun i => P1 i /\ P2 i).
  Proof.
    intros.
    intros i g l r HH; specialize (H i g l r HH); specialize (H0 i g l r HH).
    simpl in H, H0. simpl.
    tauto.
  Qed.

  Lemma sound1_strengthen: forall (P1 P2: reach_input -> Prop) Q, (forall i, P1 i -> P2 i) -> sound1 P2 Q -> sound1 P1 Q.
  Proof.
    intros.
    intros ? ? ?.
    apply H in H1.
    apply H0 in H1; auto.
  Qed.

  Lemma sound1_and: forall (P: reach_input -> Prop) Q1 Q2, sound1 P Q1 -> sound1 P Q2 -> sound1 P (fun i => Q1 i /\ Q2 i).
  Proof.
    intros.
    intros ? ? ?.
    pose proof H _ _ H1.
    pose proof H0 _ _ H1.
    tauto.
  Qed.

  (* Invariance 0 *)
  Definition reachable_bounded x i := forall l, NoDup l -> Forall (reachable G x) l -> length l <= rch1 i.

  (* Invariance 1 *)
  Definition Forall_reachable x i := Forall (reachable G x) (rch2 i ++ rch3 i).

  (* Invariance 2 *)
  Definition input_nodup i := NoDup (rch3 i) /\ (forall x, In x (rch2 i) -> In x (rch3 i) -> False).

  (* Invariance 3 *)
  Definition reachable_covered x i := forall y, reachable G x y -> exists z, In z (rch2 i ++ rch3 i) /\ reachable G z y /\ reachable G x z.

  (* Invariance 4 *)
  Definition edge_closed i:= forall x y, In x (rch3 i) -> edge G x y -> In y (rch2 i ++ rch3 i).

  (* Conclusion 1 *)
  Definition res_reachable_sound x res := Forall (reachable G x) res.

  (* Conclusion 2 *)
  Definition res_nodup: list V -> Prop := @NoDup V.

  (* Conclusion 3 *)
  Definition res_reachable_covered x res := forall y, reachable G x y -> exists z, In z res /\ reachable G z y.

  (* Conclusion 4 *)
  Definition res_reachable_closed res := forall x y, In x res -> reachable G x y -> In y res.

  Lemma Invariance0: forall x, invariant (reachable_bounded x).
  Proof.
    unfold reachable_bounded.
    intros; intros len g l r; simpl; intros.
    apply H0; auto.
  Qed.

  Lemma Invariance1: forall x, invariant (Forall_reachable x).
  Proof.
    unfold Forall_reachable.
    intros; intros len g l r. simpl. intros.
    rewrite Forall_forall in *. intro y; intros; simpl in *.
    rewrite in_app_iff in H1.
    destruct H1.
    + pose proof new_working_list_sublist l (map (dst G) (edge_func G g)) (g :: r) y H1.
      rewrite in_app_iff in H2.
      destruct H2; [apply H0; right; rewrite in_app_iff; tauto |].
      rewrite <- edge_func_step in H2.
      apply reachable_step with g; auto.
      rewrite step_spec in H2.
      destruct H2 as [e [? [? ?]]].
      apply (valid_graph G) in H2. rewrite H4 in H2.
      destruct H2 as [_ [? | ?]]; auto.
      rewrite in_new_working_list in H1.
      tauto.
    + apply H0.
      destruct H1; [left | right]; auto.
      rewrite in_app_iff; tauto.
  Qed.

  Lemma sound1_inv1: forall x, sound1 (Forall_reachable x) (res_reachable_sound x).
  Proof.
    intros.
    unfold sound1, Forall_reachable, res_reachable_sound.
    simpl; intros; auto.
  Qed.

  Lemma Invariance2: invariant input_nodup.
  Proof.
    unfold input_nodup.
    intros; intros len g l r; simpl; intros.
    split.
    + constructor; [| tauto].
      destruct H0 as [_ ?].
      specialize (H0 g).
      spec H0; [left; auto |].
      exact H0.
    + intros.
      rewrite in_new_working_list in H1.
      simpl in H1.
      tauto.
  Qed.

  Lemma sound1_inv2: sound1 input_nodup res_nodup.
  Proof.
    intros.
    unfold sound1, input_nodup, res_nodup.
    simpl; intros; tauto.
  Qed.

  Lemma Invariance3: forall x, invariant (reachable_covered x).
  Proof.
    unfold reachable_covered.
    intros; intros len g l r; simpl; intros.
    specialize (H0 y H1).
    destruct H0 as [z [? [? ?]]].
    rewrite in_app_iff in H0.
    exists z; split; [| split]; auto.
    destruct_eq_dec g z; [| destruct H0; [tauto |]; destruct (in_dec equiv_dec z r); [| destruct H0; try tauto]].
    + subst.
      rewrite in_app_iff; right.
      left; auto.
    + rewrite in_app_iff; right.
      right; auto.
    + rewrite in_app_iff.
      left.
      rewrite in_new_working_list.
      split.
      - rewrite in_app_iff.
        rewrite <- edge_func_step.
        unfold edge in H0; tauto.
      - pose proof valid_not_null G z.
        apply reachable_foot_valid in H3.
        simpl; tauto.
  Qed.
            
  Lemma sound1_inv3: forall x, sound1 (reachable_covered x) (res_reachable_covered x).
  Proof.
    intros.
    unfold sound1, reachable_covered, res_reachable_covered.
    simpl; intros.
    destruct (H y H0) as [z [? [? ?]]]; exists z; tauto.
  Qed.

  Lemma Invariance4: invariant edge_closed.
  Proof.
    unfold edge_closed.
    intros; intros len g l r; simpl; intros.
    destruct H1.
    + rewrite in_app_iff.
      destruct (in_dec equiv_dec y (g :: r)); [right; auto | left].
      rewrite in_new_working_list, in_app_iff.
      subst; unfold edge in H2.
      split; [| split; [auto | pose proof valid_not_null G y; tauto]].
      right.
      rewrite <- edge_func_step.
      tauto.
    + specialize (H0 x y H1 H2).
      rewrite in_app_iff in H0 |- *.
      destruct (in_dec equiv_dec y (g :: r)); [right; auto | left].
      simpl in n.
      destruct H0 as [? | [? | ?]]; [tauto | | tauto].
      rewrite in_new_working_list, in_app_iff.
      unfold edge in H2.
      split; [| split; [auto | pose proof valid_not_null G y; tauto]].
      left; auto.
  Qed.

  Lemma sound1_inv4: sound1 edge_closed res_reachable_closed.
  Proof.
    intros.
    unfold sound1, edge_closed, res_reachable_closed.
    simpl. intros ? ? ?.
    apply closed_edge_closed_reachable; auto.
  Qed.

  End Soundness.

  Lemma finite_reachable_computable': forall x (X: EnumCovered V (reachable G x)) l', vvalid G x -> l' = construct_reachable (length (proj1_sig X), x :: nil, @nil V) ->
                                                                                      reachable_list G x l' /\ NoDup l'.
  Proof.
    intros. subst l'. destruct X as [l [? ?H]]. simpl. clear n. set (i := (length l, x :: nil, @nil V)). unfold Ensembles.In in *.
    pose proof sound_by_invariance'
      (fun i => reachable_bounded x i /\
                Forall_reachable x i /\
                input_nodup i /\
                reachable_covered x i /\
                edge_closed i)
      (fun l => res_reachable_sound x l /\
                res_nodup l /\
                res_reachable_covered x l /\
                res_reachable_closed l)
      i as MainTheorem.
    spec MainTheorem; [| spec MainTheorem; [| spec MainTheorem; [| spec MainTheorem]]];
      [clear MainTheorem .. |].
    + (* Prove all invariances are true on input *)
      subst i; repeat split; simpl.
      - unfold reachable_bounded; simpl.
        intros.
        rewrite Forall_forall in H2.
        assert (incl l0 l).  unfold incl. exact (fun a H => H0 a (H2 a H)).
        apply NoDup_incl_length; auto.
      - unfold Forall_reachable; simpl.
        repeat constructor.
        apply reachable_refl; auto.
      - constructor.
      - intros; auto.
      - unfold reachable_covered; simpl.
        intros.
        exists x.
        repeat split; auto.
        apply reachable_refl; auto.
      - unfold edge_closed; simpl.
        intros; auto.
    + (* Prove that rch1_is_bound is implied by invariance *)
      intros ? [? [? [? _]]].
      unfold reachable_bounded, Forall_reachable, input_nodup, rch1_is_bound in *.
      intros.
      rewrite Forall_app_iff in H2. destruct H2.
      destruct H3.
      specialize (H1 (nodup equiv_dec (rch2 i0) ++ rch3 i0)).
      spec H1.
      1: {
        apply NoDup_app_inv.
        + apply NoDup_nodup.
        + auto.
        + intros; intro.
          rewrite nodup_In in H7.
          eapply H6; eauto.
      }
      spec H1.
      1: {
        apply Forall_app_iff; split; auto.
        rewrite Forall_forall in H2 |- *; intros.
        rewrite nodup_In in H7.
        apply H2; auto.
      }
      rewrite app_length in H1.
      assert (length (nodup equiv_dec (rch2 i0)) = 0) by omega.
      clear - H7. remember (rch2 i0). clear Heql. induction l; auto.
      simpl in H7. destruct (in_dec equiv_dec a l).
      * specialize (IHl H7). subst. inversion i.
      * simpl in H7. inversion H7.
    + (* Prove all invariances are invariant *)
      apply invariant_and; [apply Invariance0 |].
      apply invariant_and; [apply Invariance1 |].
      apply invariant_and; [apply Invariance2 |].
      apply invariant_and; [apply Invariance3 | apply Invariance4].
    + (* Prove that terminating condition is entailed by invariances *)
      apply sound1_and; [eapply sound1_strengthen; [| apply sound1_inv1]; intros; tauto |].
      apply sound1_and; [eapply sound1_strengthen; [| apply sound1_inv2]; intros; tauto |].
      apply sound1_and; [eapply sound1_strengthen; [| apply sound1_inv3]; intros; tauto |].
      eapply sound1_strengthen; [| apply sound1_inv4]; intros; tauto.
    + (* Prove that terminating condition implies conclusion *)
      unfold res_reachable_sound, res_nodup, res_reachable_covered, res_reachable_closed, reachable_list in *.
      destruct MainTheorem as [? [? [? ?]]]; split; [intro; split; intro |].
      - clear - H1 H5.
        rewrite Forall_forall in H1; apply H1; auto.
      - destruct (H3 _ H5) as [z [? ?]].
        apply H4 with z; auto.
      - auto.
  Qed.

  Theorem finite_reachable_computable: forall x, vvalid G x -> (EnumCovered V (reachable G x)) ->
                                          {l': list V | reachable_list G x l' /\ NoDup l'}.
  Proof.
    intros. remember (construct_reachable (length (proj1_sig X), x :: nil, nil)).
    pose proof (finite_reachable_computable' x X l H Heql). exists l; auto.
  Qed.

  Corollary finite_reachable_enumcovered_enumerable: forall x, vvalid G x -> EnumCovered V (reachable G x) -> Enumerable V (reachable G x).
  Proof. intros. destruct (finite_reachable_computable _ H X) as [l [? ?]]. exists l. split; auto. Qed.
  
  Lemma compute_reachable: forall x L,
                             reachable_list G x L -> forall y, reachable G x y ->
                                                          {L' : list V | reachable_list G y L' /\ NoDup L'}.
  Proof.
    intros.
    assert (vvalid G y) by (apply reachable_foot_valid in H0; auto).
    apply finite_reachable_computable; auto.
    apply EnumCovered_strengthen with (reachable G x).
    + intros ? ?.
      apply reachable_by_trans with y; auto.
    + eapply reachable_list_EnumCovered; eauto.
  Qed.

  Lemma compute_neighbor: forall x l,
                            vvalid G x -> reachable_list G x l -> forall y, step G x y -> 
                                                              {l' | reachable_list G y l' /\ NoDup l'}.
  Proof.
    intros.
    pose proof valid_step _ _ _ H1.
    destruct (@null_or_valid _ _ _ _ _ G _ _ (proj2 H2)).
    + subst. exists nil. split.
      - intro. split; intro; [inversion H3 |]. apply reachable_head_valid in H3. 
        apply (@valid_not_null _ _ _ _ G is_null) in H3; auto.
      - apply NoDup_nil.
    + apply (compute_reachable x l).
      - auto.
      - apply reachable_edge with x. 1: apply reachable_refl; auto.
        hnf. auto.
  Qed.
(*
  Lemma reachable_from_children:
    forall x y, reachable pg x y -> y = x \/ exists z, pg |= x ~> z /\ reachable pg z y.
  Proof.
    intros. destruct H as [p ?]. destruct p. destruct H. destruct H. inversion H. destruct H as [[? ?] [? ?]].
    simpl in H. inversion H. subst. destruct p. simpl in H0. inversion H0. left; auto. right. hnf in H1. destruct H1.
    exists v. split; auto. destruct H1 as [? [? ?]]. exists (v :: p). split; split. simpl. auto. simpl in H0. simpl. apply H0.
    auto. hnf. intros. hnf. auto.
  Qed.
*)
  Lemma finite_reachable_set_single:
    forall S, EnumCovered V (reachable_through_set G S) ->
              forall s, In s S -> vvalid G s ->
              {l : list V | reachable_list G s l /\ NoDup l}.
  Proof.
    intros.
    apply finite_reachable_computable; auto.
    apply EnumCovered_strengthen with (reachable_through_set G S); auto.
    intros ? ?.
    exists s; split; auto.
  Qed.

  Lemma reachable_through_single_reachable':
    forall S l, reachable_set_list G S l ->
      forall s, In s S -> vvalid G s -> {l' : list V | reachable_list G s l' /\ NoDup l'}.
  Proof.
    intros.
    apply finite_reachable_set_single with S; auto.
    eapply reachable_set_list_EnumCovered; eauto.
  Qed.

  Lemma reachable_set_enumcovered_single_reachable:
    forall S, EnumCovered V (reachable_through_set G S) ->
      forall s, In s S -> weak_valid G s -> {l' : list V | reachable_list G s l' /\ NoDup l'}.
  Proof.
    intros.
    destruct (@null_or_valid _ _ _ _ _ G _ _ H0).
    + subst. exists nil. split.
      - unfold reachable_list. intro. split; intros.
        * inversion H1.
        * apply reachable_head_valid in H1. apply (@valid_not_null _ _ _ _ G is_null) in H1; auto.
      - apply NoDup_nil.
    + apply finite_reachable_set_single with S; auto.
  Qed.

  Lemma reachable_through_single_reachable:
    forall S l, reachable_set_list G S l ->
      forall s, In s S -> weak_valid G s -> {l' : list V | reachable_list G s l' /\ NoDup l'}.
  Proof.
    intros. apply (reachable_set_enumcovered_single_reachable S); auto.
    eapply reachable_set_list_EnumCovered; eauto.
  Qed.

  Lemma reachable_through_set_enum:
    forall S, EnumCovered V (reachable_through_set G S) ->
              forall s, incl s S -> well_defined_list G s -> Enumerable V (reachable_through_set G s).
  Proof.
    intros. induction s.
    - exists nil. split. 1: apply NoDup_nil.
      simpl. unfold reachable_through_set. unfold Ensembles.In. intros. split; intros.
      + exfalso; auto.
      + destruct H1 as [? [? ?]]. inversion H1.
    - spec IHs; [eapply incl_tran; [apply incl_tl, incl_refl | apply H] |].
      spec IHs; [intros x HH; apply (H0 x); right; auto |].
      destruct IHs as [l1 [? ?]].
      destruct (reachable_set_enumcovered_single_reachable S X a) as [l2 [? ?]].
      1: apply (H a); left; auto.
      1: specialize (H0 a); spec H0; [left; auto |]; destruct H0; [left | right]; auto.
      exists (nodup equiv_dec (l1 ++ l2)). split. 1: apply NoDup_nodup.
      unfold reachable_list, reachable_through_set, Ensembles.In in *.
      intros x; rewrite nodup_In.
      rewrite in_app_iff. specialize (H2 x). specialize (H3 x).
      split; intros.
      + destruct H5; [| exists a; split; [left; auto | tauto]].
        rewrite H2 in H5.
        destruct H5 as [s0 ?H]; exists s0.
        split; [right|]; tauto.
      + destruct H5 as [s0 ?H].
        destruct_eq_dec a s0; [right | left]; subst; try tauto.
        apply H2.
        exists s0; simpl in H5; tauto.
  Qed.

  Lemma reachable_through_sublist_reachable:
    forall S l, reachable_set_list G S l ->
      forall s, incl s S -> well_defined_list G s -> { l' : list V | reachable_set_list G s l' /\ NoDup l'}.
  Proof.
    intros. cut (Enumerable V (reachable_through_set G s)).
    + intros. destruct X as [l1 [? ?]]. unfold Ensembles.In in H3. exists l1. split; auto.
    + apply (reachable_through_set_enum S); auto.
      apply reachable_set_list_EnumCovered in H; auto.
  Qed.

  Lemma reachable_decidable_prime:
    forall x,
      vvalid G x ->
      EnumCovered V (reachable G x) ->
      forall y, {reachable G x y} + {~ reachable G x y}.
  Proof.
    intros.
    destruct (finite_reachable_computable x H X) as [l' [? ?]]. specialize (H0 y).
    destruct (in_dec equiv_dec y l').
    + rewrite H0 in i. left; auto.
    + rewrite H0 in n. right; auto.
  Qed.

  Lemma reachable_decidable:
    forall x,
      {vvalid G x} + {~ vvalid G x} ->
      EnumCovered V (reachable G x) ->
      forall y, {reachable G x y} + {~ reachable G x y}.
  Proof.
    intros.
    destruct H as [H | H].
    + apply reachable_decidable_prime; auto.
    + right.
      intro.
      apply reachable_head_valid in H0.
      tauto.
  Qed.

  End UniquePreGraph.

  Lemma reachable_by_decidable (G: PreGraph V E) {is_null: DecidablePred V} {MA: MathGraph G is_null} {LF: LocalFiniteGraph G}:
    forall (p : NodePred V) x ,
      {vvalid G x} + {~ vvalid G x} ->
      EnumCovered V (reachable G x) ->
      ReachDecidable G x p.
  Proof.
    intros.
    destruct H as [H | H].
    2: {
      right.
      intro; apply reachable_by_is_reachable in H0.
      apply reachable_head_valid in H0; tauto.
    }
    remember (predicate_subgraph G p) as pdg.
    destruct (node_pred_dec p x).
    + assert (vvalid pdg x) by (subst; split; auto).
      assert (EnumCovered V (reachable pdg x)). {
        subst.
        apply EnumCovered_strengthen with (reachable G x); auto.
        apply predicate_subgraph_reachable_included.
      } subst.
      intro y.
      destruct (@reachable_decidable_prime _ _ (predicate_sub_mathgraph _ p _) (predicate_sub_localfinitegraph _ p _) x H0 X0 y).
      - rewrite <- reachable_by_eq_subgraph_reachable in r. left; auto.
      - rewrite <- reachable_by_eq_subgraph_reachable in n. right; auto.
    + right.
      intro.
      apply reachable_by_head_prop in H0.
      tauto.
  Qed.

End REACHABLE_COMPUTABLE.
