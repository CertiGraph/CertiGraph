Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.
Require Import RamifyCoq.Coqlib.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.

Section REACHABLE_COMPUTABLE.

  Context {V E : Type}.

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
  Context {MA: MathGraph G}.
  Context {LF: LocalFiniteGraph G}.
  
  Lemma weak_In_dec: forall l x, {In x l \/ is_null x} + {~ (In x l \/ is_null x)}.
  Proof.
    intros.
    apply sumbool_dec_or; [| apply is_null_dec].
    apply in_dec; intros.
    apply t_eq_dec.
  Qed.

  Definition new_working_list (l1 l2 l3 : list V) : list V :=
    filter (fun x => if weak_In_dec l3 x then false else true) (l1 ++ l2).
  (* l1 is the tail of original working list,
     l2 is all hop-1 neighbor of the head of original working list,
     l3 is visited list. *)

  Lemma new_working_list_sublist: forall l1 l2 l3, Sublist (new_working_list l1 l2 l3) (l1 ++ l2).
  Proof. intros; apply filter_sublist; auto. Qed.

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
                                         else let newL := new_working_list l (map dst (edge_func G g)) (g :: r) in f (len, newL, g :: r) _
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
                                  else let newL := new_working_list l (map dst (edge_func G g)) (g :: r) in
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
      let newL := new_working_list l (map dst (edge_func G g)) (g :: r) in P (len, newL, g :: r).

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
    simpl in H, H0.
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
    intros; intros len g l r; intros.
    rewrite Forall_forall in *. intro y; intros; simpl in *.
    rewrite in_app_iff in H1.
    destruct H1.
    + pose proof new_working_list_sublist l (map dst (edge_func G g)) (g :: r) y H1.
      rewrite in_app_iff in H2.
      destruct H2; [apply H0; right; rewrite in_app_iff; tauto |].
      rewrite <- edge_func_step in H2.
      apply reachable_step with g; auto.
      rewrite step_spec in H2.
      destruct H2 as [e [? [? ?]]].
      apply valid_graph in H2; rewrite H4 in H2.
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
    destruct (t_eq_dec g z); [| destruct H0; [tauto |]; destruct (in_dec t_eq_dec z r); [| destruct H0; try tauto]].
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
      - pose proof valid_not_null z.
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
      destruct (in_dec t_eq_dec y (g :: r)); [right; auto | left].
      rewrite in_new_working_list, in_app_iff.
      subst; unfold edge in H2.
      split; [| split; [auto | pose proof valid_not_null y; tauto]].
      right.
      rewrite <- edge_func_step.
      tauto.
    + specialize (H0 x y H1 H2).
      rewrite in_app_iff in H0 |- *.
      destruct (in_dec t_eq_dec y (g :: r)); [right; auto | left].
      simpl in n.
      destruct H0 as [? | [? | ?]]; [tauto | | tauto].
      rewrite in_new_working_list, in_app_iff.
      unfold edge in H2.
      split; [| split; [auto | pose proof valid_not_null y; tauto]].
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

  Lemma finite_reachable_computable: forall x, vvalid x -> (EnumCovered V (reachable G x)) ->
                                          {l': list V | reachable_list G x l' /\ NoDup l'}.
  Proof.
    intros.
    destruct X as [l [_ ?H]]; unfold Ensembles.In in *.
    set (i := (length l, x :: nil, @nil V)). exists (construct_reachable i).
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
        assert (Sublist l0 l) by (unfold Sublist; firstorder).
        apply NoDup_Sublist_length; [apply t_eq_dec | |]; auto.
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
      specialize (H1 (remove_dup t_eq_dec (rch2 i0) ++ rch3 i0)).
      spec H1.
      Focus 1. {
        apply NoDup_app_inv.
        + apply remove_dup_nodup.
        + auto.
        + intros; intro.
          rewrite <- remove_dup_in_inv in H7.
          eapply H6; eauto.
      } Unfocus.
      spec H1.
      Focus 1. {
        apply Forall_app_iff; split; auto.
        rewrite Forall_forall in H2 |- *; intros.
        rewrite <- remove_dup_in_inv in H7.
        apply H2; auto.
      } Unfocus.
      rewrite app_length in H1.
      assert (length (remove_dup t_eq_dec (rch2 i0)) = 0) by omega.
      clear - H7.
      rewrite remove_dup_unfold in H7.
      destruct (rch2 i0); [auto | inversion H7].
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

  Lemma compute_reachable: forall x L,
                             reachable_list G x L -> forall y, reachable G x y ->
                                                          {L' : list V | reachable_list G y L' /\ NoDup L'}.
  Proof.
    intros.
    assert (vvalid y) by (apply reachable_foot_valid in H0; auto).
    apply finite_reachable_computable; auto.
    apply EnumCovered_strengthen with (reachable G x).
    + intros ? ?.
      apply reachable_by_merge with y; auto.
    + eapply reachable_list_EnumCovered; eauto.
  Qed.

  Lemma compute_neighbor: forall x l,
                            vvalid x -> reachable_list G x l -> forall y, step G x y -> 
                                                              {l' | reachable_list G y l' /\ NoDup l'}.
  Proof.
    intros.
    pose proof valid_step _ _ _ H1.
    destruct (null_or_valid _ _ (proj2 H2)).
    + subst. exists nil. split.
      - intro. split; intro; [inversion H3 |]. apply reachable_head_valid in H3. apply valid_not_null in H3. exfalso; auto. auto.
      - apply NoDup_nil.
    + apply (compute_reachable x l).
      - auto.
      - exists (x :: y :: nil). split; split; simpl; auto.
        * split; auto. split; auto.
        * hnf; intros; hnf; auto.
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
              forall s, In s S -> vvalid s ->
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
      forall s, In s S -> vvalid s -> {l' : list V | reachable_list G s l' /\ NoDup l'}.
  Proof.
    intros.
    apply finite_reachable_set_single with S; auto.
    eapply reachable_set_list_EnumCovered; eauto.
  Qed.

  Lemma reachable_through_single_reachable:
    forall S l, reachable_set_list G S l ->
      forall s, In s S -> weak_valid s -> {l' : list V | reachable_list G s l' /\ NoDup l'}.
  Proof.
    intros.
    destruct (null_or_valid _ _ H1).
    + subst. exists nil. split.
      - unfold reachable_list. intro. split; intros.
        * inversion H2.
        * apply reachable_head_valid in H2. apply valid_not_null in H2. exfalso; auto. auto.
      - apply NoDup_nil.
    + apply finite_reachable_set_single with S; auto.
      eapply reachable_set_list_EnumCovered; eauto.
  Qed.

  Lemma reachable_through_sublist_reachable:
    forall S l, reachable_set_list G S l ->
      forall s, Sublist s S -> well_defined_list G s -> { l' : list V | reachable_set_list G s l' /\ NoDup l'}.
  Proof.
    intros.
    induction s.
    + exists nil. simpl; split; hnf; [| constructor].
      intros.
      unfold reachable_through_set.
      split; intro HH; inversion HH.
      destruct (proj1 H2).
    + spec IHs; [eapply Sublist_trans; [apply Sublist_cons | apply H0] |].
      spec IHs; [intros x HH; apply (H1 x); right; auto |].
      destruct IHs as [l1 ?H].
      destruct (reachable_through_single_reachable S l H a) as [l2 ?].
      1: apply (H0 a); left; auto.
      1: specialize (H1 a); spec H1; [left; auto |]; destruct H1; [left | right]; auto.
      exists (remove_dup t_eq_dec (l1 ++ l2)).
      split; [| apply remove_dup_nodup].
      unfold reachable_set_list, reachable_list, reachable_through_set in *.
      destruct H2 as [?H _], a0 as [?H _].
      intros x; rewrite <- remove_dup_in_inv.
      rewrite in_app_iff.
      specialize (H2 x).
      specialize (H3 x).
      split; intros.
      - destruct H4 as [s0 ?H].
        destruct (t_eq_dec a s0); [right | left]; subst; try tauto.
        apply H2.
        exists s0; simpl in H4; tauto.
      - destruct H4; [| exists a; split; [left; auto | tauto]].
        rewrite <- H2 in H4.
        destruct H4 as [s0 ?H]; exists s0.
        split; [right|]; tauto.
  Qed.

  Lemma reachable_decidable:
    forall x,
      vvalid x ->
      EnumCovered V (reachable G x) ->
      forall y, {reachable G x y} + {~ reachable G x y}.
  Proof.
    intros.
    destruct (finite_reachable_computable x H X) as [l' [? ?]]. specialize (H0 y).
    destruct (in_dec t_eq_dec y l').
    + rewrite H0 in i. left; auto.
    + rewrite H0 in n. right; auto.
  Qed.

  End UniquePreGraph.

  Lemma reachable_by_decidable (G: PreGraph V E) {MA: MathGraph G} {LF: LocalFiniteGraph G}:
    forall (p : NodePred G) x ,
      vvalid x -> EnumCovered V (reachable G x) ->
      forall y, {G |= x ~o~> y satisfying p} + {~ G |= x ~o~> y satisfying p}.
  Proof.
    intros. remember (predicate_subgraph G p) as pdg.
    destruct (node_pred_dec p x).
    + assert (@vvalid _ _ pdg x) by (subst; split; auto).
      assert (EnumCovered V (reachable pdg x)). {
        subst.
        apply EnumCovered_strengthen with (reachable G x); auto.
        admit.
      } subst.
      destruct (@reachable_decidable _ (predicate_sub_mathgraph _ p) (predicate_sub_localfinitegraph _ p) x H0 X0 y).
      - rewrite <- reachable_by_eq_subgraph_reachable in r. left; auto.
      - rewrite <- reachable_by_eq_subgraph_reachable in n. right; auto.
    + right.
      intro.
      apply reachable_by_head_prop in H0.
      tauto.
  Qed.

(*
  Lemma update_reachable_path_in:
    forall {bi : BiGraph pg} {ma : MathGraph pg null} {x : V} {d : D}  {l r: V} {p: list V} {h y: V},
      x <> null -> h <> x -> (update_PreGraph pg x d l r) |= p is h ~o~> y satisfying (fun _: D => True) ->
      In x p -> reachable pg h x.
  Proof.
    intros. generalize (reachable_path_in _ p h y H1 x H2). intro. unfold reachable in H3. rewrite reachable_acyclic in H3.
    destruct H3 as [path [? ?]]. destruct H4 as [[? ?] [? ?]]. apply foot_explicit in H5. destruct H5 as [p' ?]. destruct p'.
    subst. simpl in H4. inversion H4. exfalso; auto. subst. simpl in H4. inversion H4. subst. remember (foot (h :: p')).
    destruct o. apply eq_sym in Heqo. apply foot_explicit in Heqo. destruct Heqo as [pt ?]. generalize H6; intro Hv.
    rewrite H5 in *. rewrite <- app_cons_assoc in H3, H6. clear H7. apply valid_path_split in H6. destruct H6. simpl in H7.
    destruct H7. destruct H7 as [? [? ?]]. simpl in H10. unfold change_edge_func in H10. simpl in H10. generalize H3; intro Hnd.
    apply NoDup_app_r in H3. apply NoDup_cons_2 in H3. apply (not_in_app t_eq_dec) in H3. destruct H3. simpl in H7.
    unfold change_valid in H7. destruct H7. destruct (t_eq_dec v x). exfalso; auto.
    destruct (weak_valid_complete _ (valid_graph v H7 x H10)) as [?H | ?H]. exfalso; auto. rewrite <- H5 in Hv.
    exists ((h :: p') +:: x). split. split. simpl. auto. rewrite foot_last. auto. split. rewrite H5 in *. clear H5 p'.
    rewrite <- app_cons_assoc in Hv. rewrite <- app_cons_assoc. clear H6. induction pt. simpl in Hv. simpl.
    split; auto. destruct Hv as [[? [? ?]] ?]. split; auto. rewrite <- app_comm_cons.
    simpl. destruct (pt ++ v :: x :: nil) eqn:? . destruct pt; inversion Heql0. rewrite <- app_comm_cons in Hnd, Hv.
    rewrite Heql0 in Hnd, Hv. split. assert (a <> x). apply NoDup_cons_2 in Hnd. rewrite <- Heql0 in Hnd. intro. subst.
    apply Hnd. apply in_or_app. right. apply in_cons, in_eq. assert (v0 <> x). destruct pt. simpl in Heql0. inversion Heql0.
    subst. apply NoDup_cons_1 in Hnd. apply NoDup_cons_2 in Hnd. intro. subst. apply Hnd. apply in_eq.
    rewrite <- app_comm_cons in Heql0. inversion Heql0. subst. apply NoDup_cons_1 in Hnd. apply NoDup_cons_2 in Hnd.
    intro; subst; apply Hnd. apply in_or_app. right; apply in_cons, in_eq. rewrite <- (app_nil_l l0) in Hv.
    do 2 rewrite app_comm_cons in Hv. apply valid_path_split in Hv. destruct Hv. simpl in H13. destruct H13 as [[? [? ?]] _].
    simpl in H13, H15, H16. unfold change_valid in H13, H15. unfold change_edge_func in H16. simpl in H16. destruct H13.
    destruct H15. destruct (t_eq_dec a x). exfalso; auto. split; auto. exfalso; auto. exfalso; auto. apply IHpt.
    apply valid_path_tail in Hv. unfold tl in Hv. apply Hv. apply NoDup_cons_1 in Hnd. auto. repeat intro; hnf; auto.
    exfalso; auto. apply eq_sym in Heqo. apply foot_none_nil in Heqo. inversion Heqo.
  Qed.

  Lemma update_reachable_tail_reachable:
    forall {x h: V} {p: list V} {d: D} {l r y: V},
      NoDup (x :: h :: p) -> (update_PreGraph pg x d l r) |= x :: h :: p is x ~o~> y satisfying (fun _ : D => True) ->
      reachable pg h y.
  Proof.
    intros. assert ((update_PreGraph pg x d l r) |= (h :: p) is h ~o~> y satisfying (fun _ : D => True)). split; split.
    simpl. auto. destruct H0 as [[_ ?] _]. rewrite <- (app_nil_l (h :: p)) in H0. rewrite app_comm_cons in H0.
    rewrite foot_app in H0. auto. intro; inversion H1. destruct H0 as [_ [? _]]. rewrite <- (app_nil_l (h :: p)) in H0.
    rewrite app_comm_cons in H0. apply valid_path_split in H0. destruct H0. auto. repeat intro; hnf; auto. exists (h :: p).
    clear H0. split; split. simpl. auto. destruct H1 as [[_ ?] _]. auto. destruct H1 as [_ [? _]]. remember (h :: p) as pa.
    clear Heqpa. induction pa. simpl. auto. simpl in H0. simpl. destruct pa. unfold change_valid in H0. destruct H0; auto.
    subst. apply NoDup_cons_2 in H. exfalso; apply H, in_eq. destruct H0 as [[? [? ?]] ?]. split. assert (a <> x). intro. subst.
    apply NoDup_cons_2 in H. apply H, in_eq. split. simpl in H0. unfold change_valid in H0. destruct H0; auto. exfalso; auto.
    split. simpl in H1. unfold change_valid in H1. destruct H1; auto. subst. apply NoDup_cons_2 in H; exfalso.
    apply H, in_cons, in_eq. simpl in H2. unfold change_edge_func in H2. simpl in H2. destruct (t_eq_dec a x). exfalso; auto.
    auto. apply IHpa. apply NoDup_cons. apply NoDup_cons_2 in H. intro; apply H, in_cons; auto. do 2 apply NoDup_cons_1 in H.
    auto. auto. repeat intro; hnf; auto.
  Qed.

  Lemma update_reachable_by_path_not_in:
    forall {x: V} {p: list V} {d: D} {l r h y: V} {P : Ensemble D},
      ~ In x p -> ((update_PreGraph pg x d l r) |= p is h ~o~> y satisfying P <-> pg |= p is h ~o~> y satisfying P).
  Proof.
    intros; split; intro; split; split. apply reachable_by_path_head in H0; auto. apply reachable_by_path_foot in H0; auto.
    destruct H0 as [_ [? _]]. induction p. simpl; auto. simpl. simpl in H0. destruct p. hnf in H0. destruct H0. auto. subst.
    exfalso; apply H, in_eq. destruct H0. split. destruct H0 as [? [? ?]]. hnf in H0, H2, H3. split. destruct H0. auto. subst.
    exfalso; apply H, in_eq. split. destruct H2. auto. subst. exfalso; apply H, in_cons, in_eq. simpl in H3.
    unfold change_edge_func in H3. destruct (t_eq_dec a x). subst. exfalso; apply H, in_eq. auto. apply IHp. intro. apply H.
    apply in_cons. auto. auto. destruct H0 as [_ [_ ?]]. repeat intro; hnf. specialize (H0 n H1). hnf in H0. simpl in H0.
    unfold change_node_label in H0. destruct (t_eq_dec n x). subst. exfalso; auto. auto.

    apply reachable_by_path_head in H0; auto. apply reachable_by_path_foot in H0; auto.
    destruct H0 as [_ [? _]]. induction p. simpl; auto. simpl. simpl in H0. destruct p. hnf. left. auto. split. destruct H0.
    destruct H0 as [? [? ?]]. split. left; auto. split. left; auto. simpl. unfold change_edge_func. destruct (t_eq_dec a x).
    subst. exfalso; apply H, in_eq. auto. apply IHp. intro. apply H. apply in_cons. auto. destruct H0. auto.
    destruct H0 as [_ [_ ?]]. repeat intro; hnf. specialize (H0 n H1). hnf in H0. simpl. unfold change_node_label.
    destruct (t_eq_dec n x). subst. exfalso; auto. auto.
  Qed.

  End UniquePreGraph.

  (* Definition b_pg_g (g: BiMathGraph V D null) : PreGraph V D := @b_pg V D EDV (@bm_bi V D null EDV g). *)

  (* Definition pg_g (g: BiMathGraph V D null) : PreGraph V D := @pg V D null EDV (@bm_ma V D null EDV g). *)

  (* Definition bm_bi_g (g: BiMathGraph V D null) : BiGraph V D := @bm_bi V D null EDV g. *)

  (* Definition bm_ma_g (g: BiMathGraph V D null) : MathGraph V D null := @bm_ma V D null EDV g. *)

  Definition valid_g (g: PreGraph V D) : V -> Prop := @valid V D EDV g.

  Lemma unreachable_sub_eq_belong_to:
    forall {pg pg' : PreGraph V D} {bi : BiGraph pg} {ma : MathGraph pg null} {bi' : BiGraph pg'} {ma' : MathGraph pg' null} (S1 S1': list V),
      (unreachable_subgraph pg S1) -=- (unreachable_subgraph pg' S1') ->
      forall x S2, ~ reachable_through_set pg S1 x /\ reachable_through_set pg S2 x ->
                   ~ reachable_through_set pg' S1' x /\ reachable_through_set pg' S2 x.
  Proof.
    intros. destruct H as [? [? ?]]. destruct H0. simpl in H, H1, H2. unfold unreachable_valid in H, H1, H2.
    assert (valid_g pg x /\ ~ reachable_through_set pg S1 x). split; auto. destruct H3 as [s [? ?]].
    apply reachable_foot_valid in H4. apply H4. unfold valid_g in H4. rewrite (H x) in H4. split. destruct H4; auto.
    assert (forall s, reachable_through_set pg S1 s -> reachable_through_set pg S2 s ->
                      forall y, reachable pg s y -> reachable_through_set pg S1 y /\
                                                            reachable_through_set pg S2 y). intros; split.
    destruct H5 as [ss [? ?]]. exists ss. split; auto. apply reachable_by_merge with s; auto.
    destruct H6 as [ss [? ?]]. exists ss. split; auto. apply reachable_by_merge with s; auto.
    destruct H3 as [s [? ?]]. destruct H6 as [p ?].
    assert (forall z, In z p -> valid_g pg z /\ ~ reachable_through_set pg S1 z). intros.
    assert (reachable_through_set pg S2 z). generalize (reachable_path_in pg p s x H6 z H7); intro. exists s.
    split; auto. split. destruct H8 as [ss [? ?]]. apply reachable_foot_valid in H9. apply H9.
    assert (reachable pg z x). destruct (reachable_by_path_split_in _ _ _ _ _ _ _ _ _ H6 H7) as [p1 [p2 [? [? ?]]]].
    exists p2. auto. intro. specialize (H5 z H10 H8 x H9). destruct H5. auto.

    exists s. split; auto. exists p. destruct H6 as [[? ?] [? _]]. split; split; auto. clear H4 H5 H6 H8. induction p.
    simpl; auto. unfold valid_g in H7. assert (valid_g pg' a). assert (In a (a :: p)). apply in_eq.
    specialize (H7 _ H4). rewrite H in H7. destruct H7. apply H5. simpl. simpl in H9. destruct p. apply H4. split. split.
    apply H4. split. assert (In v (a :: v :: p)). apply in_cons, in_eq. specialize (H7 _ H5). rewrite H in H7. destruct H7.
    apply H6. destruct H9 as [[_ [_ ?]] _]. assert (In a (a :: v :: p)). apply in_eq. specialize (H7 _ H6).
    specialize (H2 a H7). rewrite <- H2. auto. apply IHp. destruct H9; auto. intros. unfold valid_g. apply H7.
    apply in_cons. auto. repeat intro; hnf; auto.
  Qed.

  Lemma unreachable_sub_eq_unrch_rch_eq:
    forall {pg pg' : PreGraph V D} {bi : BiGraph pg} {ma : MathGraph pg null} {bi' : BiGraph pg'} {ma' : MathGraph pg' null} {S1 S1': list V},
      (unreachable_subgraph pg S1) -=- (unreachable_subgraph pg' S1') ->
      forall x S2, ~ reachable_through_set pg S1 x /\ reachable_through_set pg S2 x <->
                   ~ reachable_through_set pg' S1' x /\ reachable_through_set pg' S2 x.
  Proof.
    intros. split.
    apply (unreachable_sub_eq_belong_to _ _ H x S2). apply vi_sym in H.
    apply (unreachable_sub_eq_belong_to _ _ H x S2).
  Qed.

  Lemma unreachable_node_add_graph_eq:
    forall (pg : PreGraph V D) {bi : BiGraph pg} {ma : MathGraph pg null} x y d l r (Hn: x <> null) (Hi: in_math ma x l r),
      In y (l :: r :: nil) -> (~ reachable pg y x) -> y <> x ->
      ((reachable_subgraph pg (y :: nil)) -=-
       (reachable_subgraph (update_PreGraph pg x d l r) (y :: nil))).
  Proof.
    Implicit Arguments valid [[Vertex] [Data] [EV]].
    Implicit Arguments node_label [[Vertex] [Data] [EV]].
    Implicit Arguments edge_func [[Vertex] [Data] [EV]].
    intros until r. intros ? ? Hin. intros. hnf.
    assert (forall v : V, valid (reachable_subgraph pg (y :: nil)) v <->
                          valid (reachable_subgraph (update_PreGraph pg x d l r) (y :: nil)) v). {
      split; intros; destruct H1 as [? [s [? ?]]]; simpl in H2; destruct H2; try tauto; subst.
      - hnf. simpl. unfold change_valid. split; auto. exists s. split.
        * apply in_eq.
        * destruct H3 as [p ?]. exists p.
          rewrite update_reachable_by_path_not_in. auto.
          intro. apply H. apply (reachable_path_in _ p _ v); auto.
      - hnf in H1. destruct H1.
        * hnf. split; auto. exists s. split. apply in_eq.
          unfold reachable in H3. generalize H3; intro Hv.
          rewrite reachable_acyclic in H3.
          destruct H3 as [p [? ?]]. destruct p.
          Focus 1. { destruct H3 as [[? ?] _]. inversion H3. } Unfocus.
          Focus 1. {
            generalize H3; intro Hr. destruct Hr as [[? _] _].

            simpl in H4. inversion H4. subst. clear H4.
            apply (@update_reachable_tail_reachable _ x _ p d l r _).
            constructor; auto. intro. simpl in H4. destruct H4. auto.
            apply H. apply (@update_reachable_path_in pg bi ma x d l r (s :: p) s v); auto.
            apply in_cons; auto.
            assert (x :: s :: p = path_glue _ (x :: s :: nil) (s :: p)) by (unfold path_glue; simpl; auto).
            rewrite H4. apply reachable_by_path_merge with s; auto. split.
            + split; simpl; auto.
            + split. 2: hnf; intros; hnf; auto.
              simpl. split. hnf. split; simpl. unfold change_valid. right; auto.
              split. apply reachable_head_valid in Hv. simpl in Hv. auto.
              unfold change_edge_func. destruct (t_eq_dec x x). auto. tauto.
              apply reachable_head_valid in Hv. simpl in Hv. auto.
          } Unfocus.
        * subst. exfalso. apply H.
          destruct H3 as [p ?].
          apply (@update_reachable_path_in pg bi ma x d l r p s x); auto.
          destruct H1 as [[? ?] _]. apply foot_in; auto.
    } assert (~ valid (reachable_subgraph pg (y :: nil)) x). {
      intro. rewrite H1 in H2. clear H1. simpl in H2. unfold reachable_valid in H2. simpl in H2.
      destruct H2 as [_ ?]. destruct H1 as [? [? ?]]. simpl in H1. destruct H1. 2: tauto.
      apply eq_sym in H1. subst. apply H. destruct H2 as [p ?].
      apply (@update_reachable_path_in pg bi ma x d l r p y x); auto.
      destruct H1 as [[? ?] _]. apply foot_in; auto.
    } split; [|split]; intros.
    + apply H1.
    + simpl. unfold change_node_label. destruct (t_eq_dec v x). 2: auto. subst. tauto. 
    + simpl. unfold change_edge_func. destruct (t_eq_dec v x). 2: auto. subst. tauto.
    Implicit Arguments valid [[Vertex] [Data] [EV] [PreGraph]].
    Implicit Arguments node_label [[Vertex] [Data] [EV] [PreGraph]].
    Implicit Arguments edge_func [[Vertex] [Data] [EV] [PreGraph]].
  Qed.

  Lemma reachable_list_update_graph_right:
    forall pg {bi : BiGraph pg} {ma : MathGraph pg null} x d r (Hn: x <> null) (Hi: in_math ma x x r) li,
      ~ In x li -> reachable_list pg r li ->
      reachable_list (update_PreGraph pg x d x r) x (x :: li).
  Proof.
    intros. unfold reachable_list in *.
    intros. split; intros.
    + simpl in H1. destruct H1.
      - subst. apply reachable_by_reflexive. split.
        * simpl. unfold change_valid. right; auto.
        * hnf; auto.
      - rewrite H0 in H1. simpl. apply reachable_by_cons with r.
        * hnf. simpl. unfold change_valid.
          split. right; auto.
          split. left. apply reachable_head_valid in H1. auto.
          unfold change_edge_func. destruct (t_eq_dec x x). apply in_cons, in_eq. tauto.
        * hnf. auto.
        * destruct H1 as [p ?]. exists p.
          rewrite update_reachable_by_path_not_in. auto.
          intro. apply H. rewrite H0.
          destruct (reachable_by_path_split_in _ _ _ _ _ _ _ _ _ H1 H2) as [p1 [p2 [? [? ?]]]].
          exists p1; auto.
    + intros. destruct (t_eq_dec y x). subst. apply in_eq. simpl. right. rewrite H0. simpl in H1.
      unfold reachable in H1. rewrite reachable_acyclic in H1. destruct H1 as [p [? ?]].
      generalize H2; intro Hr. destruct H2 as [[? ?] ?].
      destruct p. inversion H2. simpl in H2. inversion H2. subst.
      destruct p. simpl in H3. inversion H3. subst. tauto.
      destruct H4. simpl in H4. destruct H4 as [? _]. destruct H4 as [? [? ?]]. simpl in H7.
      unfold change_edge_func in H7. destruct (t_eq_dec). 2: tauto. simpl in H7. destruct H7 as [? | [? | ?]].
      - subst. apply NoDup_cons_2 in H1. exfalso; apply H1, in_eq.
      - subst. apply (update_reachable_tail_reachable H1 Hr).
      - tauto.
  Qed.

  Lemma reachable_list_update_graph_left:
    forall pg {bi : BiGraph pg} {ma : MathGraph pg null} x d l (Hn: x <> null) (Hi: in_math ma x l x) li,
      ~ In x li -> reachable_list pg l li ->
      reachable_list (update_PreGraph pg x d l x) x (x :: li).
  Proof.
    intros. unfold reachable_list in *.
    intros. split; intros.
    + simpl in H1. destruct H1.
      - subst. apply reachable_by_reflexive. split.
        * simpl. unfold change_valid. right; auto.
        * hnf; auto.
      - rewrite H0 in H1. simpl. apply reachable_by_cons with l.
        * hnf. simpl. unfold change_valid.
          split. right; auto.
          split. left. apply reachable_head_valid in H1. auto.
          unfold change_edge_func. destruct (t_eq_dec x x). apply in_eq. tauto.
        * hnf. auto.
        * destruct H1 as [p ?]. exists p.
          rewrite update_reachable_by_path_not_in. auto.
          intro. apply H. rewrite H0.
          destruct (reachable_by_path_split_in _ _ _ _ _ _ _ _ _ H1 H2) as [p1 [p2 [? [? ?]]]].
          exists p1; auto.
    + intros. destruct (t_eq_dec y x). subst. apply in_eq. simpl. right. rewrite H0. simpl in H1.
      unfold reachable in H1. rewrite reachable_acyclic in H1. destruct H1 as [p [? ?]].
      generalize H2; intro Hr. destruct H2 as [[? ?] ?].
      destruct p. inversion H2. simpl in H2. inversion H2. subst.
      destruct p. simpl in H3. inversion H3. subst. tauto.
      destruct H4. simpl in H4. destruct H4 as [? _]. destruct H4 as [? [? ?]]. simpl in H7.
      unfold change_edge_func in H7. destruct (t_eq_dec). 2: tauto. simpl in H7. destruct H7 as [? | [? | ?]].
      - subst. apply (update_reachable_tail_reachable H1 Hr).
      - subst. apply NoDup_cons_2 in H1. exfalso; apply H1, in_eq.
      - tauto.
  Qed.
  
End GraphReachable.

Arguments reachable_set_list {V} {D} {EDV} pg S l.

Definition subgraph {N} {D} {DEC} (g: @PreGraph N D DEC) (x: N) (g': @PreGraph N D DEC) : Prop :=
  reachable_subgraph g (x :: nil) = g'.

Arguments mark {N} {D} {EDN} _ _ _ _.
Arguments mark1 {N} {D} {EDN} _ _ _ _.

Lemma mark_null:
  forall {N} {D} {DEC} marked (g g': @PreGraph N D DEC) x, ~ @valid N D DEC g x -> mark marked g x g' -> g -=- g'.
Proof.
  intros. destruct H0 as [? [? ?]]. split; [|split]; intros.
  + destruct (H0 v); auto.
  + apply H2. intro. destruct H4 as [l [[? ?] [? ?]]].
    apply valid_path_valid in H6. rewrite Forall_forall in H6.
    apply H. apply H6. destruct l.
    - inversion H4.
    - simpl in H4. inversion H4. apply in_eq.
  + destruct (H0 v); auto.
Qed.

Lemma mark_marked_eq: forall {N} {D} {DEC} (marked: Ensemble D) (g g': @PreGraph N D DEC) x,
  marked (@node_label N D DEC g x) ->
  mark marked g x g' -> g -=- g'.
Proof.
  intros. destruct H0 as [? [? ?]]. split; [|split]; intros.
  + destruct (H0 v); auto.
  + apply H2. intro. apply reachable_by_head_prop in H4.
    hnf in H4. tauto.
  + destruct (H0 v); auto.
Qed.

*)
End REACHABLE_COMPUTABLE.
