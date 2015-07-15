Require Import graph.
Require Import Arith.
Require Import List.
Require Import utilities.
Require Import FunctionalExtensionality.
Require Import Permutation.

Section GraphReachable.

  Context {V : Type} {D : Type} {EDV : EqDec V} {null : V}.

  Definition reachable_list (pg : PreGraph V D) (x : V) (L : list V) : Prop :=
    valid x /\ forall y, In y L <-> reachable pg x y.

  Definition reach_input := (nat * list V * list V)%type.

  Definition lengthInput (i : reach_input) :=
    match i with | (len, _, re) => len - length re end.

  Definition inputOrder (i1 i2 : reach_input) := lengthInput i1 < lengthInput i2.

  Lemma inputOrder_wf': forall len i, lengthInput i <= len -> Acc inputOrder i.
  Proof.
    induction len; intros; constructor; intros; unfold inputOrder in * |-; [exfalso | apply IHlen]; intuition.
  Qed.

  Lemma inputOrder_wf : well_founded inputOrder.
  Proof. red; intro; eapply inputOrder_wf'; eauto. Defined.

  Fixpoint remove_list (l1 l2 l3 : list V) : list V :=
    match l3 with
      | nil => remove_dup t_eq_dec (remove t_eq_dec null (l1 ++ l2))
      | x :: l => remove_list l1 (remove t_eq_dec x l2) l
    end.

  Lemma remove_list_sublist: forall l1 l2 l3, Sublist (remove_list l1 l2 l3) (l1 ++ l2).
  Proof.
    intros. revert l1 l2. induction l3; intros; intro; intros; simpl in *; auto. rewrite <- remove_dup_in_inv in H.
    generalize (remove_sublist V t_eq_dec (l1 ++ l2) null a H); intro; auto. specialize (IHl3 l1 (remove t_eq_dec a l2) a0 H).
    destruct (in_app_or _ _ _ IHl3); apply in_or_app; [left | right]. auto. generalize (remove_sublist V t_eq_dec l2 a a0 H0).
    intros; auto.
  Qed.

  Lemma remove_list_null_not_in: forall l1 l2 l3, ~ In null (remove_list l1 l2 l3).
  Proof.
    intros. revert l1 l2. induction l3; intros; simpl. intro. rewrite <- remove_dup_in_inv in H. revert H. apply remove_In.
    apply IHl3.
  Qed.

  Lemma remove_list_no_dup: forall l1 l2 l3, NoDup (remove_list l1 l2 l3).
  Proof. intros; revert l1 l2; induction l3; intros; simpl. apply remove_dup_nodup. apply IHl3. Qed.

  Lemma remove_list_not_in:
    forall l1 l2 l3, exists l4, remove_list l1 l2 l3 = remove_dup t_eq_dec (remove t_eq_dec null (l1 ++ l4)) /\
                                Sublist l4 l2 /\ forall x, In x l3 -> ~ In x l4.
  Proof.
    intros. revert l1 l2; induction l3; intros; simpl. exists l2. repeat split. apply Sublist_refl. intros; auto.
    specialize (IHl3 l1 (remove t_eq_dec a l2)). destruct IHl3 as [l4 [? [? ?]]]. exists l4. repeat split; auto.
    apply Sublist_trans with (remove t_eq_dec a l2); auto. apply remove_sublist. intros. destruct H2; auto. subst. intro.
    specialize (H0 x H2). revert H0; apply remove_In.
  Qed.

  Lemma remove_list_in: forall l1 l2 l3 x, x <> null -> (~ In x l3) -> In x l2 -> In x (remove_list l1 l2 l3).
  Proof.
    intros. revert l1 l2 x H H0 H1. induction l3; intros; simpl. rewrite <- remove_dup_in_inv. assert (In x (l1 ++ l2)).
    apply in_or_app; right; auto. apply (remove_in_2 _ t_eq_dec (l1 ++ l2) x null) in H2. destruct H2; intuition.
    apply (not_in_app t_eq_dec) in H0; destruct H0. apply IHl3; auto. apply (remove_in_2 _ t_eq_dec l2 x a) in H1.
    destruct H1; intuition.
  Qed.

  Lemma remove_list_in_2: forall l1 l2 l3 x, x <> null -> In x l1 -> In x (remove_list l1 l2 l3).
  Proof.
    intros. revert l1 l2 x H H0. induction l3; intros; simpl. rewrite <- remove_dup_in_inv. assert (In x (l1 ++ l2)).
    apply in_or_app; left; auto. apply (remove_in_2 _ t_eq_dec _ _ null) in H1. destruct H1; intuition. apply IHl3; auto.
  Qed.

  Lemma construct_omega: forall len (r : list V),  (~ len <= length r) -> len - S (length r) < len - length r.
  Proof. intros; omega. Qed.

  Definition construct_reachable (pg : PreGraph V D) : reach_input -> list V.
    refine (
        Fix inputOrder_wf (fun _ => list V)
            (fun (inp : reach_input) =>
               match inp return ((forall inp2, inputOrder inp2 inp -> list V) -> list V) with
                 | (_, nil, r) => fun _ => r
                 | (len, g :: l, r) => fun f =>
                                         if le_dec len (length r)
                                         then r
                                         else let newL := remove_list l (edge_func g) (g :: r) in f (len, newL, g :: r) _
               end)).
    unfold inputOrder, lengthInput. simpl. apply construct_omega; auto.
  Defined.

  Lemma construct_reachable_unfold:
    forall pg i,
      construct_reachable pg i = match i with
                                   | (_, nil, r) => r
                                   | (len, g :: l, r) =>
                                     if le_dec len (length r)
                                     then r
                                     else let newL := remove_list l (edge_func g) (g :: r) in
                                          construct_reachable pg (len, newL, g :: r)
                                 end.
  Proof.
    intros. destruct i as [[n pr] rslt]. unfold construct_reachable at 1; rewrite Fix_eq.
    destruct pr; simpl. auto. destruct (le_dec n (length rslt)). auto. unfold construct_reachable; auto.
    intros; assert (f = g) by (extensionality y; extensionality p; auto); subst; auto.
  Qed.

  Definition rch1 (i : reach_input) := match i with (n, _, _) => n end.

  Definition rch2 (i : reach_input) := match i with (_, l, _) => l end.

  Definition rch3 (i: reach_input) := match i with (_, _, result) => result end.

  Lemma construct_reachable_reachable:
    forall (mg : MathGraph V D null) (i : reach_input) x, Forall (reachable m_pg x) (rch3 i) ->
                                                          Forall (reachable m_pg x) (rch2 i) ->
                                                          Forall (reachable m_pg x) (construct_reachable m_pg i).
  Proof.
    intros mg i. remember (lengthInput i). assert (lengthInput i <= n) by omega. clear Heqn. revert i H.
    induction n; intros; remember (construct_reachable m_pg i) as r; destruct i as [[len pr] rslt]; simpl in *;
    rewrite construct_reachable_unfold in Heqr; destruct pr; simpl in Heqr. subst; auto. destruct (le_dec len (length rslt)).
    subst; auto. exfalso; omega. subst; auto. destruct (le_dec len (length rslt)). subst; auto. rewrite Heqr. apply IHn; simpl.
    omega. apply Forall_cons. apply Forall_inv in H1. auto. auto. rewrite Forall_forall in *. intro y; intros.
    generalize (remove_list_sublist pr (remove t_eq_dec v (edge_func v)) rslt y H2); intros. apply in_app_or in H3. destruct H3.
    apply H1. apply in_cons. auto. assert (In v (v :: pr)) as S by apply in_eq. specialize (H1 v S); clear S.
    apply reachable_by_merge with v. apply H1. exists (v :: y :: nil). split. split; simpl; auto. split. simpl.
    generalize (remove_sublist V t_eq_dec (edge_func v) v y H3). intro.
    generalize (remove_list_null_not_in pr (remove t_eq_dec v (edge_func v)) rslt); intro. destruct (t_eq_dec y null). subst.
    intuition. apply reachable_foot_valid in H1. destruct (valid_graph v H1 y H4). intuition. split; auto. split; auto.
    intro; intros. hnf; auto.
  Qed.

  Lemma construct_reachable_nodup:
    forall (pg : PreGraph V D) (i : reach_input), NoDup (rch2 i ++ rch3 i) -> NoDup (construct_reachable pg i).
  Proof.
    intros pg i. remember (lengthInput i). assert (lengthInput i <= n) by omega. clear Heqn. revert i H.
    induction n; intros; remember (construct_reachable pg i) as r; destruct i as [[len pr] rslt]; simpl in *;
    rewrite construct_reachable_unfold in Heqr; destruct pr. subst. rewrite app_nil_l in H0. auto.
    destruct (le_dec len (length rslt)). subst; apply NoDup_app_r in H0; auto. exfalso; intuition. subst.
    rewrite app_nil_l in H0. auto. destruct (le_dec len (length rslt)). subst; apply NoDup_app_r in H0; auto. simpl in Heqr.
    rewrite Heqr; apply IHn; simpl. omega. clear IHn H n0 r Heqr. rewrite NoDup_app_eq in H0. destruct H0 as [? [? ?]].
    apply NoDup_app_inv. apply remove_list_no_dup. apply NoDup_cons. apply H1. apply in_eq. auto. intros.
    destruct (remove_list_not_in pr (remove t_eq_dec v (edge_func v)) rslt) as [l4 [? [? ?]]]. rewrite H3 in *; clear H3.
    rewrite <- remove_dup_in_inv in H2. generalize (remove_sublist V t_eq_dec (pr ++ l4) null x H2); intro.
    apply in_app_or in H3. destruct H3. intro. apply in_inv in H6. destruct H6. apply NoDup_cons_2 in H. subst. auto.
    revert H6; apply H1. apply in_cons. auto. intro. apply in_inv in H6. destruct H6. subst. specialize (H4 x H3).
    revert H4; apply remove_In. revert H3; apply H5. auto.
  Qed.

  Lemma construct_reachable_length_bound:
    forall (pg : PreGraph V D) (i : reach_input), length (rch3 i) <= rch1 i -> length (construct_reachable pg i) <= rch1 i.
  Proof.
    intros pg i. remember (lengthInput i). assert (lengthInput i <= n) by omega. clear Heqn. revert i H.
    induction n; intros; remember (construct_reachable pg i) as r; destruct i as [[len pr] rslt]; simpl in *;
    rewrite construct_reachable_unfold in Heqr; destruct pr. subst; auto. destruct (le_dec len (length rslt)). subst; auto.
    exfalso; intuition. subst; auto. destruct (le_dec len (length rslt)). subst; auto. simpl in Heqr.
    specialize (IHn (len, remove_list pr (remove t_eq_dec v (edge_func v)) rslt, v :: rslt)); simpl in IHn. rewrite Heqr.
    apply IHn; omega.
  Qed.

  Lemma construct_reachable_sublist:
    forall (pg : PreGraph V D) (i : reach_input), Sublist (rch3 i) (construct_reachable pg i).
  Proof.
    intros pg i. remember (lengthInput i). assert (lengthInput i <= n) by omega. clear Heqn. revert i H.
    induction n; intros; remember (construct_reachable pg i) as r; destruct i as [[len pr] rslt]; simpl in *;
    rewrite construct_reachable_unfold in Heqr; destruct pr. subst; apply Sublist_refl. destruct (le_dec len (length rslt)).
    subst; apply Sublist_refl. exfalso; intuition. subst; apply Sublist_refl. destruct (le_dec len (length rslt)).
    subst; apply Sublist_refl. specialize (IHn (len, remove_list pr (remove t_eq_dec v (edge_func v)) rslt, v :: rslt)).
    simpl in *. assert (len -S (length rslt) <= n) as S by omega. specialize (IHn S); clear S. repeat intro. rewrite Heqr.
    apply (IHn a). apply in_cons. auto.
  Qed.

  Definition ProcessingInResult (pg : PreGraph V D) (l1 l2 : list V) : Prop :=
    forall x y, In x l1 -> reachable pg x y -> In y l2.

  Lemma PIR_cons: forall (pg : PreGraph V D) x l1 l2,
                    (forall y, reachable pg x y -> In y l2) ->
                    ProcessingInResult pg l1 l2 -> ProcessingInResult pg (x :: l1) l2.
  Proof. repeat intro; apply in_inv in H1; destruct H1. subst. apply H; auto. apply (H0 x0); auto. Qed.

  Lemma PIR_sublist: forall (pg : PreGraph V D) l1 l2 l3,
                       Sublist l1 l2 -> ProcessingInResult pg l2 l3 -> ProcessingInResult pg l1 l3.
  Proof. repeat intro. specialize (H x H1). apply (H0 x y); auto. Qed.

  Definition ResultInProcessing (pg : PreGraph V D) (l1 l2 : list V) : Prop :=
    forall x y, In x l1 -> edge pg x y -> In y l1 \/ In y l2.

  Fixpoint findNotIn (l1 l2 l3: list V) : (option V * (list V * list V)) :=
    match l1 with
      | nil => (None, (nil, nil))
      | x :: l => if (in_dec t_eq_dec x l2) then findNotIn l l2 (x :: l3) else (Some x, (rev l3, l))
    end.

  Lemma find_not_in_none: forall l1 l2 l3, fst (findNotIn l1 l2 l3) = None -> Forall (fun m => In m l2) l1.
  Proof.
    induction l1; intros. apply Forall_nil. simpl in H. destruct (in_dec t_eq_dec a l2).
    apply Forall_cons. auto. apply IHl1 with (a :: l3); auto. inversion H.
  Qed.

  Lemma find_not_in_some_explicit:
    forall l1 l2 l3 x li1 li2,
      findNotIn l1 l2 l3 = (Some x, (li1, li2)) -> (Forall (fun m => In m l2) l3) ->
      (~ In x li1) /\ (~ In x l2) /\ exists l4, li1 = rev l3 ++ l4 /\ Forall (fun m => In m l2) l4 /\ l1 = l4 ++ x :: li2.
  Proof.
    induction l1; intros; simpl in H. inversion H. destruct (in_dec t_eq_dec a l2).
    assert (Forall (fun m : V => In m l2) (a :: l3)) by (apply Forall_cons; auto).
    specialize (IHl1 l2 (a :: l3) x li1 li2 H H1). destruct IHl1 as [? [? [l4 [? [? ?]]]]]. split; auto. split; auto.
    exists (a :: l4). repeat split; auto. simpl in H4. rewrite <- app_assoc in H4. rewrite <- app_comm_cons in H4.
    rewrite app_nil_l in H4. auto. rewrite H6; apply app_comm_cons. inversion H. split. intro; apply n.
    rewrite Forall_forall in H0. apply (H0 a). rewrite H2. rewrite in_rev. auto. split. rewrite <- H2. auto.
    exists nil. repeat split; auto. rewrite app_nil_r. auto.
  Qed.

  Lemma find_not_in_some:
    forall l1 l2 x li1 li2,
      findNotIn l1 l2 nil = (Some x, (li1, li2)) ->
      Forall (fun m => In m l2) li1 /\ l1 = li1 ++ x :: li2 /\ ~ In x li1 /\ ~ In x l2.
  Proof.
    intros. assert (Forall (fun m : V => In m l2) nil) by apply Forall_nil.
    destruct (find_not_in_some_explicit l1 l2 nil x li1 li2 H H0). destruct H2 as [? [l4 [? [? ?]]]].
    simpl in H3. rewrite H3 in *. repeat split; auto.
  Qed.

  Lemma foot_none_nil: forall (l : list V), foot l = None -> l = nil.
  Proof. induction l; intros; auto. simpl in H. destruct l. inversion H. specialize (IHl H). inversion IHl. Qed.

  Lemma reachable_by_path_split_dec:
    forall (pg : PreGraph V D) p a b P rslt,
      pg |= p is a ~o~> b satisfying P -> {Forall (fun m => In m (a :: rslt)) p} +
                                          {exists l1 l2 e1 s2, Forall (fun m => In m (a :: rslt)) l1 /\
                                                               pg |= l1 is a ~o~> e1 satisfying P /\
                                                               pg |= l2 is s2 ~o~> b satisfying P /\
                                                               edge pg e1 s2 /\ ~ In s2 (a::rslt) /\ p = l1 ++ l2 /\
                                                               ~ In s2 l1}.
  Proof.
    intros. remember (findNotIn p (a :: rslt) nil) as f. destruct f as [n [l1 l2]]. destruct n. right.
    apply eq_sym in Heqf. destruct (find_not_in_some _ _ _ _ _ Heqf) as [? [? [? ?]]]. exists l1, (v :: l2).
    rewrite Forall_forall in H0. destruct l1. rewrite app_nil_l in H1.
    generalize (reachable_by_path_head _ _ _ _ _ _ _ _ H); intro. rewrite H1 in *. simpl in H4. inversion H4.
    rewrite H6 in *. exfalso; apply H3; apply in_eq.
    generalize (reachable_by_path_head _ _ _ _ _ _ _ _ H); intro.
    rewrite <- app_comm_cons in H1. rewrite H1 in H4. simpl in H4. inversion H4. rewrite H6 in *. clear H4 H6 v0.
    remember (foot (a :: l1)). destruct o. exists v0, v. split. rewrite Forall_forall; auto.
    assert (paths_meet_at V (a :: l1) (v0 :: v :: l2) v0) by (repeat split; auto).
    assert (pg |= path_glue V (a :: l1) (v0 :: v :: l2) is a ~o~> b satisfying P). unfold path_glue. simpl.
    rewrite <- H1. auto. destruct (reachable_by_path_split_glue _ _ _ _ _ _ _ _ _ _ H4 H5). clear H4 H5. split; auto.
    assert (paths_meet_at V (v0 :: v :: nil) (v :: l2) v) by repeat split.
    assert (pg |= path_glue V (v0 :: v :: nil) (v :: l2) is v0 ~o~> b satisfying P). unfold path_glue. simpl. auto.
    destruct (reachable_by_path_split_glue _ _ _ _ _ _ _ _ _ _ H4 H5). clear H4 H5 H6 H7. split; auto.
    split. destruct H8. destruct H5. destruct H5. auto. split. auto. split; simpl; auto.
    apply eq_sym in Heqo. generalize (foot_none_nil (a :: l1) Heqo); intros. inversion H4.
    assert (fst (findNotIn p (a :: rslt) nil) = None) by (rewrite <- Heqf; simpl; auto). left.
    apply find_not_in_none with nil. auto.
  Qed.

  Lemma construct_reachable_contains_all_reachable:
    forall (mg : MathGraph V D null) i,
      (Forall (fun m => m <> null) (rch2 i)) ->
      ResultInProcessing m_pg (rch3 i) (rch2 i) -> length (construct_reachable m_pg i) < rch1 i ->
      ProcessingInResult m_pg (rch2 i) (construct_reachable m_pg i).
  Proof.
    intros mg i. remember (lengthInput i). assert (lengthInput i <= n) by omega. clear Heqn. revert i H.
    induction n; intros; remember (construct_reachable m_pg i) as r; destruct i as [[len pr] rslt]; simpl in *;
    rewrite construct_reachable_unfold in Heqr; destruct pr. subst; omega. destruct (le_dec len (length rslt)). subst; omega.
    exfalso; intuition. subst. repeat intro. inversion H3. destruct (le_dec len (length rslt)). subst; omega. simpl in Heqr.
    assert (ProcessingInResult m_pg (remove_list pr (remove t_eq_dec v (edge_func v)) rslt) r).
    specialize (IHn (len, remove_list pr (remove t_eq_dec v (edge_func v)) rslt, v :: rslt)); simpl in IHn.
    rewrite <- Heqr in IHn. apply IHn; auto. omega. apply Forall_forall. intros.
    generalize (remove_list_null_not_in pr (remove t_eq_dec v (edge_func v)) rslt); intro. intro. rewrite H5 in H3. intuition.
    clear IHn. repeat intro. destruct (in_dec t_eq_dec y (v :: rslt)). left; auto. right. apply (not_in_app t_eq_dec) in n1.
    destruct n1. generalize H4; intro. destruct H4 as [? [? ?]].
    apply valid_not_null in H8. apply in_inv in H3. destruct H3. rewrite <- H3 in *; clear H3. apply remove_list_in; auto.
    apply (remove_in_2 _ t_eq_dec _ _ v) in H9. destruct H9; intuition. apply remove_list_in_2; auto. specialize (H1 x y H3 H7).
    destruct H1. intuition. apply in_inv in H1. destruct H1. exfalso; intuition. auto. apply PIR_cons. intros.
    unfold reachable in H4. destruct H4 as [p ?]. destruct (reachable_by_path_split_dec _ _ _ _ _ rslt H4).
    rewrite Forall_forall in f. apply reachable_by_path_foot in H4. apply foot_in in H4. specialize (f _ H4). rewrite Heqr.
    apply (construct_reachable_sublist _ _ y). simpl. apply in_inv in f. auto.
    destruct e as [l1 [l2 [e1 [s1 [? [? [? [? [? [? ?]]]]]]]]]]. rewrite Forall_forall in H5. destruct (t_eq_dec e1 v).
    rewrite e in *; clear e e1. destruct H8 as [? [? ?]]. apply not_in_app in H9. destruct H9.
    assert (In s1 (remove t_eq_dec v (edge_func v))). destruct (remove_in_2 _ t_eq_dec _ _ v H13); intuition.
    apply (H3 s1). apply valid_not_null in H12. apply remove_list_in; auto. exists l2. apply H7. apply t_eq_dec.
    apply reachable_by_path_foot in H6. apply foot_in in H6. specialize (H5 e1 H6). apply in_inv in H5. destruct H5. exfalso.
    auto. specialize (H1 e1 s1 H5 H8). apply (not_in_app t_eq_dec) in H9. destruct H9. destruct H1. exfalso; auto.
    apply in_inv in H1. destruct H1. exfalso; auto. apply (H3 s1 y). apply remove_list_in_2. destruct H8 as [? [? ?]].
    apply valid_not_null in H13. auto. auto. exists l2. auto.
    apply PIR_sublist with (remove_list pr (remove t_eq_dec v (edge_func v)) rslt); auto. intro y; intros.
    apply remove_list_in_2; auto. rewrite Forall_forall in H0. apply H0. apply in_cons. auto.
  Qed.

  Lemma finite_reachable_computable:
    forall (mg : MathGraph V D null) x l, valid x -> (forall y, reachable m_pg x y -> In y l) ->
                                          exists l', reachable_list m_pg x l' /\ NoDup l'.
  Proof.
    intros. remember (length l, x :: nil, @nil V) as i. remember (construct_reachable m_pg i) as l'. exists l'.
    assert (Forall (reachable m_pg x) l'). rewrite Forall_forall. intro z. intros. assert (Forall (reachable m_pg x) (rch3 i)).
    rewrite Heqi. simpl. apply Forall_nil. assert (Forall (reachable m_pg x) (rch2 i)). rewrite Heqi. simpl. apply Forall_cons.
    apply reachable_by_reflexive. split; auto. hnf; auto. apply Forall_nil.
    generalize (construct_reachable_reachable mg i x H2 H3); intro. rewrite Forall_forall in H4. rewrite <- Heql' in H4.
    specialize (H4 z H1). auto. assert (NoDup l') as HS. specialize (construct_reachable_nodup m_pg i); intros. rewrite Heql'.
    apply H2. rewrite Heqi. simpl. apply NoDup_cons. apply in_nil. apply NoDup_nil. split. split. auto. intro z. split; intros.
    rewrite Forall_forall in H1. apply H1. auto. assert (Sublist l' l). intro w. intros. apply H0. rewrite Forall_forall in H1.
    apply H1. auto. assert (length l'<=length l). specialize (construct_reachable_length_bound m_pg i); rewrite Heqi; simpl.
    intros. rewrite Heql', Heqi. apply H4. omega. apply le_lt_or_eq in H4. destruct H4.
    assert (ProcessingInResult m_pg (rch2 i) (construct_reachable m_pg i)). apply construct_reachable_contains_all_reachable.
    rewrite Forall_forall. rewrite Heqi. simpl. intros. destruct H5; auto. rewrite <- H5 in *. rewrite H5 in *.
    apply reachable_head_valid in H2. apply valid_not_null in H2. auto. rewrite Heqi; hnf; simpl. intros. auto.
    rewrite Heql' in H4. rewrite Heqi at 2. simpl. auto. specialize (H5 x z). rewrite Heql'; apply H5; auto. rewrite Heqi.
    simpl. left; auto. generalize (sublist_reverse t_eq_dec l' l HS H4 H3 z); intros; apply H5. apply H0. auto. auto.
  Qed.

  Lemma compute_reachable: forall (mg : MathGraph V D null) x L,
                             reachable_list m_pg x L -> forall y, reachable m_pg x y ->
                                                                  exists L', reachable_list m_pg y L' /\ NoDup L'.
  Proof.
    intros. assert (valid y). apply reachable_foot_valid in H0; auto. assert (forall z, reachable m_pg y z -> In z L). intros.
    assert (reachable m_pg x z). apply reachable_by_merge with y; auto. destruct H. rewrite (H4 z). auto.
    destruct (finite_reachable_computable mg y L H1 H2) as [l' [? ?]]. exists l'; split; auto.
  Qed.

  Lemma reachable_from_children:
    forall (pg : PreGraph V D) x y, reachable pg x y -> y = x \/ exists z, pg |= x ~> z /\ reachable pg z y.
  Proof.
    intros. destruct H as [p ?]. destruct p. destruct H. destruct H. inversion H. destruct H as [[? ?] [? ?]].
    simpl in H. inversion H. subst. destruct p. simpl in H0. inversion H0. left; auto. right. hnf in H1. destruct H1.
    exists v. split; auto. destruct H1 as [? [? ?]]. exists (v :: p). split; split. simpl. auto. simpl in H0. simpl. apply H0.
    auto. hnf. intros. hnf. auto.
  Qed.

  Lemma reachable_all_zero:
    forall (mg: MathGraph V D null) x l, reachable_list m_pg x l -> NoDup l ->
                                         Forall (fun m => m = null) (edge_func x) -> l = x :: nil.
  Proof.
    intros. destruct H. rewrite Forall_forall in H1. assert (reachable m_pg x x). apply reachable_by_reflexive. split; auto.
    hnf; auto. rewrite <- H2 in H3. apply in_split in H3. destruct H3 as [l1 [l2 ?]]. destruct l1, l2. simpl in H3; auto.
    simpl in H3. assert (In v l). rewrite H3. apply in_cons. apply in_eq. rewrite (H2 v) in H4.
    apply reachable_from_children in H4. destruct H4. subst. apply NoDup_cons_2 in H0. exfalso; apply H0. apply in_eq.
    destruct H4 as [z [[? [? ?]] ?]]. specialize (H1 _ H6). apply valid_not_null in H5. exfalso; intuition.
    simpl in H3. assert (In v l). rewrite H3. apply in_eq. rewrite (H2 v) in H4. apply reachable_from_children in H4.
    destruct H4. subst. apply NoDup_cons_2 in H0. exfalso; apply H0. apply in_or_app. right; apply in_eq.
    destruct H4 as [z [[? [? ?]] ?]]. specialize (H1 _ H6). apply valid_not_null in H5. exfalso; intuition.
    simpl in H3. assert (In v l). rewrite H3. apply in_eq. rewrite (H2 v) in H4. apply reachable_from_children in H4.
    destruct H4. subst. apply NoDup_cons_2 in H0. exfalso; apply H0. apply in_or_app. right; apply in_eq.
    destruct H4 as [z [[? [? ?]] ?]]. specialize (H1 _ H6). apply valid_not_null in H5. exfalso; intuition.
  Qed.

  Lemma reachable_through_set_eq:
    forall (pg : PreGraph V D) a S x, reachable_through_set pg (a :: S) x <-> reachable pg a x \/ reachable_through_set pg S x.
  Proof.
    intros; split; intros. destruct H as [s [? ?]]. apply in_inv in H. destruct H. subst. left; auto. right. exists s.
    split; auto. destruct H. exists a. split. apply in_eq. auto. destruct H as [s [? ?]]. exists s. split. apply in_cons. auto.
    auto.
  Qed.

  Lemma finite_reachable_set_single:
    forall (mg : MathGraph V D null) S l, (forall x, reachable_through_set m_pg S x -> In x l) ->
                                          forall s, In s S -> valid s ->
                                                    exists l' : list V, reachable_list m_pg s l' /\ NoDup l'.
  Proof.
    intros. assert (forall y, reachable m_pg s y -> In y l). intros. apply H. exists s; split; auto.
    destruct (finite_reachable_computable mg s l H1 H2) as [l' [? ?]]. exists l'; split; auto.
  Qed.

  Definition reachable_set_list (pg : PreGraph V D) (S : list V) (l : list V) : Prop :=
    forall x : V, reachable_through_set pg S x <-> In x l.

  Lemma reachable_through_single_reachable:
    forall (mg : MathGraph V D null) S l, reachable_set_list m_pg S l ->
      forall s, In s S -> valid s -> exists l' : list V, reachable_list m_pg s l' /\ NoDup l'.
  Proof.
    intros. assert (forall x, reachable_through_set m_pg S x -> In x l). intros. rewrite <- (H x). auto.
    destruct (finite_reachable_set_single mg S l H2 s H0 H1) as [l' [? ?]]. exists l'; split; auto.
  Qed.

  Lemma finite_reachable_set_sublist:
    forall (mg : MathGraph V D null) S l,
      (forall x, reachable_through_set m_pg S x -> In x l) ->
      forall s, Sublist s S -> well_defined_list mg s -> exists l' : list V, reachable_set_list m_pg s l' /\ NoDup l'.
  Proof.
    do 5 intro; induction s; intros. exists nil. split. intro. split; intros. destruct H2 as [ll [? ?]]. inversion H2.
    inversion H2. apply NoDup_nil. assert (Sublist s S). repeat intro. apply (H0 a0). apply in_cons; auto.
    assert (well_defined_list mg s). repeat intro. apply (H1 x). apply in_cons; auto. specialize (IHs H2 H3). clear H2 H3.
    destruct IHs as [l2 [? ?]]. assert (In a (a :: s)). apply in_eq. specialize (H1 a H4). destruct H1. subst. exists l2.
    split; auto. intro. split; intro. apply (H2 x). destruct H1 as [m [? ?]]. exists m. split; auto. apply in_inv in H1.
    destruct H1. apply eq_sym in H1. subst. destruct H5 as [p [[? ?] [? ?]]]. destruct p; inversion H1. subst. simpl in H6.
    destruct p. apply valid_not_null in H6. exfalso; auto. destruct H6 as [[? [? ?]] ?]. apply valid_not_null in H6. exfalso.
    auto. auto. apply (H2 x) in H1. destruct H1 as [m [? ?]]. exists m. split; auto. apply in_cons; auto. assert (In a S).
    apply H0; auto. destruct (finite_reachable_set_single mg S l H a H5 H1) as [l1 [? ?]].
    destruct (double_list_split t_eq_dec H7 H3) as [i1 [i2 [i3 [? [? ?]]]]]. exists (i1 ++ i2 ++ i3); split; auto. intro.
    split; intro. rewrite reachable_through_set_eq in H11. destruct H11. rewrite app_assoc. apply in_or_app. left.
    apply (Permutation_in x H8). destruct H6. rewrite H12. auto. apply in_or_app. right. apply (Permutation_in x H9).
    apply H2. auto. apply in_app_or in H11. destruct H11. assert (In x (i1 ++ i2)). apply in_or_app. left; auto.
    rewrite reachable_through_set_eq. left. apply Permutation_sym in H8. apply (Permutation_in x H8) in H12. destruct H6.
    apply H13; auto. apply Permutation_sym in H9. apply (Permutation_in x H9) in H11. rewrite reachable_through_set_eq. right.
    rewrite (H2 x). auto.
  Qed.

  Lemma reachable_through_sublist_reachable:
    forall (mg : MathGraph V D null) S l, reachable_set_list m_pg S l ->
      forall s, Sublist s S -> well_defined_list mg s -> exists l' : list V, reachable_set_list m_pg s l' /\ NoDup l'.
  Proof.
    intros. assert (forall x, reachable_through_set m_pg S x -> In x l). intros. rewrite <- (H x). auto.
    destruct (finite_reachable_set_sublist mg S l H2 s H0 H1) as [l' [? ?]]. exists l'; split; auto.
  Qed.

  Lemma reachable_path_in:
    forall (pg: PreGraph V D) (p: list V) (l y : V), pg |= p is l ~o~> y satisfying (fun _ : D => True) ->
                                                     forall z, In z p -> reachable pg l z.
  Proof.
    intros. destruct H as [[? ?] [? ?]]. apply in_split in H0. destruct H0 as [l1 [l2 ?]]. exists (l1 +:: z). subst. split.
    split. destruct l1; simpl; simpl in H; auto. rewrite foot_last. auto. split. rewrite app_cons_assoc in H2.
    apply valid_path_split in H2. destruct H2. auto. repeat intro; hnf; auto.
  Qed.

  Lemma update_reachable_path_in:
    forall {g : BiMathGraph V D null} {x : V} {d : D}  {l r: V} {p: list V} {h y: V},
      x <> null -> h <> x -> (update_PreGraph b_pg x d l r) |= p is h ~o~> y satisfying (fun _: D => True) ->
      In x p -> reachable b_pg h x.
  Proof.
    intros. generalize (reachable_path_in _ p h y H1 x H2). intro. unfold reachable in H3. rewrite reachable_acyclic in H3.
    destruct H3 as [path [? ?]]. destruct H4 as [[? ?] [? ?]]. apply foot_explicit in H5. destruct H5 as [p' ?]. destruct p'.
    subst. simpl in H4. inversion H4. exfalso; auto. subst. simpl in H4. inversion H4. subst. remember (foot (h :: p')).
    destruct o. apply eq_sym in Heqo. apply foot_explicit in Heqo. destruct Heqo as [pt ?]. generalize H6; intro Hv.
    rewrite H5 in *. rewrite <- app_cons_assoc in H3, H6. clear H7. apply valid_path_split in H6. destruct H6. simpl in H7.
    destruct H7. destruct H7 as [? [? ?]]. simpl in H10. unfold change_edge_func in H10. simpl in H10. generalize H3; intro Hnd.
    apply NoDup_app_r in H3. apply NoDup_cons_2 in H3. apply (not_in_app t_eq_dec) in H3. destruct H3. simpl in H7.
    unfold change_valid in H7. destruct H7. destruct (t_eq_dec v x). exfalso; auto. rewrite <- pg_the_same in H7.
    rewrite <- pg_the_same in H10. destruct (valid_graph v H7 x H10). exfalso; auto. rewrite <- H5 in Hv.
    exists ((h :: p') +:: x). split. split. simpl. auto. rewrite foot_last. auto. split. rewrite H5 in *. clear H5 p'.
    rewrite <- app_cons_assoc in Hv. rewrite <- app_cons_assoc. clear H6. induction pt. simpl in Hv. simpl.
    rewrite pg_the_same in H12, H7, H10. split; auto. destruct Hv as [[? [? ?]] ?]. split; auto. rewrite <- app_comm_cons.
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
    forall {pg: PreGraph V D} {x h: V} {p: list V} {d: D} {l r y: V},
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
    forall {pg: PreGraph V D} {x: V} {p: list V} {d: D} {l r h y: V} {P : set D},
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

  Definition b_pg_g (g: BiMathGraph V D null) : PreGraph V D := @b_pg V D EDV (@bm_bi V D null EDV g).

  Definition m_pg_g (g: BiMathGraph V D null) : PreGraph V D := @m_pg V D null EDV (@bm_ma V D null EDV g).

  Definition bm_bi_g (g: BiMathGraph V D null) : BiGraph V D := @bm_bi V D null EDV g.

  Definition bm_ma_g (g: BiMathGraph V D null) : MathGraph V D null := @bm_ma V D null EDV g.

  Definition valid_g (g: BiMathGraph V D null) : V -> Prop := @valid V D EDV (@b_pg V D EDV (@bm_bi V D null EDV g)).

  Lemma unreachable_sub_eq_belong_to:
    forall (g g': BiMathGraph V D null) (S1 S1': list V),
      (unreachable_subgraph (b_pg_g g) S1) -=- (unreachable_subgraph (b_pg_g g') S1') ->
      forall x S2, ~ reachable_through_set (b_pg_g g) S1 x /\ reachable_through_set (b_pg_g g) S2 x ->
                   ~ reachable_through_set (b_pg_g g') S1' x /\ reachable_through_set (b_pg_g g') S2 x.
  Proof.
    intros. destruct H as [? [? ?]]. destruct H0. simpl in H, H1, H2. unfold unreachable_valid in H, H1, H2.
    assert (valid_g g x /\ ~ reachable_through_set (b_pg_g g) S1 x). split; auto. destruct H3 as [s [? ?]].
    apply reachable_foot_valid in H4. apply H4. unfold valid_g in H4. rewrite (H x) in H4. split. destruct H4; auto.
    assert (forall s, reachable_through_set (b_pg_g g) S1 s -> reachable_through_set (b_pg_g g) S2 s ->
                      forall y, reachable (b_pg_g g) s y -> reachable_through_set (b_pg_g g) S1 y /\
                                                            reachable_through_set (b_pg_g g) S2 y). intros; split.
    destruct H5 as [ss [? ?]]. exists ss. split; auto. apply reachable_by_merge with s; auto.
    destruct H6 as [ss [? ?]]. exists ss. split; auto. apply reachable_by_merge with s; auto.
    destruct H3 as [s [? ?]]. destruct H6 as [p ?].
    assert (forall z, In z p -> valid_g g z /\ ~ reachable_through_set (b_pg_g g) S1 z). intros.
    assert (reachable_through_set (b_pg_g g) S2 z). generalize (reachable_path_in (b_pg_g g) p s x H6 z H7); intro. exists s.
    split; auto. split. destruct H8 as [ss [? ?]]. apply reachable_foot_valid in H9. apply H9.
    assert (reachable (b_pg_g g) z x). destruct (reachable_by_path_split_in _ _ _ _ _ _ _ _ _ H6 H7) as [p1 [p2 [? [? ?]]]].
    exists p2. auto. intro. specialize (H5 z H10 H8 x H9). destruct H5. auto.

    exists s. split; auto. exists p. destruct H6 as [[? ?] [? _]]. split; split; auto. clear H4 H5 H6 H8. induction p.
    simpl; auto. unfold valid_g in H7. unfold b_pg_g in H7. assert (valid_g g' a). assert (In a (a :: p)). apply in_eq.
    specialize (H7 _ H4). rewrite H in H7. destruct H7. apply H5. simpl. simpl in H9. destruct p. apply H4. split. split.
    apply H4. split. assert (In v (a :: v :: p)). apply in_cons, in_eq. specialize (H7 _ H5). rewrite H in H7. destruct H7.
    apply H6. destruct H9 as [[_ [_ ?]] _]. assert (In a (a :: v :: p)). apply in_eq. specialize (H7 _ H6).
    specialize (H2 a H7). rewrite <- H2. auto. apply IHp. destruct H9; auto. intros. unfold valid_g, b_pg_g. apply H7.
    apply in_cons. auto. repeat intro; hnf; auto.
  Qed.

  Lemma unreachable_sub_eq_unrch_rch_eq:
    forall {g g': BiMathGraph V D null} {S1 S1': list V},
      (unreachable_subgraph (b_pg_g g) S1) -=- (unreachable_subgraph (b_pg_g g') S1') ->
      forall x S2, ~ reachable_through_set (b_pg_g g) S1 x /\ reachable_through_set (b_pg_g g) S2 x <->
                   ~ reachable_through_set (b_pg_g g') S1' x /\ reachable_through_set (b_pg_g g') S2 x.
  Proof.
    intros. split.
    apply (unreachable_sub_eq_belong_to _ _ _ _ H x S2). apply vi_sym in H.
    apply (unreachable_sub_eq_belong_to _ _ _ _ H x S2).
  Qed.


End GraphReachable.
