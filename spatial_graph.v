Require Import msl.msl_direct.
Require Import overlapping.
Require Import heap_model.
Require Import graph.
Require Import msl_ext.
Require Import ramify_tactics.
Require Import FunctionalExtensionality.
Require Import NPeano.
Require Import List.
Require Import Classical.
Require Import utilities.

Local Open Scope pred.

Instance natEqDec : EqDec nat := { t_eq_dec := eq_nat_dec }.

Definition trinode x d l r :=
  (mapsto x d) * (mapsto (x+1) l) * (mapsto (x+2) r).

Section SpatialGraph.
  Variable VV : Valid nat.
  Definition GV : Valid nat := fun x => VV x /\ x <> 0.
  Variable pg : @PreGraph nat nat natEqDec GV.
  Variable bi : BiGraph pg.

  Definition nodesFrom (x : adr) : list adr := @edge_func adr adr natEqDec GV pg x.

  Definition gValid (x : adr) : Prop := @valid nat natEqDec GV x.

  Definition graph_fun (Q: adr -> pred world) (x: adr) :=
    (!!(x = 0) && emp) ||
    (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r) /\ gValid x) && trinode x d l r ⊗ (Q l) ⊗ (Q r)).

  Lemma graph_fun_covariant : covariant graph_fun.
  Proof.
    unfold graph_fun. apply covariant_orp.
    apply covariant_const.
    apply covariant_exp; intro d.
    apply covariant_exp; intro l.
    apply covariant_exp; intro r.
    repeat apply covariant_ocon.
    apply covariant_andp. apply covariant_const.
    repeat apply covariant_sepcon; apply covariant_const.
    apply covariant_const'. apply covariant_const'.
  Qed.

  Definition graph := corec graph_fun.

  Lemma graph_unfold:
    forall x,
      graph x = (!!(x = 0) && emp) ||
                (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r) /\ gValid x) && trinode x d l r ⊗
                                                 (graph l) ⊗ (graph r)).
  Proof.
    intros. unfold graph at 1. rewrite corec_fold_unfold. trivial. apply graph_fun_covariant.
  Qed.

  Definition dag_fun (Q: adr -> pred world) (x: adr) :=
    (!!(x = 0) && emp) ||
    (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r) /\ gValid x) && trinode x d l r * ((Q l) ⊗ (Q r))).

  Lemma dag_fun_covariant : covariant dag_fun.
  Proof.
    unfold dag_fun.
    apply covariant_orp. apply covariant_const.
    apply covariant_exp. intro d. apply covariant_exp. intro l. apply covariant_exp. intro r.
    apply covariant_sepcon. apply covariant_const.
    apply covariant_ocon; apply covariant_const'.
  Qed.

  Definition dag := corec dag_fun.

  Lemma dag_unfold:
    forall x,
      dag x = (!!(x = 0) && emp) ||
              (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r) /\ gValid x) && trinode x d l r * ((dag l) ⊗ (dag r))).
  Proof.
    intros. unfold dag at 1. rewrite corec_fold_unfold. trivial. apply dag_fun_covariant.
  Qed.

  (* Lemma dag_eq_graph: forall x, dag x |-- graph x && !!(graph_is_acyclic (reachable_subgraph pg (x :: nil))). *)
  (* Proof. *)
  (*   admit. *)
  (* Qed. *)

  Fixpoint graphs (l : list adr) :=
    match l with
      | nil => emp
      | v :: l' => graph v ⊗ graphs l'
    end.

  Fixpoint dags (l : list adr) :=
    match l with
      | nil => emp
      | v :: l' => dag v ⊗ dags l'
    end.

  Lemma graph_path_in: forall p x y P, pg |= p is x ~o~> y satisfying P -> graph x |-- EX v : adr, (mapsto y v * TT).
  Proof.
    induction p; intros; destruct H as [[? ?] [? ?]].
    inversion H.
    simpl in H; inversion H; subst.
    destruct p. simpl in H0; inversion H0; subst. repeat intro.
    rewrite graph_unfold in H3. destruct H3. destruct H3. hnf in H3; destruct H1; intuition.
    destruct H3 as [d [l [r ?]]]. destruct_ocon H3 h. destruct_ocon H6 i.
    destruct H10. destruct_sepcon H12 j. destruct_sepcon H13 k. exists d.
    try_join k2 j2 m1; try_join m1 i3 m2; try_join m2 h3 m3. exists k1, m3; split; auto.

    assert (pg |= n :: p is n ~o~> y satisfying P).
    split; [split; [simpl; auto | auto] | split; [destruct H1; auto | repeat intro; apply H2; apply in_cons; auto]].

    repeat intro; hnf.
    rewrite graph_unfold in H4. destruct H4. destruct H4; hnf in H4; destruct H1; destruct H1; destruct H1; intuition.
    destruct H4 as [d [l [r ?]]].
    destruct_ocon H4 h. destruct_ocon H7 i. destruct H11 as [[? ?] ?].
    unfold gamma in H11.
    destruct_sepcon H14 j. destruct_sepcon H15 k. destruct H1 as [[? [? ?]] ?].
    revert H11. case_eq (biEdge bi x); intros.
    inversion H22; subst.
    generalize (biEdge_only2 bi _ _ _ _ H11 H20); intros.
    destruct H23; subst.
    specialize (IHp _ _ _ H3 _ H12). hnf in IHp. simpl in IHp.
    destruct IHp as [bb ?]. exists bb. apply join_sub_mapsto with i23; auto.
    try_join i2 i3 i23'; equate_join i23 i23'.
    assertSub i23 a S3; trivial.
    specialize (IHp _ _ _ H3 _ H8). hnf in IHp. simpl in IHp.
    destruct IHp as [bb ?]. exists bb. apply join_sub_mapsto with h23; auto.
    try_join h2 h3 h23'; equate_join h23 h23'.
    assertSub h23 a S1; trivial.
  Qed.

  Lemma graph_reachable_in: forall x y, reachable pg x y -> graph x |-- EX v : adr, (mapsto y v * TT).
  Proof. intros; destruct H; apply graph_path_in in H; trivial. Qed.

  Section ConstructReachable.

    Definition explode (x : adr) (w : world) (H : (graph x * TT)%pred w) :
      {l : adr & {r : adr | biEdge bi x = (l, r) /\ gValid x /\ (graph l * TT)%pred w /\ (graph r * TT)%pred w}} + {x = 0}.
      destruct (eq_nat_dec x 0). right; auto. left.
      rewrite graph_unfold in H.
      assert (((EX  d : adr, (EX  l : adr, (EX  r : adr,
                                                    !!(gamma bi x = (d, l, r) /\ gValid x) && trinode x d l r
                                                      ⊗ graph l ⊗ graph r))) * TT)%pred w) as S.
      destruct_sepcon H h. hnf in H0. destruct H0. destruct H0. hnf in H0. exfalso; auto.
      exists h1, h2; split; auto. clear H. remember (gamma bi x). destruct p as [[d l] r]. exists l, r.
      destruct_sepcon S h. destruct H0 as [dd [ll [rr ?]]]. destruct_ocon H0 i. destruct_ocon H4 j.
      destruct H8 as [[? ?] ?]. injection H8; intros; subst; clear H8. unfold gamma in Heqp. destruct (biEdge bi x).
      injection Heqp; intros; subst; clear Heqp. repeat split; auto. destruct H10. auto. try_join j2 j3 j23'.
      equate_join j23 j23'. try_join j1 i3 j1i3. try_join j1i3 h2 j1i3h2. exists j23, j1i3h2. repeat split; auto.
      try_join i2 i3 i23'; equate_join i23 i23'. try_join i1 h2 i1h2. exists i23, i1h2. repeat split; auto.
    Defined.

    Definition twoSubTrees (x : adr) (w : world)
               (m : {l : adr & {r : adr | biEdge bi x = (l, r) /\ gValid x /\ (graph l * TT)%pred w /\
                                          (graph r * TT)%pred w}}) : list {t : adr | (graph t * TT)%pred w }.
      destruct m as [l [r [? [? [? ?]]]]].
      remember (exist (fun t => (graph t * TT)%pred w) l H1) as sl.
      remember (exist (fun t => (graph t * TT)%pred w) r H2) as sr.
      remember (sl :: sr :: nil) as lt; apply lt.
    Defined.

    Fixpoint removeTree (w : world) (x : adr) (l : list {t : adr | (graph t * TT)%pred w}) :=
      match l with
        | nil => nil
        | y :: ttl => if eq_nat_dec x (proj1_sig y) then removeTree w x ttl else y :: removeTree w x ttl
      end.

    Lemma remove_tree_len_le: forall w x l, length (removeTree w x l) <= length l.
    Proof. induction l; simpl. trivial. destruct (eq_nat_dec x (proj1_sig a)); simpl; omega. Qed.

    Lemma remove_tree_sublist: forall w x l, Sublist (removeTree w x l) l.
    Proof.
      induction l; hnf; intros; simpl in *; auto. destruct a as [t Ht]; simpl in H. destruct (eq_nat_dec x t).
      subst. right. apply IHl; auto. destruct (in_inv H); [left | right]. auto. apply IHl; auto.
    Qed.

    Definition reach_input_fun := fun ww => (nat * list {f : adr | (graph f * TT)%pred ww} * list adr)%type.

    Definition graph_sig_fun (w : world) := fun f => (graph f * TT)%pred w.

    Definition nil_dec: forall (w : world) (l : list {t : adr | (graph t * TT)%pred w}), {l = nil} + {l <> nil}.
      intros. destruct l; [left | right]; intuition; inversion H.
    Defined.

    Definition dup_input (w : world) := list {t : adr | (graph t * TT)%pred w}.

    Definition dupLength (w : world) (i : dup_input w) := length i.

    Definition dupOrder (w : world) (i1 i2 : dup_input w) := dupLength w i1 < dupLength w i2.
  
    Lemma dupOrder_wf': forall w len i, dupLength w i <= len -> Acc (dupOrder w) i.
    Proof.
      induction len; intros; constructor; intros; unfold dupOrder in * |-; [exfalso | apply IHlen]; intuition.
    Qed.

    Lemma dupOrder_wf (w : world) : well_founded (dupOrder w).
    Proof. red; intro; eapply dupOrder_wf'; eauto. Defined.

    Definition removeDup (w : world) : dup_input w -> dup_input w.
      refine (
            Fix (dupOrder_wf w) (fun _ => dup_input w)
                (fun (inp : dup_input w) =>
                   match inp return ((forall inp2 : dup_input w, (dupOrder w) inp2 inp -> (dup_input w)) -> dup_input w) with
                     | nil => fun _ => nil
                     | x :: l => fun f => x :: (f (removeTree w (proj1_sig x) l) _)
                   end)).
        apply le_lt_trans with (dupLength w l). apply remove_tree_len_le. simpl; apply lt_n_Sn.
    Defined.

    Lemma removeDup_unfold:
      forall w i,
        removeDup w i = match i with
                          | nil => nil
                          | x :: l => x :: removeDup w (removeTree w (proj1_sig x) l)
                        end.
    Proof.
      intros. unfold removeDup at 1; rewrite Fix_eq. destruct i; auto. intros.
      assert (f = g) by (extensionality y; extensionality p; auto); subst; auto.
    Qed.

    Lemma remove_dup_len_le: forall w l, length (removeDup w l) <= length l.
    Proof.
      intros w l. remember (length l). assert (length l <= n) by omega. clear Heqn. revert H. revert l.
      induction n; intros; rewrite removeDup_unfold; destruct l; auto. inversion H.
      simpl. apply le_n_S. apply IHn. simpl in H; apply le_S_n in H. apply le_trans with (length l).
      apply remove_tree_len_le. auto.
    Qed.

    Lemma remove_dup_sublist: forall w l1 l2, Sublist l1 l2 -> Sublist (removeDup w l1) l2.
    Proof.
      intros w l1. remember (length l1). assert (length l1 <= n) by omega. clear Heqn. revert H. revert l1.
      induction n; intros; rewrite removeDup_unfold; destruct l1. apply Sublist_nil. inversion H. apply Sublist_nil.
      rewrite <- (app_nil_l (removeDup w (removeTree w (proj1_sig s) l1))). rewrite app_comm_cons. apply Sublist_app_2.
      repeat intro. apply in_inv in H1. destruct H1. subst. specialize (H0 a). apply H0. apply in_eq. inversion H1.
      apply IHn. simpl in H. apply le_trans with (length l1). apply remove_tree_len_le. apply le_S_n. apply H.
      apply Sublist_trans with l1. apply remove_tree_sublist. repeat intro. apply H0. apply in_cons. apply H1.
    Qed.
    
    Fixpoint appRemoveList (w : world) (lc la : list {t : adr | (graph t * TT)%pred w}) (lb : list adr) :=
      match lb with
        | nil => removeDup w (lc ++ la) 
        | x :: l => appRemoveList w lc (removeTree w x la) l
      end.

    Lemma remove_list_len_le: forall w lb lc la, length (appRemoveList w lc la lb) <= length lc + length la.
    Proof.
      induction lb; intros; simpl. apply le_trans with (length (lc ++ la)). apply remove_dup_len_le.
      rewrite app_length; trivial.
      apply le_trans with (length lc + length (removeTree w a la)). apply IHlb.
      apply plus_le_compat_l, remove_tree_len_le.
    Qed.

    Lemma remove_list_sublist: forall w lb lc la, Sublist (appRemoveList w lc la lb) (lc ++ la).
    Proof.
      induction lb; intros; hnf; intros; simpl in *; auto. apply (remove_dup_sublist w (lc ++ la) (lc ++ la)).
      apply Sublist_refl. apply H. specialize (IHlb lc (removeTree w a la) a0 H).
      destruct (in_app_or _ _ _ IHlb); apply in_or_app; [left | right]. auto.
      generalize (remove_tree_sublist w a la); intro Hr; hnf in Hr; apply Hr; auto.
    Qed.

    Definition graph_zero : forall (w : world), (graph 0 * TT)%pred w.
      intros. exists (core w), w; repeat split. apply core_unit. rewrite graph_unfold.
      left; hnf. split; auto. apply core_identity.
    Defined.
    
    Definition reach_input (w : world) := (nat * list {t : adr | (graph t * TT)%pred w} * list adr )%type.
      
    Definition lengthInput (w : world) (i : reach_input w) :=
      match i with
        | (len, pr, re) => 2 * len + length pr - 2 * length re
      end.

    Definition inputOrder (w : world) (i1 i2 : reach_input w) := lengthInput w i1 < lengthInput w i2.
  
    Lemma inputOrder_wf': forall w len i, lengthInput w i <= len -> Acc (inputOrder w) i.
    Proof.
      induction len; intros; constructor; intros; unfold inputOrder in * |-; [exfalso | apply IHlen]; intuition.
    Qed.

    Lemma inputOrder_wf (w : world) : well_founded (inputOrder w).
    Proof. red; intro; eapply (inputOrder_wf' w); eauto. Defined.

    Definition extractReach (w : world) : reach_input w -> list adr.
      refine (
          Fix (inputOrder_wf w) (fun _ => list adr)
              (fun (inp : reach_input w) =>
                 match inp return ((forall inp2, inputOrder w inp2 inp -> list adr) -> list adr) with
                   | (_, nil, r) => fun _ => r
                   | (len, g :: l, r) => fun f =>
                                           if le_dec len (length r)
                                           then r
                                           else match explode (proj1_sig g) w (proj2_sig g) with
                                                  | inleft hasNodes => let subT := twoSubTrees (proj1_sig g) w hasNodes in
                                                                       let newL := appRemoveList w l subT r in
                                                                       f (len, newL, (proj1_sig g) :: r) _
                                                  | inright _ => f (len, l, r) _
                                                end
                 end)).
      destruct hasNodes as [leftT [rightT [? [? [? ?]]]]]. destruct g as [x ?]. simpl in *.
      unfold newL, inputOrder, lengthInput; simpl. generalize (remove_list_len_le w r l subT); intro.
      repeat rewrite <- plus_n_O.
      apply le_lt_trans with (len + len + length l + length subT - S (length r + S (length r))). omega. simpl. omega.
      unfold inputOrder, lengthInput; simpl; repeat rewrite <- plus_n_O. omega.
    Defined.    

    Lemma extractReach_unfold:
      forall w i,
        extractReach w i = match i with
                             | (_, nil, r) => r
                             | (len, g :: l, r) =>
                               if le_dec len (length r)
                               then r
                               else match explode (proj1_sig g) w (proj2_sig g) with
                                      | inleft hasNodes => let subT := twoSubTrees (proj1_sig g) w hasNodes in
                                                           let newL := appRemoveList w l subT r in
                                                           extractReach w (len, newL, (proj1_sig g) :: r)
                                      | inright _ => extractReach w (len, l, r)
                                    end
                           end.
    Proof.
      intros. destruct i as [[n prs] rslt]. unfold extractReach at 1; rewrite Fix_eq.
      destruct prs; simpl. auto. destruct (le_dec n (length rslt)). auto.
      destruct (explode (proj1_sig s) w (proj2_sig s)); unfold extractReach; auto.
      intros; assert (f = g) by (extensionality y; extensionality p; auto); subst; auto.
    Qed.    

    Definition rch1 w (i : reach_input w) := match i with (n, _, _) => n end.
    
    Definition rch2 w (i : reach_input w) := match i with (_, l, _) => l end.
    
    Definition rch3 w (i: reach_input w) := match i with (_, _, result) => result end.

    Lemma extractReach_reachable:
      forall w (i : reach_input w) (x : adr),
        Forall (reachable pg x) (rch3 w i) ->
        Forall (fun y => reachable pg x y \/ y = 0) (map (@proj1_sig _ (graph_sig_fun w)) (rch2 w i)) ->
        Forall (reachable pg x) (extractReach w i).
    Proof.
      intros w i x; remember (lengthInput w i); assert (lengthInput w i <= n) by omega; clear Heqn; revert H x; revert i.
      induction n; intros; remember (extractReach w i) as result;
      rename Heqresult into H3; destruct i as [[len pr] rslt]; unfold rch2, rch3, lengthInput in *;
      simpl in *; rewrite extractReach_unfold in H3; destruct pr; simpl in H3. subst; apply H0; auto.
      destruct (le_dec len (length rslt)). subst; apply H0; auto. exfalso; omega.
      
      subst; apply H0; auto. destruct (le_dec len (length rslt)). subst; apply H0; auto.
      destruct s as [t Ht]; simpl in *. destruct (explode t w Ht). remember (twoSubTrees t w s) as subT.
      destruct s as [l [r [? [? [Gl Gr]]]]]. simpl in HeqsubT. assert (reachable pg x t) as HRt.
      destruct (Forall_inv H1); auto. destruct g; exfalso; auto. rewrite H3; apply IHn; simpl.
      apply le_trans with (len + (len + 0) + length pr + length subT - S (length rslt + S (length rslt + 0))).
      generalize (remove_list_len_le w rslt pr subT); intros; omega. rewrite HeqsubT; simpl; omega.
      apply Forall_cons; auto. assert (Sublist (appRemoveList w pr subT rslt) (pr ++ subT)) by apply remove_list_sublist.
      generalize (map_sublist _ _ (proj1_sig (P:=graph_sig_fun w)) _ _ H2); intros; clear H2. rewrite map_app in H4.
      apply (Forall_sublist _ _ _ H4); clear H4. apply Forall_app. apply Forall_tl in H1; auto.
      rewrite HeqsubT; simpl. rewrite Forall_forall. intro y; intros.

      destruct (in_inv H2). subst. destruct Gl as [wl [_ [_ [? _]]]]. rewrite graph_unfold in H3.
      destruct H3 as [[? ?] | [dd [ll [rr ?]]]]; [right; auto| left]. destruct_ocon H3 h. destruct_ocon H6 j.
      destruct H10 as [[? ?] ?]. apply reachable_by_merge with t. auto. exists (t :: y :: nil). hnf.
      split; split; simpl; auto. split. unfold biEdge in e. split. apply reachable_foot_valid in HRt. auto. split.
      apply H12. destruct (@only_two_neighbours nat nat natEqDec GV pg bi t) as [v1 [v2 HHH]]. inversion e; subst; clear e.
      rewrite HHH. apply in_eq. auto. repeat intro. hnf. auto. clear H2.

      destruct (in_inv H4). subst. destruct Gr as [wr [_ [_ [? _]]]]. rewrite graph_unfold in H2.
      destruct H2 as [[? ?] | [dd [ll [rr ?]]]]; [right; auto| left]. destruct_ocon H2 h. destruct_ocon H6 j.
      destruct H10 as [[? ?] ?]. apply reachable_by_merge with t. auto. exists (t :: y :: nil). hnf.
      split; split; simpl; auto. split. unfold biEdge in e. split. apply reachable_foot_valid in HRt. auto. split.
      apply H12. destruct (@only_two_neighbours nat nat natEqDec GV pg bi t) as [v1 [v2 HHH]]. inversion e; subst; clear e.
      rewrite HHH. apply in_cons, in_eq. auto. repeat intro. hnf. auto. inversion H2.

      rewrite H3; apply IHn; simpl; clear IHn H3 result; auto. omega. rewrite Forall_forall in H1. rewrite Forall_forall.
      intros. apply H1. apply in_cons; auto.
    Qed.

    Lemma extractReach_nodup: forall w i, NoDup (rch3 w i) -> NoDup (extractReach w i).
    Proof.
      intros w i; remember (lengthInput w i); assert (lengthInput w i <= n) by omega; clear Heqn; revert H. revert i.
      induction n; intros; remember (extractReach w i) as result; rename Heqresult into H1;
      destruct i as [[len pr] rslt]; unfold rch3, lengthInput in *;
      simpl in *; rewrite extractReach_unfold in H1; destruct pr; simpl in H1. subst; auto.
      destruct (le_dec len (length rslt)). subst; auto. exfalso; omega. subst; auto.
      destruct (le_dec len (length rslt)). subst; auto. destruct s as [t Ht].
      admit.
    Qed.

  End ConstructReachable.
    
  Lemma graph_reachable_finite: forall x w, graph x w -> set_finite (reachable pg x).
  Proof.
    intros. hnf. destruct (world_finite w) as [l ?].
    generalize (core_unit w); intros. unfold unit_for in H1. apply join_comm in H1.
    assert ((graph x * TT)%pred w) by (exists w, (core w); repeat split; auto).
    remember (exist (graph_sig_fun w) x H2) as g.
    remember (length l, (g::nil), nil : list adr) as s.
    assert (Forall (reachable pg x) (extractReach w s)). apply extractReach_reachable.
    unfold rch3; rewrite Heqs; simpl; apply Forall_nil. unfold rch2; rewrite Heqs; rewrite Heqg; simpl.
    apply Forall_forall; intros. apply in_inv in H3; destruct H3. subst. assert (graph x0 w) by auto.
    rewrite graph_unfold in H. destruct H as [[? ?] | [dd [ll [rr ?]]]]. hnf in H; right; auto. left.
    apply reachable_by_reflexive. split. destruct_ocon H h. destruct_ocon H6 j. destruct H10 as [[? ?] ?].
    apply H12. hnf; auto. inversion H3.
    exists (extractReach w s). intros y; split; intros.
    
    rewrite Forall_forall in H3. apply H3. auto.

    destruct (classic (reachable pg x y)); [exfalso | auto]. apply H4.
    generalize (graph_reachable_in _ _ H5). intros. specialize (H6 w H). hnf in H6. destruct H6 as [b ?].
    unfold reachable in H5. rewrite reachable_acyclic in H5.
    admit.
  Qed.

End SpatialGraph.
