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

  Definition graph_fun (Q: adr -> pred world) (x: adr) :=
    (!!(x = 0) && emp) ||
    (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r) /\ valid x) && trinode x d l r ⊗ (Q l) ⊗ (Q r)).

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
                (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r) /\ valid x) && trinode x d l r ⊗
                                                 (graph l) ⊗ (graph r)).
  Proof.
    intros. unfold graph at 1. rewrite corec_fold_unfold. trivial. apply graph_fun_covariant.
  Qed.

  Definition dag_fun (Q: adr -> pred world) (x: adr) :=
    (!!(x = 0) && emp) ||
    (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r) /\ valid x) && trinode x d l r * ((Q l) ⊗ (Q r))).

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
              (EX d:adr, EX l:adr, EX r:adr, !!(gamma bi x = (d, l, r) /\ valid x) && trinode x d l r * ((dag l) ⊗ (dag r))).
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
      {l : adr & {r : adr | biEdge bi x = (l, r) /\ x <> 0 /\ valid x /\ (graph l * TT)%pred w /\ (graph r * TT)%pred w}} +
      {x = 0}.
      destruct (eq_nat_dec x 0). right; auto. left.
      rewrite graph_unfold in H.
      assert (S : ((EX  d : adr, (EX  l : adr, (EX  r : adr,
                                                        !!(gamma bi x = (d, l, r) /\ valid x) && trinode x d l r
                                                          ⊗ graph l ⊗ graph r))) * TT)%pred w).
      destruct_sepcon H h. hnf in H0. destruct H0. destruct H0. hnf in H0. exfalso; auto.
      exists h1, h2; split; auto. clear H. remember (gamma bi x). destruct p as [[d l] r]. exists l, r.
      destruct_sepcon S h. destruct H0 as [dd [ll [rr ?]]]. destruct_ocon H0 i. destruct_ocon H4 j.
      destruct H8 as [[? ?] ?]. injection H8; intros; subst; clear H8. unfold gamma in Heqp. destruct (biEdge bi x).
      injection Heqp; intros; subst; clear Heqp. repeat split; auto. try_join j2 j3 j23'. equate_join j23 j23'.
      try_join j1 i3 j1i3. try_join j1i3 h2 j1i3h2. exists j23, j1i3h2. repeat split; auto.
      try_join i2 i3 i23'; equate_join i23 i23'. try_join i1 h2 i1h2. exists i23, i1h2. repeat split; auto.
    Defined.

    Definition twoSubTrees (x : adr) (w : world)
               (m : {l : adr & {r : adr | biEdge bi x = (l, r) /\ x <> 0 /\ valid x /\ (graph l * TT)%pred w /\
                                          (graph r * TT)%pred w}}) : list {t : adr | (graph t * TT)%pred w }.
      destruct m as [l [r [? [? [? [? ?]]]]]].
      remember (exist (fun t => (graph t * TT)%pred w) l H2) as sl.
      remember (exist (fun t => (graph t * TT)%pred w) r H3) as sr.
      remember (sl :: sr :: nil) as lt; apply lt.
    Defined.

    Definition reach_input := {w : world & (nat * list {t : adr | (graph t * TT)%pred w} * list adr )%type}.

    Definition graph_zero : forall (w : world), (graph 0 * TT)%pred w.
      intros. exists (core w), w; repeat split. apply core_unit. rewrite graph_unfold.
      left; hnf. split; auto. apply core_identity.
    Defined.

    Definition rch1 (i : reach_input) := match projT2 i with (n, _, _) => n end.
    
    Definition rch2 (i : reach_input) := match projT2 i with (_, l, _) => l end.
    
    Definition rch3 (i: reach_input) := match projT2 i with (_, _, result) => result end.

    Fixpoint removeTree (w : world) (x : adr) (l : list {t : adr | (graph t * TT)%pred w}) :=
      match l with
        | nil => nil
        | y :: ttl => if eq_nat_dec x (proj1_sig y) then removeTree w x ttl else y :: removeTree w x ttl
      end.

    Lemma remove_tree_len_le: forall w x l, length (removeTree w x l) <= length l.
    Proof. induction l; simpl. trivial. destruct (eq_nat_dec x (proj1_sig a)); simpl; omega. Qed.
    
    Fixpoint appRemoveList (w : world) (lc la : list {t : adr | (graph t * TT)%pred w}) (lb : list adr) :=
      match lb with
        | nil => lc ++ la 
        | x :: l => appRemoveList w lc (removeTree w x la) l
      end.

    Lemma remove_list_len_le: forall w lb lc la, length (appRemoveList w lc la lb) <= length lc + length la.
    Proof.
      induction lb; intros; simpl. rewrite app_length; trivial.
      apply le_trans with (length lc + length (removeTree w a la)). apply IHlb.
      apply plus_le_compat_l, remove_tree_len_le.
    Qed.

    Definition Sublist {A : Type} (l1 l2 : list A) := forall x, In x l1 -> In x l2.

    Lemma remove_tree_sublist: forall w x l, Sublist (removeTree w x l) l.
    Proof.
      induction l; hnf; intros; simpl in *; auto. destruct a as [t Ht]; simpl in H. destruct (eq_nat_dec x t).
      subst. right. apply IHl; auto. destruct (in_inv H); [left | right]. auto. apply IHl; auto.
    Qed.

    Lemma remove_list_sublist: forall w lb lc la, Sublist (appRemoveList w lc la lb) (lc ++ la).
    Proof.
      induction lb; intros; hnf; intros; simpl in *; auto. specialize (IHlb lc (removeTree w a la) x H).
      destruct (in_app_or _ _ _ IHlb); apply in_or_app; [left | right]. auto.
      generalize (remove_tree_sublist w a la); intro Hr; hnf in Hr; apply Hr; auto.
    Qed.
      
    Definition lengthInput (i : reach_input) :=
      match projT2 i with
        | (len, pr, re) => 2 * len + length pr - 2 * length re
      end.

    Definition inputOrder (i1 i2 : reach_input) := lengthInput i1 < lengthInput i2.
  
    Lemma inputOrder_wf': forall len i, lengthInput i <= len -> Acc inputOrder i.
    Proof.
      induction len; intros; constructor; intros; unfold inputOrder in * |-; [exfalso | apply IHlen]; intuition.
    Qed.

    Lemma inputOrder_wf : well_founded inputOrder.
    Proof. red; intro; eapply inputOrder_wf'; eauto. Defined.

    Definition nil_dec: forall (w : world) (l : list {t : adr | (graph t * TT)%pred w}), {l = nil} + {l <> nil}.
      intros. destruct l; [left | right]; intuition; inversion H.
    Defined.

    Definition combinNatAdr (x : nat) (l : list adr) : list adr := cons x l.

    Definition extractReach : reach_input -> list adr.
      refine (
          Fix inputOrder_wf (fun _ => list adr)
              (fun (inp : reach_input) (funcR : forall inp2, inputOrder inp2 inp -> list adr) =>
                 let w := projT1 inp in
                 let len := rch1 inp in
                 let ll := rch2 inp in
                 let r := rch3 inp in
                 let g := hd (exist _ 0 (graph_zero w)) ll in
                 let l := tl ll in
                 let x := proj1_sig g in
                 let gx := proj2_sig g in
                 if nil_dec w ll
                 then r
                 else if le_dec len (length r)
                      then r
                      else match explode x w gx with
                             | inleft hasNodes => let lt := twoSubTrees x w hasNodes in let realAdd := appRemoveList w l lt r in let newR := combinNatAdr x r in funcR (existT _ w (len, realAdd, newR)) _
                             | inright _ => funcR (existT _ w (len, l, r)) _
                           end)).
      destruct inp as [ww [[llen lll] result]]. unfold rch1, rch2, rch3 in *. simpl in *.
      unfold w, len, ll, r in *. destruct lll. exfalso; apply _H; auto. simpl in *. unfold g, l in *.
      destruct hasNodes as [leftT [rightT [? [? [? [? ?]]]]]]. unfold twoSubTrees in *. unfold combinNatAdr in *.
      unfold lt, realAdd, newR, inputOrder, lengthInput. simpl. generalize (remove_list_len_le ww result lll lt); intro.
      repeat rewrite <- plus_n_O.
      apply le_lt_trans with (llen + llen + length lll + length lt - S (length result + S (length result))). omega.
      simpl; omega.
      destruct inp as [ww [[llen lll] result]]. unfold rch1, rch2, rch3 in *. simpl in *.
      unfold w, len, ll, r in *. destruct lll. exfalso; apply _H; auto. simpl in *. unfold g, l in *.
      unfold inputOrder, lengthInput. simpl. omega.
    Defined.

    Lemma extractReach_unfold:
      forall i : reach_input,
        extractReach i = let w := projT1 i in
                         let m := projT2 i in
                         match m with
                           | (_, nil, r) => r
                           | (len, g :: l, r) =>
                             if le_dec len (length r)
                             then r
                             else let x := proj1_sig g in
                                  let gx := proj2_sig g in
                                  match explode x w gx with
                                    | inleft hasNodes => let subT := twoSubTrees x w hasNodes in
                                                         let newL := appRemoveList w l subT r in
                                                         extractReach (existT _ w (len, newL, x :: r))
                                    | inright _ => extractReach (existT _ w (len, l, r))
                                  end
                         end.
    Proof.
      intros. destruct i as [ww [[n prs] rslt]]. unfold extractReach at 1; rewrite Fix_eq.
      destruct prs; simpl. unfold rch3. simpl. auto. unfold rch1, rch2, rch3. simpl.
      destruct (le_dec n (length rslt)). auto. destruct s as [t H]. simpl. destruct (explode t ww H).
      destruct s as [? [? [? [? [? [? ?]]]]]]. unfold combinNatAdr; simpl. unfold extractReach; auto.
      unfold extractReach; auto. intros. assert (HFunEq: f = g) by (extensionality y; extensionality p; auto); subst; auto.
    Qed.

    Lemma Forall_app: forall {A : Type} (P : A -> Prop) (l1 l2 : list A), Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
    Proof.
      induction l1; intros. rewrite app_nil_l; auto. generalize (Forall_inv H); intros.
      rewrite <- app_comm_cons. apply Forall_cons; auto. apply IHl1; auto. rewrite Forall_forall.
      rewrite Forall_forall in H. intros. apply H. apply in_cons; auto.
    Qed.

    Lemma Forall_sublist: forall {A : Type} (P : A -> Prop) (l1 l2 : list A), Sublist l1 l2 -> Forall P l2 -> Forall P l1.
    Proof. intros; hnf in *. rewrite Forall_forall in *; intro y; intros. apply H0, H; auto. Qed.
    
    Definition reach_input_fun := fun ww => (nat * list {f : adr | (graph f * TT)%pred ww} * list adr)%type.

    Definition graph_sig_fun (w : world) := fun f => (graph f * TT)%pred w.

    Lemma extractReach_reachable:
      forall (x : adr) (i : reach_input),
        Forall (reachable pg x) (rch3 i) ->
        Forall (fun y => reachable pg x y \/ y = 0) (map (@proj1_sig _ (graph_sig_fun (projT1 i))) (rch2 i)) ->
        Forall (reachable pg x) (extractReach i).
    Proof.
      intros x i; remember (lengthInput i); assert (lengthInput i <= n) by omega; clear Heqn; revert H x; revert i.
      induction n; intros; intros; remember (extractReach i) as result;
      rename Heqresult into H3; destruct i as [w [[len pr] rslt]]; unfold rch2, rch3, lengthInput in *;
      simpl in *; rewrite extractReach_unfold in H3; destruct pr; simpl in H3. subst; apply H0; auto.
      destruct (le_dec len (length rslt)). subst; apply H0; auto. exfalso; omega.
      
      subst; apply H0; auto. destruct (le_dec len (length rslt)). subst; apply H0; auto.
      destruct s as [t Ht]; simpl in *. destruct (explode t w Ht). remember (twoSubTrees t w s) as subT.
      destruct s as [l [r [? [? [? [Gl Gr]]]]]]. simpl in HeqsubT. rewrite H3; apply IHn; simpl.
      apply le_trans with (len + (len + 0) + length pr + length subT - S (length rslt + S (length rslt + 0))).
      generalize (remove_list_len_le w rslt pr subT); intros; omega. rewrite HeqsubT; simpl; omega.
      apply Forall_cons; auto. apply Forall_inv in H1. destruct H1; auto. exfalso; apply n1; auto.
      assert (Sublist (appRemoveList w pr subT rslt) (pr ++ subT)) by apply remove_list_sublist.
      admit.
      admit.
    Qed.

  End ConstructReachable.
    
  Lemma graph_reachable_finite: forall x w, x <> 0 -> graph x w -> set_finite (reachable pg x).
  Proof.
    intros. hnf. destruct (world_finite w) as [l ?].
    generalize (core_unit w); intros. unfold unit_for in H2. apply join_comm in H2.
    assert ((graph x * TT)%pred w) by (exists w, (core w); repeat split; auto).
    remember (exist (graph_sig_fun w) x H3) as g.
    remember (existT reach_input_fun w (length l, (g::nil), nil)).
    exists (extractReach s). intros y; split; intros.
    admit.
    admit.
  Qed.

End SpatialGraph.
