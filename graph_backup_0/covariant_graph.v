Require Import msl.msl_direct.
Require Import overlapping.
Require Import heap_model.
Require Import graph.
Require Import msl_ext.
Require Import ramify_tactics.
Require Import FunctionalExtensionality.
Require Import NPeano.
Require Import List.
Require Import utilities.

Local Open Scope pred.

Instance natEqDec : EqDec nat := { t_eq_dec := eq_nat_dec }.

Definition trinode x d l r := !!(3 | x) && (mapsto x d) * (mapsto (x+1) l) * (mapsto (x+2) r).

Section PointwiseGraph.

  Variable pg : @PreGraph nat nat natEqDec.
  Variable bi : BiGraph pg.

  Axiom valid_not_zero: forall x, @valid nat nat natEqDec pg x -> x <> 0.

  Definition gValid (x : adr) : Prop := @valid nat nat natEqDec pg x.

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

  Definition graph_maps (v : adr) : pred world := let (dl, r) := gamma bi v in let (d, l) := dl in trinode v d l r.

  Lemma precise_graph_maps: forall v, precise (graph_maps v).
  Proof.
    intro. unfold graph_maps. destruct (gamma bi v) as [dl r]. destruct dl as [d l]. unfold trinode. apply precise_sepcon.
    apply precise_mapsto. apply precise_sepcon. apply precise_mapsto. apply precise_andp_right. apply precise_mapsto.
  Qed.

  Lemma joinable_mapsto:
    forall w x y a b, x <> y -> (mapsto x a * TT)%pred w -> (mapsto y b * TT)%pred w -> (mapsto x a * mapsto y b * TT)%pred w.
  Proof.
    intros. destruct H0 as [p [q [? [? ?]]]]. generalize H2; intro Hmap1. destruct p as [fp xp] eqn:? .
    destruct H1 as [m [n [? [? ?]]]]. generalize H4; intro Hmap2. destruct m as [fm xm] eqn:? .  hnf in H2. simpl in H2.
    hnf in H4. simpl in H4. destruct H2 as [? [? ?]]. destruct H4 as [? [? ?]].
    remember (fun xx : adr => if eq_nat_dec xx x then Some a else (if eq_nat_dec xx y then Some b else None)) as f.
    assert (finMap f). exists (x :: y :: nil). intro z. intros. rewrite Heqf. destruct (eq_nat_dec z x). rewrite e in *.
    exfalso. apply H10. apply in_eq. destruct (eq_nat_dec z y). rewrite e in *. exfalso. apply H10. apply in_cons. apply in_eq.
    trivial. remember (exist (finMap (B:=adr)) f H10) as ff. assert (join p m ff). rewrite Heqw0, Heqw1, Heqff.
    hnf; simpl. intro z. destruct (eq_nat_dec z x). rewrite e in *. rewrite H7. generalize (H8 x H); intro HS. rewrite HS.
    rewrite Heqf. destruct (eq_nat_dec x x). apply lower_None2. exfalso; auto. destruct (eq_nat_dec z y). rewrite e in *.
    rewrite H9. generalize (H6 y n0); intro HS. rewrite HS. rewrite Heqf. destruct (eq_nat_dec y x). intuition.
    destruct (eq_nat_dec y y). apply lower_None1. intuition. specialize (H6 z n0). specialize (H8 z n1). rewrite H6, H8.
    rewrite Heqf. destruct (eq_nat_dec z x). intuition. destruct (eq_nat_dec z y). intuition. apply lower_None1.
    rewrite <- Heqw0 in *. rewrite <- Heqw1 in *. destruct (join_together H0 H1 H11) as [qn ?]. exists ff, qn.
    repeat split; auto. exists p, m. split; auto.
  Qed.

  Lemma joinable_graph_maps: forall w, joinable graph_maps w.
  Proof.
    repeat intro. destruct_sepcon H0 p. destruct_sepcon H1 q. unfold graph_maps in *. destruct (gamma bi x) as [[dx lx] rx].
    destruct (gamma bi y) as [[dy ly] ry]. unfold trinode in *. destruct_sepcon H2 h. destruct_sepcon H4 i.
    destruct_sepcon H6 h. destruct H10. destruct_sepcon H8 i. destruct H13. hnf in H10, H13. assert (x + 2 <> y + 2). intro.
    apply H. rewrite Nat.add_cancel_r in H16. auto. assertSub h2 w Sub1. assertSub i2 w Sub2.
    admit.
  Qed.

  Lemma graph_path_tri_in: forall p x y P, pg |= p is x ~o~> y satisfying P -> graph x |-- graph_maps y * TT.
  Proof.
    induction p; intros; destruct H as [[? ?] [? ?]]. inversion H. simpl in H; inversion H; subst. clear H. destruct p.
    simpl in H0; inversion H0; subst; clear H0. repeat intro. rewrite graph_unfold in H. destruct H as [[? ?] | ?].
    hnf in H; apply valid_not_zero in H1; intuition. destruct H as [d [l [r ?]]]. destruct_ocon H h. destruct_ocon H4 i.
    destruct H8 as [[? ?] ?]. try_join i3 h3 i3h3. exists i12, i3h3. split; auto. split; auto. hnf.
    destruct (gamma bi y) as [dl rr].
    destruct dl as [dd ll]. inversion H8; auto. assert (pg |= n :: p is n ~o~> y satisfying P).
    split; [split; [simpl; auto | auto] | split; [destruct H1; auto | repeat intro; apply H2; apply in_cons; auto]].

    repeat intro. rewrite graph_unfold in H3. destruct H3 as [[? ?] | [d [l [r ?]]]]. hnf in H3. destruct H1 as [[? ?] ?].
    apply valid_not_zero in H1.
    intuition. destruct_ocon H3 h. destruct_ocon H6 i. destruct H10 as [[? ?] ?]. unfold gamma in H10. destruct_sepcon H13 j.
    destruct_sepcon H14 k. destruct H1 as [[? [? ?]] ?]. revert H10. case_eq (biEdge bi x); intros. inversion H21; subst.
    generalize (biEdge_only2 bi _ _ _ _ H10 H19); intros. destruct H22; subst. specialize (IHp _ _ _ H _ H11).
    destruct IHp as [l1 [l2 [? [? ?]]]]. try_join i2 i3 i23'. equate_join i23 i23'. try_join l2 i1 l2i1.
    try_join l2i1 h3 l2i1h3. exists l1, l2i1h3. split; auto. specialize (IHp _ _ _ H _ H7). destruct IHp as [l1 [l2 [? [? ?]]]].
    try_join h2 h3 h23'. equate_join h23 h23'. try_join l2 h1 l2h1. exists l1, l2h1. split; auto.
  Qed.

  Lemma graph_reachable_tri_in: forall x y, reachable pg x y -> graph x |-- graph_maps y * TT.
  Proof. intros; destruct H; apply graph_path_tri_in in H; trivial. Qed.

  Lemma graph_path_in: forall p x y P, pg |= p is x ~o~> y satisfying P -> graph x |-- EX v : adr, (mapsto y v * TT).
  Proof.
    intros. generalize (graph_path_tri_in _ _ _ _ H). intros. repeat intro. specialize (H0 a H1). destruct_sepcon H0 i.
    hnf in H2. destruct (gamma bi y) as [dl r] in H2. destruct dl as [d l]. destruct_sepcon H2 j. destruct_sepcon H4 k.
    destruct H6. try_join k2 j2 k2j2. try_join k2j2 i2 k2j2i2. exists d, k1, k2j2i2. split; auto.
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
      injection Heqp; intros; subst; clear Heqp. repeat split; auto. apply valid_not_zero in H10. try_join j2 j3 j23'.
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

    Definition graph_sig_fun (w : world) := fun f => (graph f * TT)%pred w.

    Definition fetch (w : world) := proj1_sig (P := graph_sig_fun w).

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

    Lemma remove_tree_not_in: forall w x l, ~ In x (map (fetch w) (removeTree w x l)).
    Proof.
      induction l; intro; simpl in * |-. apply H. destruct (eq_nat_dec x (proj1_sig a)). subst.
      apply IHl; auto. simpl in H. destruct H. intuition. apply IHl; auto.
    Qed.

    Lemma remove_tree_in: forall w x l y, y <> x -> In y (map (fetch w) l) -> In y (map (fetch w) (removeTree w x l)).
    Proof.
      induction l; intros; simpl in *. apply H0. destruct a as [a ?]. simpl in *. destruct (eq_nat_dec x a).
      destruct H0. subst. exfalso; apply H; auto. apply IHl; auto. simpl in *. destruct H0. left; auto.
      right. apply IHl; auto.
    Qed.
    
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

    Lemma remove_dup_in_inv: forall w x l, In x (map (fetch w) l) -> In x (map (fetch w) (removeDup w l)).
    Proof.
      intros w x l. remember (length l). assert (length l <= n) by omega. clear Heqn. revert l H.
      induction n; intros; rewrite removeDup_unfold; destruct l; auto. simpl in H. omega. destruct s as [s ?].
      simpl in *. destruct (eq_nat_dec x s); destruct H0. left; auto. left; auto. exfalso; apply n0; auto.
      right. apply IHn. apply le_trans with (length l). apply remove_tree_len_le. omega. apply remove_tree_in; auto.
    Qed.

    Lemma remove_dup_nodup: forall w l, NoDup (map (fetch w) (removeDup w l)).
    Proof.
      intros w l. remember (length l). assert (length l <= n) by omega. clear Heqn. revert H. revert l.
      induction n; intros; rewrite removeDup_unfold; destruct l; simpl. apply NoDup_nil. inversion H. apply NoDup_nil.
      apply NoDup_cons. generalize (remove_tree_not_in w (proj1_sig s) l); intro. intro; apply H0; clear H0.
      apply (map_sublist _ _ (fetch w)
                         (removeDup w (removeTree w (proj1_sig s) l)) (removeTree w (proj1_sig s) l)).
      apply remove_dup_sublist. apply Sublist_refl. auto.
      apply IHn. simpl in H. apply le_trans with (length l). apply remove_tree_len_le. apply le_S_n. apply H.
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

    Lemma remove_list_no_dup: forall w lb lc la, NoDup (map (fetch w) (appRemoveList w lc la lb)).
    Proof. induction lb; intros; simpl. apply remove_dup_nodup. apply IHlb. Qed.

    Lemma remove_list_not_in: forall w lb lc la, exists ld, (appRemoveList w lc la lb = removeDup w (lc ++ ld)) /\
                                                            Sublist ld la /\ forall x, In x lb -> ~ In x (map (fetch w) ld).
    Proof.
      induction lb; intros; simpl. exists la. repeat split. apply Sublist_refl. intros. auto.
      destruct (IHlb lc (removeTree w a la)) as [ld [? [? ?]]]. exists ld. repeat split; auto.
      apply Sublist_trans with (removeTree w a la). auto. apply remove_tree_sublist. intro y; intros.
      destruct H2; auto. subst. apply map_sublist with (f := fetch w) in H0. intro.
      specialize (H0 y H2). apply remove_tree_not_in in H0. auto.
    Qed.

    Lemma remove_list_in: forall w lb lc la a x, x <> a -> (~ In x lb) -> In x (map (fetch w) la) ->
                                                 In x (map (fetch w) (appRemoveList w lc (removeTree w a la) lb)).
    Proof.
      induction lb; intros; simpl. assert (In x (map (fetch w) (lc ++ removeTree w a la))). rewrite map_app.
      apply in_or_app; right. apply remove_tree_in; auto. apply remove_dup_in_inv. auto. apply IHlb.
      intro; apply H0; subst; apply in_eq. intro; apply H0; apply in_cons; auto. apply remove_tree_in; auto.
    Qed.

    Lemma remove_list_in_2: forall w lb lc la x, In x (map (fetch w) lc) -> In x (map (fetch w) (appRemoveList w lc la lb)).
    Proof.
      induction lb; intros; simpl. apply remove_dup_in_inv. rewrite map_app. apply in_or_app. left; auto. apply IHlb. auto.
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
                                                  | inleft hasNodes =>
                                                    let subT := twoSubTrees (proj1_sig g) w hasNodes in let m := (proj1_sig g) :: r in let newL := appRemoveList w l subT m in f (len, newL, m) _
                                                  | inright _ => f (len, l, r) _
                                                end
                 end)).
      destruct hasNodes as [leftT [rightT [? [? [? ?]]]]]. destruct g as [x ?]. simpl in subT.
      unfold newL, inputOrder, lengthInput. generalize (remove_list_len_le w m l subT); intro. 
      apply le_lt_trans with (len + len + length l + length subT - S (length r + S (length r))).
      unfold m at 2. simpl length at 2. omega. simpl. omega.
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
                                                           let newL := appRemoveList w l subT (proj1_sig g :: r) in
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
        Forall (fun y => reachable pg x y \/ y = 0) (map (fetch w) (rch2 w i)) ->
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
      destruct (Forall_inv H1); auto. apply valid_not_zero in g; exfalso; auto. rewrite H3; apply IHn; simpl.
      apply le_trans with (len + (len + 0) + length pr + length (removeTree w t subT) - S (length rslt + S (length rslt + 0))).
      generalize (remove_list_len_le w rslt pr (removeTree w t subT)); intros. omega.
      generalize (remove_tree_len_le w t subT); intros. rewrite HeqsubT in H2 at 2. simpl in H2. omega.
      apply Forall_cons; auto.
      assert (Sublist (appRemoveList w pr (removeTree w t subT) rslt) (pr ++ subT)).
      apply Sublist_trans with (pr ++ (removeTree w t subT)). apply remove_list_sublist.
      apply Sublist_app. apply Sublist_refl. apply remove_tree_sublist.
      generalize (map_sublist _ _ (fetch w) _ _ H2); intros; clear H2. rewrite map_app in H4.
      apply (Forall_sublist _ _ _ H4); clear H4. apply Forall_app. apply Forall_tl in H1; auto.
      rewrite HeqsubT; simpl. rewrite Forall_forall. intro y; intros.

      destruct (in_inv H2). subst. destruct Gl as [wl [_ [_ [? _]]]]. rewrite graph_unfold in H3.
      destruct H3 as [[? ?] | [dd [ll [rr ?]]]]; [right; auto| left]. destruct_ocon H3 h. destruct_ocon H6 j.
      destruct H10 as [[? ?] ?]. apply reachable_by_merge with t. auto. exists (t :: y :: nil). hnf.
      split; split; simpl; auto. split. unfold biEdge in e. split. apply reachable_foot_valid in HRt. auto. split.
      apply H12. destruct (@only_two_neighbours nat nat natEqDec pg bi t) as [v1 [v2 HHH]]. inversion e; subst; clear e.
      rewrite HHH. apply in_eq. auto. repeat intro. hnf. auto. clear H2.

      destruct (in_inv H4). subst. destruct Gr as [wr [_ [_ [? _]]]]. rewrite graph_unfold in H2.
      destruct H2 as [[? ?] | [dd [ll [rr ?]]]]; [right; auto| left]. destruct_ocon H2 h. destruct_ocon H6 j.
      destruct H10 as [[? ?] ?]. apply reachable_by_merge with t. auto. exists (t :: y :: nil). hnf.
      split; split; simpl; auto. split. unfold biEdge in e. split. apply reachable_foot_valid in HRt. auto. split.
      apply H12. destruct (@only_two_neighbours nat nat natEqDec pg bi t) as [v1 [v2 HHH]]. inversion e; subst; clear e.
      rewrite HHH. apply in_cons, in_eq. auto. repeat intro. hnf. auto. inversion H2.

      rewrite H3; apply IHn; simpl; clear IHn H3 result; auto. omega. rewrite Forall_forall in H1. rewrite Forall_forall.
      intros. apply H1. apply in_cons; auto.
    Qed.

    Lemma extractReach_nodup: forall w i, NoDup ((map (fetch w) (rch2 w i)) ++ (rch3 w i)) -> NoDup (extractReach w i).
    Proof.
      intros w i; remember (lengthInput w i); assert (lengthInput w i <= n) by omega; clear Heqn; revert H. revert i.
      induction n; intros; remember (extractReach w i) as result; rename Heqresult into H1;
      destruct i as [[len pr] rslt]; unfold rch3, lengthInput in *;
      simpl in *; rewrite extractReach_unfold in H1; destruct pr; simpl in H1. subst; auto.
      destruct (le_dec len (length rslt)). subst; apply NoDup_app_r in H0; auto. simpl in H; exfalso; omega. subst; auto.
      destruct (le_dec len (length rslt)). subst; apply NoDup_app_r in H0; auto. destruct s as [t Ht]. simpl in *.
      destruct (explode t w Ht). subst; apply IHn. simpl. repeat rewrite <- plus_n_O.
      apply le_trans with (len + len + length pr + length (twoSubTrees t w s) - S (length rslt + S (length rslt))).
      generalize (remove_list_len_le w rslt pr (removeTree w t (twoSubTrees t w s))); intro;
      generalize (remove_tree_len_le w t (twoSubTrees t w s)); intro; omega.
      destruct s as [leftT [rightT [? [? [? ?]]]]]; simpl; omega. simpl. generalize (NoDup_cons_1 _ _ _ H0); intro.
      apply NoDup_cons_2 in H0. rewrite NoDup_app_eq in H1. destruct H1 as [? [? ?]]. apply NoDup_app_inv.
      apply remove_list_no_dup. apply NoDup_cons. intro; apply H0. apply in_or_app. right; auto. auto.
      intros. destruct (remove_list_not_in w rslt pr (removeTree w t (twoSubTrees t w s))) as [la [? [? ?]]].
      rewrite H5 in H4; clear H5. assert (Sublist (removeDup w (pr ++ la)) (pr ++ la)). apply remove_dup_sublist.
      apply Sublist_refl. apply map_sublist with (f := fetch w) in H5. specialize (H5 x H4). clear H4. rewrite map_app in H5.
      apply in_app_or in H5. intro. apply in_inv in H4. destruct H5, H4. subst. apply H0. apply in_or_app. left; auto.
      specialize (H3 x H5). apply H3; auto. subst. apply map_sublist with (f := fetch w) in H6. specialize (H6 x H5).
      generalize (remove_tree_not_in w x (twoSubTrees x w s)); intro. apply H4; auto. specialize (H7 x H4). auto.
      subst; apply IHn. omega. simpl. rewrite <- (app_nil_l ((map (fetch w) pr) ++ rslt)) in H0. rewrite app_comm_cons in H0.
      apply NoDup_app_r in H0. auto.
    Qed.

    Definition NotNone (w : world) (e : adr) : Prop := lookup_fpm w e <> None.

    Lemma extractReach_all_not_none: forall w i, Forall (NotNone w) (rch3 w i) -> Forall (NotNone w) (extractReach w i).
    Proof.
      intros w i; remember (lengthInput w i); assert (lengthInput w i <= n) by omega; clear Heqn; revert H. revert i.
      induction n; intros; remember (extractReach w i) as result;
      rename Heqresult into H3; destruct i as [[len pr] rslt]; unfold rch2, rch3, lengthInput in *;
      simpl in *; rewrite extractReach_unfold in H3; destruct pr; simpl in H3. subst; apply H0; auto.
      destruct (le_dec len (length rslt)). subst; auto. exfalso; omega. subst; auto.
      destruct (le_dec len (length rslt)). subst; auto. destruct s as [t Ht]. simpl in *.
      destruct (explode t w Ht). rewrite H3. apply IHn. repeat rewrite <- plus_n_O. simpl.
      apply le_trans with (len + len + length pr + length (twoSubTrees t w s) - S (length rslt + S (length rslt))).
      generalize (remove_list_len_le w rslt pr (removeTree w t (twoSubTrees t w s))); intro;
      generalize (remove_tree_len_le w t (twoSubTrees t w s)); intro; omega.
      destruct s as [leftT [rightT [? [? [? ?]]]]]; simpl; omega. constructor. clear H3.
      destruct s as [leftT [rightT [? [? [? ?]]]]]. generalize (valid_not_zero _ H2); intro. destruct_sepcon Ht w.
      rewrite graph_unfold in H7.
      destruct H7 as [[? ?] | [dd [ll [rr ?]]]]. exfalso; intuition. destruct_ocon H7 h. destruct_ocon H11 j.
      destruct H15. destruct_sepcon H17 k. destruct_sepcon H18 l. destruct H20 as [Hd [? [? ?]]].
      apply lookup_fpm_join_sub with l1. try_join l2 k2 l2k2. try_join l2k2 j3 l2k2j3. try_join l2k2j3 h3 l2k2j3h3.
      try_join l2k2j3h3 w2 l2k2j3h3w2. exists l2k2j3h3w2. auto. rewrite H23. intro S; inversion S. auto.
      rewrite H3. apply IHn. omega. auto.
    Qed.

    Lemma extractReach_length_bound: forall w i, length (rch3 w i) <= rch1 w i -> length (extractReach w i) <= rch1 w i.
    Proof.
      intros w i; remember (lengthInput w i); assert (lengthInput w i <= n) by omega; clear Heqn; revert H. revert i.
      induction n; intros; remember (extractReach w i) as result;
      rename Heqresult into H3; destruct i as [[len pr] rslt]; unfold rch3, lengthInput in *;
      simpl in *; rewrite extractReach_unfold in H3; destruct pr; simpl in H3. subst; auto. simpl in H; exfalso; omega.
      subst; auto. destruct (le_dec len (length rslt)). subst; auto. destruct s as [t Ht]. simpl in *.
      destruct (explode t w Ht).
      specialize (IHn (len, appRemoveList w pr (removeTree w t (twoSubTrees t w s)) rslt, t :: rslt)). simpl in IHn.
      rewrite H3. apply IHn. repeat rewrite <- plus_n_O in *.
      apply le_trans with (len + len + length pr + length (twoSubTrees t w s) - S (length rslt + S (length rslt))).
      generalize (remove_list_len_le w rslt pr (removeTree w t (twoSubTrees t w s))); intro;
      generalize (remove_tree_len_le w t (twoSubTrees t w s)); intro; omega.
      destruct s as [leftT [rightT [? [? [? ?]]]]]; simpl; omega. omega. rewrite H3; apply IHn. omega. unfold rch1. omega.
    Qed.

    Lemma extractReach_sublist: forall w i, Sublist (rch3 w i) (extractReach w i).
    Proof.
      intros w i; remember (lengthInput w i); assert (lengthInput w i <= n) by omega; clear Heqn; revert H. revert i.
      induction n; intros; remember (extractReach w i) as result;
      rename Heqresult into H3; destruct i as [[len pr] rslt]; unfold rch3, lengthInput in *;
      simpl in *; rewrite extractReach_unfold in H3; destruct pr; simpl in H3. subst; apply Sublist_refl.
      destruct (le_dec len (length rslt)). subst. apply Sublist_refl. simpl in H; omega. subst; apply Sublist_refl.
      destruct (le_dec len (length rslt)). subst. apply Sublist_refl. destruct s as [t Ht]; simpl in *.
      destruct (explode t w Ht). 
      specialize (IHn (len, appRemoveList w pr (removeTree w t (twoSubTrees t w s)) rslt, t :: rslt)). simpl in IHn.
      assert (Sublist (t :: rslt) (extractReach w (len, appRemoveList w pr (removeTree w t (twoSubTrees t w s)) rslt,
                                                   t :: rslt))).
      apply IHn. repeat rewrite <- plus_n_O in *.
      apply le_trans with (len + len + length pr + length (twoSubTrees t w s) - S (length rslt + S (length rslt))).
      generalize (remove_list_len_le w rslt pr (removeTree w t (twoSubTrees t w s))); intro;
      generalize (remove_tree_len_le w t (twoSubTrees t w s)); intro; omega.
      destruct s as [leftT [rightT [? [? [? ?]]]]]; simpl; omega. rewrite <- H3 in H0. intro y; intros.
      apply (H0 y). apply in_cons; auto. specialize (IHn (len, pr, rslt)); simpl in IHn. rewrite H3. apply IHn.
      simpl in H; omega.
    Qed.      

    Definition ProcessingInResult (l1 l2 : list adr) : Prop := forall x y, In x l1 -> reachable pg x y -> In y l2.

    Lemma PIR_cons: forall a l1 l2, (forall y, reachable pg a y -> In y l2) -> ProcessingInResult l1 l2 ->
                                    ProcessingInResult (a :: l1) l2.
    Proof. repeat intro; apply in_inv in H1; destruct H1. subst. apply H; auto. apply (H0 x); auto. Qed.

    Lemma PIR_sublist: forall l1 l2 l3, Sublist l1 l2 -> ProcessingInResult l2 l3 -> ProcessingInResult l1 l3.
    Proof. repeat intro. specialize (H x H1). apply (H0 x y); auto. Qed.

    Definition ResultInProcessing (l1 l2 : list adr) : Prop := forall x y, In x l1 -> edge pg x y -> In y l1 \/ In y l2.

    Lemma neg_eq_in_neq_nin: forall a (l : list adr) x, ~ (a = x \/ In x l) -> x <> a /\ ~ In x l.
    Proof. intros; split. destruct (eq_nat_dec x a); auto. destruct (in_dec eq_nat_dec x l); auto. Qed.

    Fixpoint findNotIn (l1 l2 l3: list adr) : (option adr * (list adr * list adr)) :=
      match l1 with
        | nil => (None, (nil, nil))
        | x :: l => if (in_dec eq_nat_dec x l2) then findNotIn l l2 (x :: l3) else (Some x, (rev l3, l))
      end.

    Lemma find_not_in_none: forall l1 l2 l3, fst (findNotIn l1 l2 l3) = None -> Forall (fun m => In m l2) l1.
    Proof.
      induction l1; intros. apply Forall_nil. simpl in H. destruct (in_dec eq_nat_dec a l2).
      apply Forall_cons. auto. apply IHl1 with (a :: l3); auto. inversion H.
    Qed.

    Lemma find_not_in_some_explicit:
      forall l1 l2 l3 x li1 li2,
        findNotIn l1 l2 l3 = (Some x, (li1, li2)) -> (Forall (fun m => In m l2) l3) ->
        (~ In x li1) /\ (~ In x l2) /\ exists l4, li1 = rev l3 ++ l4 /\ Forall (fun m => In m l2) l4 /\ l1 = l4 ++ x :: li2.
    Proof.
      induction l1; intros; simpl in H. inversion H. destruct (in_dec eq_nat_dec a l2).
      assert (Forall (fun m : adr => In m l2) (a :: l3)) by (apply Forall_cons; auto).
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
      intros. assert (Forall (fun m : adr => In m l2) nil) by apply Forall_nil.
      destruct (find_not_in_some_explicit l1 l2 nil x li1 li2 H H0). destruct H2 as [? [l4 [? [? ?]]]].
      simpl in H3. rewrite H3 in *. repeat split; auto.
    Qed.

    Lemma foot_none_nil: forall (l : list adr), foot l = None -> l = nil.
    Proof. induction l; intros; auto. simpl in H. destruct l. inversion H. specialize (IHl H). inversion IHl. Qed.

    Lemma reachable_by_path_split_dec:
      forall p a b P rslt,
        pg |= p is a ~o~> b satisfying P -> {Forall (fun m => In m (a :: rslt)) p} +
                                            {exists l1 l2 e1 s2, Forall (fun m => In m (a :: rslt)) l1 /\
                                                                 pg |= l1 is a ~o~> e1 satisfying P /\
                                                                 pg |= l2 is s2 ~o~> b satisfying P /\
                                                                 edge pg e1 s2 /\ ~ In s2 (a::rslt) /\ p = l1 ++ l2 /\
                                                                 ~ In s2 l1}.
    Proof.
      intros. remember (findNotIn p (a :: rslt) nil) as f. destruct f as [n [l1 l2]]. destruct n. right.
      apply eq_sym in Heqf. destruct (find_not_in_some _ _ _ _ _ Heqf) as [? [? [? ?]]]. exists l1, (a0 :: l2).
      rewrite Forall_forall in H0. destruct l1. rewrite app_nil_l in H1.
      generalize (reachable_by_path_head _ _ _ _ _ _ _ _ H); intro. rewrite H1 in *. simpl in H4. inversion H4.
      rewrite H6 in *. exfalso; apply H3; apply in_eq.
      generalize (reachable_by_path_head _ _ _ _ _ _ _ _ H); intro.
      rewrite <- app_comm_cons in H1. rewrite H1 in H4. simpl in H4. inversion H4. rewrite H6 in *. clear H4 H6 a1.
      remember (foot (a :: l1)). destruct o. exists n, a0. split. rewrite Forall_forall; auto.
      assert (paths_meet_at adr (a :: l1) (n :: a0 :: l2) n) by (repeat split; auto).
      assert (pg |= path_glue adr (a :: l1) (n :: a0 :: l2) is a ~o~> b satisfying P). unfold path_glue. simpl.
      rewrite <- H1. auto. destruct (reachable_by_path_split_glue _ _ _ _ _ _ _ _ _ _ H4 H5). clear H4 H5. split; auto.
      assert (paths_meet_at adr (n :: a0 :: nil) (a0 :: l2) a0) by repeat split.
      assert (pg |= path_glue adr (n :: a0 :: nil) (a0 :: l2) is n ~o~> b satisfying P). unfold path_glue. simpl. auto.
      destruct (reachable_by_path_split_glue _ _ _ _ _ _ _ _ _ _ H4 H5). clear H4 H5 H6 H7. split; auto.
      split. destruct H8. destruct H5. destruct H5. auto. split. auto. split; simpl; auto.
      apply eq_sym in Heqo. generalize (foot_none_nil (a :: l1) Heqo); intros. inversion H4.
      assert (fst (findNotIn p (a :: rslt) nil) = None) by (rewrite <- Heqf; simpl; auto). left.
      apply find_not_in_none with nil. auto.
    Qed.
      
    Lemma extractReach_contains_all:
      forall w i, ResultInProcessing (rch3 w i) (map (fetch w) (rch2 w i)) -> length (extractReach w i) < rch1 w i ->
                  ProcessingInResult (map (fetch w) (rch2 w i)) (extractReach w i).
    Proof.
      intros w i; remember (lengthInput w i); assert (lengthInput w i <= n) by omega; clear Heqn; revert H. revert i.
      induction n; intros; remember (extractReach w i) as result; rename Heqresult into H3;
      destruct i as [[len pr] rslt]; unfold rch1, rch2, rch3, lengthInput in *; simpl in *; rewrite extractReach_unfold in H3;
      destruct pr; simpl in *. subst; omega. destruct (le_dec len (length rslt)). subst; omega. omega.
      repeat intro; inversion H2. destruct (le_dec len (length rslt)). subst. omega. destruct s as [t Ht]. simpl in *.
      destruct (explode t w Ht).
      assert (ProcessingInResult (map (fetch w) (appRemoveList w pr (removeTree w t (twoSubTrees t w s)) rslt)) result).
      specialize (IHn (len, appRemoveList w pr (removeTree w t (twoSubTrees t w s)) rslt, t :: rslt)). simpl in IHn.
      rewrite H3; apply IHn; clear IHn.
      apply le_trans with (len + len + length pr + length (twoSubTrees t w s) - S (length rslt + S (length rslt))).
      generalize (remove_list_len_le w rslt pr (removeTree w t (twoSubTrees t w s))); intro;
      generalize (remove_tree_len_le w t (twoSubTrees t w s)); intro; omega.
      destruct s as [leftT [rightT [? [? [? ?]]]]]; simpl; omega. repeat intro; destruct (in_dec eq_nat_dec y (t :: rslt)).
      left; auto. right. remember (twoSubTrees t w s) as subT. apply neg_eq_in_neq_nin in n1. destruct n1.
      apply in_inv in H2. destruct H2. rewrite <- H2 in *. clear H2.
      destruct H4 as [? [? ?]]. destruct s as [lT [rT [? [? [? ?]]]]]. simpl in *. unfold biEdge in e.
      destruct (@only_two_neighbours nat nat natEqDec pg bi t) as [v1 [v2 HHH]]. inversion e. rewrite H9 in *.
      rewrite H10 in *. clear H9 H10 v1 v2. rewrite HHH in H7.
      assert (In y (map (fetch w) subT)) by (rewrite HeqsubT; simpl in *; apply H7). apply remove_list_in; auto.
      specialize (H0 x y H2 H4). destruct H0. exfalso; apply H6; auto. apply in_inv in H0. destruct H0. exfalso.
      apply H5; auto. apply remove_list_in_2. auto. rewrite H3 in H1; auto.

      apply PIR_cons. intros. unfold reachable in H4. destruct H4 as [p ?].
      destruct (reachable_by_path_split_dec _ _ _ _ rslt H4). rewrite Forall_forall in f. apply reachable_by_path_foot in H4.
      apply foot_in in H4. specialize (f _ H4). rewrite H3. apply (extractReach_sublist _ _ y). simpl. simpl in f. auto.
      destruct e as [l1 [l2 [e1 [s1 [? [? [? [? [? [? ?]]]]]]]]]]. rewrite Forall_forall in H5.
      destruct (eq_nat_dec e1 t). rewrite e in *; clear e e1. destruct H8 as [? [? ?]]. remember (twoSubTrees t w s) as subT.
      destruct s as [lT [rT [? [? [? ?]]]]]. simpl in *. unfold biEdge in e.
      destruct (@only_two_neighbours nat nat natEqDec pg bi t) as [v1 [v2 HHH]]. inversion e. rewrite H15 in *.
      rewrite H16 in *. clear H15 H16 v1 v2. rewrite HHH in H13. assert (In s1 (map (fetch w) subT)). rewrite HeqsubT.
      simpl map. auto. apply (H2 s1 y). apply neg_eq_in_neq_nin in H9. destruct H9. apply remove_list_in; auto.
      exists l2. auto. apply reachable_by_path_foot in H6. apply foot_in in H6. specialize (H5 e1 H6). apply in_inv in H5.
      destruct H5. exfalso; auto. specialize (H0 e1 s1 H5 H8). simpl in H9. apply neg_eq_in_neq_nin in H9; destruct H9.
      destruct H0. exfalso; auto. apply in_inv in H0. destruct H0. exfalso; auto. apply (H2 s1 y). apply remove_list_in_2.
      auto. exists l2. auto.
      apply PIR_sublist with (map (fetch w) (appRemoveList w pr (removeTree w t (twoSubTrees t w s)) rslt)); auto.
      intro y; intros. apply remove_list_in_2; auto. apply PIR_cons. intros. apply reachable_is_valid in H2.
      apply valid_not_zero in H2. omega. rewrite H3. specialize (IHn (len, pr, rslt)). simpl in IHn. apply IHn. omega.
      repeat intro. specialize (H0 x y H2 H4). destruct H0; [left | right]. auto. apply in_inv in H0. destruct H0.
      subst. destruct H4 as [? [? ?]]. apply valid_not_zero in H3. omega. auto. rewrite H3 in H1. auto.
    Qed.
    
  End ConstructReachable.

  Lemma graph_reachable_finite:
    forall x w, graph x w -> exists (l : list adr), NoDup l /\ forall y, (In y l -> reachable pg x y) /\
                                                                         (~ In y l -> ~ reachable pg x y).
  Proof.
    intros. hnf. destruct (world_finite w) as [l ?].
    generalize (core_unit w); intros. unfold unit_for in H1. apply join_comm in H1.
    assert ((graph x * TT)%pred w) by (exists w, (core w); repeat split; auto).
    remember (exist (graph_sig_fun w) x H2) as g. remember (length l, (g::nil), nil : list adr) as s.
    assert (Forall (reachable pg x) (extractReach w s)). apply extractReach_reachable.
    unfold rch3; rewrite Heqs; simpl; apply Forall_nil. unfold rch2; rewrite Heqs; rewrite Heqg; simpl.
    apply Forall_forall; intros. apply in_inv in H3; destruct H3. subst. assert (graph x0 w) by auto.
    rewrite graph_unfold in H. destruct H as [[? ?] | [dd [ll [rr ?]]]]. hnf in H; right; auto. left.
    apply reachable_by_reflexive. split. destruct_ocon H h. destruct_ocon H6 j. destruct H10 as [[? ?] ?].
    apply H12. hnf; auto. inversion H3. exists (extractReach w s). assert (NoDup (extractReach w s)) as Hn.
    apply extractReach_nodup. rewrite Heqs. simpl. apply NoDup_cons. auto. apply NoDup_nil. split. auto.
    intros y; split; intros. rewrite Forall_forall in H3. apply H3. auto.

    intro. assert (Sublist (extractReach w s) l) as Hs. assert (Forall (NotNone w) (extractReach w s)).
    apply extractReach_all_not_none; rewrite Heqs; simpl; apply Forall_nil. rewrite Forall_forall in H6.
    unfold NotNone in H6. intro z; intros. rewrite H0. apply H6. auto. assert (In y l) as Hy.
    generalize (graph_reachable_in _ _ H5). intros. specialize (H6 w H). hnf in H6. destruct H6 as [b ?].
    destruct_sepcon H6 h. destruct H7 as [? [? ?]]. assert (lookup_fpm w y <> None). apply lookup_fpm_join_sub with h1.
    exists h2; auto. rewrite H10. intro S; inversion S. rewrite <- H0 in H11. auto. apply H4.
    generalize (extractReach_length_bound w s); intro. rewrite Heqs in H6 at 1 2; simpl in H6.
    assert (0 <= length l) as S by omega; specialize (H6 S); clear S. apply le_lt_eq_dec in H6. destruct H6.
    assert (ResultInProcessing (rch3 w s) (map (fetch w) (rch2 w s))). rewrite Heqs; simpl. repeat intro. inversion H6.
    generalize (extractReach_contains_all w s H6 l0); intro. rewrite Heqs in H7 at 1. rewrite Heqg in H7. simpl in H7.
    apply (H7 x y); auto. apply in_eq. rewrite Heqs in e at 2; simpl in e.
    apply (sublist_reverse eq_nat_dec (extractReach w s) l Hn e Hs y Hy).
  Qed.

  Lemma graph_sepcon:
    forall w x, graph x w -> exists (l : list adr),
                               NoDup l /\
                               (forall y, (In y l -> reachable pg x y) /\ (~ In y l -> ~ reachable pg x y)) /\
                               iter_sepcon l graph_maps w.
  Proof.
    intros. destruct (graph_reachable_finite x w H) as [l [? ?]]. exists l. split. auto. split. auto.
    induction l. simpl. rewrite graph_unfold in H. destruct H. destruct H. auto. destruct H as [dd [ll [rr ?]]].
    destruct_ocon H h. destruct_ocon H4 h. destruct H8 as [[? ?] ?]. destruct (H1 x).
    assert (~ In x nil) by apply in_nil. specialize (H13 H14). clear H14. assert (reachable pg x x).
    apply reachable_by_reflexive. split; auto. hnf. auto. exfalso; apply H13. apply H14. simpl.
    admit.
  Qed.


End PointwiseGraph.
