Require Import Coq.Sets.Ensembles.
Require Import Coq.Classes.Morphisms.
Require Import RamifyCoq.Coqlib.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_ind.
Require RamifyCoq.graph.marked_graph.
Import RamifyCoq.graph.marked_graph.WeakMarkGraph.

Module SIMPLE_SPANNING_TREE.

  Section SIMPLE_SPANNING.

    Context {V E: Type}.
    Context {EV: EqDec V eq}.
    Context {EE: EqDec E eq}.

    Notation Graph := (PreGraph V E).

    Definition is_tree (g : Graph) (x : V) : Prop :=
      forall y, reachable g x y -> exists !(p : path), g |= p is x ~o~> y satisfying (fun _ => True).

    Instance is_tree_proper : Proper (structurally_identical ==> eq ==> iff) is_tree.
    Proof.
      cut (forall g1 g2 x y, g1 ~=~ g2 -> x = y -> is_tree g1 x -> is_tree g2 y); intros.
      + constructor; intros; [apply (H x y x0) | apply (H y x y0)]; auto. symmetry; auto.
      + subst. hnf. intro v; intros. rewrite <- H in H0. specialize (H1 v H0).
        destruct H1 as [p [? ?]]. exists p.
        pose proof (reachable_by_path_si g1 g2 p y v (fun _ : V => True) H); split.
        - rewrite <- (reachable_by_path_si g1 g2); auto.
        - intros. apply H2. rewrite (reachable_by_path_si g1 g2); auto.
    Qed.

    Definition spanning_tree (g1 : Graph) (root : V) (P: V -> Prop) (g2: Graph) := 
      (predicate_partialgraph g1 (fun n => ~ g1 |= root ~o~> n satisfying P)) ~=~
      (predicate_partialgraph g2 (fun n => ~ g1 |= root ~o~> n satisfying P)) /\
      (P root -> is_tree (predicate_partialgraph g2 (reachable_by g1 root P)) root) /\
      (forall n, g1 |= root ~o~> n satisfying P -> reachable g2 root n) /\
      (forall a b, g1 |= root ~o~> a satisfying P -> ~ g1 |= root ~o~> b satisfying P -> ~ reachable g2 a b).

    Definition edge_spanning_tree (g1 : Graph) (e : E) (P: V -> Prop) (g2 : Graph) : Prop :=
      (P (dst g1 e) /\ spanning_tree g1 (dst g1 e) P g2) \/ (~ P (dst g1 e) /\ gremove_edge g1 e g2).

    Lemma gremove_edge_is_partial_graph: forall (g1 : Graph) (e : E) (g2 : Graph),
        evalid g1 e -> gremove_edge g1 e g2 -> is_partial_graph g2 g1.
    Proof.
      intros. destruct H0 as [? [? [? [? ?]]]]. split; [|split; [|split]]; intros.
      + rewrite H0; auto.
      + destruct_eq_dec e0 e.
        - subst. auto.
        - specialize (H1 _ H6). intuition.
      + destruct_eq_dec e0 e.
        - subst. destruct H4.
          * exfalso; auto.
          * intuition.
        - specialize (H1 _ H7). assert (evalid g1 e0) by intuition. symmetry. apply H2; auto.
      + destruct_eq_dec e0 e.
        - subst. exfalso. destruct H4 as [? | [? _]]; auto.
        - specialize (H1 _ H7). assert (evalid g1 e0) by intuition. symmetry. apply H3; auto.
    Qed.

    Lemma spanning_tree_is_pratial_graph: forall (g1 : Graph) (root : V) (P: V -> Prop) (g2: Graph),
        spanning_tree g1 root P g2 -> is_partial_graph g2 g1.
    Proof.
      intros. destruct H as [? [? [? ?]]].
    Abort.

    Lemma edge_spanning_tree_invalid: forall (g: Graph) e (P: NodePred V),
        evalid g e -> ~ vvalid g (dst g e) -> edge_spanning_tree g e P g.
    Proof.
      intros. hnf. destruct (node_pred_dec P (dst g e)); [left | right]; split; auto.
      + remember (dst g e) as v. split; [|split; [|split]].
        - reflexivity.
        - repeat intro. apply reachable_head_valid in H2. destruct H2. exfalso; auto.
        - intros. apply reachable_by_head_valid in H1. exfalso; auto.
        - intros. apply reachable_by_head_valid in H1. exfalso; auto.
      + split; [|split; [|split; [|split]]]; intros; [tauto | tauto | tauto |tauto |].
        right; auto.
    Qed.

    Lemma spanning_tree_vvalid: forall (g1 : Graph) (root : V) (P: V -> Prop) (g2 : Graph) x,
        ReachDecidable g1 root P -> spanning_tree g1 root P g2 -> (vvalid g1 x <-> vvalid g2 x).
    Proof.
      intros. destruct H as [? [? [? ?]]]. destruct (X x).
      + split; intros.
        - specialize (H1 _ r). apply reachable_foot_valid in H1. auto.
        - apply reachable_by_foot_valid in r. auto.
      + destruct H as [? _]. simpl in H. unfold predicate_vvalid in H.
        specialize (H x). split; intros.
        - assert (vvalid g1 x /\ ~ g1 |= root ~o~> x satisfying P) by (split; auto).
          rewrite H in H4. tauto.
        - assert (vvalid g2 x /\ ~ g1 |= root ~o~> x satisfying P) by (split; auto).
          rewrite <- H in H4. tauto.
    Qed.

    Lemma edge_spanning_tree_vvalid: forall (g1: Graph) e (P: V -> Prop) (g2: Graph) x,
        ReachDecidable g1 (dst g1 e) P -> edge_spanning_tree g1 e P g2 -> (vvalid g1 x <-> vvalid g2 x).
    Proof.
      intros. destruct H as [[_ ?]|[_ [? _]]].
      + apply (spanning_tree_vvalid g1 (dst g1 e) P g2); auto.
      + apply H.
    Qed.

    Lemma edge_spanning_tree_reachable_vvalid: forall (g1 g2: Graph) e (P: V -> Prop),
        ReachDecidable g1 (dst g1 e) P -> edge_spanning_tree g1 e P g2 -> Included (reachable g1 (src g1 e)) (vvalid g2).
    Proof.
      intros. intro y; unfold Ensembles.In; intros. apply reachable_foot_valid in H0.
      rewrite <- edge_spanning_tree_vvalid; eauto.
    Qed.

    Lemma spanning_tree_not_reachable: forall (g1 : Graph) (root : V) (P: V -> Prop) (g2 : Graph) x y,
        spanning_tree g1 root P g2 -> (~ g1 |= root ~o~> y satisfying P) -> reachable g2 x y ->
        g2 |= x ~o~> y satisfying (Complement _ (reachable_by g1 root P)).
    Proof.
      intros. destruct H as [? [? [? ?]]]. destruct H1 as [p ?]. exists p. split; [|split].
      + destruct H1; auto.
      + destruct H1 as [_ [? _]]; auto.
      + rewrite Forall_forall. intro v. intros. unfold Complement. unfold Ensembles.In.
        destruct (reachable_by_path_split_in _ _ _ _ _ _ H1 H5) as [p1 [p2 [? [? ?]]]].
        apply reachable_by_path_is_reachable in H8. intro.
        specialize (H4 _ _ H9 H0). auto.
    Qed.

    Lemma spanning_tree_equiv: forall (P1 P2: V -> Prop) (g1: Graph) (v: V) (g2: Graph),
        (forall x, P1 x <-> P2 x) -> (spanning_tree g1 v P1 g2 <-> spanning_tree g1 v P2 g2).
    Proof.
      cut (forall P1 P2 g1 v g2, (forall x, P1 x <-> P2 x) -> spanning_tree g1 v P1 g2 -> spanning_tree g1 v P2 g2); intros.
      + split; intros; [apply (H P1 P2) | apply (H P2 P1)]; firstorder.
      + destruct H0 as [? [? [? ?]]]. split; [|split; [|split]]; intros.
        - apply (si_stronger_partialgraph _ _ (fun n : V => ~ g1 |= v ~o~> n satisfying P1)
                                          (fun n : V => ~ g1 |= v ~o~> n satisfying P1) _ _ (fun _ => True)); auto;
          intros; pose proof (reachable_by_eq g1 v v0 P1 P2 H); rewrite H4; intuition.
        - rewrite <- H in H4. specialize (H1 H4).
          assert
            ((predicate_partialgraph g2 (reachable_by g1 v P1)) ~=~ (predicate_partialgraph g2 (reachable_by g1 v P2))). {
            apply partialgraph_proper. reflexivity. hnf.
            intros. apply reachable_by_eq. intuition.
          } apply (is_tree_proper _ _ H5 v v); auto.
        - apply H2. rewrite (reachable_by_eq _ _ _ P1 P2); auto.
        - apply H3; rewrite (reachable_by_eq _ _ _ P1 P2); auto.
    Qed.

    Lemma si_spanning_tree: forall (g1 g2 g3: Graph) (v: V) (P: V -> Prop),
        g1 ~=~ g2 -> (spanning_tree g1 v P g3 <-> spanning_tree g2 v P g3).
    Proof.
      cut (forall g1 g2 g3 v P, g1 ~=~ g2 -> spanning_tree g1 v P g3 -> spanning_tree g2 v P g3); intros.
      + split; intros; [apply H with g1 | apply H with g2]; auto. symmetry; auto.
      + destruct H0 as [? [? [? ?]]]. split; [|split; [|split]]; intros.
        - rewrite <- H. clear -H0 H. destruct H0 as [? [? [? ?]]]. hnf. simpl in *.
          unfold predicate_vvalid in *. unfold predicate_weak_evalid in *. split; [|split;[|split]]; intros; rewrite <- H in *.
          * specialize (H0 v0). intuition.
          * specialize (H1 e). intuition.
          * apply H2; auto.
          * apply H3; auto.
        - rewrite <- H. apply H1. auto.
        - apply H2. rewrite H. auto.
        - apply H3; rewrite H; auto.
    Qed.

    Lemma si_spanning_tree': forall (g1 g2 g3: Graph) (v: V) (P: V -> Prop),
        g2 ~=~ g3 -> (spanning_tree g1 v P g2 <-> spanning_tree g1 v P g3).
    Proof.
      cut (forall g1 g2 g3 v P, g2 ~=~ g3 -> spanning_tree g1 v P g2 -> spanning_tree g1 v P g3); intros.
      + split; intros; [apply H with g2 | apply H with g3]; auto. symmetry; auto.
      + destruct H0 as [? [? [? ?]]]. split; [|split; [|split]]; intros.
        - rewrite <- H. auto.
        - specialize (H1 H4). rewrite <- H. auto.
        - rewrite <- H. apply H2; auto.
        - rewrite <- H. apply H3; auto.
    Qed.

    Lemma si_edge_spanning_tree': forall (g1 g2 g3: Graph) (e: E) (P: V -> Prop),
        g2 ~=~ g3 -> (edge_spanning_tree g1 e P g2 <-> edge_spanning_tree g1 e P g3).
    Proof.
      cut (forall g1 g2 g3 e P, g2 ~=~ g3 -> edge_spanning_tree g1 e P g2 -> edge_spanning_tree g1 e P g3); intros.
      + split; intros; [apply H with g2 | apply H with g3]; auto. symmetry; auto.
      + destruct H0 as [[? ?] | [? ?]]; [left | right]; split; auto.
        - rewrite <- (si_spanning_tree' _ _ _ _ _ H); auto.
        - destruct H as [? [? [? ?]]]. destruct H1 as [? [? [? [? ?]]]].
          split; [|split; [|split; [|split]]]; intros.
          * specialize (H v). specialize (H1 v). intuition.
          * specialize (H2 e0). specialize (H5 _ H9). intuition.
          * specialize (H2 e0). assert (evalid g2 e0) by intuition.
            specialize (H3 _ H12 H11). specialize (H6 _ H9 H10 H12). rewrite <- H3. rewrite H6. auto.
          * specialize (H2 e0). assert (evalid g2 e0) by intuition.
            specialize (H4 _ H12 H11). specialize (H7 _ H9 H10 H12). rewrite <- H4. rewrite H7. auto.
          * destruct H8 as [? | [? [? ?]]]; [left | right]. rewrite <- H2. auto.
            specialize (H2 e). assert (evalid g3 e) by intuition.
            specialize (H4 _ H10 H11). specialize (H3 _ H10 H11).
            rewrite <- H4. rewrite <- H3. rewrite H9. rewrite <- H. auto.
    Qed.

    Lemma edge_spanning_tree_equiv: forall (P1 P2: V -> Prop) (g1: Graph) (e: E) (g2: Graph),
        (forall x, P1 x <-> P2 x) -> (edge_spanning_tree g1 e P1 g2 <-> edge_spanning_tree g1 e P2 g2).
    Proof.
      cut (forall (P1 P2: V -> Prop) g1 e g2,
              (forall x, P1 x <-> P2 x) -> edge_spanning_tree g1 e P1 g2 -> edge_spanning_tree g1 e P2 g2); intros.
      + split; intros; [apply (H P1 P2) | apply (H P2 P1)]; firstorder.
      + destruct H0; [left | right]; destruct H0.
        - split. apply H; auto. rewrite <- (spanning_tree_equiv P1 P2); auto.
        - split; auto. intro. apply H0. rewrite H; auto.
    Qed.

    Lemma gremove_predicate_partial_si: forall (g1 g2: Graph) (e: E) (root: V) (P: V -> Prop),
        out_edges g1 root e -> vvalid g1 root -> P root -> gremove_edge g1 e g2 ->
        (predicate_partialgraph g1 (fun n : V => ~ g1 |= root ~o~> n satisfying P)) ~=~
        (predicate_partialgraph g2 (fun n : V => ~ g1 |= root ~o~> n satisfying P)).
    Proof.
      intros. destruct H2 as [? [? [? [? ?]]]]. 
      assert (g1 |= root ~o~> src g1 e satisfying P). {
        destruct H. rewrite H7.
        apply reachable_by_reflexive; auto.
      }
      hnf. simpl. unfold predicate_vvalid. unfold predicate_weak_evalid.
      split; [|split; [|split]]; intros.
      - specialize (H2 v). intuition.
      - destruct_eq_dec e0 e.
        * subst. split; intro. destruct H8; exfalso; auto.
          destruct H6. destruct H8. exfalso; auto.
          destruct H6 as [? [? ?]]. rewrite H9. destruct H. destruct H8. intuition.
        * specialize (H3 _ H8). specialize (H4 _ H8).
          rewrite H3. split; intros; destruct H9; split; auto; assert (evalid g1 e0) by intuition; specialize (H4 H11 H9).
          rewrite <- H4; auto. rewrite H4. intuition.
      - intros. destruct H8. destruct H9. apply H4; auto. intro. subst. auto.
      - intros. destruct H8. destruct H9. apply H5; auto. intro. subst. auto.
    Qed.

    Lemma gremove_root_not_reachable_equiv: forall (g1 g2: Graph) (e: E) (root: V) (P: V -> Prop),
        out_edges g1 root e -> vvalid g1 root -> P root -> gremove_edge g1 e g2 ->
        (~ (P (dst g1 e) /\ dst g1 e <> root)) -> forall n,
            (~ g1 |= root ~o~> n satisfying P <-> ~ g2 |= root ~o~> n satisfying P).
    Proof.
      intros. split; intros; intro; apply H4; clear H4; destruct H; destruct H2 as [? [? [? [? ?]]]].
      + destruct H5 as [p [? [? ?]]]. exists p. split; [|split]; auto.
        clear H5 H11. induction p; simpl; auto. simpl in H10. destruct p.
        - rewrite H2; auto.
        - destruct H10. split. 2: apply IHp; auto.
          destruct H5 as [? [? ?]]. split; [|split]; [rewrite H2 ..|]; auto.
          rewrite step_spec in H12 |-* . destruct H12 as [e' [? [? ?]]].
          exists e'. destruct_eq_dec e' e.
          * subst. exfalso. destruct H9. auto. destruct H4. auto.
          * specialize (H6 _ H15). specialize (H7 _ H15). specialize (H8 _ H15). subst a. subst v. intuition.
      + rewrite reachable_acyclic in H5. destruct H5 as [p [? ?]]. exists p.
        destruct H10 as [? [? ?]]. split; [|split]; auto. destruct p. simpl; auto.
        destruct H10. simpl in H10. inversion H10. subst v. clear H10 H13.
        pose proof (NoDup_cons_2 _ _ _ H5). simpl in H11 |-* . destruct p. rewrite <- H2; auto.
        destruct H11. split.
        - destruct H11 as [? [? ?]]. split; [|split]; [rewrite <- H2 ..|]; auto.
          rewrite step_spec in H15 |-* . destruct H15 as [e' [? [? ?]]]. exists e'. destruct_eq_dec e' e.
          * exfalso. subst e'. apply H3. split.
            Focus 1. {
              unfold path_prop in H12. rewrite Forall_forall in H12.
              assert (P v). apply H12. apply in_cons. apply in_eq. subst. auto.
            } Unfocus.
            Focus 1. {
              rewrite H17 in *. clear H17. intro. apply H10.
              subst v. apply in_eq.
            } Unfocus.
          * specialize (H6 _ H18). assert (evalid g2 e') by intuition.
            specialize (H7 _ H18 H15 H19). specialize (H8 _ H18 H15 H19).
            rewrite <- H7, <- H8. intuition.
        - clear H5 H11. assert (path_prop P (v :: p)). {
            apply path_prop_sublist with (root :: v :: p); auto.
            apply Sublist_cons; auto.
          } clear H12.
          revert v H13 H10 H5. induction p; intros.
          1: simpl in *. rewrite <- H2; auto.
          simpl in H13 |-* . destruct H13. split.
          * clear H12. destruct H11 as [? [? ?]]. split; [|split]; [rewrite <- H2 ..|]; auto.
            rewrite step_spec in H13 |-* . destruct H13 as [e' [? [? ?]]]. exists e'. destruct_eq_dec e' e.
            Focus 1. {
              exfalso. subst e'. apply H3. split.
              + unfold path_prop in H5. rewrite Forall_forall in H5.
                assert (P a). apply H5. apply in_cons, in_eq. subst; auto.
              + rewrite H15. intro. apply H10. rewrite H16. apply in_cons, in_eq.
            } Unfocus.
            Focus 1. {
              specialize (H6 _ H16). assert (evalid g2 e') by intuition.
              specialize (H7 _ H16 H13 H17). specialize (H8 _ H16 H13 H17).
              rewrite <- H7, <- H8. intuition.
            } Unfocus.
          * apply IHp.
            1: apply H12.
            1: intro; apply H10; apply in_cons; auto.
            1: apply path_prop_sublist with (v :: a :: p); auto; apply Sublist_cons; auto.
    Qed.

    Inductive spanning_list' : (V -> Prop) -> Graph -> list E -> Graph -> Prop :=
    | spanning_list_nil': forall P g1 g2, g1 ~=~ g2 -> spanning_list' P g1 nil g2
    | spanning_list_cons':
        forall P g1 g2 g3 e es,
          spanning_list' P g1 es g2 ->
          edge_spanning_tree g2 e (fun x => P x /\ ~ reachable_by_through_set g1 (map (dst g1) es) P x) g3 ->
          spanning_list' P g1 (es +:: e) g3.

    Lemma spanning_list_trans': forall P g1 g2 g3 l1 l2,
        Forall (evalid g1) (l1 ++ l2) ->
        spanning_list' P g1 l1 g2 ->
        spanning_list' (fun x => P x /\ ~ reachable_by_through_set g1 (map (dst g1) l1) P x) g2 l2 g3 ->
        spanning_list' P g1 (l1 ++ l2) g3.
    Proof.
      intros. remember (fun x : V => P x /\ ~ reachable_by_through_set g1 (map (dst g1) l1) P x) as P0. induction H1.
      + rewrite app_nil_r. induction H0.
        - apply spanning_list_nil'. rewrite H0. auto.
        - apply spanning_list_cons' with g0; auto. rewrite <- si_edge_spanning_tree'. apply H2. apply H1.
      + assert (Forall (evalid g1) (l1 ++ es)). {
          rewrite Forall_forall in H |-* . intros.
          apply H. rewrite app_assoc. apply in_or_app. left; auto.
        }
        specialize (IHspanning_list' H3 H0 HeqP0). rewrite app_assoc.
        apply spanning_list_cons' with g2; auto.
        rewrite (edge_spanning_tree_equiv _ (fun x : V =>
                                               P0 x /\ ~ reachable_by_through_set g0 (map (dst g0) es) P0 x)); auto.
        intros. subst P0. split; intros.
        - destruct H4. split; [split|]; auto.
          * intro. apply H5. destruct H6 as [s [? ?]]. exists s. split; auto.
            rewrite Coqlib.list_append_map. apply in_or_app. left; auto.
          * clear H1 H2 IHspanning_list' H. induction H0.
            Focus 1. {
              rewrite app_nil_l in *. simpl. intro. apply H5. clear H5.
              assert (map (dst g0) es = map (dst g1) es). {
                clear H0.
                induction es; simpl; auto. f_equal.
                + destruct H as [? [? [? ?]]].
                  rewrite Forall_forall in H3. assert (evalid g1 a) by (apply H3, in_eq).
                  assert (evalid g0 a) by (rewrite <- H0; auto).
                  symmetry. apply H2; auto.
                + apply IHes. rewrite Forall_forall in H3 |-* . intros.
                  apply H3. apply in_cons; auto.
              } rewrite H1 in H0.
              rewrite (si_reachable_by_through_set g1 g0 _ _
                                                   (fun x0 : V => P x0 /\ ~ reachable_by_through_set g1 nil P x0)); auto.
              hnf. intros. simpl. rewrite reachable_by_through_nil. intuition.
            } Unfocus.
            Focus 1. {
              assert (Forall (evalid g1) (es0 ++ es)). {
                rewrite Forall_forall in H3 |-* . intros.
                apply H3. apply in_app_or in H1. apply in_or_app.
                destruct H1; [left | right]; auto. apply in_or_app. left; auto.
              } specialize (IHspanning_list' H1 H4).
              assert (~ reachable_by_through_set g1 (map (dst g1) (es0 ++ es)) P x). {
                intro. apply H5. destruct H2 as [s [? ?]]. exists s. split; auto.
                rewrite Coqlib.list_append_map in H2 |-* . apply in_app_or in H2.
                apply in_or_app. destruct H2; [left | right]; auto.
                rewrite Coqlib.list_append_map. apply in_or_app. left; auto.
              } specialize (IHspanning_list' H2).
    Abort.
    
    Inductive spanning_list : (V -> Prop) -> Graph -> list E -> Graph -> Prop :=
    | spanning_list_nil: forall P g1 g2, g1 ~=~ g2 -> spanning_list P g1 nil g2
    | spanning_list_cons:
        forall P g1 g2 g3 e es, edge_spanning_tree g1 e P g2 ->
                                spanning_list (fun x => P x /\ ~ g1 |= (dst g1 e) ~o~> x satisfying P) g2 es g3 ->
                                spanning_list P g1 (e :: es) g3.

    Lemma spanning_list_eq: forall P g1 g2 es, Forall (evalid g1) es -> (spanning_list P g1 es g2 <-> spanning_list' P g1 es g2).
    Proof.
      intros. split; intros; induction H0.
      + apply spanning_list_nil'; auto.
      + pose proof (app_cons_assoc nil es e).
        do 2 rewrite app_nil_l in H2. rewrite H2.
    Abort.

    Lemma spanning_list_derive: forall (P1 P2: V -> Prop) (g1 g2 : Graph) e,
        (forall x, P1 x <-> P2 x) -> spanning_list P1 g1 e g2 -> spanning_list P2 g1 e g2.
    Proof.
      intros. revert P1 P2 g1 H H0. induction e; intros.
      + constructor. inversion H0. auto.
      + inversion H0. subst. apply spanning_list_cons with g3.
        - rewrite <- (edge_spanning_tree_equiv P1 P2); auto.
        - apply (IHe (fun x : V => P1 x /\ ~ g1 |= dst g1 a ~o~> x satisfying P1)
                     (fun x : V => P2 x /\ ~ g1 |= dst g1 a ~o~> x satisfying P2)); auto.
          intros; split; intros; destruct H1; split.
          * rewrite <- H; auto.
          * rewrite <- (reachable_by_eq _ _ _ P1 P2); auto.
          * rewrite H; auto.
          * rewrite (reachable_by_eq _ _ _ P1 P2); auto.
    Qed.

    Lemma spanning_list_spanning_tree: forall (P: V -> Prop) g1 root g2 l,
        NoDup l -> (forall e, In e l <-> out_edges g1 root e) ->
        vvalid g1 root -> P root ->
        spanning_list' (fun x => P x /\ x <> root) g1 l g2 ->
        spanning_tree g1 root P g2.
    Proof.
      intros. remember (fun x : V => P x /\ x <> root) as P0. split; [|split]; intros.
      + assert (forall e : E, In e l -> out_edges g1 root e) by (intros; rewrite <- H0; auto).
        clear H0. induction H3.
        - rewrite H0. reflexivity.
        - assert (out_edges g1 root e) by (apply H4; apply in_or_app; right; apply in_eq).
          pose proof (NoDup_app_l _ _ _ H).
          assert (forall e0 : E, In e0 es -> out_edges g1 root e0) by (intros; apply H4; apply in_or_app; left; auto).
          specialize (IHspanning_list' H6 H1 HeqP0 H7). rewrite IHspanning_list'. clear IHspanning_list'.
          destruct H0 as [[[? ?] [? _]] | [? ?]].
          * apply si_stronger_partialgraph_simple with
            (fun n : V => ~ g2 |= dst g2 e ~o~> n satisfying
                            (fun x : V => P0 x /\ ~ reachable_by_through_set g1 (map (dst g1) es) P0 x)); auto.
            intro n. unfold Ensembles.In . do 2 intro. apply H10. clear H10. clear H9. subst P0. destruct H0.
            admit.
          * assert (out_edges g2 root e) by admit.
            assert (vvalid g2 root) by admit.
            pose proof (gremove_predicate_partial_si _ _ _ _ _ H9 H10 H2 H8).
            apply si_stronger_partialgraph_simple with (fun n : V => ~ g2 |= root ~o~> n satisfying P); auto.
            intro n. unfold Ensembles.In . do 2 intro. apply H12. clear H12.
            admit.
      + induction H3.
        - admit.
        - destruct H5 as [[[? ?] [? [? [? ?]]]] | ?].
          * assert (P0 (dst g2 e) /\ ~ reachable_by_through_set g1 (map (dst g1) es) P0 (dst g2 e)) by intuition.
            specialize (H8 H11). clear H7 H9 H10 H11.
    Abort.

  End SIMPLE_SPANNING.
End SIMPLE_SPANNING_TREE.
    
(* Module SPANNING_TREE.     *)

Section SPANNING.

  Context {V E: Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.
  Context {DV DE: Type}.
  Context {MGS: MarkGraphSetting DV}.
  Context {P: PreGraph V E -> (V -> DV) -> (E -> DE) -> Type}.
  Notation Graph := (GeneralGraph V E DV DE P).

  Definition is_tree (g : PreGraph V E) (x : V) : Prop := SIMPLE_SPANNING_TREE.is_tree g x.
  
  Definition marked_reachable (g1 : Graph) (x : V) (g2 : Graph) : Prop :=
    (forall y, g1 |= x ~o~> y satisfying (unmarked g1) -> marked g2 y) /\
    forall y, ~ g1 |= x ~o~> y satisfying (unmarked g1) -> (marked g1 y <-> marked g2 y).

  Definition spanning_tree (g1 : Graph) (root : V) (g2 : Graph) : Prop :=
    marked_reachable g1 root g2 /\
    (predicate_partialgraph g1 (fun n => ~ g1 |= root ~o~> n satisfying (unmarked g1))) ~=~
    (predicate_partialgraph g2 (fun n => ~ g1 |= root ~o~> n satisfying (unmarked g1))) /\
    (unmarked g1 root -> is_tree (predicate_partialgraph g2 (reachable_by g1 root (unmarked g1))) root /\
                         forall n, g1 |= root ~o~> n satisfying (unmarked g1) -> reachable g2 root n) /\
    (forall a b, g1 |= root ~o~> a satisfying (unmarked g1) ->
                 ~ g1 |= root ~o~> b satisfying (unmarked g1) -> ~ reachable g2 a b).

  Definition edge_spanning_tree (g1 : Graph) (e : E) (g2 : Graph) : Prop :=
    if node_pred_dec (marked g1) (dst g1 e)
    then gremove_edge g1 e g2 /\ forall v, marked g1 v <-> marked g2 v
    else spanning_tree g1 (dst g1 e) g2.

  Lemma spanning_tree_inj: forall g1 root g2, spanning_tree g1 root g2 <->
                                              (marked_reachable g1 root g2 /\
                                               SIMPLE_SPANNING_TREE.spanning_tree g1 root (unmarked g1) g2).
  Proof.
    intros. split; intro; destruct H; split; auto.
    + destruct H0 as [? [? ?]]. split; auto. destruct (node_pred_dec (marked g1) root).
      - split; intros; [|split; intros].
        * unfold unmarked in H3. rewrite negateP_spec in H3; exfalso; auto.
        * apply reachable_by_head_prop in H3; unfold unmarked in H3; rewrite negateP_spec in H3; exfalso; auto.
        * apply H2; auto.
      - unfold unmarked in H1 at 1. rewrite negateP_spec in H1. specialize (H1 n).
        destruct H1; split; intros; auto.
    + destruct H0 as [? [? [? ?]]]. unfold is_tree. split; auto. 
  Qed.

  Lemma edge_spanning_tree_inj: forall g1 root g2, edge_spanning_tree g1 root g2 <->
                                                   (marked_reachable g1 (dst g1 root) g2 /\
                                                    SIMPLE_SPANNING_TREE.edge_spanning_tree g1 root (unmarked g1) g2).
  Proof.
    intros. split; intro.
    + hnf in H. destruct (node_pred_dec (marked g1) (dst g1 root)).
      - destruct H. split; [split | right]; intros; auto.
        apply reachable_by_head_prop in H1. unfold unmarked in H1.
        rewrite negateP_spec in H1. exfalso; auto.
      - rewrite spanning_tree_inj in H. destruct H. split; auto. left. auto.
    + destruct H. hnf. destruct (node_pred_dec (marked g1) (dst g1 root)); destruct H0 as [[? ?] | [? ?]].
      - unfold unmarked in H0. rewrite negateP_spec in H0. exfalso; auto.
      - split; auto. intros. destruct H. apply H2. intro; apply H0.
        apply reachable_by_head_prop in H3. auto.
      - rewrite spanning_tree_inj. auto.
      - exfalso; auto.
  Qed.
    
  Lemma edge_spanning_tree_invalid: forall (g: Graph) e,
      evalid g e -> ~ vvalid g (dst g e) -> edge_spanning_tree g e g.
  Proof.
    intros. rewrite edge_spanning_tree_inj. split.
    + split; intros. 2: tauto. apply reachable_by_head_valid in H1. exfalso; auto.
    + apply SIMPLE_SPANNING_TREE.edge_spanning_tree_invalid; auto.
  Qed.

  Lemma spanning_tree_vvalid: forall (g1 : Graph) (root : V) (g2 : Graph) x,
      ReachDecidable g1 root (unmarked g1) -> spanning_tree g1 root g2 -> (vvalid g1 x <-> vvalid g2 x).
  Proof.
    intros. rewrite spanning_tree_inj in H. destruct H.
    apply (SIMPLE_SPANNING_TREE.spanning_tree_vvalid _ root (unmarked g1)); auto.
  Qed.

  Lemma edge_spanning_tree_vvalid: forall (g1 g2: Graph) e x,
      ReachDecidable g1 (dst g1 e) (unmarked g1) -> edge_spanning_tree g1 e g2 -> (vvalid g1 x <-> vvalid g2 x).
  Proof.
    intros. rewrite edge_spanning_tree_inj in H. destruct H.
    apply (SIMPLE_SPANNING_TREE.edge_spanning_tree_vvalid _ e (unmarked g1)); auto.
  Qed.
  
  Lemma edge_spanning_tree_reachable_vvalid: forall (g1 g2: Graph) e,
      ReachDecidable g1 (dst g1 e) (unmarked g1) -> edge_spanning_tree g1 e g2 ->
      Included (reachable g1 (src g1 e)) (vvalid g2).
  Proof.
    intros. rewrite edge_spanning_tree_inj in H. destruct H.
    apply SIMPLE_SPANNING_TREE.edge_spanning_tree_reachable_vvalid with (unmarked g1); auto.
  Qed.

  Lemma spanning_tree_not_reachable: forall (g1 : Graph) (root : V) (g2 : Graph) x y,
      spanning_tree g1 root g2 -> (~ g1 |= root ~o~> y satisfying (unmarked g1)) -> reachable g2 x y ->
      g2 |= x ~o~> y satisfying (Complement _ (reachable_by g1 root (unmarked g1))).
  Proof.
    intros. rewrite spanning_tree_inj in H. destruct H.
    apply SIMPLE_SPANNING_TREE.spanning_tree_not_reachable; auto.
  Qed.

  Lemma spanning_tree_unmarked_equiv: forall (g1 g2: Graph) (root: V),
      ReachDecidable g1 root (unmarked g1) ->
      spanning_tree g1 root g2 ->
      forall x, (unmarked g1 x /\ ~ g1 |= root ~o~> x satisfying (unmarked g1)) <-> unmarked g2 x.
  Proof.
    intros. split; intros.
    + destruct H as [[? ?] _]. destruct H0. intro. apply H0.
      rewrite (H1 x). auto. intro. apply H2. auto.
    + destruct H as [[? ?] _]. destruct (X x).
      - specialize (H _ r). exfalso; auto.
      - specialize (H1 _ n). split; auto. intro. apply H0. rewrite <- H1. auto.
  Qed.

  Lemma edge_spanning_tree_unmarked_equiv: forall (g1 g2: Graph) (e: E),
      ReachDecidable g1 (dst g1 e) (unmarked g1) ->
      edge_spanning_tree g1 e g2 ->
      forall x, (unmarked g1 x /\ ~ g1 |= (dst g1 e) ~o~> x satisfying (unmarked g1)) <-> unmarked g2 x.
  Proof.
    intros. hnf in H. destruct (node_pred_dec (marked g1) (dst g1 e)).
    + destruct H. split; intros.
      - destruct H1. intro. apply H1. rewrite (H0 x). auto.
      - split.
        * intro. apply H1. rewrite <- (H0 x). auto.
        * intro. apply reachable_by_head_prop in H2. auto.
    + apply spanning_tree_unmarked_equiv; auto.
  Qed.

  Inductive spanning_list : Graph -> list E -> Graph -> Prop :=
  | spanning_list_nil: forall (g1 g2 : Graph), g1 ~=~ g2%GeneralGraph -> spanning_list g1 nil g2
  | spanning_list_cons:
      forall g1 g2 g3 e rest, edge_spanning_tree g1 e g2 -> spanning_list g2 rest g3 -> spanning_list g1 (e :: rest) g3.

  Lemma spanning_list_inj: forall (g1 g2 : Graph) (es : list E),
      spanning_list g1 es g2 -> mark_list g1 (map (dst g1) es) g2 /\ SIMPLE_SPANNING_TREE.spanning_list (unmarked g1) g1 es g2.
  Proof.
    intros. induction H; split; simpl.
    + constructor; auto.
    + constructor; destruct H; auto.
    + destruct IHspanning_list. apply mark_list_cons with g2; admit.
    + destruct IHspanning_list. apply SIMPLE_SPANNING_TREE.spanning_list_cons with g2.
      - rewrite edge_spanning_tree_inj in H. destruct H. auto.
      - apply (SIMPLE_SPANNING_TREE.spanning_list_derive (unmarked g2)); auto.
        intro. symmetry. apply edge_spanning_tree_unmarked_equiv; auto.
  Abort.

  
End SPANNING.
