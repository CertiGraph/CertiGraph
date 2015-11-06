Require Import Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_ind.
Require Import Coq.Logic.Classical.
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

    Lemma not_reachable_ST_vvalid: forall (g1 : Graph) (root : V) (P: V -> Prop) (g2 : Graph) x,
        ~ g1 |= root ~o~> x satisfying P -> spanning_tree g1 root P g2 -> (vvalid g1 x <-> vvalid g2 x).
    Proof.
      intros. destruct H0 as [[? _] _]. simpl in H0. unfold predicate_vvalid in H0.
      specialize (H0 x). split; intros.
      + assert (vvalid g1 x /\ ~ g1 |= root ~o~> x satisfying P) by (split; auto).
        rewrite H0 in H2. tauto.
      + assert (vvalid g2 x /\ ~ g1 |= root ~o~> x satisfying P) by (split; auto).
        rewrite <- H0 in H2. tauto.
    Qed.

    Lemma spanning_tree_vvalid: forall (g1 : Graph) (root : V) (P: V -> Prop) (g2 : Graph) x,
        ReachDecidable g1 root P -> spanning_tree g1 root P g2 -> (vvalid g1 x <-> vvalid g2 x).
    Proof.
      intros. destruct (X x).
      + destruct H as [? [? [? ?]]]. split; intros.
        - specialize (H1 _ r). apply reachable_foot_valid in H1. auto.
        - apply reachable_by_foot_valid in r. auto.
      + eapply not_reachable_ST_vvalid; eauto.
    Qed.

    Lemma spanning_tree_root_vvalid: forall (g1 : Graph) (root : V) (P: V -> Prop) (g2 : Graph),
        spanning_tree g1 root P g2 -> P root -> vvalid g1 root -> vvalid g2 root.
    Proof.
      intros. destruct H as [_ [_ [? _]]]. 
      assert (g1 |= root ~o~> root satisfying P) by (apply reachable_by_reflexive; auto).
      specialize (H _ H2). apply reachable_head_valid in H. auto.
    Qed.

    Lemma edge_spanning_tree_vvalid: forall (g1: Graph) e (P: V -> Prop) (g2: Graph) x,
        ReachDecidable g1 (dst g1 e) P -> edge_spanning_tree g1 e P g2 -> (vvalid g1 x <-> vvalid g2 x).
    Proof.
      intros. destruct H as [[_ ?]|[_ [? _]]].
      + apply (spanning_tree_vvalid g1 (dst g1 e) P g2); auto.
      + apply H.
    Qed.

    Lemma not_reachable_EST_vvalid: forall (g1: Graph) e (P: V -> Prop) (g2: Graph) x,
        ~ g1 |= (dst g1 e) ~o~> x satisfying P -> edge_spanning_tree g1 e P g2 -> (vvalid g1 x <-> vvalid g2 x).
    Proof.
      intros. destruct H0 as [[? ?] | [? ?]].
      + eapply not_reachable_ST_vvalid; eauto.
      + destruct H1. apply H1.
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
            apply partialgraph_proper. reflexivity.
            apply reachable_by_proper'; try reflexivity.
            rewrite Same_set_spec; hnf; auto.
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

    Lemma si_edge_spanning_tree: forall (g1 g2 g3: Graph) (e: E) (P: V -> Prop),
        g1 ~=~ g2 -> evalid g1 e -> (edge_spanning_tree g1 e P g3 <-> edge_spanning_tree g2 e P g3).
    Proof.
      cut (forall g1 g2 g3 e P, g1 ~=~ g2 -> evalid g1 e -> edge_spanning_tree g1 e P g3 -> edge_spanning_tree g2 e P g3);
      intros.
      + split; intros; [apply H with g1 | apply H with g2]; auto.
        - symmetry; auto.
        - destruct H0 as [_ [? _]]. specialize (H0 e). intuition.
      + assert (dst g1 e = dst g2 e). {
          destruct H as [_ [? [_ ?]]].
          specialize (H e). specialize (H2 e).
          rewrite <- H2; intuition.
        }
        destruct H1 as [[? ?] | [? ?]]; [left | right]; split; [rewrite <- H2 .. |]; auto.
        - rewrite <- (si_spanning_tree g1); auto.
        - destruct H as [? [? [? ?]]]. destruct H3 as [? [? [? [? ?]]]].
          split; [|split; [|split; [|split]]]; intros.
          * specialize (H v). specialize (H3 v). intuition.
          * specialize (H4 e0). specialize (H7 e0 H11). intuition.
          * specialize (H7 e0 H11). specialize (H5 e0). specialize (H8 e0 H11). rewrite H5 in H8; intuition.
          * specialize (H7 e0 H11). specialize (H6 e0). specialize (H9 e0 H11). rewrite H6 in H9; intuition.
          * destruct H10; [left | right]; auto. intuition. rewrite <- H10. symmetry.
            specialize (H4 e). apply H5; intuition.
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

    Instance spanning_tree_proper:
      Proper ((@structurally_identical V E _ _) ==> eq ==> (pointwise_relation V iff) ==> structurally_identical ==> iff)
             spanning_tree.
    Proof.
      intros g1 g2 ? v1 v2 ? P1 P2 ? g3 g4 ?. subst.
      rewrite (si_spanning_tree g1 g2); auto.
      rewrite (spanning_tree_equiv P1 P2). 2: apply H1.
      rewrite (si_spanning_tree' g2 g3 g4); auto.
      tauto.
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

    Lemma spanning_tree_predicate_partial_si: forall (g1 g2: Graph) (e: E) (root: V) (P R: V -> Prop),
        Included R P -> out_edges g1 root e -> vvalid g1 root -> P root -> spanning_tree g1 (dst g1 e) R g2 ->
        (predicate_partialgraph g1 (fun n : V => ~ g1 |= root ~o~> n satisfying P)) ~=~
        (predicate_partialgraph g2 (fun n : V => ~ g1 |= root ~o~> n satisfying P)).
    Proof.
      intros. destruct H3.
      apply si_stronger_partialgraph_simple with
      (fun n : V => ~ g1 |= dst g1 e ~o~> n satisfying R); auto.
      intro. unfold Ensembles.In. intros. intro. apply H5.
      apply reachable_by_weaken with (Q := P) in H6; auto.
      apply reachable_by_cons with (dst g1 e); auto. destruct H0. split; auto. split.
      + apply reachable_by_head_valid in H6; auto.
      + rewrite step_spec. exists e. auto.
    Qed.

    Lemma EST_predicate_partial_si: forall (g1 g2: Graph) (e: E) (root: V) (P R: V -> Prop),
        Included R P -> out_edges g1 root e -> vvalid g1 root -> P root -> edge_spanning_tree g1 e R g2 ->
        (predicate_partialgraph g1 (fun n : V => ~ g1 |= root ~o~> n satisfying P)) ~=~
        (predicate_partialgraph g2 (fun n : V => ~ g1 |= root ~o~> n satisfying P)).
    Proof.
      intros. destruct H3 as [[? ?] | [? ?]].
      + apply (spanning_tree_predicate_partial_si g1 g2 e root P R); auto.
      + apply (gremove_predicate_partial_si g1 g2 e); auto.
    Qed.

    Lemma gremove_root_reachable_by_equiv: forall (g1 g2: Graph) (e: E) (root: V) (P: V -> Prop),
        out_edges g1 root e -> gremove_edge g1 e g2 ->
        (~ (P (dst g1 e) /\ dst g1 e <> root)) ->
        forall n, (g1 |= root ~o~> n satisfying P <-> g2 |= root ~o~> n satisfying P).
    Proof.
      intros. split; intros; destruct H; destruct H0 as [? [? [? [? ?]]]].
      + rewrite reachable_acyclic in H2. destruct H2 as [p [? ?]]. exists p.
        destruct H8 as [? [? ?]]. split; [|split]; auto. destruct p. simpl; auto.
        destruct H8. simpl in H8. inversion H8. subst v. clear H8 H11.
        pose proof (NoDup_cons_2 _ _ _ H2). simpl in H9 |-* . destruct p. rewrite <- H0; auto.
        destruct H9. split.
        - destruct H9 as [? [? ?]]. split; [|split]; [rewrite <- H0 ..|]; auto.
          rewrite step_spec in H13 |-* . destruct H13 as [e' [? [? ?]]]. exists e'. destruct_eq_dec e' e.
          * exfalso. subst e'. apply H1. split.
            Focus 1. {
              unfold path_prop in H10. rewrite Forall_forall in H10.
              assert (P v). apply H10. apply in_cons. apply in_eq. subst. auto.
            } Unfocus.
            Focus 1. {
              rewrite H15 in *. clear H15. intro. apply H8.
              subst v. apply in_eq.
            } Unfocus.
          * specialize (H4 _ H16). assert (evalid g2 e') by intuition.
            specialize (H5 _ H16 H13 H17). specialize (H6 _ H16 H13 H17).
            rewrite <- H5, <- H6. intuition.
        - clear H2 H9. assert (path_prop P (v :: p)). {
            apply path_prop_sublist with (root :: v :: p); auto.
            apply Sublist_cons; auto.
          } clear H10.
          revert v H11 H8 H2. induction p; intros.
          1: simpl in *. rewrite <- H0; auto.
          simpl in H11 |-* . destruct H11. split.
          * clear H10. destruct H9 as [? [? ?]]. split; [|split]; [rewrite <- H0 ..|]; auto.
            rewrite step_spec in H11 |-* . destruct H11 as [e' [? [? ?]]]. exists e'. destruct_eq_dec e' e.
            Focus 1. {
              exfalso. subst e'. apply H1. split.
              + unfold path_prop in H2. rewrite Forall_forall in H2.
                assert (P a). apply H2. apply in_cons, in_eq. subst; auto.
              + rewrite H13. intro. apply H8. rewrite H14. apply in_cons, in_eq.
            } Unfocus.
            Focus 1. {
              specialize (H4 _ H14). assert (evalid g2 e') by intuition.
              specialize (H5 _ H14 H11 H15). specialize (H6 _ H14 H11 H15).
              rewrite <- H5, <- H6. intuition.
            } Unfocus.
          * apply IHp.
            1: apply H10.
            1: intro; apply H8; apply in_cons; auto.
            1: apply path_prop_sublist with (v :: a :: p); auto; apply Sublist_cons; auto.
      + destruct H2 as [p [? [? ?]]]. exists p. split; [|split]; auto.
        clear H2 H9. induction p; simpl; auto. simpl in H8. destruct p.
        - rewrite H0; auto.
        - destruct H8. split. 2: apply IHp; auto.
          destruct H2 as [? [? ?]]. split; [|split]; [rewrite H0 ..|]; auto.
          rewrite step_spec in H10 |-* . destruct H10 as [e' [? [? ?]]].
          exists e'. destruct_eq_dec e' e.
          * subst. exfalso. destruct H7. auto. destruct H3. auto.
          * specialize (H4 _ H13). specialize (H5 _ H13). specialize (H6 _ H13). subst a. subst v. intuition.
    Qed.

    Lemma spanning_tree_root_reachable_by: forall (g1 g2: Graph) (e: E) (root: V) (P: V -> Prop),
        out_edges g1 root e -> vvalid g1 root -> P root ->
        ReachDecidable g1 (dst g1 e) (fun x => P x /\ x <> root) ->
        spanning_tree g1 (dst g1 e) (fun x => P x /\ x <> root) g2 ->
        Included (reachable_by g2 root P) (reachable_by g1 root P).
    Proof.
      intros. hnf. unfold Ensembles.In. intros. destruct (X x).
      + assert (g1 |= dst g1 e ~o~> x satisfying P). {
          apply reachable_by_weaken with (fun x => P x /\ x <> root); auto.
          hnf. unfold Ensembles.In . intuition.
        }
        apply reachable_by_cons with (dst g1 e); auto.
        apply reachable_by_head_valid in H4. do 2 (split; auto).
        rewrite step_spec. destruct H. exists e; auto.
      + destruct H3 as [p ?].
        assert (forall v, In v p -> ~ g1 |= dst g1 e ~o~> v satisfying (fun x0 : V => P x0 /\ x0 <> root)). {
          intros. intro. destruct H2 as [_ [_ [_ ?]]]. specialize (H2 v x H5 n).
          apply H2. apply (reachable_path_in' g2 p root); auto.
          clear -H3. destruct H3 as [? [? ?]]. do 2 (split; auto).
          hnf. rewrite Forall_forall. intros; auto.
        } exists p. destruct H2 as [? _].
        rewrite (ppg_reachable_by_path_eq g1 g2 _ _ p root x H2 H4); auto.
    Qed.
    
    Lemma EST_root_reachable_by: forall (g1 g2: Graph) (e: E) (root: V) (P: V -> Prop),
        out_edges g1 root e -> vvalid g1 root -> P root ->
        ReachDecidable g1 (dst g1 e) (fun x => P x /\ x <> root) ->
        edge_spanning_tree g1 e (fun x => P x /\ x <> root) g2 ->
        Included (reachable_by g2 root P) (reachable_by g1 root P).
    Proof.
      intros. destruct H2 as [[? ?] | [? ?]].
      + apply (spanning_tree_root_reachable_by g1 g2 e); auto.
      + intro n. unfold Ensembles.In . intros. rewrite (gremove_root_reachable_by_equiv g1 g2 e); auto.
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

    Lemma ppg_out_edges: forall (P: V -> Prop) g1 root g2 (v: V),
        ~ P root ->
        (predicate_partialgraph g1 (fun n : V => ~ g1 |= v ~o~> n satisfying P)) ~=~
        (predicate_partialgraph g2 (fun n : V => ~ g1 |= v ~o~> n satisfying P)) ->
        forall e', out_edges g1 root e' <-> out_edges g2 root e'.
    Proof.
      intros. hnf in H0. simpl in H0.
      unfold predicate_vvalid in H0. unfold predicate_weak_evalid in H0.
      destruct H0 as [_ [? [? _]]]. specialize (H0 e'). specialize (H1 e').
      split; intros; destruct H2; rewrite H3 in * .
      + assert (evalid g1 e' /\ ~ g1 |= v ~o~> root satisfying P). {
          split; auto. intro. apply reachable_by_foot_prop in H4. auto.
        } split; intuition.
      + assert (evalid g2 e' /\ ~ g1 |= v ~o~> root satisfying P). {
          split; auto. intro. apply reachable_by_foot_prop in H4. auto.
        } split; intuition.
    Qed.

    Lemma EST_out_edges: forall (P: V -> Prop) g1 root g2 (e1 e2 : E),
        e1 <> e2 -> ~ P root -> out_edges g1 root e2 -> edge_spanning_tree g1 e1 P g2 -> out_edges g2 root e2.
    Proof.
      intros. destruct H2 as [[? ?] | [? ?]].
      + destruct H3 as [? _]. rewrite <- ppg_out_edges; eauto.
      + destruct H3 as [? [? [? [? ?]]]]. assert (e2 <> e1) by intuition.
        specialize (H4 e2 H8). specialize (H5 e2 H8). specialize (H6 e2 H8).
        destruct H1. split; [|rewrite <- H5]; intuition.
    Qed.

    Lemma ppg_the_same_dst: forall (P: V -> Prop) g1 root g2 (v: V) (e : E),
        ~ P root -> out_edges g1 root e ->
        (predicate_partialgraph g1 (fun n : V => ~ g1 |= v ~o~> n satisfying P)) ~=~
        (predicate_partialgraph g2 (fun n : V => ~ g1 |= v ~o~> n satisfying P)) ->
        dst g1 e = dst g2 e.
    Proof.
      intros. hnf in H1. simpl in H1. destruct H0.
      unfold predicate_vvalid in H1. unfold predicate_weak_evalid in H1.
      destruct H1 as [_ [? [_ ?]]]. specialize (H1 e). specialize (H3 e).
      rewrite H2 in *.
      assert (evalid g1 e /\ ~ g1 |= v ~o~> root satisfying P). {
        split; auto. intro. apply reachable_by_foot_prop in H4. auto.
      } apply H3; intuition.
    Qed.

    Lemma EST_the_same_dst: forall (P: V -> Prop) g1 root g2 (e1 e2 : E),
        e1 <> e2 -> ~ P root -> out_edges g1 root e2 -> edge_spanning_tree g1 e1 P g2 -> dst g1 e2 = dst g2 e2.
    Proof.
      intros. destruct H2 as [[? ?] | [? ?]].
      + destruct H3 as [? _]. eapply ppg_the_same_dst; eauto.
      + destruct H3 as [? [? [? [? ?]]]]. assert (e2 <> e1) by intuition.
        specialize (H4 _ H8). specialize (H6 _ H8). destruct H1.
        apply H6; intuition.
    Qed.

    Lemma root_reachable_by_derive: forall (P: V -> Prop) g root,
        forall n, g |= root ~o~> n satisfying P ->
                  n = root \/
                  exists e, out_edges g root e /\ g |= dst g e ~o~> n
                                        satisfying (fun x : V => P x /\ x <> root).
    Proof.
      intros. destruct_eq_dec n root; [left; auto | right].
      rewrite reachable_acyclic in H.
      destruct H as [p [? ?]]. destruct p.
      1: destruct H1 as [[? _] _]; inversion H1; auto.
      assert (v = root) by (destruct H1 as [[? _] _]; inversion H1; auto). subst.
      destruct p.
      + destruct H1 as [[_ ?] _]. simpl in H1. inversion H1. exfalso; auto.
      + destruct H1 as [? [[? ?] ?]]. destruct H2 as [? [? ?]].
        rewrite step_spec in H6. destruct H6 as [e [? [? ?]]].
        exists e. split. 1: split; auto.
        exists (v :: p). split; [|split]; auto.
        - split. simpl. subst v. auto. destruct H1.
          rewrite foot_simpl in H9. auto.
        - apply path_prop_tail in H4. unfold path_prop in H4 |-* .
          rewrite Forall_forall in H4 |-* . intros; split.
          * apply H4; auto.
          * apply NoDup_cons_2 in H. intro. subst x. auto.
    Qed.

    Lemma root_not_reachable_derive: forall (g: Graph) root,
        forall n, (n <> root /\ forall e, out_edges g root e -> ~ reachable g (dst g e) n) -> ~ reachable g root n.
    Proof.
      intros. destruct H. intro. apply (root_reachable_by_derive _ g root) in H1.
      destruct H1; auto. destruct H1 as [e [? ?]]. specialize (H0 _ H1).
      apply H0. revert H2. apply reachable_by_weaken. compute. auto.
    Qed.

    Lemma EST_reverse_out_edges: forall (P: V -> Prop) (g1 g2: Graph) (e: E) (root: V),
        ~ P root -> out_edges g1 root e -> edge_spanning_tree g1 e P g2 ->
        forall e', out_edges g2 root e' -> out_edges g1 root e'.
    Proof.
      intros. destruct H1 as [[_ [? _]] | [_ [_ [? [? [_ ?]]]]]].
      + pose proof (ppg_out_edges _ _ _ _ _ H H1). rewrite H3; auto.
      + destruct_eq_dec e' e.
        - subst. destruct H4; [destruct H2|]; auto.
        - specialize (H1 _ H5). specialize (H3 _ H5).
          hnf. destruct H2. subst root; intuition.
    Qed.

    Lemma spanning_tree_not_reachable_derive:
      forall (g1 : Graph) (root : V) (P : V -> Prop) (g2 : Graph) (x y : V),
        spanning_tree g1 root P g2 ->
        ~ g1 |= root ~o~> x satisfying P ->
        ~ g1 |= root ~o~> y satisfying P ->
        ~ reachable g1 x y -> ~ reachable g2 x y.
    Proof.
      intros. intro; apply H2; clear H2. rename H3 into H2.
      destruct H as [? [? [? ?]]].
      destruct (classic
                  (g2 |= x ~o~> y
                      satisfying (fun n : V => ~ g1 |= root ~o~> n satisfying P))).
      + destruct H6 as [p ?].
        assert (forall v, In v p -> ~ g1 |= root ~o~> v satisfying P). {
          intros. pose proof (reachable_by_path_in _ _ _ _ _ H6 v H7).
          apply reachable_by_foot_prop in H8. auto.
        }
        rewrite <- ppg_reachable_by_path_eq in H6; eauto.
        apply reachable_by_path_is_reachable_by in H6.
        revert H6. apply reachable_by_weaken.
        hnf; unfold Ensembles.In ; intros; auto.
      + destruct H2 as [p ?].
        destruct (classic (exists v, In v p /\ g1 |= root ~o~> v satisfying P)).
        - destruct H7 as [v [? ?]]. specialize (H5 _ _ H8 H1). exfalso; apply H5.
          eapply reachable_by_path_in'; eauto.
        - assert (forall v, In v p -> ~ g1 |= root ~o~> v satisfying P). {
            intros. apply not_ex_all_not with (n := v) in H7.
            apply not_and_or in H7. destruct H7; auto.
          } clear H7. exfalso. apply H6. exists p.
          destruct H2 as [? [? ?]]. do 2 (split; auto).
          hnf. rewrite Forall_forall. apply H8.
    Qed.

    Lemma gremove_not_reachable_derive:
      forall (g1 : Graph) (e : E) (g2 : Graph) (x y : V),
        gremove_edge g1 e g2 -> ~ reachable g1 x y -> ~ reachable g2 x y.
    Proof.
      intros. intro. apply H0; clear H0. destruct H as [? [? [? [? ?]]]].
      destruct H1 as [p [? [? ?]]]. exists p; do 2 (split; auto). clear H1 H6.
      induction p; simpl; auto. destruct p.
      + simpl in H5. rewrite H; auto.
      + destruct H5. split.
        - destruct H1 as [? [? ?]]. split; [|split]; [rewrite H; auto ..|].
          rewrite step_spec in H7 |-* . destruct H7 as [e' [? [? ?]]].
          exists e'. assert (e' <> e). {
            intro. subst e'. destruct H4; auto.
            destruct H4 as [? [? ?]]. subst v. auto.
          } specialize (H0 _ H10). specialize (H2 _ H10). specialize (H3 _ H10).
          subst a v. intuition.
        - apply IHp; auto.
    Qed.

    Lemma EST_not_reachable_derive:
      forall (g1 : Graph) (e : E) (P : V -> Prop) (g2 : Graph) (x y : V),
        edge_spanning_tree g1 e P g2 ->
        ~ g1 |= dst g1 e ~o~> x satisfying P ->
        ~ g1 |= dst g1 e ~o~> y satisfying P ->
        ~ reachable g1 x y -> ~ reachable g2 x y.
    Proof.
      intros. destruct H as [[? ?] | [? ?]].
      + apply (spanning_tree_not_reachable_derive g1 (dst g1 e) P g2 x y); auto.
      + apply (gremove_not_reachable_derive g1 e g2 x y); auto.
    Qed.

    Lemma spanning_list_spanning_tree2_reachable:
      forall (P: V -> Prop) (g1 g2 g3: Graph) root (e1 e2 : E) n,
        (e1 <> e2) -> (forall e, In e (e1 :: e2 :: nil) <-> out_edges g1 root e) ->
        vvalid g1 root -> P root ->
        ReachDecidable g1 (dst g1 e1) (fun x => P x /\ x <> root) ->
        edge_spanning_tree g1 e1 (fun x : V => P x /\ x <> root) g2 ->
        edge_spanning_tree g2 e2
                           (fun x : V =>
                              (P x /\ x <> root) /\
                              ~ g1 |= dst g1 e1 ~o~> x
                                satisfying (fun x0 : V => P x0 /\ x0 <> root)) g3 ->
        g1 |= root ~o~> n satisfying P -> reachable g3 root n.
    Proof.
      intros. rename H5 into H9. rename H3 into H5. rename H4 into H6.
      assert (out_edges g1 root e1) by (rewrite <- H0; apply in_eq).
      assert (out_edges g1 root e2) by (rewrite <- H0; apply in_cons, in_eq).
      assert (vvalid g2 root) by
          (rewrite <- (edge_spanning_tree_vvalid
                         g1 e1 (fun x : V => P x /\ x <> root)); auto).
      assert (out_edges g2 root e2) by
          (apply (EST_out_edges (fun x : V => P x /\ x <> root) g1 _ _ e1);intuition).
      assert (vvalid g3 root). {
        rewrite <- (not_reachable_EST_vvalid g2 e2); eauto.
        intro. apply reachable_by_foot_prop in H10.
        destruct H10 as [[_ ?] _]. apply H10; auto.
      }
      destruct_eq_dec n root. 1: subst; apply reachable_by_reflexive; split; auto.
      destruct (X n).
      + destruct H5 as [[? ?] | [? ?]].
        2: apply reachable_by_head_prop in r; exfalso; apply H5; auto.
        destruct H12 as [? [_ [? ?]]]. specialize (H13 _ r).
        assert (vvalid g2 (dst g1 e1)) by
            (apply reachable_by_head_valid in H13; auto).
        destruct H13 as [p ?].
        assert (forall v, In v p -> g1 |= dst g1 e1 ~o~> v satisfying
                                       (fun x : V => P x /\ x <> root)). {
          intros. destruct (X v); auto.
          pose proof (reachable_path_in _ _ _ _ H13 _ H16).
          assert (g1 |= dst g1 e1 ~o~> dst g1 e1 satisfying
                     (fun x : V => P x /\ x <> root)). {
            apply reachable_by_reflexive. split; auto.
            apply reachable_by_head_valid in r; auto.
          }
          specialize (H14 _ _ H18 n0). exfalso; auto.
        }
        assert (g2 |= (root :: p) is root ~o~> n satisfying (fun _ : V => True)). {
          assert (root :: p = path_glue (root :: dst g1 e1 :: nil) p). {
            unfold path_glue. rewrite <- app_comm_cons. f_equal.
            destruct p; destruct H13 as [[? _] _];
            simpl in H13 |-* ; inversion H13; f_equal.
          } rewrite H17. apply reachable_by_path_merge with (dst g1 e1); auto.
          split; split; simpl; auto.
          2: hnf; rewrite Forall_forall; intros; auto.
          do 3 (split; auto). rewrite step_spec. exists e1.
          pose proof H3.
          rewrite (ppg_out_edges (fun x : V => P x /\ x <> root)) in H18; eauto.
          2: intro; destruct H19; auto. destruct H18.
          eapply ppg_the_same_dst in H12; eauto.
          intro. destruct H20; auto.
        } exists (root :: p). destruct H6 as [[? ?] | [? ?]].
        - destruct H18 as [? _].
          rewrite <- (ppg_reachable_by_path_eq g2 g3 _ _ _ _ _ H18); auto.
          intros. simpl in H19. destruct H19; intro; [subst | apply H16 in H19];
                                apply reachable_by_foot_prop in H20; destruct H20 as [[? ?] ?]; auto.
        - destruct H17 as [? [? ?]]. do 2 (split; auto).
          destruct p. 1: simpl; auto. destruct H19. split.
          Focus 1. {
            assert (v = dst g1 e1)
              by (destruct H13 as [[? _] _]; simpl in H13; inversion H13; auto).
            subst v. split; auto. destruct H18 as [? [? [? [? ?]]]]. split.
            + rewrite <- H18; auto.
            + rewrite step_spec. exists e1.
              assert (out_edges g2 root e1). {
                rewrite <- (ppg_out_edges (fun x => P x /\ x <> root) g1); eauto.
                intro. destruct H26; auto.
              } destruct H26. 
              specialize (H22 _ H). specialize (H23 _ H). specialize (H24 _ H).
              split; [|split].
            - intuition.
            - rewrite <- H23; intuition.
            - rewrite <- H24; auto. 2: intuition.
              eapply ppg_the_same_dst in H12; eauto.
              intro. destruct H28; auto.
          } Unfocus.
          Focus 1. {
            clear H17 H20 H13 H19. revert v H16 H21. induction p; intros.
            + simpl in H21 |-* . destruct H18. rewrite <- H13; auto.
            + specialize (IHp a). destruct H21. split.
            - destruct H13 as [? [? ?]]. destruct H18 as [? [? [? [? ?]]]].
              split; [| split]; [rewrite <- H18 ..|]; auto.
              rewrite step_spec in H20 |-* .
              destruct H20 as [e [? [? ?]]].
              assert (e <> e2). {
                intro. subst e. destruct H8. rewrite H27 in H25. subst v.
                assert (In root (root :: a :: p)) by apply in_eq.
                specialize (H16 _ H25). apply reachable_by_foot_prop in H16.
                destruct H16; auto.
              } exists e. specialize (H21 _ H27). specialize (H22 _ H27).
              specialize (H23 _ H27). subst v a. intuition.
            - apply IHp; auto. intros. apply H16. apply in_cons; auto.
          } Unfocus.
      + apply (root_reachable_by_derive _ _ _) in H9.
        destruct H9. 1: exfalso; auto. destruct H9 as [e [? ?]].
        rewrite <- H0 in H9.
        simpl in H9. destruct H9 as [? | [? | ?]]; [subst e ..|].
        1: exfalso; auto. 2: exfalso; auto.
        assert (g1 |= dst g1 e2 ~o~> n
                   satisfying
                   (fun x : V =>
                      (P x /\ x <> root) /\
                      ~ g1 |= dst g1 e1 ~o~> x
                        satisfying (fun x0 : V => P x0 /\ x0 <> root))). {
          destruct H12 as [p ?]. pose proof (reachable_by_path_in' _ _ _ _ _ H9).
          destruct H9 as [? [? ?]]. exists p. do 2 (split; auto).
          unfold path_prop in H14 |-* . rewrite Forall_forall in H14 |-* .
          intros. split. apply H14; auto. intro. apply n0.
          specialize (H12 _ H15). apply reachable_by_merge with x; auto.
        }
        pose proof H5. apply (EST_the_same_dst _ _ root _ _ e2) in H13; auto.
        2: intro; destruct H14; auto. rewrite H13 in H9.
        destruct H6 as [[? ?] | [? ?]].
        2: apply reachable_by_head_prop in H9; exfalso; auto.
        assert (out_edges g3 root e2). {
          destruct H14 as [? _].
          apply (ppg_out_edges _ _ root) with (e' := e2) in H14; auto.
          2: intro; destruct H15 as [[_ ?] _]; auto. rewrite <- H14; auto.
        }
        assert (dst g2 e2 = dst g3 e2). {
          destruct H14 as [? _].
          apply (ppg_the_same_dst _ _ root) with (e := e2) in H14; auto.
          intro. destruct H16 as [[_ ?] _]; auto.
        }
        apply reachable_by_cons with (dst g3 e2); auto.
        - split; auto; split.
          2: rewrite step_spec; exists e2; destruct H15; auto.
          rewrite <- H16.
          apply reachable_by_head_valid in H9.
          apply edge_spanning_tree_vvalid with (x := dst g2 e2) in H5; auto.
          rewrite H5 in H9.
          apply (spanning_tree_root_vvalid _ _ _ _ H14); auto.
        - destruct H14 as [_ [_ [? _]]]. rewrite <- H16. apply H14.
          destruct H5 as [[? ?] | [? ?]].
          Focus 1. {
            destruct H17 as [? _]. destruct H9 as [p ?]. exists p.
            rewrite <- (ppg_reachable_by_path_eq g1 g2); eauto.
            intros. simpl. destruct H9 as [_ [_ ?]].
            hnf in H9. rewrite Forall_forall in H9.
            specialize (H9 _ H18). destruct H9; auto.
          } Unfocus.
          Focus 1. {
            destruct H9 as [p [? [? ?]]]. exists p.
            do 2 (split; auto).
            assert (forall v, In v p -> P v /\ v <> root). {
              intros. hnf in H19. rewrite Forall_forall in H19.
              specialize (H19 _ H20). destruct H19; auto.
            } clear H9 H19. induction p. simpl; auto.
            destruct p.
            + simpl in H18 |-* . destruct H17. rewrite <- H9; auto.
            + destruct H18. split.
            - clear -H17 H5 H9 H20. destruct H17 as [? [? [? [? ?]]]].
              destruct H9 as [? [? ?]].
              split; [|split]; [rewrite <- H; auto..|].
              rewrite step_spec in H7 |-* .
              destruct H7 as [e [? [? ?]]]. exists e.
              assert (e <> e1). {
                intro. subst e.
                assert (In v (a :: v :: p)) by apply in_cons, in_eq.
                specialize (H20 _ H10). subst v. auto.
              } specialize (H0 _ H10). specialize (H1 _ H10).
              specialize (H2 _ H10). subst a v. intuition.
            - apply IHp; auto. intros. apply H20.
              apply in_cons; auto.
          } Unfocus.
    Qed.

    Lemma EST_not_reachable: forall (P Q: V -> Prop) g1 root g2 (e: E) n,
        ~ P root -> Q root -> vvalid g1 root -> Included P Q ->
        out_edges g1 root e -> edge_spanning_tree g1 e P g2 ->
        ~ g1 |= root ~o~> n satisfying Q ->
        (~ reachable g2 (dst g2 e) n \/ ~ out_edges g2 root e).
    Proof.
      intros. destruct (classic (g1 |= dst g1 e ~o~> dst g1 e satisfying P)).
      + destruct H4 as [[? ?] | [? ?]].
        2: apply reachable_by_head_prop in H6; exfalso; auto.
        destruct H7 as [? [_ [_ ?]]].
        assert (~ g1 |= dst g1 e ~o~> n satisfying P). {
          intro. apply H5. apply reachable_by_cons with (dst g1 e); auto.
          + split; auto. apply reachable_by_head_valid in H9; split; auto.
            rewrite step_spec. exists e. destruct H3; auto.
          + revert H9. apply reachable_by_weaken; auto.
        } specialize (H8 _ _ H6 H9).
        assert (out_edges g2 root e) by (rewrite <- (ppg_out_edges P g1); eauto).
        assert (dst g1 e = dst g2 e)
          by (apply (ppg_the_same_dst _ _ root _ _ e H) in H7; auto).
        rewrite H11 in *. left; auto.
      + destruct H4 as [[? ?] | [? ?]].
        - assert (~ vvalid g1 (dst g1 e)). {
            intro. apply H6. apply reachable_by_reflexive; auto.
          } pose proof H7. destruct H7 as [? _].
          assert (dst g1 e = dst g2 e)
            by (apply (ppg_the_same_dst _ _ root g2 _ e) in H7; auto).
          rewrite H10 in *. left.
          assert (out_edges g2 root e) by (rewrite <- (ppg_out_edges P g1); eauto).
          assert (~ reachable g1 (dst g2 e) n)
            by (intro; apply reachable_by_head_valid in H12; auto).
          apply (spanning_tree_not_reachable_derive g1 _ _ g2 _ _ H9); auto.
          intro. apply reachable_by_head_valid in H13; auto.
        - destruct H7 as [? [? [? [? ?]]]]. destruct H11.
          * right. intro. apply H11. destruct H12; auto.
          * destruct H11 as [? [? ?]].
            left; intro. apply H11. apply reachable_by_head_valid in H14; auto.
    Qed.
        
    Lemma spanning_list_spanning_tree2: forall (P: V -> Prop) g1 root g2 (e1 e2 : E),
        (e1 <> e2) -> (forall e, In e (e1 :: e2 :: nil) <-> out_edges g1 root e) ->
        vvalid g1 root -> P root ->
        ReachDecidable g1 (dst g1 e1) (fun x => P x /\ x <> root) ->
        spanning_list' (fun x => P x /\ x <> root) g1 (e1 :: e2 :: nil) g2 ->
        spanning_tree g1 root P g2.
    Proof.
      intros. assert (out_edges g1 root e1) by (rewrite <- H0; apply in_eq).
      assert (out_edges g1 root e2) by (rewrite <- H0; apply in_cons, in_eq).
      inversion H3. subst. destruct es.
      rewrite app_nil_l in H6. inversion H6. destruct es.
      2: inversion H6; destruct es; inversion H12.
      inversion H6. subst. clear H6. inversion H7. subst.
      destruct es. 2: inversion H6; destruct es; inversion H13.
      inversion H6. subst. clear H6. inversion H8. 2: destruct es; inversion H6.
      rewrite <- si_edge_spanning_tree with (g1 := g1) in H12; auto.
      2: destruct H4; auto. subst. clear g4 H8 H6.
      rename g2 into g3'. rename g3 into g2. rename g3' into g3.
      clear H3 H7. rename H4 into H3. rename H5 into H4.
      rename H12 into H5. rename H10 into H6.
      rewrite <- (edge_spanning_tree_equiv (fun x => P x /\ x <> root)) in H5.
      2: intros; simpl; rewrite reachable_by_through_nil; intuition. simpl in H6.
      rewrite <- (edge_spanning_tree_equiv
                    (fun x => (P x /\ x <> root) /\
                              ~ g1 |= dst g1 e1 ~o~> x
                                satisfying (fun x0 : V => P x0 /\ x0 <> root))) in H6.
      2: intros; rewrite reachable_by_through_singleton; intuition.
      assert (vvalid g2 root) by
          (rewrite <- (edge_spanning_tree_vvalid
                         g1 e1 (fun x : V => P x /\ x <> root)); auto).
      assert (out_edges g2 root e2) by
          (apply (EST_out_edges (fun x : V => P x /\ x <> root) g1 _ _ e1);intuition).
      split; [|split; [|split]]; intros.
      + pose proof H5. apply (EST_predicate_partial_si g1 g2 e1 root P) in H9; auto.
        2: intro; unfold Ensembles.In ; intuition. rewrite H9. clear H9.
        apply (EST_predicate_partial_si g2 g3 e2 root P) in H6; auto.
        2: intro; unfold Ensembles.In ; intuition.
        apply si_stronger_partialgraph_simple with
        (fun n : V => ~ g2 |= root ~o~> n satisfying P); auto.
        cut (Included (reachable_by g2 root P) (reachable_by g1 root P)).
        - unfold Included. unfold Ensembles.In . intros. intuition.
        - apply EST_root_reachable_by with e1; auto.
      + admit.
      + apply (spanning_list_spanning_tree2_reachable P g1 g2 g3 root e1 e2 n); auto.
      + apply (spanning_list_spanning_tree2_reachable _ _ g2 g3 _ e1 e2) in H9; auto.
        intro.
        assert (reachable g3 root b) by (apply reachable_by_merge with a; auto).
        cut (~ reachable g3 root b). 1: intro. apply H13; auto.
        clear H9 H11. destruct_eq_dec b root.
        1: subst; exfalso; apply H10; apply reachable_by_reflexive; auto.
        assert (~ g2 |= root ~o~> b satisfying P). {
          intro. apply H10. apply EST_root_reachable_by in H5; auto. apply H5, H11.
        }
        assert (N1: forall v,
                   ~ g2 |= dst g2 e2 ~o~> b
                     satisfying
                     (fun x : V =>
                         (P x /\ x <> root) /\
                         ~ g1 |= v ~o~> x
                           satisfying (fun x0 : V => P x0 /\ x0 <> root))). {
          repeat intro. apply H11. apply reachable_by_cons with (dst g2 e2); auto.
          + split; auto. apply reachable_by_head_valid in H13. split; auto.
            rewrite step_spec. exists e2. destruct H8; auto.
          + revert H13. apply reachable_by_weaken.
              hnf. unfold Ensembles.In . intros. destruct H13 as [[? _] _]; auto.
        }
        assert (~ reachable g3 (dst g3 e1) b \/ ~ out_edges g3 root e1). {
          destruct (X (dst g1 e1)).
          + destruct H5 as [[? ?] | [? ?]].
            2: apply reachable_by_head_prop in r; exfalso; auto.
            destruct H13 as [? [_ [_ ?]]].
            assert (~ g1 |= dst g1 e1 ~o~> b
                      satisfying (fun x : V => P x /\ x <> root)). {
              intro. apply H10. apply reachable_by_cons with (dst g1 e1); auto.
              + split; auto. apply reachable_by_head_valid in H15. split; auto.
                rewrite step_spec. exists e1. destruct H3. auto.
              + apply reachable_by_weaken with (fun x : V => P x /\ x <> root); auto.
                compute; tauto.
            } specialize (H14 _ _ r H15).
            assert (out_edges g2 root e1). {
              rewrite <- (ppg_out_edges (fun x => P x /\ x <> root) g1); eauto.
              intro. destruct H16; auto.
            }
            assert (dst g1 e1 = dst g2 e1). {
              apply (ppg_the_same_dst _ _ root) with (e := e1) in H13; auto.
              intuition.
            } rewrite H17 in *.
            assert (dst g2 e1 = dst g3 e1). {
              apply (EST_the_same_dst _ _ root _ _ e1) in H6; auto.
              intro. destruct H18 as [[_ ?] _]. auto.
            } rewrite H18 in *.
            left. apply (EST_not_reachable_derive _ _ _ _ _ _ H6); auto.
            intro. apply reachable_by_foot_prop in H19.
            destruct H19 as [_ ?]. auto.
          + destruct H5 as [[? ?] | [? ?]].
            - assert (~ vvalid g1 (dst g1 e1)). {
                intro. apply n. apply reachable_by_reflexive; auto.
              } pose proof H13. destruct H13 as [? _].
              assert (dst g1 e1 = dst g2 e1). {
                apply (ppg_the_same_dst _ _ root) with (e := e1) in H13; auto.
                intuition.
              } rewrite H16 in *.
              assert (out_edges g2 root e1). {
                rewrite <- (ppg_out_edges (fun x => P x /\ x <> root) g1); eauto.
                intro. destruct H17; auto.
              }              
              assert (dst g2 e1 = dst g3 e1). {
                apply (EST_the_same_dst _ _ root _ _ e1) in H6; auto.
                intro. destruct H18 as [[_ ?] _]. auto.
              } rewrite H18 in *.
              assert (~ reachable g1 (dst g3 e1) b). {
                intro. apply reachable_by_head_valid in H19; auto.
              }
              assert (~ reachable g2 (dst g3 e1) b). {
                apply (spanning_tree_not_reachable_derive g1 _ _ g2 _ _ H15); auto.
                intro. apply reachable_by_head_valid in H20; auto.
              } left.
              apply (EST_not_reachable_derive _ _ _ _ _ _ H6); auto.
              intro. apply reachable_by_foot_valid in H21.
              rewrite <- not_reachable_ST_vvalid in H21; eauto.
            - destruct H13 as [? [? [? [? ?]]]]. destruct H17.
              * right. intro. apply H17.
                apply (EST_reverse_out_edges
                         (fun x : V =>
                            (P x /\ x <> root) /\
                            ~ g1 |= dst g1 e1 ~o~> x
                              satisfying (fun x0 : V => P x0 /\ x0 <> root))
                         g2 _ e2) in H18; auto.
                2: intro; destruct H19 as [[_ ?] _]; auto.
                destruct H18; auto.
              * destruct H17 as [? [? ?]].
                assert (out_edges g2 root e1). {
                  clear -H3 H18 H19. destruct H3. subst root. split; auto.
                }              
                assert (dst g2 e1 = dst g3 e1). {
                  apply (EST_the_same_dst _ _ root _ _ e1) in H6; auto.
                  intro. destruct H21 as [[_ ?] _]. auto.
                } rewrite H21 in *.
                assert (~ reachable g2 (dst g3 e1) b). {
                  clear -H17. intro. apply H17.
                  apply reachable_head_valid in H. auto.
                } left.
                apply (EST_not_reachable_derive _ _ _ _ _ _ H6); auto.
                intro. apply reachable_by_foot_valid in H23; auto.
        }
        assert (~ reachable g3 (dst g3 e2) b \/ ~ out_edges g3 root e2). {
          apply (EST_not_reachable
                   (fun x : V =>
                      (P x /\ x <> root) /\
                      ~ g1 |= dst g1 e1 ~o~> x
                        satisfying (fun x0 : V => P x0 /\ x0 <> root))
                   P g2); auto.
          + intro. destruct H14 as [[_ ?] _]; auto.
          + hnf. unfold Ensembles.In . intros. destruct H14 as [[? _] _]; auto.
        }
        assert (forall e, out_edges g3 root e -> In e (e1 :: e2 :: nil)). {
          intros.
          apply
            (EST_reverse_out_edges
               (fun x : V =>
                  (P x /\ x <> root) /\
                  ~ g1 |= dst g1 e1 ~o~> x
                    satisfying (fun x0 : V => P x0 /\ x0 <> root))
               g2 g3 e2 root) in H15; auto.
          2: intro; destruct H16 as [[_ ?] _]; auto.
          apply (EST_reverse_out_edges
                   (fun x : V => P x /\ x <> root) g1 g2 e1 root) in H15; auto.
          2: intro; destruct H16; auto.
          rewrite H0; auto.
        }
        apply root_not_reachable_derive.
        destruct H13, H14; split; auto; intros; pose proof H16; apply H15 in H16;
        destruct H16 as [? | [? | ?]]; auto; subst; auto.
    Qed.

    Lemma spanning_list_spanning_tree: forall (P: V -> Prop) g1 root g2 l,
        NoDup l -> (forall e, In e l <-> out_edges g1 root e) ->
        vvalid g1 root -> P root ->
        spanning_list' (fun x => P x /\ x <> root) g1 l g2 ->
        spanning_tree g1 root P g2.
    Proof.
      intros. remember (fun x : V => P x /\ x <> root) as P0. split; [|split; [|split]]; intros.
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
      + admit.
      + induction H3.
        - rewrite <- H3. apply reachable_by_is_reachable in H4. auto.
        - destruct H5 as [[[? ?] [? [? [? ?]]]] | ?].
          * admit.
          * admit.
      + revert a b H4 H5. induction H3.
        - admit.
        - intros.
    Abort.

  End SIMPLE_SPANNING.
End SIMPLE_SPANNING_TREE.

Existing Instance SIMPLE_SPANNING_TREE.spanning_tree_proper .

(* Module SPANNING_TREE.     *)

Section SPANNING.

  Context {V E: Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.
  Context {DV DE: Type}.
  Context {MGS: MarkGraphSetting DV}.
  Context {P: LabeledGraph V E DV DE -> Type}.
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

  Lemma spanning_tree_marked_equiv: forall (g1 g2: Graph) (root: V),
      ReachDecidable g1 root (unmarked g1) ->
      spanning_tree g1 root g2 ->
      forall x, (marked g1 x \/ g1 |= root ~o~> x satisfying (unmarked g1)) <-> marked g2 x.
  Proof.
    intros; split; intros; destruct H as [[? ?] _].
    + destruct (X x).
      - specialize (H x r). auto.
      - specialize (H1 x n). destruct H0; [rewrite <- H1|]; auto.
    + destruct (X x); [right | left ]; auto.
      specialize (H1 x n). rewrite H1; auto.
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

  Lemma mark1_unmarked_eq: forall (g g1: Graph) root x, mark1 g root g1 -> (unmarked g1 x <-> unmarked g x /\ x <> root).
  Proof.
    intros. destruct H as [? [? [? ?]]]. unfold unmarked. rewrite !negateP_spec. split; intros.
    + split; [rewrite H2; auto|]; intro; subst; auto.
    + destruct H3. rewrite <- H2; auto.
  Qed.

  Inductive spanning_list : Graph -> list E -> Graph -> Prop :=
  | spanning_list_nil: forall (g1 g2 : Graph), g1 ~=~ g2%LabeledGraph -> spanning_list g1 nil g2
  | spanning_list_cons:
      forall g1 g2 g3 e rest, edge_spanning_tree g1 e g2 -> spanning_list g2 rest g3 -> spanning_list g1 (e :: rest) g3.

  Lemma spanning_list_spanning_tree2: forall (g g1 g2 g3: Graph) root (e1 e2 : E),
      (e1 <> e2) -> (forall e, In e (e1 :: e2 :: nil) <-> out_edges g root e) ->
      (forall e, In e (e1 :: e2 :: nil) -> ReachDecidable g1 (dst g1 e) (unmarked g1)) ->
      vvalid g root -> unmarked g root -> mark1 g root g1 ->
      edge_spanning_tree g1 e1 g2 -> edge_spanning_tree g2 e2 g3 ->
      spanning_tree g root g3.
  Proof.
    intros. rewrite edge_spanning_tree_inj in H4, H5. rewrite spanning_tree_inj.
    pose proof H3. destruct H6 as [? _]. rewrite H6. clear H6.
    destruct H4, H5. split; [|split; [|split; [|split]]].
    + admit.
    + destruct H3 as [? [? [? ?]]].
      assert (out_edges g root e1) by (rewrite <- H0; apply in_eq).
      assert (out_edges g1 root e1) by (rewrite <- (out_edges_si g); auto). 
      assert (Included (unmarked g1) (unmarked g)). {
        intro n. unfold Ensembles.In . unfold unmarked. rewrite !negateP_spec.
        intros. rewrite H10; auto. intro; subst. auto.
      }
      assert (vvalid g1 root) by (destruct H3; rewrite <- H3; auto).
      pose proof (SIMPLE_SPANNING_TREE.EST_predicate_partial_si _ _ _ _ _ _ H13 H12 H14 H2 H6).
      rewrite H15.
      assert (X1: ReachDecidable g1 (dst g1 e1) (unmarked g1)) by (apply X, in_eq).
      assert (Included (unmarked g2) (unmarked g)). {
        intro n. unfold Ensembles.In . intros.
        rewrite <- (edge_spanning_tree_unmarked_equiv g1 g2 e1) in H16; auto.
        + apply H13. destruct H16. apply H16.
        + rewrite edge_spanning_tree_inj. auto.
      }
      assert (out_edges g root e2) by (rewrite <- H0; apply in_cons, in_eq).
      assert (out_edges g1 root e2) by (rewrite <- (out_edges_si g); auto).
      assert (~ (unmarked g1) root) by (intro; auto).
      pose proof (SIMPLE_SPANNING_TREE.EST_out_edges _ _ _ _ _ _ H H19 H18 H6).
      assert (vvalid g2 root) by (rewrite <- (SIMPLE_SPANNING_TREE.edge_spanning_tree_vvalid g1 e1 (unmarked g1)); auto).
      pose proof (SIMPLE_SPANNING_TREE.EST_predicate_partial_si _ _ _ _ _ _ H16 H20 H21 H2 H7).
      apply si_stronger_partialgraph_simple with (fun n : V => ~ g2 |= root ~o~> n satisfying (unmarked g)); auto.
      assert (forall x, unmarked g1 x <-> unmarked g x /\ x <> root). {
        intros; rewrite <- (mark1_unmarked_eq g g1); [tauto | split; auto].
      }
      intro n. unfold Ensembles.In . destruct H6 as [[? ?] | [? ?]].
      - assert (spanning_tree g1 (dst g1 e1) g2) by (rewrite spanning_tree_inj; auto).
        pose proof (spanning_tree_unmarked_equiv _ _ _ X1 H25).
        intros. intro; apply H27; clear H27. destruct (X1 n).
        * admit.
        * destruct H4. specialize (H27 n n0). destruct H24 as [? _].
  Abort.  

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
