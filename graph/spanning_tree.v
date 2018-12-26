Require Import Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.EnumEnsembles.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_ind.
Require Import Coq.Logic.Classical.
Require RamifyCoq.graph.weak_mark_lemmas.
Import RamifyCoq.graph.weak_mark_lemmas.WeakMarkGraph.

Module SIMPLE_SPANNING_TREE.

  Section SIMPLE_SPANNING.

    Context {V E: Type}.
    Context {EV: EqDec V eq}.
    Context {EE: EqDec E eq}.

    Notation Graph := (PreGraph V E).

    Instance is_tree_proper : Proper (structurally_identical ==> eq ==> iff) (@is_tree V E EV EE).
    Proof.
      cut (forall (g1 g2: Graph) x y, g1 ~=~ g2 -> x = y -> is_tree g1 x -> is_tree g2 y); intros.
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

    Lemma spanning_tree_vvalid:
      forall (g1 : Graph) (root : V) (P: V -> Prop) (g2 : Graph) x,
        spanning_tree g1 root P g2 -> (vvalid g1 x <-> vvalid g2 x).
    Proof.
      intros. destruct (classic (g1 |= root ~o~> x satisfying P)) as [r | n].
      + destruct H as [? [? [? ?]]]. split; intros.
        - specialize (H1 _ r). apply reachable_foot_valid in H1. auto.
        - apply reachable_by_foot_valid in r. auto.
      + eapply not_reachable_ST_vvalid; eauto.
    Qed.

    Lemma spanning_tree_root_vvalid: forall (g1 : Graph) (root : V) (P: V -> Prop) (g2 : Graph),
        spanning_tree g1 root P g2 -> P root -> vvalid g1 root -> vvalid g2 root.
    Proof.
      intros. destruct H as [_ [_ [? _]]].
      assert (g1 |= root ~o~> root satisfying P) by (apply reachable_by_refl; auto).
      specialize (H _ H2). apply reachable_head_valid in H. auto.
    Qed.

    Lemma edge_spanning_tree_vvalid:
      forall (g1: Graph) e (P: V -> Prop) (g2: Graph) x,
        edge_spanning_tree g1 e P g2 -> (vvalid g1 x <-> vvalid g2 x).
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
        edge_spanning_tree g1 e P g2 -> Included (reachable g1 (src g1 e)) (vvalid g2).
    Proof.
      intros. intro y; unfold Ensembles.In; intros. apply reachable_foot_valid in H0.
      rewrite <- edge_spanning_tree_vvalid; eauto.
    Qed.

    Lemma spanning_tree_not_reachable: forall (g1 : Graph) (root : V) (P: V -> Prop) (g2 : Graph) x y,
        spanning_tree g1 root P g2 -> (~ g1 |= root ~o~> y satisfying P) -> reachable g2 x y ->
        g2 |= x ~o~> y satisfying (Complement _ (reachable_by g1 root P)).
    Proof.
      intros. destruct H as [? [? [? ?]]]. destruct H1 as [p ?]. exists p. assert (valid_path g2 p) by (destruct H1 as [_ [? _]]; auto). split; [|split]; auto.
      + destruct H1; auto.
      + rewrite (path_prop_equiv _ _ _ H5). intro v; intros. unfold Complement. unfold Ensembles.In.
        destruct (reachable_by_path_split_in _ _ _ _ _ _ H1 H6) as [p1 [p2 [? [? ?]]]].
        apply reachable_by_path_is_reachable in H9. intro.
        specialize (H4 _ _ H10 H0). auto.
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
        apply reachable_by_refl; auto.
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
      apply edge_reachable_by with (dst g1 e); auto. destruct H0. split; auto. split.
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

    Lemma gremove_not_reachable_by_derive:
      forall (g1 : Graph) (e : E) (g2 : Graph) (x y : V) (p: path) (P: V -> Prop),
        gremove_edge g1 e g2 ->
        g2 |= p is x ~o~> y satisfying P ->
        g1 |= p is x ~o~> y satisfying P.
    Proof.
      intros. destruct H as [? [? [? [? ?]]]]. destruct H0 as [[? ?] [? ?]].
      assert (forall e', In e' (snd p) -> e' <> e). {
        repeat intro. subst.
        destruct H4 as [? | [? _]]; apply H0; destruct p as [v p]; pose proof (valid_path_strong_evalid _ _ _ e H6 H8); destruct H4 as [? [? ?]]; auto.
      }
      assert (Hv: valid_path g1 p). {
        clear H0 H5 H7. destruct p as [v p]. simpl in H8. revert v H6 H8. induction p; intros.
        + simpl in H6 |-* . rewrite H; auto.
        + rewrite valid_path_cons_iff in H6 |-* . destruct H6 as [? [? ?]]. destruct H5 as [? [? ?]]. unfold strong_evalid.
          assert (a <> e) by (apply H8, in_eq). specialize (H1 _ H10); specialize (H2 _ H10); specialize (H3 _ H10).
          assert (src g1 a = src g2 a) by (apply H2; intuition). assert (dst g1 a = dst g2 a) by (apply H3; intuition). rewrite H11, H12.
          subst v. rewrite !H. do 2 (split; [intuition |]). apply IHp; auto. intros. apply H8. right; auto.
      } split; split; auto.
      + rewrite pfoot_spec in H5 |-* . destruct H5; [left; auto | right].
        destruct H5 as [v [l [e' [? ?]]]]. exists v, l, e'. split; auto. rewrite <- H9.
        assert (In e' (l +:: e')) by (apply in_or_app; right; apply in_eq). subst p. unfold snd in H8. specialize (H8 _ H10).
        assert (strong_evalid g2 e') by (apply (valid_path_strong_evalid _ v (l +:: e')); auto). destruct H5 as [? [? ?]].
        specialize (H1 _ H8). specialize (H3 _ H8). apply H3; intuition.
      + rewrite path_prop_equiv in H7 |-* ; auto. intros. apply H7. unfold In_path in H9 |-* . destruct H9; [left | right]; auto.
        destruct H9 as [e' [? ?]]. exists e'. split; auto. specialize (H8 _ H9). specialize (H1 _ H8). specialize (H2 _ H8). specialize (H3 _ H8).
        assert (strong_evalid g2 e') by (destruct p as [v p]; apply (valid_path_strong_evalid _ v p); auto). destruct H11 as [? _].
        assert (src g1 e' = src g2 e') by (apply H2; intuition). assert (dst g1 e' = dst g2 e') by (apply H3; intuition). rewrite <- H12, <- H13; auto.
    Qed.

    Lemma gremove_reachable_by_derive: forall (g1 : Graph) (e : E) (g2 : Graph) (x y : V) (p: path) (P: V -> Prop),
        gremove_edge g1 e g2 -> (forall e', In e' (snd p) -> e' <> e) -> g1 |= p is x ~o~> y satisfying P -> g2 |= p is x ~o~> y satisfying P.
    Proof.
      intros. destruct H as [? [? [? [? ?]]]]. destruct H1 as [[? ?] [? ?]].
      assert (valid_path g2 p). {
        clear H1 H6 H8. destruct p as [v p]. simpl in H0. revert v H0 H7. induction p; intros.
        + simpl in H7 |-* . rewrite <- H; auto.
        + rewrite valid_path_cons_iff in H7 |-* . destruct H7 as [? [? ?]]. destruct H6 as [? [? ?]]. unfold strong_evalid.
          assert (a <> e) by (apply H0, in_eq). specialize (H2 _ H10). specialize (H3 _ H10). specialize (H4 _ H10).
          assert (src g1 a = src g2 a) by (apply H3; intuition). assert (dst g1 a = dst g2 a) by (apply H4; intuition).
          rewrite <- H11, <- H12. subst v. rewrite <- !H. do 2 (split; [intuition |]). apply IHp; auto. intros; apply H0; right; auto.
      } split; split; auto.
      + rewrite pfoot_spec in H6 |-* . destruct H6; [left; auto | right]. destruct H6 as [v [l [e' [? ?]]]].
        exists v, l, e'. split; auto. rewrite <- H10. symmetry.
        assert (In e' (l +:: e')) by (apply in_or_app; right; apply in_eq). subst p. unfold snd in H0. specialize (H0 _ H11).
        assert (strong_evalid g1 e') by (apply (valid_path_strong_evalid _ v (l +:: e')); auto). destruct H6 as [? [? ?]].
        specialize (H2 _ H0). specialize (H4 _ H0). apply H4; intuition.
      + rewrite path_prop_equiv in H8 |-* ; auto. intros. apply H8. unfold In_path in H10 |-* . destruct H10; [left | right]; auto.
        destruct H10 as [e' [? ?]]. exists e'. split; auto. specialize (H0 _ H10). specialize (H2 _ H0). specialize (H3 _ H0). specialize (H4 _ H0).
        assert (strong_evalid g1 e') by (destruct p as [v p]; apply (valid_path_strong_evalid _ v p); auto). destruct H12 as [? _].
        assert (src g1 e' = src g2 e') by (apply H3; intuition). assert (dst g1 e' = dst g2 e') by (apply H4; intuition). rewrite H13, H14; auto.
    Qed.

    Lemma gremove_root_reachable_by_equiv: forall (g1 g2: Graph) (e: E) (root: V) (P: V -> Prop),
        out_edges g1 root e -> gremove_edge g1 e g2 ->
        (~ (P (dst g1 e) /\ dst g1 e <> root)) ->
        forall n, (g1 |= root ~o~> n satisfying P <-> g2 |= root ~o~> n satisfying P).
    Proof.
      intros. split; intros; destruct H. 
      + rewrite reachable_acyclic in H2. destruct H2 as [p [? ?]]. exists p. apply (gremove_reachable_by_derive g1 e); auto.
        intros. destruct p as [v p]. simpl in H5. intro. subst. apply H1. clear H1. destruct H4 as [[? ?] [? ?]]. split.
        - rewrite (path_prop_equiv _ _ _ H4) in H6. apply H6. right. exists e. simpl. split; auto.
        - cut (src g1 e <> dst g1 e). intuition. apply NoDup_epath_to_vpath_edge with (v, p); auto.
      + destruct H2 as [p ?]. exists p. apply (gremove_not_reachable_by_derive _ e g2); auto.
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
        apply edge_reachable_by with (dst g1 e); auto.
        apply reachable_by_head_valid in H4. do 2 (split; auto).
        rewrite step_spec. destruct H. exists e; auto.
      + destruct H3 as [p ?].
        assert (forall v, In_path g2 v p -> ~ g1 |= dst g1 e ~o~> v satisfying (fun x0 : V => P x0 /\ x0 <> root)). {
          intros. intro. destruct H2 as [_ [_ [_ ?]]]. specialize (H2 v x H5 n).
          apply H2. apply (reachable_path_in' g2 p root); auto.
          clear -H3. destruct H3 as [? [? ?]]. do 2 (split; auto).
          rewrite path_prop_equiv; auto.
        } exists p. destruct H2 as [? _]. symmetry in H2.
        apply (ppg_reachable_by_path_to g2 g1 _ _ p root x H2 H4); auto.
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
            1: {
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
            }
            1: {
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
        ~ g1 |= root ~o~> y satisfying P ->
        reachable g2 x y -> reachable g1 x y.
    Proof.
      intros. apply (spanning_tree_not_reachable _ _ _ _ _ _ H) in H1; auto.
      unfold Complement in H1. unfold Ensembles.In in H1.
      destruct H1 as [p ?].
      assert (forall v, In_path g2 v p -> ~ g1 |= root ~o~> v satisfying P). {
        intros. pose proof (reachable_by_path_in _ _ _ _ _ H1 v H2).
        apply reachable_by_foot_prop in H3. auto.
      } destruct H. symmetry in H.
      apply (ppg_reachable_by_path_to g2 g1 _ _ _ _ _ H) in H1; eauto.
      apply reachable_by_path_is_reachable_by in H1.
      revert H1. apply reachable_by_weaken.
      hnf; unfold Ensembles.In ; intros; auto.
    Qed.

    Lemma spanning_tree_not_edge_derive:
      forall (g1 : Graph) (root : V) (P : V -> Prop) (g2 : Graph) (x y : V),
        spanning_tree g1 root P g2 ->
        ~ g1 |= root ~o~> x satisfying P ->
        g2 |= x ~> y -> g1 |= x ~> y.
    Proof.
      intros. destruct H1 as [? [? ?]]. hnf.
      split; [|split]; [rewrite spanning_tree_vvalid; eauto ..|].
      rewrite step_spec in H3 |-* . destruct H3 as [e [? [? ?]]].
      destruct H as [? _]. hnf in H. simpl in H.
      unfold predicate_weak_evalid in H. destruct H as [_ [? [? ?]]].
      specialize (H e). specialize (H6 e). specialize (H7 e). rewrite <- H4 in *.
      assert (evalid g2 e /\ ~ g1 |= root ~o~> src g2 e satisfying P) by intuition.
      subst y. exists e. intuition.
    Qed.

    Lemma gremove_not_edge_derive:
      forall (g1 : Graph) (e : E) (g2 : Graph) (x y : V),
        gremove_edge g1 e g2 -> g2 |= x ~> y -> g1 |= x ~> y.
    Proof.
      intros. destruct H0 as [? [? ?]]. destruct H as [? [? [? [? ?]]]].
      split; [|split]; [rewrite H; auto..|].
      rewrite step_spec in H2 |-* . destruct H2 as [e' [? [? ?]]]. exists e'.
      assert (e' <> e). {
        intro. subst e'. destruct H6; auto.
        destruct H6 as [? [? ?]]. subst y. auto.
      } specialize (H3 _ H9). specialize (H4 _ H9). specialize (H5 _ H9).
      subst x y. intuition.
    Qed.

    Lemma gremove_not_reachable_derive:
      forall (g1 : Graph) (e : E) (g2 : Graph) (x y : V),
        gremove_edge g1 e g2 -> ~ reachable g1 x y -> ~ reachable g2 x y.
    Proof.
      intros. intro. apply H0; clear H0.
      destruct H1 as [p ?]. exists p.
      apply (gremove_not_reachable_by_derive _ e g2); auto.
    Qed.

    Lemma EST_not_edge_derive:
      forall (g1 : Graph) (e : E) (P : V -> Prop) (g2 : Graph) (x y : V),
        edge_spanning_tree g1 e P g2 ->
        ~ g1 |= dst g1 e ~o~> x satisfying P ->
        g2 |= x ~> y -> g1 |= x ~> y.
    Proof.
      intros. destruct H as [[? ?] | [? ?]].
      + apply (spanning_tree_not_edge_derive _ (dst g1 e) P g2); auto.
      + apply (gremove_not_edge_derive _ e g2); auto.
    Qed.

    Lemma EST_not_reachable_derive:
      forall (g1 : Graph) (e : E) (P : V -> Prop) (g2 : Graph) (x y : V),
        edge_spanning_tree g1 e P g2 ->
        ~ g1 |= dst g1 e ~o~> y satisfying P ->
        ~ reachable g1 x y -> ~ reachable g2 x y.
    Proof.
      intros. destruct H as [[? ?] | [? ?]].
      + intro. apply H1.
        apply (spanning_tree_not_reachable_derive g1 (dst g1 e) P g2 x y); auto.
      + apply (gremove_not_reachable_derive g1 e g2 x y); auto.
    Qed.

    Lemma EST_not_reachable: forall (P Q: V -> Prop) g1 root g2 (e: E) n,
        ~ P root -> Q root -> vvalid g1 root -> Included P Q ->
        out_edges g1 root e -> edge_spanning_tree g1 e P g2 ->
        ~ g1 |= dst g1 e ~o~> n satisfying P ->
        (~ reachable g2 (dst g2 e) n \/ ~ out_edges g2 root e).
    Proof.
      intros. destruct (classic (g1 |= dst g1 e ~o~> dst g1 e satisfying P)).
      + destruct H4 as [[? ?] | [? ?]].
        2: apply reachable_by_head_prop in H6; exfalso; auto.
        destruct H7 as [? [_ [_ ?]]]. specialize (H8 _ _ H6 H5).
        assert (out_edges g2 root e) by (rewrite <- (ppg_out_edges P g1); eauto).
        assert (dst g1 e = dst g2 e)
          by (apply (ppg_the_same_dst _ _ root _ _ e H) in H7; auto).
        rewrite H10 in *. left; auto.
      + destruct H4 as [[? ?] | [? ?]].
        - assert (~ vvalid g1 (dst g1 e)). {
            intro. apply H6. apply reachable_by_refl; auto.
          } pose proof H7. destruct H7 as [? _].
          assert (dst g1 e = dst g2 e)
            by (apply (ppg_the_same_dst _ _ root g2 _ e) in H7; auto).
          rewrite H10 in *. left.
          assert (out_edges g2 root e) by (rewrite <- (ppg_out_edges P g1); eauto).
          assert (~ reachable g1 (dst g2 e) n)
            by (intro; apply reachable_by_head_valid in H12; auto).
          intro; apply H12.
          apply (spanning_tree_not_reachable_derive g1 _ _ g2 _ _ H9); auto.
        - destruct H7 as [? [? [? [? ?]]]]. destruct H11.
          * right. intro. apply H11. destruct H12; auto.
          * destruct H11 as [? [? ?]].
            left; intro. apply H11. apply reachable_by_head_valid in H14; auto.
    Qed.

    Lemma ST2_not_reachable: forall (P Q: V -> Prop) g1 root g2 g3 (e1 e2: E) n,
        e1 <> e2 -> ~ P root -> Q root -> vvalid g1 root -> Included P Q ->
        out_edges g1 root e1 -> out_edges g1 root e2 ->
        edge_spanning_tree g1 e1 P g2 ->
        ReachDecidable g1 (dst g1 e1) P ->
        ~ g1 |= (dst g1 e1) ~o~> n satisfying P ->
        edge_spanning_tree g2 e2 (fun x : V =>
                                    P x /\ ~ g1 |= dst g1 e1 ~o~> x
                                             satisfying P) g3 ->
        ~ g2 |= dst g2 e2 ~o~> n
          satisfying (fun x : V => P x /\
                                   ~ g1 |= dst g1 e1 ~o~> x satisfying P) ->
        (~ reachable g3 (dst g3 e1) n \/ ~ out_edges g3 root e1).
    Proof.
      intros.
      assert (vvalid g2 root)
        by (rewrite <- (edge_spanning_tree_vvalid g1 e1 P); auto).
      assert (out_edges g2 root e2) by
          (apply (EST_out_edges P g1 _ _ e1); intuition).
      destruct (X (dst g1 e1)); destruct H6 as [[? ?] | [? ?]].
      + destruct H12 as [? [_ [_ ?]]]. specialize (H13 _ _ r H7).
        assert (out_edges g2 root e1) by (rewrite <- (ppg_out_edges P g1); eauto).
        assert (dst g1 e1 = dst g2 e1)
          by (apply (ppg_the_same_dst _ _ root) with (e := e1) in H12; auto).
        rewrite H15 in *.
        assert (dst g2 e1 = dst g3 e1). {
          apply (EST_the_same_dst _ _ root _ _ e1) in H8; auto.
          intro. destruct H16 as [? _]. auto.
        } rewrite H16 in *. left.
        apply (EST_not_reachable_derive _ _ _ _ _ _ H8); auto.
      + apply reachable_by_head_prop in r; exfalso; auto.
      + assert (~ vvalid g1 (dst g1 e1)). {
          intro. apply n0. apply reachable_by_refl; auto.
        } pose proof H12. destruct H12 as [? _].
        assert (dst g1 e1 = dst g2 e1)
          by (apply (ppg_the_same_dst _ _ root) with (e := e1) in H12; auto).
        rewrite H15 in *.
        assert (out_edges g2 root e1) by (rewrite <- (ppg_out_edges P g1); eauto).
        assert (dst g2 e1 = dst g3 e1). {
          apply (EST_the_same_dst _ _ root _ _ e1) in H8; auto.
          intro. destruct H17 as [? _]. auto.
        } rewrite H17 in *.
        assert (~ vvalid g2 (dst g3 e1))
          by (rewrite <- (not_reachable_ST_vvalid
                            g1 (dst g3 e1) P); auto). left.
        apply not_reachable_EST_vvalid with (x := (dst g3 e1)) in H8; auto.
        2: intro; apply reachable_by_foot_valid in H19; auto.
        rewrite H8 in H18. intro. apply H18.
        apply reachable_by_head_valid in H19. auto.
      + destruct H12 as [? [? [? [? ?]]]]. destruct H16.
        - right. intro. apply H16.
          apply (EST_reverse_out_edges
                   (fun x : V =>
                      P x /\
                      ~ g1 |= dst g1 e1 ~o~> x
                        satisfying P) g2 _ e2) in H17; auto.
          2: intro; destruct H18 as [? _]; auto.
          destruct H17; auto.
        - destruct H16 as [? [? ?]].
          assert (out_edges g2 root e1). {
            clear -H4 H17 H18. destruct H4. subst root. split; auto.
          }
          assert (dst g2 e1 = dst g3 e1). {
            apply (EST_the_same_dst _ _ root _ _ e1) in H8; auto.
            intro. destruct H20 as [? _]. auto.
          } rewrite H20 in *.
          assert (~ reachable g2 (dst g3 e1) n). {
            clear -H16. intro. apply H16.
            apply reachable_head_valid in H. auto.
          } left.
          apply (EST_not_reachable_derive _ _ _ _ _ _ H8); auto.
    Qed.

    Lemma list_first_prop: forall {A} (n : A) (l : list A) (s : A) (P: A -> Prop),
        P n -> ~ P s -> In s l -> exists l1 l2 n1 n2, P n1 /\ ~ P n2 /\
                                                      n :: l = l1 ++ n1 :: n2 :: l2.
    Proof.
      intros. revert n H. induction l. inversion H1. simpl in H1. intros. destruct H1.
      + subst a. exists nil, l, n, s. split; auto.
      + destruct (classic (P a)).
        - specialize (IHl H1 a H2). destruct IHl as [l1 [l2 [n1 [n2 [? [? ?]]]]]].
          exists (n :: l1), l2, n1, n2. do 2 (split; auto).
          rewrite H5. rewrite <- app_comm_cons. auto.
        - exists nil, l, n, a. split; auto.
    Qed.

    Lemma not_sat_edge: forall (g: Graph) s v p (P: V -> Prop), valid_path g (s, p) -> In_path g v (s, p) -> P s -> ~ P v
                                                                -> exists e, In e p /\ P (src g e) /\ ~ P (dst g e).
    Proof.
      intros g s v p. revert s v. induction p; intros. 1: destruct H0 as [? | [e [? _]]]; simpl in H0; exfalso; [subst| ]; auto.
      rewrite in_path_or_cons in H0. 2: destruct H; auto. destruct H0. 1: subst; exfalso; auto. destruct (classic (P (dst g a))).
      + apply valid_path_cons in H. specialize (IHp _ _ _ H H0 H3 H2). destruct IHp as [e [? ?]]. exists e; split; auto. right; auto.
      + exists a. destruct H. subst s. split; auto. left; auto.
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
      destruct_eq_dec n root. 1: subst; apply reachable_by_refl; auto.
      destruct (X n).
      + destruct H5 as [[? ?] | [? ?]].
        2: apply reachable_by_head_prop in r; exfalso; apply H5; auto.
        destruct H12 as [? [_ [? ?]]]. specialize (H13 _ r).
        assert (vvalid g2 (dst g1 e1)) by
            (apply reachable_by_head_valid in H13; auto).
        destruct H13 as [p ?].
        assert (forall v, In_path g2 v p -> g1 |= dst g1 e1 ~o~> v satisfying
                                             (fun x : V => P x /\ x <> root)). {
          intros. destruct (X v); auto.
          pose proof (reachable_path_in _ _ _ _ H13 _ H16).
          assert (g1 |= dst g1 e1 ~o~> dst g1 e1 satisfying
                     (fun x : V => P x /\ x <> root)). {
            apply reachable_by_refl; auto.
            apply reachable_by_head_valid in r; auto.
          }
          specialize (H14 _ _ H18 n0). exfalso; auto.
        }
        assert (Hd: dst g1 e1 = dst g2 e1) by (eapply ppg_the_same_dst in H12; eauto; intro; destruct H17; apply H18; auto).
        assert (g2 |= path_glue (root, e1 :: nil) p is root ~o~> n satisfying (fun _ : V => True)). {
          apply reachable_by_path_merge with (dst g1 e1); auto.
          split; split; simpl; auto.
          + pose proof H3. rewrite (ppg_out_edges (fun x : V => P x /\ x <> root)) in H17; eauto.
            2: intro; destruct H18; auto. destruct H17. unfold strong_evalid. rewrite H18, <- Hd.
            do 3 (split; auto).
          + hnf; rewrite Forall_forall; intros; auto.
        } exists (path_glue (root, e1 :: nil) p). destruct H6 as [[? ?] | [? ?]].
        - destruct H18 as [? _]. apply (ppg_reachable_by_path_to g2 g3 _ _ _ _ _ H18); auto. intros.
          assert (v = root \/ In_path g2 v p). {
            destruct H13 as [[? _] _]. destruct p as [v' p]. unfold path_glue in *. simpl in *.
            destruct H17 as [_ [[? ?] _]]. subst v'. rewrite in_path_or_cons in H19; auto. rewrite Hd. auto.
          }
          clear H19; rename H20 into H19.
          destruct H19; intro; [subst | apply H16 in H19]; apply reachable_by_foot_prop in H20; destruct H20 as [[? ?] ?]; auto.
        - apply (gremove_reachable_by_derive g2 e2 g3); auto. destruct p as [v p]. simpl. intros. destruct H19. 1: subst e'; auto.
          intro. subst. assert (In_path g2 (src g2 e2) (v, p)) by (right; exists e2; simpl; split; auto).
          specialize (H16 _ H20). apply reachable_by_foot_prop in H16. destruct H8. subst root. destruct H16; auto.
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
          rewrite path_prop_equiv in H14 |-* ; auto.
          intros. split. apply H14; auto. intro. apply n0.
          specialize (H12 _ H15). apply reachable_by_trans with n1; auto.
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
        apply edge_reachable_by with (dst g3 e2); auto.
        - split; auto; split.
          2: rewrite step_spec; exists e2; destruct H15; auto.
          rewrite <- H16.
          apply reachable_by_head_valid in H9.
          apply edge_spanning_tree_vvalid with (x := dst g2 e2) in H5; auto.
          rewrite H5 in H9.
          apply (spanning_tree_root_vvalid _ _ _ _ H14); auto.
        - destruct H14 as [_ [_ [? _]]]. rewrite <- H16. apply H14.
          destruct H5 as [[? ?] | [? ?]].
          1: {
            destruct H17 as [? _]. destruct H9 as [p ?]. exists p.
            eapply (ppg_reachable_by_path_to g1 g2); eauto.
            intros. simpl. destruct H9 as [_ [? ?]].
            rewrite path_prop_equiv in H19; auto. 
            specialize (H19 _ H18). destruct H19; auto.
          }
          1: {
            destruct H9 as [p ?]. exists p. apply (gremove_reachable_by_derive g1 e1 g2); auto.
            repeat intro. subst. destruct H9 as [_ [? ?]]. rewrite path_prop_equiv in H19; auto.
            assert (In_path g1 (src g1 e1) p) by (right; exists e1; split; auto). specialize (H19 _ H20).
            destruct H19 as [[_ ?] _]. destruct H3. subst root. auto.
          }
    Qed.

    Lemma spanning_bi_tree: forall (P: V -> Prop) g1 root g2 g3 (e1 e2 : E),
        (e1 <> e2) -> (forall e, In e (e1 :: e2 :: nil) <-> out_edges g1 root e) ->
        vvalid g1 root -> P root ->
        ReachDecidable g1 (dst g1 e1) (fun x => P x /\ x <> root) ->
        edge_spanning_tree g1 e1 (fun x : V => P x /\ x <> root) g2 ->
        edge_spanning_tree g2 e2
                           (fun x : V =>
                              (P x /\ x <> root) /\
                              ~ g1 |= dst g1 e1 ~o~> x
                                satisfying (fun x0 : V => P x0 /\ x0 <> root)) g3 ->
        spanning_tree g1 root P g3.
    Proof.
      intros. rename H3 into H5. rename H4 into H6.
      assert (out_edges g1 root e1) by (rewrite <- H0; apply in_eq).
      assert (out_edges g1 root e2) by (rewrite <- H0; apply in_cons, in_eq).
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
      + rewrite is_tree_ppg_spec. intros.
        pose proof H10. destruct H11 as [p ?].
        exists p. unfold unique. split; auto. intros.
        destruct x' as [v x']. assert (v = root) by (destruct H12 as [[? _] _]; simpl in H12; inversion H12; auto). subst v.
        destruct p as [v p]. assert (v = root) by (destruct H11 as [[? _] _]; simpl in H11; inversion H11; auto). subst v.
        assert (forall e path, ~ g3 |= (root, e :: path) is root ~o~> root
                                 satisfying (reachable_by g1 root P)). {
          intros. intro. pose proof H13. destruct H14 as [_ [[? ?] _]].
          assert (strong_evalid g3 e) by (simpl in H15; destruct path; intuition). destruct H16 as [? [? ?]].
          assert (out_edges g1 root e). {
              apply (EST_reverse_out_edges
                       (fun x : V => P x /\ x <> root) g1 g2 e1); auto.
              intro. destruct H19; auto.
              apply (EST_reverse_out_edges
                       (fun x : V =>
                          (P x /\ x <> root) /\
                          ~ g1 |= dst g1 e1 ~o~> x
                            satisfying
                            (fun x0 : V => P x0 /\ x0 <> root)) g2 g3 e2); auto.
              intro. destruct H19 as [[_ ?] _]; auto.
              split; auto.
            } rewrite <- H0 in H19. simpl in H19.
          destruct H19 as [? | [? | ?]]; auto; subst e.
          + assert (~ reachable g3 (dst g3 e1) root \/ ~ out_edges g3 root e1). {
              apply (ST2_not_reachable
                       (fun x : V => P x /\ x <> root) P g1 _ g2 _ _ e2); auto.
              + intro. destruct H19; auto.
              + compute. tauto.
              + intro. apply reachable_by_foot_prop in H19. destruct H19; auto.
              + intro. apply reachable_by_foot_prop in H19. destruct H19 as [[_ ?] _]; auto.
            } destruct H19.
            - apply H19. exists (dst g3 e1, path). destruct H13 as [[_ ?] [? _]].
              split; split; auto.
              * rewrite pfoot_cons in H13; auto.
              * clear -H15. simpl in *. destruct path. 1: hnf in H15; intuition. destruct H15; auto.
              * hnf. destruct path; simpl; auto. hnf. rewrite Forall_forall. intros; auto.
            - apply H19. split; auto.
          + assert (~ reachable g3 (dst g3 e2) root \/ ~ out_edges g3 root e2). {
              apply (EST_not_reachable
                       (fun x : V =>
                          (P x /\ x <> root) /\
                          ~ g1 |= dst g1 e1 ~o~> x
                            satisfying (fun x0 : V => P x0 /\ x0 <> root))
                       P g2); auto.
              + intro. destruct H19 as [[_ ?] _]; auto.
              + hnf. unfold Ensembles.In . intuition.
              + intro. apply reachable_by_foot_prop in H19. destruct H19 as [[_ ?] _]; auto.
            } destruct H19.
            - apply H19. exists (dst g3 e2, path). clear -H13.
              destruct H13 as [[? ?] [? ?]]. split; split; auto.
              * rewrite pfoot_cons in H0; auto.
              * apply valid_path_cons in H1; auto.
              * hnf. rewrite Forall_forall. split; intros; auto.
            - apply H19. split; auto.
        }
        destruct x'; destruct p; auto.
        - destruct H12 as [[_ ?] _]. simpl in H12. inversion H12. subst y. exfalso. specialize (H13 e p). auto.
        - destruct H11 as [[_ ?] _]. simpl in H11. inversion H11. subst y. exfalso. specialize (H13 e x'). auto.
        - clear H13.
          assert (forall m ms, g3 |= (root, m :: ms) is root ~o~> y
                                  satisfying (reachable_by g1 root P) ->
                               g3 |= (dst g3 m, ms) is dst g3 m ~o~> y
                                  satisfying (reachable_by g1 root P)). {
            intros. clear -H13. destruct H13 as [[_ ?] [? ?]]. assert (valid_path g3 (dst g3 m, ms)) by (apply valid_path_cons in H0; auto).
            split; split; auto.
            + rewrite pfoot_cons in H; auto.
            + rewrite path_prop_equiv in H1 |-* ; auto. intros. apply H1. rewrite in_path_or_cons.
              2: destruct H0; auto. right; auto.
          }
          assert (forall e, evalid g3 e -> src g3 e = root -> out_edges g2 root e). {
            intros.
            apply (EST_reverse_out_edges
                     (fun x : V =>
                        (P x /\ x <> root) /\
                        ~ g1 |= dst g1 e1 ~o~> x
                          satisfying
                          (fun x0 : V => P x0 /\ x0 <> root)) g2 g3 e2); auto.
            intro. destruct H16 as [[_ ?] _]; auto. split; auto.
          }
          assert (forall e, evalid g3 e -> src g3 e = root -> out_edges g1 root e). {
            intros.
            apply (EST_reverse_out_edges
                     (fun x : V => P x /\ x <> root) g1 g2 e1); auto.
            intro. destruct H17; auto.
          }
          assert (evalid g3 e1 -> src g3 e1 = root ->
                  vvalid g3 (dst g3 e1) -> (P (dst g1 e1) /\ dst g1 e1 <> root) /\
                                           dst g1 e1 = dst g2 e1 /\
                                           dst g2 e1 = dst g3 e1). {
            intros. clear H11 H12 H13. destruct H5 as [[? ?] | [? ?]].
            + split; auto. destruct H11 as [? [? [? ?]]].
              assert (dst g1 e1 = dst g2 e1). {
                apply (ppg_the_same_dst _ _ root _ _ e1) in H11; auto.
                intro. destruct H20. auto.
              } rewrite H20 in *.
              assert (out_edges g2 root e1). {
                rewrite <- (ppg_out_edges (fun x : V => P x /\ x <> root) g1); eauto.
                intro. destruct H21. auto.
              }
              assert (dst g2 e1 = dst g3 e1). {
                apply (EST_the_same_dst _ _ root _ _ e1) in H6; auto.
                intro. destruct H22 as [[_ ?] _]. auto.
              } rewrite H22 in *. auto.
            + exfalso. specialize (H14 _ H16 H17). destruct H14.
              destruct H11 as [? [? [? [? ?]]]]. destruct H21; auto.
              destruct H21 as [? [? ?]]. pose proof H6.
              apply (EST_the_same_dst _ _ root _ _ e1) in H24; auto.
              - rewrite H24 in *.
                apply (edge_spanning_tree_vvalid _ _ _ _ (dst g3 e1)) in H6.
                rewrite <- H6 in H18. auto.
              - intro. destruct H25 as [[_ ?] _]; auto.
              - split; auto.
          }
          assert (evalid g3 e2 -> src g3 e2 = root ->
                  vvalid g3 (dst g3 e2) ->
                  ((P (dst g2 e2) /\ dst g2 e2 <> root) /\
                   ~ g1 |= dst g1 e1 ~o~> dst g2 e2
                     satisfying (fun x0 : V => P x0 /\ x0 <> root)) /\
                  dst g2 e2 = dst g3 e2). {
            intros. clear H11 H12 H13. destruct H6 as [[? ?] | [? ?]].
            + split; auto. destruct H11 as [? _].
              apply (ppg_the_same_dst _ _ root _ _ e2) in H11; auto.
              intro. destruct H12 as [[_ ?] _]. auto.
            + exfalso. specialize (H14 _ H17 H18). destruct H14.
              destruct H11 as [? [? [? [? ?]]]]. destruct H22 as [? | [? _]]; auto.
          }
          assert (forall ms, evalid g3 e1 -> src g3 e1 = root ->
                             vvalid g3 (dst g3 e1) ->
                             g3 |= (dst g3 e1, ms) is dst g3 e1 ~o~> y
                                satisfying (reachable_by g1 root P) ->
                             g2 |= (dst g3 e1, ms) is dst g3 e1 ~o~> y
                                satisfying
                                (reachable_by g1 (dst g3 e1)
                                              (fun x : V => P x /\ x <> root))). {
            clear H11 H12 H13 H17. intros. specialize (H16 H11 H12 H13).
            pose proof H5. destruct H16 as [? [? ?]]. destruct H5 as [[_ ?] | [? ?]].
            2: exfalso; auto. destruct H5 as [? [? [? ?]]].
            rewrite H19 in *. rewrite H20 in *.
            assert (g1 |= dst g3 e1 ~o~> dst g3 e1
                         satisfying (fun x : V => P x /\ x <> root)). {
              apply reachable_by_refl; auto.
              rewrite <- (edge_spanning_tree_vvalid _ _ _ _ _ H6) in H13.
              rewrite <- (edge_spanning_tree_vvalid _ _ _ _ _ H18) in H13.
              auto.
            }
            assert (forall v, In_path g3 v (dst g3 e1, ms) ->
                              g1 |= dst g3 e1 ~o~> v
                                 satisfying (fun x : V => P x /\ x <> root)). {
              intros. destruct (X v); auto. destruct H17 as [? [? ?]].
              pose proof (not_sat_edge _ _ _ _ (reachable_by g1 (dst g3 e1) (fun x : V => P x /\ x <> root)) H26 H25 H24 n).
              destruct H28 as [e3 [? [? ?]]]. specialize (H23 _ _ H29 H30). 
              assert (strong_evalid g3 e3) by (apply (valid_path_strong_evalid _ (dst g3 e1) ms); auto).
              assert (g3 |= src g3 e3 ~> (dst g3 e3)) by (destruct H31 as [? [? ?]]; hnf; do 2 (split; auto); rewrite step_spec; exists e3; split; auto).
              apply (EST_not_edge_derive _ _ _ _ _ _ H6) in H32. 2: intro; apply reachable_by_foot_prop in H33; destruct H33; auto.
              clear -H32 H23. exfalso. apply H23. apply edge_reachable_by with (dst g3 e3); auto.
              apply reachable_by_refl; auto. destruct H32 as [? [? ?]]. auto.
            }
            assert (g3 |= (dst g3 e1, ms) is dst g3 e1 ~o~> y
                       satisfying
                       (reachable_by g1 (dst g3 e1)
                                     (fun x : V => P x /\ x <> root))). {
              destruct H17 as [[? ?] [? ?]]. split; split; auto.
              rewrite path_prop_equiv; auto.
            } destruct H6 as [[? ?] | [? ?]].
            + destruct H27.
              apply (ppg_reachable_by_path_to
                       g3 g2
                       (fun n : V =>
                         ~ g2 |= dst g2 e2 ~o~> n
                           satisfying
                           (fun x : V =>
                              (P x /\ x <> root) /\
                              ~ g1 |= dst g3 e1 ~o~> x
                                satisfying
                                (fun x0 : V => P x0 /\ x0 <> root)))) in H26; [|symmetry|]; auto.
                  intros. specialize (H25 _ H29). intro.
                  apply reachable_by_foot_prop in H30. destruct H30; auto.
            + apply (gremove_not_reachable_by_derive _ e2 g3); auto.
          }
          assert
          (forall ms,
              evalid g3 e2 -> src g3 e2 = root -> vvalid g3 (dst g3 e2) ->
              g3 |= (dst g3 e2, ms) is dst g3 e2 ~o~> y
                 satisfying (reachable_by g1 root P) ->
              g3 |= (dst g3 e2, ms) is dst g2 e2 ~o~> y
                 satisfying (
                   reachable_by g2 (dst g2 e2)
                                (fun x : V =>
                                   (P x /\ x <> root) /\
                                   ~ g1 |= dst g1 e1 ~o~> x
                                     satisfying (fun x0 : V => P x0 /\
                                                               x0 <> root)))). {
            clear H11 H12 H13 H16 H18. intros. specialize (H17 H11 H12 H13).
            destruct H17. destruct H6 as [[_ ?] | [? _]]. 2: exfalso; auto.
            pose proof H6. destruct H6 as [? [? [? ?]]]. rewrite H18 in *.
            assert (g2 |= dst g3 e2 ~o~> dst g3 e2
                       satisfying
                       (fun x : V =>
                          (P x /\ x <> root) /\
                          ~ g1 |= dst g1 e1 ~o~> x
                            satisfying (fun x0 : V => P x0 /\ x0 <> root))). {
              apply reachable_by_refl; auto.
              rewrite <- (spanning_tree_vvalid _ _ _ _ _ H19) in H13. auto.
            }
            assert (forall v,
                       In_path g3 v (dst g3 e2, ms) ->
                       (g2 |= dst g3 e2 ~o~> v
                           satisfying
                           (fun x : V =>
                              (P x /\ x <> root) /\
                              ~ g1 |= dst g1 e1 ~o~> x
                                satisfying (fun x0 : V => P x0 /\ x0 <> root)))). {
              intros.
              destruct (classic (g2 |= dst g3 e2 ~o~> v satisfying
                                    (fun x : V => (P x /\ x <> root) /\ ~ g1 |= dst g1 e1 ~o~> x satisfying (fun x0 : V => P x0 /\ x0 <> root)))); auto.
              destruct H16 as [? [? ?]].
              pose proof (not_sat_edge _ _ _ _
                                       (reachable_by g2 (dst g3 e2)
                                                     (fun x : V => (P x /\ x <> root) /\
                                                                   ~ g1 |= dst g1 e1 ~o~> x satisfying (fun x0 : V => P x0 /\ x0 <> root))) H26 H24 H23 H25).
              destruct H28 as [e3 [? [? ?]]]. specialize (H22 _ _ H29 H30).
              assert (strong_evalid g3 e3) by (apply (valid_path_strong_evalid _ (dst g3 e2) ms); auto).
              assert (g3 |= src g3 e3 ~> (dst g3 e3)) by (destruct H31 as [? [? ?]]; hnf; do 2 (split; auto); rewrite step_spec; exists e3; split; auto).              
              clear -H32 H22. exfalso. apply H22. apply edge_reachable_by with (dst g3 e3); auto.
              apply reachable_by_refl; auto. destruct H32 as [? [? ?]]. auto.
            }
            destruct H16 as [[? ?] [? ?]]. split; split; auto.
            rewrite path_prop_equiv; auto.
          }
          pose proof (H13 _ _ H11). pose proof (H13 _ _ H12). clear H13.
          destruct H11 as [_ [? _]]. rewrite valid_path_cons_iff in H11. destruct H11 as [? [[? [? ?]] ?]].
          destruct H12 as [_ [? _]]. rewrite valid_path_cons_iff in H12. destruct H12 as [? [[? [? ?]] ?]].
          symmetry in H12, H11. pose proof (H15 _ H13 H11). pose proof (H15 _ H25 H12). clear H15.
          rewrite <- H0 in H29. rewrite <- H0 in H30. simpl in H29. simpl in H30.
          destruct H29 as [? | [? | ?]]; [subst e0..| exfalso; tauto];
          destruct H30 as [? | [? | ?]]; try (exfalso; tauto); subst e.
          * specialize (H16 H25 H12 H27). destruct H16 as [? [? ?]].
            destruct H5 as [[_ ?] | [? ?]]. 2: exfalso; auto.
            pose proof (H18 _ H13 H12 H27 H20). pose proof (H18 _ H13 H12 H27 H21).
            destruct H5 as [_ [? _]]. specialize (H5 H15).
            rewrite is_tree_ppg_spec in H5. rewrite <- H29 in *. rewrite <- H16 in *.
            pose proof (reachable_by_path_is_reachable_by _ _ _ _ _ H30).
            specialize (H5 _ H32). destruct H5 as [path' ?]. destruct H5.
            pose proof (H33 _ H30). pose proof (H33 _ H31). rewrite H34 in H35. inversion H35. auto.
          * specialize (H16 H13 H11 H23). destruct H16 as [? [? ?]].
            destruct H5 as [[_ ?] | [? _]]. 2: exfalso; auto.
            specialize (H17 H25 H12 H27). destruct H17 as [? ?].
            destruct H6 as [[_ ?] | [? _]]. 2: exfalso; auto.
            specialize (H18 _ H13 H11 H23 H20).
            apply reachable_by_path_is_reachable_by in H18.
            apply reachable_by_foot_prop in H18.
            pose proof H6. destruct H6 as [_ [_ [_ ?]]]. rewrite <- H29 in *.
            assert (~ g2 |= dst g3 e2 ~o~> y
                      satisfying
                      (fun x : V =>
                         (P x /\ x <> root) /\
                         ~ g1 |= dst g1 e1 ~o~> x
                           satisfying (fun x0 : V => P x0 /\ x0 <> root))). {
              intro. apply reachable_by_foot_prop in H32. destruct H32.
              rewrite <- H16 in *. auto. 
            }
            assert (g2 |= dst g3 e2 ~o~> dst g3 e2
                      satisfying
                      (fun x : V =>
                         (P x /\ x <> root) /\
                         ~ g1 |= dst g1 e1 ~o~> x
                           satisfying (fun x0 : V => P x0 /\ x0 <> root))). {
              rewrite H30 in *. apply reachable_by_refl; auto.
              rewrite <- (spanning_tree_vvalid _ _ _ _ _ H31) in H27; auto.
            } rewrite H30 in *.
            specialize (H6 _ _ H33 H32). exfalso; apply H6.
            apply reachable_by_path_is_reachable in H21; auto.
          * specialize (H16 H25 H12 H27). destruct H16 as [? [? ?]].
            destruct H5 as [[_ ?] | [? _]]. 2: exfalso; auto.
            specialize (H17 H13 H11 H23). destruct H17 as [? ?].
            destruct H6 as [[_ ?] | [? _]]. 2: exfalso; auto.
            specialize (H18 _ H25 H12 H27 H21).
            apply reachable_by_path_is_reachable_by in H18.
            apply reachable_by_foot_prop in H18.
            pose proof H6. destruct H6 as [_ [_ [_ ?]]]. rewrite <- H29 in *.
            assert (~ g2 |= dst g3 e2 ~o~> y
                      satisfying
                      (fun x : V =>
                         (P x /\ x <> root) /\
                         ~ g1 |= dst g1 e1 ~o~> x
                           satisfying (fun x0 : V => P x0 /\ x0 <> root))). {
              intro. apply reachable_by_foot_prop in H32. destruct H32.
              rewrite <- H16 in *. auto.
            }
            assert (g2 |= dst g3 e2 ~o~> dst g3 e2
                      satisfying
                      (fun x : V =>
                         (P x /\ x <> root) /\
                         ~ g1 |= dst g1 e1 ~o~> x
                           satisfying (fun x0 : V => P x0 /\ x0 <> root))). {
              rewrite <- H30 in *. apply reachable_by_refl; auto.
              rewrite <- (spanning_tree_vvalid _ _ _ _ _ H31) in H23; auto.
            } rewrite <- H30 in *.
            specialize (H6 _ _ H33 H32). exfalso; apply H6.
            apply reachable_by_path_is_reachable in H20; auto.
          * specialize (H17 H13 H11 H23). destruct H17 as [? ?].
            destruct H6 as [[_ ?] | [? _]]. 2: exfalso; auto.
            destruct H6 as [_ [? _]]. specialize (H6 H15).
            pose proof (H19 _ H13 H11 H23 H20). pose proof (H19 _ H13 H11 H23 H21).
            pose proof (reachable_by_path_is_reachable_by _ _ _ _ _ H29).
            rewrite is_tree_ppg_spec in H6. rewrite H17 in *.
            specialize (H6 _ H31). destruct H6 as [path' ?]. destruct H6.
            pose proof (H32 _ H29). pose proof (H32 _ H30). rewrite H33 in H34. inversion H34. auto.
      + apply (spanning_list_spanning_tree2_reachable P g1 g2 g3 root e1 e2 n); auto.
      + apply (spanning_list_spanning_tree2_reachable _ _ g2 g3 _ e1 e2) in H9; auto.
        intro.
        assert (reachable g3 root b) by (apply reachable_by_trans with a; auto).
        cut (~ reachable g3 root b). 1: intro. apply H13; auto.
        clear H9 H11. destruct_eq_dec b root.
        1: subst; exfalso; apply H10; apply reachable_by_refl; auto.
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
          repeat intro. apply H11. apply edge_reachable_by with (dst g2 e2); auto.
          + split; auto. apply reachable_by_head_valid in H13. split; auto.
            rewrite step_spec. exists e2. destruct H8; auto.
          + revert H13. apply reachable_by_weaken.
              hnf. unfold Ensembles.In . intros. destruct H13 as [[? _] _]; auto.
        }
        assert (~ reachable g3 (dst g3 e1) b \/ ~ out_edges g3 root e1). {
          apply (ST2_not_reachable
                   (fun x : V => P x /\ x <> root) P g1 _ g2 _ _ e2); auto.
          + intro. destruct H13; auto.
          + compute. tauto.
          + intro. apply H10. apply edge_reachable_by with (dst g1 e1); auto.
            - split; auto. apply reachable_by_head_valid in H13. split; auto.
              rewrite step_spec. exists e1. destruct H3. auto.
            - apply reachable_by_weaken with (fun x : V => P x /\ x <> root); auto.
              compute; tauto.
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

    Lemma spanning_list_spanning_tree2': forall (P: V -> Prop) g1 root g2 (e1 e2 : E),
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
      apply (spanning_bi_tree P g1 root g2 g3 e1 e2); auto.
    Qed.

    Lemma spanning_list_spanning_tree2: forall (P: V -> Prop) g1 root g2 (e1 e2 : E),
        (e1 <> e2) -> (forall e, In e (e1 :: e2 :: nil) <-> out_edges g1 root e) ->
        vvalid g1 root -> P root ->
        ReachDecidable g1 (dst g1 e1) (fun x => P x /\ x <> root) ->
        spanning_list (fun x => P x /\ x <> root) g1 (e1 :: e2 :: nil) g2 ->
        spanning_tree g1 root P g2.
    Proof.
      intros. inversion H3. subst. clear H3. inversion H10. subst. clear H10.
      inversion H11. subst. rewrite (si_edge_spanning_tree' _ g4 g2) in H7; auto.
      clear H3 H11. apply (spanning_bi_tree P g1 root g3 g2 e1 e2); auto.
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
  Context {DV DE DG: Type}.
  Context {MGS: MarkGraphSetting DV}.
  Context {P: LabeledGraph V E DV DE DG -> Type}.
  Notation Graph := (GeneralGraph V E DV DE DG P).
  Local Coercion pg_lg : LabeledGraph >-> PreGraph.
  Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.

  Definition marked_reachable (g1 : Graph) (x : V) (g2 : Graph) : Prop :=
    (forall y, marked g2 y <-> marked g1 y \/ g1 |= x ~o~> y satisfying (unmarked g1)).
(*    (forall y, g1 |= x ~o~> y satisfying (unmarked g1) -> marked g2 y) /\
    forall y, ~ g1 |= x ~o~> y satisfying (unmarked g1) -> (marked g1 y <-> marked g2 y). *)

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
    + destruct H0 as [? [? [? ?]]]. split; auto.
  Qed.

  Lemma edge_spanning_tree_inj: forall g1 root g2, edge_spanning_tree g1 root g2 <->
                                                   (marked_reachable g1 (dst g1 root) g2 /\
                                                    SIMPLE_SPANNING_TREE.edge_spanning_tree g1 root (unmarked g1) g2).
  Proof.
    intros. split; intro.
    + hnf in H. destruct (node_pred_dec (marked g1) (dst g1 root)).
      - destruct H. split; [| right]; intros; auto.
        intro y.
        assert (~ g1 |= dst g1 root ~o~> y satisfying (unmarked g1)); [| firstorder].
        intro.
        apply reachable_by_head_prop in H1. unfold unmarked in H1.
        rewrite negateP_spec in H1. exfalso; auto.
      - rewrite spanning_tree_inj in H. destruct H. split; auto. left. auto.
    + destruct H. hnf. destruct (node_pred_dec (marked g1) (dst g1 root)); destruct H0 as [[? ?] | [? ?]].
      - unfold unmarked in H0. rewrite negateP_spec in H0. exfalso; auto.
      - split; auto.
        intro v; specialize (H v).
        assert (~ g1 |= dst g1 root ~o~> v satisfying (unmarked g1)); [| tauto].
        intro.
        apply reachable_by_head_prop in H2. unfold unmarked in H2.
        rewrite negateP_spec in H2. exfalso; auto.
      - rewrite spanning_tree_inj. auto.
      - exfalso; auto.
  Qed.

  Lemma edge_spanning_tree_invalid: forall (g: Graph) e,
      evalid g e -> ~ vvalid g (dst g e) -> edge_spanning_tree g e g.
  Proof.
    intros. rewrite edge_spanning_tree_inj. split.
    + intro v. pose proof reachable_by_head_valid g (dst g e) v (unmarked g). tauto.
    + apply SIMPLE_SPANNING_TREE.edge_spanning_tree_invalid; auto.
  Qed.

  Lemma spanning_tree_vvalid: forall (g1 : Graph) (root : V) (g2 : Graph) x,
      spanning_tree g1 root g2 -> (vvalid g1 x <-> vvalid g2 x).
  Proof.
    intros. rewrite spanning_tree_inj in H. destruct H.
    apply (SIMPLE_SPANNING_TREE.spanning_tree_vvalid _ root (unmarked g1)); auto.
  Qed.

  Lemma edge_spanning_tree_vvalid: forall (g1 g2: Graph) e x,
      edge_spanning_tree g1 e g2 -> (vvalid g1 x <-> vvalid g2 x).
  Proof.
    intros. rewrite edge_spanning_tree_inj in H. destruct H.
    apply (SIMPLE_SPANNING_TREE.edge_spanning_tree_vvalid _ e (unmarked g1)); auto.
  Qed.

  Lemma edge_spanning_tree_reachable_vvalid: forall (g1 g2: Graph) e,
      edge_spanning_tree g1 e g2 ->
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
      spanning_tree g1 root g2 ->
      forall x, (unmarked g1 x /\ ~ g1 |= root ~o~> x satisfying (unmarked g1)) <-> unmarked g2 x.
  Proof.
    intros.
    destruct H as [? _].
    specialize (H x).
    unfold unmarked at 1 3. rewrite !negateP_spec.
    tauto.
  Qed.

  Lemma spanning_tree_marked_equiv: forall (g1 g2: Graph) (root: V),
      ReachDecidable g1 root (unmarked g1) ->
      spanning_tree g1 root g2 ->
      forall x, (marked g1 x \/ g1 |= root ~o~> x satisfying (unmarked g1)) <-> marked g2 x.
  Proof.
    intros.
    destruct H as [? _].
    specialize (H x).
    tauto.
  Qed.

  Lemma edge_spanning_tree_unmarked_equiv: forall (g1 g2: Graph) (e: E),
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

  Lemma mark1_unmarked_eq: forall (g g1: Graph) root x, mark1 root g g1 -> (unmarked g1 x <-> unmarked g x /\ x <> root).
  Proof.
    intros. destruct H as [? [? ?]]. unfold unmarked. rewrite !negateP_spec. split; intros.
    + destruct_eq_dec x root. subst; auto. rewrite H1; auto.
    + destruct H2. rewrite <- H1; auto.
  Qed.

  Lemma spanning_tree_is_componded_mark: forall root x g1 g2,
      spanning_tree g1 x g2 -> componded root (mark x) g1 g2.
  Proof.
    intros. apply mark_is_componded_mark.
    intros. destruct H as [? [? _]].
    split; auto.
  Qed.

  Lemma gremove_is_nothing: forall root (g1 g2: Graph) e,
      out_edges g1 root e -> gremove_edge g1 e g2 ->
      (forall v : V, (marked g1) v <-> (marked g2) v) ->
      nothing root g1 g2.
  Proof.
    intros. split; auto. hnf. simpl. unfold predicate_vvalid.
    unfold predicate_weak_evalid. destruct H0 as [? [? [? [? ?]]]].
    split; [|split;[|split]]; intros.
    + specialize (H0 v). intuition.
    + destruct_eq_dec e0 e.
      - subst.
        split; intros; destruct H6; unfold Complement in H7;
        unfold Ensembles.In in H7; destruct H; exfalso; auto.
        destruct H5; auto. destruct H5 as [_ [? _]]. apply H7. rewrite <- H5. auto.
      - specialize (H2 _ H6). specialize (H3 _ H6).
        split; intros; [rewrite <- H3 | rewrite H3]; intuition.
    + destruct H6, H7. rewrite H3; auto. intro. subst.
      unfold Complement in H8. unfold Ensembles.In in H8. destruct H; auto.
    +  destruct H6, H7. rewrite H4; auto. intro. subst.
      unfold Complement in H8. unfold Ensembles.In in H8. destruct H; auto.
  Qed.

  Lemma gremove_is_componded_mark: forall root (g1 g2: Graph) e,
      out_edges g1 root e -> (marked g1) (dst g1 e) -> gremove_edge g1 e g2 ->
      (forall v : V, (marked g1) v <-> (marked g2) v) ->
      componded root (mark (dst g1 e)) g1 g2.
  Proof.
    intros. unfold componded.
    apply (compond_intro (compond_relation (nothing root) (mark (dst g1 e)))
                         (nothing root) g1 g1 g2).
    + apply (compond_intro (nothing root) (mark (dst g1 e)) g1 g1 g1).
      - apply eq_do_nothing; auto.
      - split; intros.
        * reflexivity.
        * pose proof reachable_by_head_prop g1 (dst g1 e) n (unmarked g1).
          unfold unmarked at 2 in H3.
          rewrite negateP_spec in H3.
          tauto.
    + apply (gremove_is_nothing root g1 g2 e); auto.
  Qed.

  Inductive spanning_list : Graph -> list E -> Graph -> Prop :=
  | spanning_list_nil: forall (g1 g2 : Graph), g1 = g2 -> spanning_list g1 nil g2
  | spanning_list_cons:
      forall g1 g2 g3 e rest, edge_spanning_tree g1 e g2 -> spanning_list g2 rest g3 -> spanning_list g1 (e :: rest) g3.
  
  Lemma spanning_list_inj: forall (g1 g2 : Graph) (es : list E) (root: V),
      marked g1 root ->
      NoDup es ->
      Forall (out_edges g1 root) es ->
      spanning_list g1 es g2 ->
      componded_mark_list root (map (dst g1) es) g1 g2 /\
      SIMPLE_SPANNING_TREE.spanning_list (unmarked g1) g1 es g2.
  Proof.
    intros. induction H2; simpl.
    + subst. split; constructor. reflexivity.
    + pose proof H2. rewrite edge_spanning_tree_inj in H2. destruct H2 as [? ?].
      assert (marked g2 root) by (rewrite (H2 root); auto).
      assert (NoDup rest) by (apply NoDup_cons_1 in H0; auto).
      assert (Forall (out_edges g2 root) rest). {
        pose proof (Forall_tl _ _ _ H1). rewrite Forall_forall in H8 |-* .
        intros. specialize (H8 _ H9).
        apply (SIMPLE_SPANNING_TREE.EST_out_edges (unmarked g1) g1 root g2 e); auto.
        apply NoDup_cons_2 in H0. intro. apply H0. subst; auto.
      }
      specialize (IHspanning_list H6 H7 H8). destruct IHspanning_list. split.
      - unfold componded_mark_list. simpl. split_relation_list ((lg_gg g2) :: nil); auto.
        * hnf in H4. destruct (node_pred_dec (marked g1) (dst g1 e)).
          1: {
            destruct H4. apply gremove_is_componded_mark; auto.
            apply Forall_inv in H1. auto.
          }
          1: {
            apply spanning_tree_is_componded_mark; auto.
          }
        * unfold componded_mark_list in H9.
          assert (map (dst g1) rest = map (dst g2) rest). {
            apply NoDup_cons_2 in H0. apply Forall_tl in H1.
            clear -H0 H H0 H5 H1.
            induction rest; simpl; auto. f_equal.
            + apply Forall_inv in H1.
              apply (SIMPLE_SPANNING_TREE.EST_the_same_dst (unmarked g1) _ root _ e); auto.
              intro. apply H0. subst. apply in_eq.
            + apply IHrest.
              - intro; apply H0, in_cons; auto.
              - apply Forall_tl in H1. auto.
          } rewrite H11; auto.
      - apply SIMPLE_SPANNING_TREE.spanning_list_cons with g2; auto.
        apply (SIMPLE_SPANNING_TREE.spanning_list_derive (unmarked g2)); auto.
        intro. symmetry. apply edge_spanning_tree_unmarked_equiv; auto.
  Qed.

  Lemma spanning_list_spanning_tree2: forall (g g1 g2: Graph) root (e1 e2 : E),
      (e1 <> e2) -> (forall e, In e (e1 :: e2 :: nil) <-> out_edges g root e) ->
      ReachDecidable g1 (dst g1 e1) (unmarked g1) ->
      vvalid g root -> unmarked g root -> mark1 root g g1 ->
      spanning_list g1 (e1 :: e2 :: nil) g2 ->
      spanning_tree g root g2.
  Proof.
    intros. rewrite spanning_tree_inj.
    apply (spanning_list_inj _ _ _ root) in H4.
    2: { destruct H3 as [_ [? _]]; auto. }
    2: {
      constructor.
      + intro. apply H. simpl in H5. destruct H5; [|exfalso]; auto.
      + constructor. intro. inversion H5. constructor.
    }
    2: {
      rewrite Forall_forall. intros. rewrite H0 in H5.
      destruct H3. apply (out_edges_si _ _ root x) in H3. intuition.
    }
    destruct H4. split.
    + assert (step_list g root (map (dst g1) (e1 :: e2 :: nil))). {
        hnf. destruct H3. intros.
        assert (HD: forall e, evalid g e -> dst g e = dst g1 e). {
          intros. destruct H3 as [_ [? [_ ?]]]. specialize (H3 e).
          specialize (H8 e). intuition.
        } split; intro.
        + simpl in H7.
          destruct H7 as [? | [? | ?]]; [| |exfalso; auto]; subst n';
          rewrite step_spec.
          - assert (out_edges g root e1) by (rewrite <- H0; apply in_eq).
            exists e1. destruct H7. auto. 
          - assert (out_edges g root e2) by (rewrite <- H0; apply in_cons, in_eq).
            exists e2. destruct H7. auto. 
        + rewrite step_spec in H7. destruct H7 as [e [? [? ?]]].
          assert (out_edges g root e) by (split; auto).
          rewrite <- H0 in H10. simpl in H10.
          destruct H10 as [? | [? | ?]]; [| |exfalso; auto]; subst e;
          subst n'; simpl; [|right]; left; rewrite HD; intuition.
      }
      assert (relation_list (nothing root :: mark1 root :: nothing root ::
              componded_mark_list root (map (dst g1) (e1 :: e2 :: nil)) ::
              nothing root :: nil) g g2). {
        split_relation_list ((lg_gg g) :: nil). apply eq_do_nothing; auto.
        split_relation_list ((lg_gg g1) :: nil); auto.
        split_relation_list ((lg_gg g1) :: nil). apply eq_do_nothing; auto.
        split_relation_list ((lg_gg g2) :: nil); auto.
        apply eq_do_nothing; auto.
      } apply mark1_componded_mark_list_mark in H7; auto.
      - destruct H7. exact H8.
    + assert (forall x, unmarked g1 x <-> unmarked g x /\ x <> root). {
        intros. destruct H3 as [? [? ?]]. unfold unmarked.
        rewrite !negateP_spec. split; intros.
        + specialize (H7 x). destruct_eq_dec root x.
          - subst. exfalso; auto.
          - rewrite H7; intuition.
        + destruct H8. rewrite <- H7; intuition.
      } destruct H3. rewrite H3.
      apply (SIMPLE_SPANNING_TREE.spanning_list_spanning_tree2 _ _ _ _ e1 e2); auto.
      - intros. rewrite H0. apply out_edges_si; auto.
      - destruct H3. rewrite <- H3; auto.
      - apply (ReachDecidable_si g1 g1 (unmarked g1)); auto.
        * reflexivity.
        * hnf. intros. rewrite H6; intuition.
      - apply (SIMPLE_SPANNING_TREE.spanning_list_derive (unmarked g1)); auto.
  Qed.

  Lemma spanning_tree_root_reachable: forall (g1 g2: Graph) (root: V),
      ReachDecidable g1 root (unmarked g1) ->
      spanning_tree g1 root g2 ->
      forall x, reachable g2 root x -> reachable g1 root x.
  Proof.
    intros. destruct (X x).
    - apply reachable_by_is_reachable in r. auto.
    - apply spanning_tree_inj in H. destruct H.
      apply (SIMPLE_SPANNING_TREE.spanning_tree_not_reachable_derive
               _ root (unmarked g1) g2); auto.
  Qed.

  Lemma spanning_tree_totally_unmarked_root_reachable:
    forall (g1 g2: Graph) (root: V),
      totally_unmarked g1 root ->
      (vvalid g1 root -> ReachDecidable g1 root (unmarked g1)) ->
      spanning_tree g1 root g2 ->
      forall x, reachable g1 root x <-> reachable g2 root x.
  Proof.
    intros. split; intro.
    - apply H in H1. apply spanning_tree_inj in H0.
      destruct H0 as [_ [_ [_ [? _]]]]. apply H0; auto.
    - apply spanning_tree_root_reachable with g2; auto.
      apply X. rewrite (spanning_tree_vvalid g1 root g2); auto.
      apply reachable_head_valid in H1; auto.
  Qed.

  Lemma spanning_tree_totally_unmarked_parent_reachable:
    forall (g1 g2: Graph) (root: V) (e: E),
      out_edges g1 root e -> vvalid g1 root -> marked g1 root ->
      totally_unmarked g1 (dst g1 e) ->
      (vvalid g1 (dst g1 e) -> ReachDecidable g1 (dst g1 e) (unmarked g1)) ->
      spanning_tree g1 (dst g1 e) g2 ->
      forall x, reachable g1 root x <-> reachable g2 root x.
  Proof.
    intros. pose proof (spanning_tree_totally_unmarked_root_reachable _ g2 _ H2 X H3). destruct (classic (reachable g1 (dst g1 e) x)).
    - pose proof H5. rewrite H4 in H6. split; intros; apply edge_reachable with (dst g1 e); auto; destruct H; hnf; rewrite step_spec; split; [|split | |split]; auto.
      + rewrite <- (spanning_tree_vvalid g1 (dst g1 e)); auto.
      + apply reachable_head_valid in H6; auto.
      + exists e. destruct H3 as [_ [[_ [? [? ?]]] _]]. simpl in *. unfold predicate_weak_evalid in *.
        specialize (H3 e). specialize (H9 e). specialize (H10 e). rewrite H8 in *.
        assert (evalid g1 e /\ ~ g1 |= dst g1 e ~o~> root satisfying (unmarked g1)) by (split; auto; intro; apply reachable_by_foot_prop in H11; exfalso; auto).
        pose proof H11. rewrite H3 in H12. split; [|split]; intuition.
      + apply reachable_head_valid in H5; auto.
      + exists e. auto.
    - assert (~ g1 |= (dst g1 e) ~o~> x satisfying (unmarked g1)) by (intro; apply H5; apply reachable_by_is_reachable in H6; auto). split; intros.
      + assert (~ reachable g1 (dst g1 e) x) by (intro; apply H6; apply H2; auto).
        assert (g1 |= root ~o~> x satisfying (Complement V (reachable_by g1 (dst g1 e) (unmarked g1)))). {
          destruct H7 as [p ?]. pose proof H7. destruct H7 as [? [? ?]]. exists p. split; [|split]; auto. rewrite path_prop_equiv; auto.
          intros. unfold Complement, Ensembles.In . intro. apply (reachable_path_in' g1 _ root x) in H12; auto. apply reachable_by_is_reachable in H13.
          apply H8. apply reachable_trans with n; auto.
        } rewrite reachable_by_eq_partialgraph_reachable in H9. destruct H3 as [_ [? _]]. rewrite H3 in H9.
        rewrite <- reachable_by_eq_partialgraph_reachable in H9. apply reachable_by_is_reachable in H9. auto.
      + apply spanning_tree_inj in H3. destruct H3. eapply SIMPLE_SPANNING_TREE.spanning_tree_not_reachable_derive; eauto.
  Qed.

  (* Print Assumptions spanning_list_spanning_tree2. *)

End SPANNING.
