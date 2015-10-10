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

    Lemma edge_spanning_tree_invalid: forall (g: Graph) e (P: NodePred V),
        ~ vvalid g (dst g e) -> edge_spanning_tree g e P g.
    Proof.
      intros. hnf. destruct (node_pred_dec P (dst g e)); [left | right]; split; auto.
      + remember (dst g e) as v. split; [|split; [|split]].
        - reflexivity.
        - repeat intro. apply reachable_head_valid in H1. destruct H1. exfalso; auto.
        - intros. apply reachable_by_is_reachable in H0. apply reachable_head_valid in H0. exfalso; auto.
        - intros. apply reachable_by_is_reachable in H0. apply reachable_head_valid in H0. exfalso; auto.
      + split; [|split; [|split; [|split]]]; intros; [tauto | tauto | tauto |tauto |].
        right. split; auto.
    Qed.

    Lemma spanning_tree_vvalid: forall (g1 : Graph) (root : V) (P: V -> Prop) (g2 : Graph) x,
        ReachDecidable g1 root P -> spanning_tree g1 root P g2 -> (vvalid g1 x <-> vvalid g2 x).
    Proof.
      intros. destruct H as [? [? [? ?]]]. destruct (X x).
      + split; intros.
        - specialize (H1 _ r). apply reachable_foot_valid in H1. auto.
        - apply reachable_by_is_reachable in r. apply reachable_foot_valid in r. auto.
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
          destruct H6. rewrite H9. destruct H. destruct H8. intuition.
        * specialize (H3 _ H8). specialize (H4 _ H8).
          rewrite H3. rewrite H4. intuition.
      - intros. destruct H8. apply H4. intro. subst. auto.
      - intros. destruct H8. apply H5. intro. subst. auto.
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
          * specialize (H6 _ H18). specialize (H7 _ H18). specialize (H8 _ H18).
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
              specialize (H6 _ H16). specialize (H7 _ H16). specialize (H8 _ H16).
              rewrite <- H7, <- H8. intuition.
            } Unfocus.
          * apply IHp.
            1: apply H12.
            1: intro; apply H10; apply in_cons; auto.
            1: apply path_prop_sublist with (v :: a :: p); auto; apply Sublist_cons; auto.
    Qed.

    Inductive spanning_list : (V -> Prop) -> Graph -> list E -> Graph -> Prop :=
    | spanning_list_nil: forall P g1 g2, g1 ~=~ g2 -> spanning_list P g1 nil g2
    | spanning_list_cons:
        forall P g1 g2 g3 e es, edge_spanning_tree g1 e P g2 ->
                                spanning_list (fun x => P x /\ ~ g1 |= (dst g1 e) ~o~> x satisfying P) g2 es g3 ->
                                spanning_list P g1 (e :: es) g3.

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
        spanning_list (fun x => P x /\ x <> root) g1 l g2 ->
        spanning_tree g1 root P g2.
    Proof.
      intros. split; [|split]; intros.
      + revert g1 g2 H0 H1 H3. induction l; intros; inversion H3; subst; clear H3.
        rewrite H4; reflexivity. destruct H8 as [? | [? ?]].
        - admit.
        - assert (out_edges g1 root a) by (apply H0; apply in_eq).
          pose proof (gremove_predicate_partial_si _ _ _ _ _ H5 H1 H2 H4).
          rewrite H6. clear H6. 
          pose proof (gremove_root_not_reachable_equiv _ _ _ _ _ H5 H1 H2 H4 H3).
          
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
    
  Lemma edge_spanning_tree_invalid: forall (g: Graph) e, ~ vvalid g (dst g e) -> edge_spanning_tree g e g.
  Proof.
    intros. rewrite edge_spanning_tree_inj. split.
    + split; intros. 2: tauto. apply reachable_by_is_reachable in H0.
      apply reachable_head_valid in H0. exfalso; auto.
    + apply SIMPLE_SPANNING_TREE.edge_spanning_tree_invalid. auto.
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
