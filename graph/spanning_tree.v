Require Import Coq.Sets.Ensembles.
Require Import RamifyCoq.Coqlib.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require RamifyCoq.graph.marked_graph.
Import RamifyCoq.graph.marked_graph.MarkGraph.

Module SIMPLE_SPANNING_TREE.

  Section SIMPLE_SPANNING.

    Context {V E: Type}.
    Context {EV: EqDec V eq}.
    Context {EE: EqDec E eq}.

    Notation Graph := (PreGraph V E).

    Definition is_tree (g : Graph) (x : V) : Prop :=
      forall y, reachable g x y -> exists !(p : path), g |= p is x ~o~> y satisfying (fun _ => True).
    
    Definition spanning_tree (g1 : Graph) (root : V) (P: V -> Prop) (g2: Graph) := 
      (predicate_partialgraph g1 (fun n => ~ g1 |= root ~o~> n satisfying P)) ~=~
      (predicate_partialgraph g2 (fun n => ~ g1 |= root ~o~> n satisfying P)) /\
      (P root -> is_tree g2 root) /\ (forall n, g1 |= root ~o~> n satisfying P -> reachable g2 root n).

    Definition edge_spanning_tree (g1 : Graph) (e : E) (P: V -> Prop) (g2 : Graph) : Prop :=
      (P (dst g1 e) /\ spanning_tree g1 (dst g1 e) P g2) \/ (~ P (dst g1 e) /\ gremove_edge g1 e g2).

    Inductive spanning_list : (V -> Prop) -> Graph -> list E -> Graph -> Prop :=
    | spanning_list_nil: forall P g1 g2, g1 ~=~ g2 -> spanning_list P g1 nil g2
    | spanning_list_cons: forall P g1 g2 g3 e rest, edge_spanning_tree g1 e P g2 ->
                                                    spanning_list (fun x => P x /\ ~ reachable g1 (dst g1 e) x) g2 rest g3 ->
                                                    spanning_list P g1 (e :: rest) g3.

    Lemma edge_spanning_tree_invalid: forall (g: Graph) e (P: NodePred V),
        ~ vvalid g (dst g e) -> edge_spanning_tree g e P g.
    Proof.
      intros. hnf. destruct (node_pred_dec P (dst g e)); [left | right]; split; auto.
      + remember (dst g e) as v. split; [|split].
        - reflexivity.
        - repeat intro. apply reachable_head_valid in H1. exfalso; auto.
        - intros. apply reachable_by_is_reachable in H0. apply reachable_head_valid in H0. exfalso; auto.
      + split; [|split; [|split; [|split]]]; intros; [tauto | tauto | tauto |tauto |].
        intro; apply H. destruct H0 as [_ [_ ?]]. auto.
    Qed.

    Lemma spanning_tree_vvalid: forall (g1 : Graph) (root : V) (P: V -> Prop) (g2 : Graph) x,
        ReachDecidable g1 root P -> spanning_tree g1 root P g2 -> (vvalid g1 x <-> vvalid g2 x).
    Proof.
      intros. destruct H as [? [? ?]]. destruct (X x).
      + split; intros.
        - specialize (H1 _ r). apply reachable_foot_valid in H1. auto.
        - apply reachable_by_is_reachable in r. apply reachable_foot_valid in r. auto.
      + destruct H as [? _]. simpl in H. unfold predicate_vvalid in H.
        specialize (H x). split; intros.
        - assert (vvalid g1 x /\ ~ g1 |= root ~o~> x satisfying P) by (split; auto).
          rewrite H in H3. tauto.
        - assert (vvalid g2 x /\ ~ g1 |= root ~o~> x satisfying P) by (split; auto).
          rewrite <- H in H3. tauto.
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

    Lemma spanning_list_spanning_tree: forall (P: V -> Prop) g1 root g2 l,
        (forall e, In e l <-> out_edges g1 root e) ->
        vvalid g1 root -> P root ->
        spanning_list (fun x => P x /\ x <> root) g1 l g2 ->
        spanning_tree g1 root P g2.
    Proof.
      intros. split; [|split]; intros.
      + remember (fun x : V => P x /\ x <> root).
        remember (fun n : V => ~ g1 |= root ~o~> n satisfying P).
        assert (Included P1 (fun n : V => ~ g1 |= root ~o~> n satisfying P)). {
          intro. rewrite HeqP1. auto.
        } clear HeqP1.
        assert (forall e, In e l -> out_edges g1 root e). {
          intros. apply H; auto.
        } clear H.
        induction H2. rewrite H. reflexivity. subst.
        apply si_trans with (predicate_partialgraph g2 P1).
        - clear IHspanning_list H2.
          destruct H as [[[? ?] ?] | [? ?]].
          * admit.
          * apply si_stronger_partialgraph_simple with (fun n : V => ~ g1 |= root ~o~> n satisfying P); auto.
            (* evalid e -> (vvalid g1 (src g1 e) \/ vvalid g2 (src g2 e)) -> src g1 e = src g2 e *)
            destruct H2 as [? [? [? [? ?]]]]. split; [|split; [|split]]; intros; simpl.
            Focus 1. {
              unfold predicate_vvalid. specialize (H2 v). intuition.
            } Unfocus.
            Focus 1. {
              unfold predicate_weak_evalid.
              destruct (equiv_dec e0 e).
              + admit.
              + unfold equiv in c. specialize (H5 _ c). specialize (H6 _ c).
                rewrite H5, H6. tauto.
            } Unfocus.
            Focus 1. {
              destruct (equiv_dec e0 e).
              + unfold equiv in e1. subst. clear H5 H6 H7.
                exfalso; apply H8. hnf.
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

  Definition is_tree (g : Graph) (x : V) : Prop := SIMPLE_SPANNING_TREE.is_tree g x.
  
  Definition marked_reachable (g1 : Graph) (x : V) (g2 : Graph) : Prop :=
    (forall y, g1 |= x ~o~> y satisfying (unmarked g1) -> marked g2 y) /\
    forall y, ~ g1 |= x ~o~> y satisfying (unmarked g1) -> (marked g1 y <-> marked g2 y).

  Definition spanning_tree (g1 : Graph) (root : V) (g2 : Graph) : Prop :=
    marked_reachable g1 root g2 /\
    (predicate_partialgraph g1 (fun n => ~ g1 |= root ~o~> n satisfying (unmarked g1))) ~=~
    (predicate_partialgraph g2 (fun n => ~ g1 |= root ~o~> n satisfying (unmarked g1))) /\
    (unmarked g1 root -> is_tree g2 root /\
                         forall n, g1 |= root ~o~> n satisfying (unmarked g1) -> reachable g2 root n).

  Definition edge_spanning_tree (g1 : Graph) (e : E) (g2 : Graph) : Prop :=
    if node_pred_dec (marked g1) (dst g1 e)
    then gremove_edge g1 e g2 /\ forall v, marked g1 v <-> marked g2 v
    else spanning_tree g1 (dst g1 e) g2.

  Lemma spanning_tree_inj: forall g1 root g2, spanning_tree g1 root g2 <->
                                              (marked_reachable g1 root g2 /\
                                               SIMPLE_SPANNING_TREE.spanning_tree g1 root (unmarked g1) g2).
  Proof.
    intros. split; intro; destruct H; split; auto.
    + destruct H0. split; auto. destruct (node_pred_dec (marked g1) root).
      - split; intros; [ | apply reachable_by_head_prop in H2]; unfold unmarked in H2;
        rewrite negateP_spec in H2; exfalso; auto.
      - unfold unmarked in H1 at 1. rewrite negateP_spec in H1. specialize (H1 n).
        destruct H1; split; intros; auto.
    + destruct H0 as [? [? ?]]. unfold is_tree. split; auto. 
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
    
End SPANNING.
