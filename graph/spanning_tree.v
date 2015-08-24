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
      is_tree g2 root /\ (forall n, g1 |= root ~o~> n satisfying P -> reachable g2 root n).

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
        - repeat intro. apply reachable_head_valid in H0. exfalso; auto.
        - intros. apply reachable_by_is_reachable in H0. apply reachable_head_valid in H0. exfalso; auto.
      + split; [|split; [|split; [|split]]]; intros; [tauto | tauto | tauto |tauto |].
        intro; apply H. destruct H0 as [_ [_ ?]]. auto.
    Qed.

    Lemma spanning_tree_vvalid: forall (g1 : Graph) (root : V) (P: V -> Prop) (g2 : Graph) x,
        ReachDecidable g1 root P -> spanning_tree g1 root P g2 -> (vvalid g1 x <-> vvalid g2 x).
    Proof.
      intros. destruct H as [? [? ?]]. 
    Abort.

    Lemma spanning_list_spanning_tree: forall (P: V -> Prop) g1 root g2 l,
        (forall e, In e l <-> out_edges g1 root e) ->
        P root ->
        spanning_list (fun x => P x /\ x <> root) g1 l g2 ->
        spanning_tree g1 root P g2.
    Proof.
      intros.  
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
  
  Definition marked_reachable (g1 : Graph) (x : V) (g2 : Graph) : Prop :=
    (forall y, g1 |= x ~o~> y satisfying (unmarked g1) -> marked g2 y) /\
    forall y, ~ g1 |= x ~o~> y satisfying (unmarked g1) -> (marked g1 y <-> marked g2 y).

  Definition spanning_tree (g1 : Graph) (root : V) (g2 : Graph) : Prop :=
    marked_reachable g1 root g2 /\
    (predicate_partialgraph g1 (fun n => ~ g1 |= root ~o~> n satisfying (unmarked g1))) ~=~
    (predicate_partialgraph g2 (fun n => ~ g1 |= root ~o~> n satisfying (unmarked g1))) /\
    (unmarked g1 root -> SIMPLE_SPANNING_TREE.is_tree g2 root /\
                         forall n, g1 |= root ~o~> n satisfying (unmarked g1) -> reachable g2 root n).

  Definition edge_spanning_tree (g1 : Graph) (e : E) (g2 : Graph) : Prop :=
    if node_pred_dec (marked g1) (dst g1 e)
    then gremove_edge g1 e g2 /\ forall v, marked g1 v <-> marked g2 v
    else spanning_tree g1 (dst g1 e) g2.

  Lemma edge_spanning_tree_invalid: forall (g: Graph) e,
    ~ vvalid g (dst g e) ->
    edge_spanning_tree g e g.
  Admitted.

  Lemma spanning_tree_vvalid: forall (g1 : Graph) (root : V) (g2 : Graph) x,
      ReachDecidable g1 root (unmarked g1) -> spanning_tree g1 root g2 -> (vvalid g1 x <-> vvalid g2 x).
  Proof.
  Admitted.
    
End SPANNING.
