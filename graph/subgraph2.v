Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import RamifyCoq.Coqlib.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.

Section SubGraph.

Context {V E: Type}.
Context (g: PreGraph V E).
Context {MA: MathGraph g}.
Context {LF: LocalFiniteGraph g}.
Context (p: NodePred g).

Definition predicate_vvalid : Ensemble V :=
  fun n => vvalid n /\ p n.

Definition predicate_evalid : Ensemble E :=
  fun e => evalid e /\ p (src e) /\ p (dst e).

(*
Definition predicate_edge_func {N D DEC} (g : @PreGraph N D DEC) (p : GraphPredicate g) (x: N) : list N :=
  filter (fun s => if ((projT2 p) (node_label s)) then true else false) (edge_func x).
*)

Definition predicate_subgraph : PreGraph V E :=
  Build_PreGraph V E EV EE predicate_vvalid predicate_evalid src dst.

Definition predicate_sub_mathgraph : MathGraph predicate_subgraph.
Proof.
  refine (Build_MathGraph V E _ is_null is_null_dec _ _).
  + unfold predicate_subgraph, predicate_vvalid, predicate_evalid; simpl; intros.
    pose proof valid_graph e.
    unfold weak_valid in H0.
    tauto.
  + unfold predicate_subgraph, predicate_vvalid, predicate_evalid; simpl; intros.
    pose proof valid_not_null x.
    tauto.
Defined.

Definition predicate_sub_localfinitegraph : LocalFiniteGraph predicate_subgraph.
Proof.
  refine (Build_LocalFiniteGraph V E _ _).
  intros.
  exists (filter (fun e => if (sumbool_dec_and (projT2 p (src e)) (projT2 p (dst e))) then true else false) (edge_func g x)).
  split.
  + apply NoDup_filter.
    unfold edge_func.
    destruct (local_enumerable x); simpl.
    tauto.
  + intros.
    unfold predicate_subgraph, predicate_vvalid, predicate_evalid; simpl; intros.
    rewrite filter_In.
    rewrite edge_func_spec.
    destruct (sumbool_dec_and (projT2 p (src x0)) (projT2 p (dst x0)));
    change (projT1 p (src x0)) with (p (src x0)) in *;
    change (projT1 p (dst x0)) with (p (dst x0)) in *.
    - unfold out_edges, Ensembles.In in *; simpl.
      assert (true = true) by auto; tauto.
    - unfold out_edges, Ensembles.In in *; simpl.
      assert (~ false = true) by congruence; tauto.
Defined.

Lemma reachable_by_eq_subgraph_reachable:
  forall (n1 n2: V),
    g |= n1 ~o~> n2 satisfying p <-> reachable predicate_subgraph n1 n2.
Proof.
  intros; split; intros; destruct H as [path [? [? ?]]]; exists path.
  + split; auto. split. 2: repeat intro; hnf; auto.
    (* destruct path. simpl; auto. *)
    clear H.
    destruct path. simpl; auto.
    revert v H0 H1. induction path; intros.
    - simpl in *. unfold predicate_vvalid. split; auto.
      hnf in H1. inversion H1; auto.
    - specialize (IHpath a). simpl in *. destruct H0. split.
      * hnf in H. destruct H as [? [? ?]]. hnf.
        unfold vvalid. unfold edge_func.
        unfold predicate_subgraph.
        unfold predicate_vvalid, predicate_evalid.
        hnf in H1. inversion H1; subst. inversion H7; subst.
        split; auto.
        split; auto.
        rewrite step_spec in H3 |- *; simpl in H3 |- *.
        destruct H3 as [e [? [? ?]]]; exists e; subst; tauto.
      * apply IHpath. apply H0. hnf in H1. hnf; intros. inversion H1; subst; auto.
    - rewrite Forall_forall; intros; auto.
  + split; auto. split.
    - clear H H1. destruct path. simpl; auto.
      revert v H0. induction path; intros; simpl in *.
      * destruct H0; auto.
      * destruct H0. split. hnf in H.
        destruct H as [[? ?] [[? ?] ?]].
        split; auto. split; auto. unfold edge_func in H4.
        unfold predicate_subgraph in H4.
        unfold predicate_vvalid, predicate_evalid in H4.
        rewrite step_spec in H4 |- *; simpl in H4 |- *.
        destruct H4 as [e [? [? ?]]]; exists e; subst; tauto.
        apply IHpath. apply H0.
    - clear H H1. destruct path. hnf; intros. constructor.
      revert v H0. induction path; intros.
      * unfold predicate_subgraph in *.
        hnf. intros. simpl in H0. destruct H0. repeat constructor; auto.
      * unfold path_prop in *. 
        specialize (IHpath a).
        inversion H0.
        unfold edge, predicate_subgraph, predicate_vvalid in H; simpl in H.
        constructor; [tauto | auto].
Qed.

End SubGraph.

(*


*)