Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import RamifyCoq.Coqlib.
Require Import RamifyCoq.graph.graph.
Require Import RamifyCoq.graph.graph_reachable.

Definition GraphPredicate {N D DEC} (g : @PreGraph N D DEC) :=
  {p : Ensemble D & forall x, {Ensembles.In D p (node_label x)} + {~ Ensembles.In D p (node_label x)}}.

Definition app_graph_predicate {N D DEC} (g : @PreGraph N D DEC) (p : GraphPredicate g) (v : D) := projT1 p v.

Coercion app_graph_predicate : GraphPredicate >-> Funclass.

Definition predicate_valid {N D DEC} (g : @PreGraph N D DEC) (p : GraphPredicate g) : N -> Prop :=
  fun n => valid n /\ p (node_label n).

Definition predicate_edge_func {N D DEC} (g : @PreGraph N D DEC) (p : GraphPredicate g) (x: N) : list N :=
  filter (fun s => if ((projT2 p) s) then true else false) (edge_func x).

Definition predicate_subgraph {N D DEC} (g : @PreGraph N D DEC) (p : GraphPredicate g) : PreGraph N D :=
  Build_PreGraph N D DEC (predicate_valid g p) node_label (predicate_edge_func g p).

Definition predicate_sub_mathgraph {N D DEC} {g : @PreGraph N D DEC} {nV : N}
           (mg: MathGraph g nV) (p : GraphPredicate g) : MathGraph (predicate_subgraph g p) nV.
Proof.
  refine (Build_MathGraph N D DEC _ nV _ _); intros.
  + destruct (t_eq_dec y nV).
    - trivial.
    - unfold edge_func in H0.
      unfold predicate_subgraph in H0.
      unfold predicate_edge_func in H0.
      rewrite filter_In in H0. destruct H0.
      destruct (projT2 p y) eqn:? . 2: inversion H1.
      destruct H. split.
      * apply (valid_graph x H y) in H0. hnf in H0. destruct (t_eq_dec y nV). exfalso; auto. auto.
      * hnf in i. hnf. auto.
  + destruct H. apply valid_not_null. auto.
Defined.

Lemma reachable_by_eq_subgraph_reachable {N D DEC}:
  forall (g : @PreGraph N D DEC) (p : GraphPredicate g) (n1 n2: N),
    g |= n1 ~o~> n2 satisfying p <-> reachable (predicate_subgraph g p) n1 n2.
Proof.
  intros; split; intros; destruct H as [path [? [? ?]]]; exists path.
  + split; auto. split. 2: repeat intro; hnf; auto.
    (* destruct path. simpl; auto. *)
    clear H.
    destruct path. simpl; auto.
    revert n H0 H1. induction path; intros.
    - simpl in *. unfold predicate_valid. split; auto.
      hnf in H1. unfold node_prop in H1. apply H1. apply in_eq.
    - specialize (IHpath a). simpl in *. destruct H0. split.
      * hnf in H. destruct H as [? [? ?]]. hnf.
        unfold valid. unfold edge_func.
        unfold predicate_subgraph.
        unfold predicate_valid. unfold predicate_edge_func.
        hnf in H1. unfold node_prop in H1.
        split. split; auto. apply H1. apply in_eq.
        split. split; auto. apply H1. apply in_cons, in_eq.
        rewrite filter_In. split; auto. destruct (projT2 p a). auto.
        exfalso; apply n0. hnf. apply H1. apply in_cons, in_eq.
      * apply IHpath. apply H0. hnf in H1. hnf; intros. apply H1.
        apply in_cons. auto.
  + split; auto. split.
    - clear H H1. destruct path. simpl; auto.
      revert n H0. induction path; intros; simpl in *.
      * destruct H0; auto.
      * destruct H0. split. hnf in H.
        destruct H as [[? ?] [[? ?] ?]].
        split; auto. split; auto. unfold edge_func in H4.
        unfold predicate_subgraph in H4.
        unfold predicate_edge_func in H4.
        rewrite filter_In in H4. destruct H4. auto.
        apply IHpath. apply H0.
    - clear H H1. destruct path. hnf; intros. inversion H.
      revert n H0. induction path; intros.
      * hnf. intros. simpl in H. destruct H. 2: exfalso; auto. subst.
        destruct H0. hnf. hnf in H0. auto.
      * unfold path_prop in *. rewrite <- Forall_forall in *.
        apply Forall_cons. destruct H0. hnf in H. destruct H as [[? ?] _].
        hnf in H1. hnf. auto. rewrite Forall_forall.
        apply IHpath. simpl in *. destruct H0. apply H0.
Qed.

Lemma mark_exists: forall {N} {D} {DEC} (marked: Ensemble D) (g: @PreGraph N D DEC) x v,
                   marked v -> exists g', mark marked g x g'.
Proof.
Abort.
