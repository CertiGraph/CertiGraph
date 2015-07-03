Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Lists.List.
Require Import RamifyCoq.Coqlib.
Require Import RamifyCoq.graph.graph_model.

Section GRAPH_GEN.

Variable V : Type.
Variable E : Type.
Notation Gph := (PreGraph V E).

Variable g: Gph.
Context {BI: BiGraph g}.
Context {MA: MathGraph g}.

Definition change_vvalid (v: V): Ensemble V :=
  fun n => vvalid n \/ n = v.

Definition change_node_pred (P: NodePred g) (v: V) (Pv: {Pv : Prop & {Pv} + {~ Pv}}) : NodePred g.
  intros.
  exists (fun n: V => (if t_eq_dec n v then projT1 Pv else P n)).
  intros.
  destruct (t_eq_dec x v).
  + destruct Pv; auto.
  + destruct P; simpl; auto.
Defined.

Definition change_evalid v : Ensemble E :=
  fun e => evalid e \/ src e = v.

Definition change_dst (v l r: V) : E -> V.
  intro e.
  refine (if t_eq_dec (src e) v then _ else dst e).
  exact (if left_or_right _ _ v e _H then l else r).
Defined.

Definition update_PreGraph v l r : Gph :=
  Build_PreGraph V E EV EE (change_vvalid v) (change_evalid v) src (change_dst v l r).

Definition update_BiGraph v l r: BiGraph (update_PreGraph v l r).
  refine (Build_BiGraph V E _ left_out_edge right_out_edge _ _ _ _ _ _).
  + unfold update_PreGraph; simpl; apply left_sound.
  + unfold update_PreGraph; simpl; apply right_sound.
  + unfold update_PreGraph; simpl.
    unfold change_vvalid, change_evalid.
    intros.
    rewrite left_sound.
    pose proof left_valid x.
    tauto.
  + unfold update_PreGraph; simpl.
    unfold change_vvalid, change_evalid.
    intros.
    rewrite right_sound.
    pose proof right_valid x.
    tauto.
  + unfold update_PreGraph; simpl; apply bi_consist.
  + unfold update_PreGraph; simpl; apply only_two_edges.
Defined.

Definition in_math (v l r: V) : Type :=
  forall y, In y (l :: r :: nil) -> {vvalid y} + {y = v} + {is_null y}.

Definition update_MathGraph v l r (Hi: in_math v l r) (Hn: ~ is_null v): MathGraph (update_PreGraph v l r).
  refine (Build_MathGraph V E _ is_null is_null_dec _ _).
  + unfold update_PreGraph, change_vvalid, change_evalid, change_dst; simpl.
    intros.
    destruct (t_eq_dec (src e) v).
    - split; [right; auto |].
      destruct (left_or_right g BI v e e0); [destruct (Hi l) | destruct (Hi r)]; simpl; tauto.
    - assert (evalid e) by tauto.
      apply valid_graph in H0; unfold weak_valid in H0.
      tauto.
  + unfold update_PreGraph, change_vvalid; simpl.
    intros.
    destruct H; [| subst]; auto.
    apply valid_not_null with x; tauto.
Defined.

End GRAPH_GEN.
