Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Lists.List.
Require Import RamifyCoq.Coqlib.
Require Import RamifyCoq.graph.graph_model.

Section GRAPH_GEN.

Variable V : Type.
Variable E : Type.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Notation Gph := (PreGraph V E).

Variable g: Gph.
Variable left_out_edge right_out_edge: V -> E.
Context {BI: BiGraph g left_out_edge right_out_edge}.
Context {MA: MathGraph g}.

Definition change_vvalid (v: V): Ensemble V :=
  fun n => vvalid g n \/ n = v.

Definition change_node_pred (P: NodePred V) (v: V) (Pv: {Pv : Prop & {Pv} + {~ Pv}}) : NodePred V.
  intros.
  exists (fun n: V => (if equiv_dec n v then projT1 Pv else P n)).
  intros.
  destruct_eq_dec x v.
  + destruct Pv; auto.
  + destruct P; simpl; auto.
Defined.

Definition change_evalid v : Ensemble E :=
  fun e => evalid g e \/ src g e = v.

Definition change_dst (v l r: V) : E -> V.
  intro e.
  refine (if equiv_dec (src g e) v then _ else dst g e).
  exact (if left_or_right _ _ v e _H then l else r).
Defined.

Definition update_PreGraph v l r : Gph :=
  Build_PreGraph EV EE (change_vvalid v) (change_evalid v) (src g) (change_dst v l r).

Definition update_BiGraph v l r: BiGraph (update_PreGraph v l r) left_out_edge right_out_edge.
  refine (Build_BiGraph _ _ _ _ _ _ _).
  + unfold update_PreGraph; simpl.
    unfold change_vvalid, change_evalid.
    intros.
    rewrite (left_sound g).
    pose proof left_valid g x.
    tauto.
  + unfold update_PreGraph; simpl.
    unfold change_vvalid, change_evalid.
    intros.
    rewrite (right_sound g).
    pose proof right_valid g x.
    tauto.
  + unfold update_PreGraph; simpl; apply (bi_consist g).
  + unfold update_PreGraph; simpl; apply (only_two_edges g).
Defined.

Definition in_math (v l r: V) : Type :=
  forall y, In y (l :: r :: nil) -> {vvalid g y} + {y = v} + {is_null g y}.

Definition update_MathGraph v l r (Hi: in_math v l r) (Hn: ~ is_null g v): MathGraph (update_PreGraph v l r).
  refine (Build_MathGraph _ (is_null g) (is_null_dec g) _ _).
  + unfold update_PreGraph, change_vvalid, change_evalid, change_dst; simpl.
    intros.
    destruct_eq_dec (src g e) v.
    - split; [right; auto |].
      destruct (left_or_right g BI v e H0); [destruct (Hi l) | destruct (Hi r)]; simpl; tauto.
    - assert (evalid g e) by tauto.
      apply (valid_graph g) in H1.
      unfold weak_valid in H1.
      tauto.
  + unfold update_PreGraph, change_vvalid; simpl.
    intros.
    destruct H; [| subst]; auto.
    apply (valid_not_null g) with x; tauto.
Defined.

End GRAPH_GEN.
