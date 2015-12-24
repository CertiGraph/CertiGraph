Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Lists.List.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.subgraph2.

Section LABELED_GRAPH_GEN.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE: Type}.

Notation Graph := (LabeledGraph V E DV DE).

Definition empty_pregraph (v0: V): PreGraph V E :=
  @Build_PreGraph V E EV EE (fun v => False) (fun e => False) (fun e => v0) (fun e => v0).

Definition single_vertex_pregraph (v0: V): PreGraph V E :=
  @Build_PreGraph V E EV EE (eq v0) (fun e => False) (fun e => v0) (fun e => v0).

Definition union_pregraph (PV : V -> Prop) (PE: E -> Prop) (PVD: forall v, Decidable (PV v)) (PED: forall e, Decidable (PE e)) (g1 g2: PreGraph V E): PreGraph V E :=
  @Build_PreGraph V E EV EE
    (fun v => if PVD v then vvalid g1 v else vvalid g2 v)
    (fun e => if PED e then evalid g1 e else evalid g2 e)
    (fun e => if PED e then src g1 e else src g2 e)
    (fun e => if PED e then dst g1 e else dst g2 e).

Definition update_vlabel (vlabel: V -> DV) (x: V) (d: DV) :=
  fun v => if equiv_dec x v then d else vlabel v.

Definition update_dst (destination : E -> V) (e : E) (target: V) :=
  fun v => if equiv_dec e v then target else destination v.

Definition labeledgraph_vgen (g: Graph) (x: V) (a: DV) : Graph := Build_LabeledGraph _ _ g (update_vlabel (vlabel g) x a) (elabel g).

Definition pregraph_gen_dst (g : PreGraph V E) (e : E) (t : V) :=
  @Build_PreGraph V E EV EE (vvalid g) (evalid g) (src g) (update_dst (dst g) e t).

Definition labeledgraph_gen_dst (g : Graph) (e : E) (t : V) :=
  Build_LabeledGraph _ _ (pregraph_gen_dst g e t) (vlabel g) (elabel g).

Lemma lg_vgen_stable: forall (g: Graph) (x: V) (d: DV),
  (predicate_partial_labeledgraph (labeledgraph_vgen g x d) (fun y => x <> y)) ~=~
   (predicate_partial_labeledgraph (labeledgraph_vgen g x d) (fun y => x <> y))%LabeledGraph.
Proof.
  intros.
  split; [| split].
  + simpl.
    reflexivity.
  + intros; simpl.
    unfold update_vlabel.
    if_tac; auto.
  + intros; simpl.
    reflexivity.
Qed.

Lemma pregraph_join_empty_single: forall v0 v1,
  pregraph_join (eq v0) (Empty_set _) (empty_pregraph v1) (single_vertex_pregraph v0).
Proof.
  intros.
  unfold empty_pregraph, single_vertex_pregraph.
  split; [| split; [| split]]; simpl.
  + split; intros.
    - destruct_eq_dec v0 a; tauto.
    - auto.
  + split; intros.
    - tauto.
    - auto.
  + intros; tauto.
  + intros; tauto.
Qed.

End LABELED_GRAPH_GEN.

(*
Section LABELED_GRAPH_EXPAND.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE: Type}.

Notation Graph := (LabeledGraph V E DV DE).

Definition expand_vvalid (g: PreGraph V E) (vs: list V) := fun v => vvalid g v \/ In v vs.

Definition expand_evalid (g: PreGraph V E) (es: list E) := fun e => evalid g e \/ In e es.

Definition expand_src (g: PreGraph V E) (es: list E) (src': E -> V) :=
  fun e => if in_dec equiv_dec e es then src' e else src g e.

Definition expand_dst (g: PreGraph V E) (es: list E) (dst': E -> V) :=
  fun e => if in_dec equiv_dec e es then dst' e else dst g e.

Definition expand_vlabel (g: Graph) (vs: list V) (src': E -> V) :=
  fun e => if in_dec equiv_dec e es then src' e else src g e.

Definition pregraph_expand (g: PreGraph V E) vs es src' dst' :=
  @Build_PreGraph V E EV EE (expand_vvalid g vs) (expand_evalid g es)
   (expand_src g es src') (expand_dst g es dst').

Definition labeledgraph_expand (g: Graph) vs es src' dst' :=
  @Build_PreGraph V E EV EE (expand_vvalid g vs) (expand_evalid g es)
   (expand_src g es src') (expand_dst g es dst').

End LABELED_GRAPH_EXPAND.
*)
Section GENERAL_GRAPH_GEN.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE: Type}.
Context {P: LabeledGraph V E DV DE -> Type}.

Notation Graph := (GeneralGraph V E DV DE P).

Definition generalgraph_vgen (g: Graph) (x: V) (d: DV) (sound': P _): Graph := @Build_GeneralGraph V E EV EE DV DE P (labeledgraph_vgen g x d) sound'.

Definition generalgraph_gen_dst (g: Graph) (e : E) (t : V)
           (sound' : P _) : Graph :=
  @Build_GeneralGraph V E EV EE DV DE P (labeledgraph_gen_dst g e t) sound'.

Lemma gen_dst_preserve_bi: forall (g: PreGraph V E) e t left_edge right_edge,
    BiGraph g left_edge right_edge -> BiGraph (pregraph_gen_dst g e t) left_edge right_edge.
Proof.
  intros. apply Build_BiGraph; intros.
  + simpl in *. eapply left_valid; eauto.
  + simpl in *. eapply right_valid; eauto.
  + apply (bi_consist g).
  + simpl. apply (only_two_edges g).
Qed.

Lemma gen_dst_preserve_math: forall (g: PreGraph V E) e t (M: MathGraph g),
    weak_valid g t -> MathGraph (pregraph_gen_dst g e t).
Proof.
  intros. refine (Build_MathGraph (pregraph_gen_dst g e t) (is_null g) (is_null_dec g) _ (valid_not_null g)).
  simpl. intros. apply (valid_graph g) in H0. destruct H0. split.
  + auto.
  + unfold update_dst.
    destruct_eq_dec e e0.
    - apply H.
    - apply H1.
Defined.

Lemma gen_dst_preserve_finite: forall (g: PreGraph V E) e t, FiniteGraph g -> FiniteGraph (pregraph_gen_dst g e t).
Proof.
  intros. apply Build_FiniteGraph; simpl.
  + apply finiteV.
  + apply finiteE.
Qed.

End GENERAL_GRAPH_GEN.

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
