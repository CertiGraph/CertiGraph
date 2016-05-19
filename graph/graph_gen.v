Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.Equivalence_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import VST.msl.Coqlib2.
Require Import Coq.Lists.List.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_ind.

Section AUXILIARY_COMPONENT_CONSTR.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE: Type}.

(* TODO: Maybe redefine these three using respectful_set. *)
(* TODO: rename them into edge_prop_11/10/01. *)
Definition strong_edge_prop (P: V -> Prop) (g: PreGraph V E): E -> Prop := fun e => P (src g e) /\ P (dst g e).

Definition weak_edge_prop (P: V -> Prop) (g: PreGraph V E): E -> Prop := fun e => P (src g e).

Definition weak'_edge_prop (P: V -> Prop) (g: PreGraph V E): E -> Prop := fun e => P (dst g e).

Instance weak_edge_prop_proper: Proper (Same_set ==> eq ==> Same_set) weak_edge_prop.
Proof.
  do 2 (hnf; intros); subst.
  rewrite Same_set_spec in *.
  intro e; unfold weak_edge_prop.
  auto.
Defined.
Global Existing Instance weak_edge_prop_proper.

Definition predicate_vvalid (g: PreGraph V E) (p: V -> Prop): Ensemble V :=
  fun n => vvalid g n /\ p n.

Definition predicate_evalid (g: PreGraph V E) (p: V -> Prop): Ensemble E :=
  fun e => evalid g e /\ p (src g e) /\ p (dst g e).

Definition predicate_weak_evalid (g: PreGraph V E) (p: V -> Prop): Ensemble E :=
  fun e => evalid g e /\ p (src g e).

Definition update_vlabel (vlabel: V -> DV) (x: V) (d: DV) :=
  fun v => if equiv_dec x v then d else vlabel v.

Definition update_dst (destination : E -> V) (e : E) (target: V) :=
  fun v => if equiv_dec e v then target else destination v.

End AUXILIARY_COMPONENT_CONSTR.

Section PREGRAPH_GEN.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Notation Graph := (PreGraph V E).

Definition empty_pregraph (src0 dst0: E -> V): Graph :=
  @Build_PreGraph V E EV EE (fun v => False) (fun e => False) src0 dst0.

Definition single_vertex_pregraph (v0: V): Graph :=
  @Build_PreGraph V E EV EE (eq v0) (fun e => False) (fun e => v0) (fun e => v0).

Definition pregraph_gen_dst (g : Graph) (e : E) (t : V) :=
  @Build_PreGraph V E EV EE (vvalid g) (evalid g) (src g) (update_dst (dst g) e t).

Definition union_pregraph (PV : V -> Prop) (PE: E -> Prop) (PVD: forall v, Decidable (PV v)) (PED: forall e, Decidable (PE e)) (g1 g2: Graph): Graph :=
  @Build_PreGraph V E EV EE
    (fun v => if PVD v then vvalid g1 v else vvalid g2 v)
    (fun e => if PED e then evalid g1 e else evalid g2 e)
    (fun e => if PED e then src g1 e else src g2 e)
    (fun e => if PED e then dst g1 e else dst g2 e).

(* TODO: rename them into sub_pregraph, v11_sub_pregraph, v10_sub_pregraph *)
Definition gpredicate_subgraph (PV: V -> Prop) (PE: E -> Prop) (g: Graph): Graph :=
  Build_PreGraph EV EE (Intersection _ (vvalid g) PV) (Intersection _ (evalid g) PE) (src g) (dst g).

Definition predicate_subgraph (g: Graph) (p: V -> Prop): Graph :=
  Build_PreGraph EV EE (predicate_vvalid g p) (predicate_evalid g p) (src g) (dst g).

Definition predicate_partialgraph (g: Graph) (p: V -> Prop): Graph :=
  Build_PreGraph EV EE (predicate_vvalid g p) (predicate_weak_evalid g p) (src g) (dst g).

Instance subgraph_proper: Proper (structurally_identical ==> @Same_set V ==> structurally_identical) predicate_subgraph.
Proof.
  do 2 (hnf; intros).
  destruct H as [? [? [? ?]]].
  rewrite Same_set_spec in H0; hnf in H0.
  split; [| split; [| split]]; intros; simpl.
  + unfold predicate_vvalid.
    rewrite H0, H.
    reflexivity.
  + unfold predicate_evalid. rewrite !H0, !H1. specialize (H1 e).
    split; intros; destruct H4 as [? [? ?]]; [rewrite <- H2, <- H3 | rewrite H2, H3]; tauto.
  + simpl in * |- . unfold predicate_evalid in * |- . apply H2; tauto.
  + simpl in * |- . unfold predicate_evalid in * |- . apply H3; tauto.
Defined.

Global Existing Instance subgraph_proper.

Instance partialgraph_proper: Proper (structurally_identical ==> @Same_set V ==> structurally_identical) predicate_partialgraph.
Proof.
  do 2 (hnf; intros).
  destruct H as [? [? [? ?]]].
  rewrite Same_set_spec in H0; hnf in H0.
  split; [| split; [| split]]; intros; simpl.
  + unfold predicate_vvalid.
    rewrite H0, H.
    reflexivity.
  + unfold predicate_weak_evalid. rewrite !H0, !H1. specialize (H1 e).
    split; intro; intuition; [rewrite <- H2 | rewrite H2]; auto.
  + simpl in * |- . unfold predicate_weak_evalid in * |- . apply H2; tauto.
  + simpl in * |- . unfold predicate_weak_evalid in * |- . apply H3; tauto.
Defined.

Global Existing Instance partialgraph_proper.

Lemma predicate_partialgraph_gpredicate_subgraph (g: Graph) (p: V -> Prop): 
  (predicate_partialgraph g p) ~=~ (gpredicate_subgraph p (Intersection _ (weak_edge_prop p g) (evalid g)) g).
Proof.
  split; [| split; [| split]]; simpl; intros.
  + rewrite Intersection_spec.
    reflexivity.
  + rewrite !Intersection_spec.
    unfold predicate_weak_evalid.
    unfold weak_edge_prop.
    tauto.
  + auto.
  + auto.
Qed.

End PREGRAPH_GEN.

Section LABELED_GRAPH_GEN.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE: Type}.

Notation Graph := (LabeledGraph V E DV DE).

Local Coercion pg_lg : LabeledGraph >-> PreGraph.

Definition empty_labeledgraph (src0 dst0: E -> V) (v_default: DV) (e_default: DE): Graph :=
  @Build_LabeledGraph V E EV EE DV DE (empty_pregraph src0 dst0) (fun v => v_default) (fun e => e_default).

Definition single_vertex_labeledgraph (v0: V) (v_default: DV) (e_default: DE): Graph :=
  @Build_LabeledGraph V E EV EE DV DE (single_vertex_pregraph v0) (fun v => v_default) (fun e => e_default).

Definition labeledgraph_vgen (g: Graph) (x: V) (a: DV) : Graph := Build_LabeledGraph _ _ g (update_vlabel (vlabel g) x a) (elabel g).

Definition labeledgraph_gen_dst (g : Graph) (e : E) (t : V) :=
  Build_LabeledGraph _ _ (pregraph_gen_dst g e t) (vlabel g) (elabel g).

Definition gpredicate_sub_labeledgraph (PV: V -> Prop) (PE: E -> Prop) (g: Graph): Graph :=
  Build_LabeledGraph _ _ (gpredicate_subgraph PV PE g) (vlabel g) (elabel g).

Definition predicate_sub_labeledgraph (g: Graph) (p: V -> Prop) :=
  Build_LabeledGraph _ _ (predicate_subgraph g p) (vlabel g) (elabel g).

Definition predicate_partial_labeledgraph (g: Graph) (p: V -> Prop) :=
  Build_LabeledGraph _ _ (predicate_partialgraph g p) (vlabel g) (elabel g).

Instance sub_labeledgraph_proper: Proper (labeled_graph_equiv ==> @Same_set V ==> labeled_graph_equiv) predicate_sub_labeledgraph.
Proof.
  do 2 (hnf; intros).
  destruct H as [? [? ?]].
  split; [| split].
  + apply subgraph_proper; auto.
  + simpl; intros.
    destruct H3, H4.
    apply H1; auto.
  + simpl; intros.
    destruct H3, H4.
    apply H2; auto.
Defined.

Global Existing Instance sub_labeledgraph_proper.

Instance partial_labeledgraph_proper: Proper (labeled_graph_equiv ==> @Same_set V ==> labeled_graph_equiv) predicate_partial_labeledgraph.
Proof.
  do 2 (hnf; intros).
  destruct H as [? [? ?]].
  split; [| split].
  + apply partialgraph_proper; auto.
  + simpl; intros.
    destruct H3, H4.
    apply H1; auto.
  + simpl; intros.
    destruct H3, H4.
    apply H2; auto.
Defined.

Global Existing Instance partial_labeledgraph_proper.

Lemma lg_vgen_stable: forall (g: Graph) (x: V) (d: DV),
  (predicate_partial_labeledgraph g (Complement V (eq x))) ~=~
   (predicate_partial_labeledgraph (labeledgraph_vgen g x d) (Complement V (eq x)))%LabeledGraph.
Proof.
  intros.
  split; [| split].
  + simpl.
    reflexivity.
  + intros; simpl.
    unfold update_vlabel.
    if_tac; auto.
    destruct H.
    exfalso; apply H2, H1.
  + intros; simpl.
    reflexivity.
Qed.

End LABELED_GRAPH_GEN.

Section GENERAL_GRAPH_GEN.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.
Context {DV DE: Type}.
Context {P: LabeledGraph V E DV DE -> Type}.

Notation Graph := (GeneralGraph V E DV DE P).

Local Coercion pg_lg : LabeledGraph >-> PreGraph.
Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.

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

Section ADD_GRAPH_GEN.

  Context {V E: Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.
  Context {DV DE: Type}.
  Notation Gph := (PreGraph V E).

  Variable g: Gph.
  Variable left_out_edge right_out_edge: V -> E.
  Context {BI: BiGraph g left_out_edge right_out_edge}.
  Context {MA: MathGraph g}.
  Context {FA: FiniteGraph g}.
  
  Definition change_vvalid (v: V): Ensemble V :=
    fun n => vvalid g n \/ n = v.
  
  Definition change_node_pred (P: NodePred V) (v: V) (Pv: {Pv : Prop & {Pv} + {~ Pv}}) : NodePred V.
  Proof.
    intros.
    exists (fun n: V => (if equiv_dec n v then projT1 Pv else P n)).
    intros.
    destruct_eq_dec x v.
    + destruct Pv; auto.
    + destruct P; simpl; auto.
  Defined.

  Definition change_evalid v : Ensemble E := fun e => evalid g e \/ src g e = v.

  Definition change_dst (v l r: V) : E -> V.
  Proof.
    intro e.
    refine (if equiv_dec (src g e) v then _ else dst g e).
    exact (if left_or_right _ _ v e _H then l else r).
  Defined.

  Definition update_PreGraph v l r : Gph :=
    Build_PreGraph EV EE (change_vvalid v) (change_evalid v) (src g) (change_dst v l r).

  Definition update_BiGraph v l r: BiGraph (update_PreGraph v l r) left_out_edge right_out_edge.
  Proof.
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
  Proof.
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

  Definition update_FiniteGraph v l r: FiniteGraph (update_PreGraph v l r).
  Proof.
    refine (Build_FiniteGraph _ _ _); unfold update_PreGraph, change_vvalid, change_evalid, change_dst; simpl.
    + destruct FA as [? _]. unfold EnumEnsembles.Enumerable, Ensembles.In in *.
      destruct finiteV as [l0 [? ?]]. destruct (in_dec equiv_dec v l0).
      - exists l0. split; auto. intro. split; intros.
        * left. apply H0 in H1. auto.
        * destruct H1; [rewrite H0 | subst]; auto.
      - exists (v :: l0). split. constructor; auto. intros. split; intro.
        * destruct H1; [right | left]. auto. specialize (H0 x); intuition.
        * simpl. destruct H1; [right | left]; auto. specialize (H0 x); intuition.
    + destruct FA as [_ ?]. unfold EnumEnsembles.Enumerable, Ensembles.In in *.
      destruct finiteE as [l0 [? ?]].
      destruct (in_dec equiv_dec (left_out_edge v) l0); destruct (in_dec equiv_dec (right_out_edge v) l0).
      - exists l0. split; auto. intros; split; intros.
        left; specialize (H0 x); intuition. destruct H1.
        * specialize (H0 x); intuition.
        * destruct BI. specialize (only_two_edges v x). rewrite only_two_edges in H1.
          destruct H1; subst; auto.
      - remember (left_out_edge v) as e1. remember (right_out_edge v) as e2. exists (e2 :: l0).
        split. constructor; auto. intro; split; intro.
        * destruct H1; [right | left]. subst x. subst e2. destruct BI.
          rewrite only_two_edges. right; auto. specialize (H0 x); intuition.
        * simpl. destruct H1. right; specialize (H0 x); intuition. destruct BI.
          rewrite only_two_edges in H1. destruct H1.
          Focus 1. { right. subst e1. subst x. auto. } Unfocus.
          Focus 1. { left. subst e2. subst x. auto. } Unfocus.
      - remember (left_out_edge v) as e1. remember (right_out_edge v) as e2. exists (e1 :: l0).
        split. constructor; auto. intro; split; intro.
        * destruct H1; [right | left]. subst x. subst e1. destruct BI.
          rewrite only_two_edges. left; auto. specialize (H0 x); intuition.
        * simpl. destruct H1. right; specialize (H0 x); intuition. destruct BI.
          rewrite only_two_edges in H1. destruct H1.
          Focus 1. { left. subst e1. subst x. auto. } Unfocus.
          Focus 1. { right. subst e2. subst x. auto. } Unfocus.
      - remember (left_out_edge v) as e1. remember (right_out_edge v) as e2. exists (e1 :: e2 :: l0). split.
        * constructor. intro. destruct H1; auto. destruct BI.
          specialize (bi_consist v). subst. auto. constructor; auto.
        * intro. split; intro.
          Focus 1. {
            simpl in H1. destruct H1; [|destruct H1].
            + right. subst x. subst e1. destruct BI. rewrite only_two_edges. left; auto.
            + right. subst x. subst e2. destruct BI. rewrite only_two_edges. right; auto.
            + left. specialize (H0 x). intuition.
          } Unfocus.
          Focus 1. {
            destruct H1.
            + simpl. right; right. specialize (H0 x). intuition.
            + destruct BI. rewrite only_two_edges in H1. simpl. destruct H1.
              - left. subst x. subst e1. auto.
              - right; left. subst x. subst e2. auto.
          } Unfocus.
  Qed.
End ADD_GRAPH_GEN.

Section ADD_LABELED_GRAPH_GEN.

  Context {V E: Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.
  Context {DV DE: Type}.
  
  Notation Graph := (LabeledGraph V E DV DE).

  Local Coercion pg_lg: LabeledGraph >-> PreGraph.

  Variable g: Graph.
  Variable left_out_edge right_out_edge: V -> E.
  Context {BI: BiGraph g left_out_edge right_out_edge}.

  Definition update_LabeledGraph (x l r: V) :=
    Build_LabeledGraph _ _ (update_PreGraph g left_out_edge right_out_edge x l r) (vlabel g) (elabel g).

End ADD_LABELED_GRAPH_GEN.

Section ADD_GENERAL_GRAPH_GEN.

  Context {V E: Type}.
  Context {EV: EqDec V eq}.
  Context {EE: EqDec E eq}.
  Context {DV DE: Type}.
  Context {P: LabeledGraph V E DV DE -> Type}.
  
  Notation Graph := (GeneralGraph V E DV DE P).

  Local Coercion pg_lg: LabeledGraph >-> PreGraph.
  Local Coercion lg_gg: GeneralGraph >-> LabeledGraph.

  Variable g: Graph.
  Variable left_out_edge right_out_edge: V -> E.
  Context {BI: BiGraph g left_out_edge right_out_edge}.
  
  Definition update_GeneralGraph (x l r: V) (sound': P _): Graph :=
    @Build_GeneralGraph V E EV EE DV DE P (update_LabeledGraph g left_out_edge right_out_edge x l r) sound'.

End ADD_GENERAL_GRAPH_GEN.
