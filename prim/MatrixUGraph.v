(*Described a pure undirected graph that can be represented by an adjacency matrix*)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.
Require Import Coq.Lists.List.
Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.graph_relation.
Require Import CertiGraph.graph.FiniteGraph.
Require Import compcert.lib.Coqlib.
Require Import CertiGraph.graph.undirected_graph.
Require Import CertiGraph.graph.AdjMatGraph.

Local Open Scope logic.
Local Open Scope Z_scope.

(*Move this*)
Lemma Permutation_Zlength:
  forall {A: Type} (l l': list A), Permutation l l' -> Zlength l = Zlength l'.
Proof.
intros. assert (length l = length l'). apply Permutation_length. apply H.
repeat rewrite Zlength_correct. rewrite H0. auto.
Qed.

Section MATRIXUGRAPH.

Instance V_EqDec: EqDec V eq.
Proof. hnf. apply Z.eq_dec. Qed.

Instance E_EqDec: EqDec E eq.
Proof.
  hnf. intros [x] [y].
  destruct (equiv_dec x y).
  - hnf in e. destruct (Z.eq_dec z z0); subst.
    + left; reflexivity.
    + right. intro. apply n. inversion H. reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

Context {inf: Z} {size: Z}.

Class AdjMatUSoundness (g: LabeledGraph V E DV DE DG) := {
  size_rep: 0 <= size <= Int.max_signed;
  inf_rep: 0 <= inf <= Int.max_signed; 
  vert_representable: forall v, vvalid g v <-> 0 <= v < size;
  edge_strong_evalid: forall e, evalid g e -> vvalid g (src g e) /\ vvalid g (dst g e);
  edge_weight_representable: forall e, evalid g e -> Int.min_signed <= elabel g e <= Int.max_signed;
  edge_weight_not_inf: forall e, evalid g e -> elabel g e <> inf;
  invalid_edge_weight: forall e, ~ evalid g e -> elabel g e = inf;
  src_fst: forall e, evalid g e -> src g e = fst e;
  dst_snd: forall e, evalid g e -> dst g e = snd e;
  fin: FiniteGraph g;
  undirected_edge_rep: forall e, evalid g e -> src g e <= dst g e;
}.

(*Hm, was wondering if I could incorporate "soundness" in*)
Definition MatrixUGraph := (GeneralGraph V E DV DE DG (fun g => AdjMatUSoundness g)).

Definition sound_MatrixUGraph (g: MatrixUGraph) := (@sound_gg _ _ _ _ _ _ _ _ g).

Instance Finite_MatrixUPGraph (g: MatrixUGraph): FiniteGraph g.
Proof. apply (@fin g (sound_MatrixUGraph g)). Qed.

Lemma evalid_strong_evalid:
forall (g: MatrixUGraph) e, evalid g e -> strong_evalid g e.
Proof.
intros; split. auto. apply (@edge_strong_evalid _ (sound_MatrixUGraph g) e); auto.
Qed.

Lemma evalid_inf_iff:
forall (g: MatrixUGraph) e, evalid g e <-> elabel g e <> inf.
Proof.
intros; split; intros. apply (@edge_weight_not_inf _ (sound_MatrixUGraph g)); auto.
destruct (evalid_dec g e). auto. apply (@invalid_edge_weight _ (sound_MatrixUGraph g)) in n. lia.
Qed.

Lemma weight_representable:
forall (g: MatrixUGraph) e, Int.min_signed <= elabel g e <= Int.max_signed.
Proof.
intros. destruct (evalid_dec g e).
apply (@edge_weight_representable g (sound_MatrixUGraph g) e). auto.
apply (@invalid_edge_weight g (sound_MatrixUGraph g) e) in n. rewrite n.
pose proof (@inf_rep g (sound_MatrixUGraph g)). split.
set (i:=Int.min_signed); compute in i; subst i. lia.
apply H.
Qed.

(****************Edgeless graph again*****************)

Section EDGELESS_MUGRAPH.

Context {inf_bound: 0 <= size < Int.max_signed}.
Context {size_bound: 0 <= inf < Int.max_signed}.

Definition edgeless_lgraph: LabeledGraph V E DV DE DG :=
@Build_LabeledGraph V E V_EqDec E_EqDec DV DE DG
  (@Build_PreGraph V E V_EqDec E_EqDec (fun v => 0 <= v < size) (fun e => False) fst snd)
  (fun v => tt) (fun e => inf) tt. (*<--- different from edgeless_WEdgeGraph because of the default value*)

Instance AdjMatUSound_edgeless:
  AdjMatUSoundness edgeless_lgraph.
Proof.
constructor.
all: simpl; intros; try contradiction.
+lia.
+lia.
+lia.
+auto.
+constructor; unfold EnumEnsembles.Enumerable.
(*vertices*)
exists (nat_inc_list (Z.to_nat size)); split. apply nat_inc_list_NoDup.
simpl. intros. rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by lia. split; intros; lia.
destruct H. rewrite H. unfold Z.max; simpl. split; lia.
rewrite Z.max_l by lia. split; auto.
(*edges*)
exists nil. simpl. split. apply NoDup_nil. intros; split; intros; auto.
Qed.

Definition edgeless_graph: MatrixUGraph :=
  @Build_GeneralGraph V E V_EqDec E_EqDec DV DE DG AdjMatUSoundness
    edgeless_lgraph (AdjMatUSound_edgeless).

Instance Fin_edgeless_lgraph: FiniteGraph edgeless_graph.
Proof. apply (@fin edgeless_graph (AdjMatUSound_edgeless)). Qed.

Lemma edgeless_graph_vvalid:
  forall k, vvalid edgeless_graph k <-> 0 <= k < size.
Proof. simpl. intros; split; intros; auto. Qed.

Lemma edgeless_graph_Permutation:
  Permutation (VList edgeless_graph) (nat_inc_list (Z.to_nat size)).
Proof.
intros. apply NoDup_Permutation. apply NoDup_VList. apply nat_inc_list_NoDup.
intros. rewrite VList_vvalid. rewrite edgeless_graph_vvalid.
rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by lia. split; intros; lia.
destruct H. rewrite H. unfold Z.max; simpl. split; lia.
rewrite Z.max_l by lia. split; auto.
Qed.

Lemma edgeless_graph_evalid:
  forall e, ~ evalid edgeless_graph e.
Proof.
intros. unfold edgeless_graph; simpl. auto.
Qed.

Lemma edgeless_graph_EList:
  EList edgeless_graph = nil.
Proof.
  intros. unfold edgeless_graph, EList.
  destruct finiteE. simpl in *.
  destruct a.
  destruct x; [trivial | exfalso].
  assert (In e (e::x)) by (apply in_eq).
  apply (H0 e). apply H1.
Qed.

Lemma uforest'_edgeless_graph:
  uforest' edgeless_graph.
Proof.
split; intros.
(*no self-loops*)
apply edgeless_graph_evalid in H; contradiction.
split; intros.
(*only one edge between two vertices*)
destruct H. destruct H. destruct H.
apply edgeless_graph_evalid in H; contradiction.
(*no rubbish edges*)
split; intros.
apply edgeless_graph_evalid in H; contradiction.
(*main forest definition*)
unfold unique_simple_upath; intros. destruct H0 as [? [? ?]].
destruct p1. inversion H3. destruct p1.
inversion H3. inversion H4. subst u; subst v.
destruct H2 as [? [? ?]]. destruct p2. inversion H5.
destruct p2. inversion H5. subst v. auto.
destruct H2. destruct H2. destruct H2. destruct H2. simpl in H2. contradiction.
destruct H0. destruct H0. destruct H0. destruct H0. simpl in H0. contradiction.
Qed.

End EDGELESS_MUGRAPH.

(**************MST******************)
(*copy...*)
Definition sum_LE (g: MatrixUGraph) : DE :=
  fold_left Z.add (DEList g) 0.

Definition minimum_spanning_forest (t g: MatrixUGraph) :=
 labeled_spanning_uforest t g /\
  forall (t': MatrixUGraph), labeled_spanning_uforest t' g ->
    Z.le (sum_DE Z.add t 0) (sum_DE Z.add t' 0).

(*The following are to let us reason about lists instead of graphs*)
Lemma sum_LE_equiv:
  forall (g: MatrixUGraph) (l: list E),
  Permutation (EList g) l -> sum_DE Z.add g 0 = fold_left Z.add (map (elabel g) l) 0.
Proof.
unfold sum_LE, DEList; intros. apply fold_left_comm. intros; lia.
apply Permutation_map. auto.
Qed.

End MATRIXUGRAPH.
