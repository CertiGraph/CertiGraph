(*Described a pure undirected graph that can be represented by an adjacency matrix*)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.
Require Import Coq.Lists.List.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.FiniteGraph.
Require Import compcert.lib.Coqlib.
Require Import RamifyCoq.graph.undirected_graph.

Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

Local Open Scope logic.
Local Open Scope Z_scope.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).

Definition V : Type := Z. (*0...V-1*)
Definition E : Type := V * V.
Definition DE : Type := Z. (*weight*)
Definition DV: Type := unit. (*I don't think we need this*)
Definition DG: Type := unit.

Instance V_EqDec: EqDec V eq.
Proof. hnf. apply Z.eq_dec. Qed.

Instance E_EqDec: EqDec E eq.
Proof.
  hnf. intros [x] [y].
  destruct (equiv_dec x y).
  - hnf in e. destruct (Z.eq_dec v v0); subst.
    + left; reflexivity.
    + right. intro. apply n. inversion H. reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

(*I think that, ideally these shouldn't be here
But because I've trouble with evalid_dec (see spatial_undirected_matrix), I've trouble saying "if (u,v) isn't valid, g[u][v] = inf"
Therefore, we coerce that elabel forces inf on in-evalid edges
*)
Definition SIZE := 8.
Definition inf := Int.max_signed - Int.max_signed / SIZE.

Definition vertex_valid (g: PreGraph V E): Prop :=
  forall v, vvalid g v -> 0 <= v < Int.max_signed.

Definition edge_valid (g: PreGraph V E): Prop :=
  forall e, evalid g e -> (vvalid g (src g e) /\ vvalid g (dst g e)).

(*Restrict graphs to talk only about (u,v) where u <= v. This is not reflected in a symmetric matrix, where (u,v) is treated as = (v,u), but we need a clear distinction here*)
Definition undirected_edge_valid (g: PreGraph V E): Prop :=
  forall e, evalid g e -> src g e <= dst g e.

Definition weight_valid (g: LabeledGraph V E DV DE DG): Prop :=
  forall e, evalid g e -> Int.min_signed <= elabel g e <= Int.max_signed. (*< IFTY*)

Definition weight_invalid (g: LabeledGraph V E DV DE DG): Prop :=
  forall e, ~ evalid g e -> elabel g e = inf.

Definition src_edge (g: PreGraph V E) : Prop :=
  forall e, evalid g e -> src g e = fst e.

Definition dst_edge (g: PreGraph V E): Prop :=
  forall e, evalid g e -> dst g e = snd e.

Definition sound_undirected_matrix_graph (g: LabeledGraph V E DV DE DG): Prop :=
  vertex_valid g /\ edge_valid g /\ weight_valid g /\ src_edge g /\ dst_edge g /\ weight_invalid g /\ undirected_edge_valid g.

(*Hm, was wondering if I could incorporate "soundness" in*)
Definition MatrixUGraph := (GeneralGraph V E DV DE DG (fun g => FiniteGraph g)).

Instance finGraph (g: MatrixUGraph): FiniteGraph g := (@sound_gg _ _ _ _ _ _ _ _ g).

(*because it keeps appearing*)
Lemma sound_src:
  forall (g: MatrixUGraph) e, sound_undirected_matrix_graph g -> evalid g e -> fst e = src g e.
Proof. intros. symmetry. apply H. auto. Qed.

Lemma sound_dst:
  forall (g: MatrixUGraph) e, sound_undirected_matrix_graph g -> evalid g e -> snd e = dst g e.
Proof. intros. symmetry. apply H. auto. Qed.

Lemma sound_strong_evalid: (*literally the definition of edge_valid*)
  forall (g: MatrixUGraph) e, sound_undirected_matrix_graph g -> evalid g e -> strong_evalid g e.
Proof. intros. split. auto. apply H. auto. Qed.

Corollary sound_uv_vvalid:
  forall (g: MatrixUGraph) u v, sound_undirected_matrix_graph g -> evalid g (u,v) -> vvalid g u /\ vvalid g v.
Proof.
intros. apply sound_strong_evalid in H0; auto. destruct H0.
destruct H as [? [? [? [? [? ?]]]]].
rewrite H4, H5 in H1; auto.
Qed.

(****************Edgeless graph again*****************)

Definition edgeless_lgraph (z: Z): LabeledGraph V E DV DE DG :=
@Build_LabeledGraph V E V_EqDec E_EqDec DV DE DG
  (@Build_PreGraph V E V_EqDec E_EqDec (fun v => 0 <= v < z) (fun e => False) fst snd)
  (fun v => tt) (fun e => inf) tt. (*<--- different from edgeless_WEdgeGraph because of the default value*)

Instance Fin_edgeless_lgraph (z: Z):
  FiniteGraph (edgeless_lgraph z).
Proof.
constructor; unfold EnumEnsembles.Enumerable.
(*vertices*)
exists (nat_inc_list (Z.to_nat z)); split. apply nat_inc_list_NoDup.
simpl. intros. rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
destruct (Z.lt_trichotomy z 0). rewrite Z.max_r by lia. split; intros; lia.
destruct H. subst z. unfold Z.max; simpl. split; lia.
rewrite Z.max_l by lia. split; auto.
(*edges*)
exists nil. simpl. split. apply NoDup_nil. intros; split; intros; auto.
Qed.
(*
Local Coercion FiniteWEdgeListGraph_WEdgeListGraph: MatrixUGraph >-> WEdgeListGraph.
Local Identity Coercion WEdgeListGraph_LabeledGraph: WEdgeListGraph >-> LabeledGraph.
*)
Definition edgeless_graph (z: Z): MatrixUGraph :=
  @Build_GeneralGraph V E V_EqDec E_EqDec DV DE DG FiniteGraph
    (edgeless_lgraph z) (Fin_edgeless_lgraph z).

Lemma edgeless_graph_vvalid:
  forall v k, vvalid (edgeless_graph v) k <-> 0 <= k < v.
Proof.
simpl. intros; split; intros; auto.
Qed.

Lemma edgeless_graph_Permutation:
  forall v, Permutation (VList (edgeless_graph v)) (nat_inc_list (Z.to_nat v)).
Proof.
intros. apply NoDup_Permutation. apply NoDup_VList. apply nat_inc_list_NoDup.
intros. rewrite VList_vvalid. rewrite edgeless_graph_vvalid.
rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
destruct (Z.lt_trichotomy v 0). rewrite Z.max_r by lia. split; intros; lia.
destruct H. subst v. unfold Z.max; simpl. split; lia.
rewrite Z.max_l by lia. split; auto.
Qed.

(*Move this*)
Lemma Permutation_Zlength:
  forall {A: Type} (l l': list A), Permutation l l' -> Zlength l = Zlength l'.
Proof.
intros. assert (length l = length l'). apply Permutation_length. apply H.
repeat rewrite Zlength_correct. rewrite H0. auto.
Qed.
(*
Lemma edgeless_graph_numV:
  forall v, 0 <= v -> numV (edgeless_graph v) = v.
Proof.
unfold numV. intros.
assert (Zlength (VList (edgeless_graph v)) = Zlength (Zseq v)).
apply Permutation_Zlength. apply edgeless_graph_Permutation.
rewrite H0. rewrite Zseq_Zlength. auto. apply H.
Qed.
*)
Lemma edgeless_graph_evalid:
  forall v e, ~ evalid (edgeless_graph v) e.
Proof.
intros. unfold edgeless_graph; simpl. auto.
Qed.

Lemma edgeless_graph_EList:
  forall v, EList (edgeless_graph v) = nil.
Proof.
  intros. unfold edgeless_graph, EList.
  destruct finiteE. simpl in *.
  destruct a.
  destruct x; [trivial | exfalso].
  assert (In e (e::x)) by (apply in_eq).
  apply (H0 e). apply H1.
Qed.
(*
Corollary edgeless_graph_numE:
  forall v, numE (edgeless_graph v) = 0.
Proof.
unfold numE. intros. rewrite edgeless_graph_EList. apply Zlength_nil.
Qed.
*)
Lemma edgeless_graph_sound:
  forall z, 0 <= z <= Int.max_signed -> sound_undirected_matrix_graph (edgeless_graph z).
Proof.
intros. split. unfold vertex_valid; intros. rewrite edgeless_graph_vvalid in H0. lia.
split. unfold edge_valid; intros. rewrite <- EList_evalid in H0. rewrite edgeless_graph_EList in H0. contradiction.
split. unfold weight_valid; intros. rewrite <- EList_evalid in H0. rewrite edgeless_graph_EList in H0. contradiction.
split. split. (*I forgot about this in FiniteWEdgeListGraph, but I guess if a goal can be intros;auto, split somehow works?*)
split. split.
split. split.
unfold undirected_edge_valid; intros. contradiction.
Qed.

Lemma uforest'_edgeless_graph:
  forall z, uforest' (edgeless_graph z).
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