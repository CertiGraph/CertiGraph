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

Class AdjMatUSoundness (g: AdjMatLG) := {
  sadjmat: SoundAdjMat (size:=size) (inf:=inf) g;
  edge_strong_evalid: forall e, evalid g e -> strong_evalid g e;
  strong_inf_bound: forall e, evalid g e -> elabel g e < inf; (*no reason to have <>*)
  undirected_edge_rep: forall e, evalid g e -> src g e <= dst g e;
}.

(*Hm, was wondering if I could incorporate "soundness" in*)
Definition MatrixUGraph := (GeneralGraph V E DV DE DG (fun g => AdjMatUSoundness g)).

Definition sound_MatrixUGraph (g: MatrixUGraph) := (@sound_gg _ _ _ _ _ _ _ _ g).
Definition sound_adjMatGraph (g: MatrixUGraph) := (@sadjmat g (sound_MatrixUGraph g)).
Definition finGraph (g: MatrixUGraph) := (@fin _ _ g (sound_adjMatGraph g)).

Instance Finite_MatrixUPGraph (g: MatrixUGraph): FiniteGraph g.
Proof. apply (finGraph g). Qed.

(****************Edgeless graph again*****************)

Section EDGELESS_MUGRAPH.

Context {inf_bound: 0 <= inf <= Int.max_signed}.
Context {size_bound: 0 <= size <= Int.max_signed}.

Instance AdjMatUSound_edgeless2:
  AdjMatUSoundness (@edgeless_lgraph2 size inf).
Proof.
constructor.
all: simpl; intros; try contradiction.
constructor.
auto. auto.
all: simpl; intros; try auto; try contradiction.
split; intros; auto.
split; intros. contradiction. destruct H. contradiction.
split; intros; auto.
constructor; unfold EnumEnsembles.Enumerable.
(*vertices*)
exists (nat_inc_list (Z.to_nat size)); split. apply nat_inc_list_NoDup.
simpl. intros. rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by lia. split; intros; lia.
destruct H. rewrite H. unfold Z.max; simpl. split; lia.
rewrite Z.max_l by lia. split; auto.
(*edges*)
exists nil. simpl. split. apply NoDup_nil. intros; split; intros; auto.
Qed.

(* Can't build, because it expects a LabeledGraph
Definition edgeless_graph2: MatrixUGraph :=
  @Build_GeneralGraph V E V_EqDec E_EqDec DV DE DG AdjMatUSoundness
    edgeless_lgraph2 (AdjMatUSound_edgeless2).
*)

(*ASDF: Error message
... has type "LabeledGraph V E DV DE DG" while it is expected to have type
 "AdjMatLG".*)

Definition edgeless_lgraph: AdjMatLG := (*nor does (@AdjMatLG size inf) work*)
@Build_LabeledGraph V E V_EqDec E_EqDec DV DE DG
  (@Build_PreGraph V E V_EqDec E_EqDec (fun v => 0 <= v < size) (fun e => False) fst snd)
  (fun v => tt) (fun e => inf) tt. (*<--- different from edgeless_WEdgeGraph because of the default value*)



End MATRIXUGRAPH.
