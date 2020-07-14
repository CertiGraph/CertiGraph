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

Definition vertex_valid (g: PreGraph V E): Prop :=
  forall v, vvalid g v -> 0 <= v < Int.max_signed.

Definition edge_valid (g: PreGraph V E): Prop :=
  forall e, evalid g e -> (vvalid g (src g e) /\ vvalid g (dst g e)).

(*Restrict graphs to talk only about (u,v) where u <= v. This is not reflected in a symmetric matrix, where (u,v) is treated as = (v,u), but we need a clear distinction here*)
Definition undirected_edge_valid (g: PreGraph V E): Prop :=
  forall e, evalid g e -> src g e <= dst g e.

Definition weight_valid (g: LabeledGraph V E DV DE DG): Prop :=
  forall e, evalid g e -> Int.min_signed <= elabel g e <= Int.max_signed. (*< IFTY*)

Definition src_edge (g: PreGraph V E) : Prop :=
  forall e, evalid g e -> src g e = fst e.

Definition dst_edge (g: PreGraph V E): Prop :=
  forall e, evalid g e -> dst g e = snd e.

Definition sound_undirected_matrix_graph (g: LabeledGraph V E DV DE DG): Prop :=
  vertex_valid g /\ edge_valid g /\ weight_valid g /\ src_edge g /\ dst_edge g /\ undirected_edge_valid g.

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