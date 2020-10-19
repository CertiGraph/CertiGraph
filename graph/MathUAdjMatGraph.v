Require Import VST.floyd.proofauto.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Export CertiGraph.lib.find_lemmas.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.graph_relation.
Require Export CertiGraph.graph.undirected_graph.
Require Export CertiGraph.graph.MathAdjMatGraph.

Local Open Scope logic.
Local Open Scope Z_scope.

Section Mathematical_Undirected_AdjMat_Model.
  
Context {size: Z} {inf: Z}.

Definition UAdjMatLG := AdjMatLG.

(* We just add a further constraint to AdjMat's soundness *)
Class SoundUAdjMat (g: UAdjMatLG) := {
  sadjmat: @SoundAdjMat size inf g;
  uer: forall e, evalid g e -> src g e <= dst g e;
}.

Definition UAdjMatGG := (GeneralGraph V E DV DE DG (fun g => SoundUAdjMat g)).

(* Some handy coercions: *)
Identity Coercion AdjMatLG_UAdjMatLG: UAdjMatLG >-> AdjMatLG.
Identity Coercion LabeledGraph_AdjMatLG: AdjMatLG >-> LabeledGraph.

Definition SoundUAdjMat_UAdjMatGG (g: UAdjMatGG) := (@sound_gg _ _ _ _ _ _ _ _ g).

(* We can always drag out SoundAdjMat *)
Definition SoundAdjMat_UAdjMatGG (g: UAdjMatGG) :=
  @sadjmat g (SoundUAdjMat_UAdjMatGG g).

(* A UAdjMatGG can be weakened into an AdjMatGG *)
Definition AdjMatGG_UAdjMatGG (g: UAdjMatGG) : AdjMatGG :=
  Build_GeneralGraph DV DE DG SoundAdjMat g (SoundAdjMat_UAdjMatGG g).

Coercion AdjMatGG_UAdjMatGG: UAdjMatGG >-> AdjMatGG.

(* Great! So now when we want to access an AdjMat
   plugin, we can simply use the AdjMat getter 
   and pass it a UAdjMatGG. The coercion will be seamless. 
 *)

(* For the one new UAdjMat-specific plugin, we create a getter *)
Definition undirected_edge_rep (g: UAdjMatGG) :=
  @uer g (SoundUAdjMat_UAdjMatGG g).

(* 
   A nice-to-do future step:
   Move any known lemmas that depend only on
   AdjMatSoundness + the above soundness plugin
   to this file instead of leaving it down below.
 *)

(* Downstream, we will need a little utility to
   reorder our vertices for the purposes of representation *)
Definition eformat (e: E) := if fst e <=? snd e then e else (snd e, fst e).

(* Some lemmas about eformat *)

Lemma eformat1: forall (e: E), fst e <= snd e -> eformat e = e.
Proof. unfold eformat; intros. rewrite Zle_is_le_bool in H; rewrite H. auto. Qed.

Lemma eformat2': forall (e: E), snd e < fst e -> eformat e = (snd e, fst e).
Proof. unfold eformat; intros. rewrite <- Z.leb_gt in H; rewrite H. auto. Qed.

Lemma eformat2: forall (e: E), snd e <= fst e -> eformat e = (snd e, fst e).
Proof.
  intros. apply Z.le_lteq in H. destruct H. rewrite eformat2'; auto. rewrite eformat1, H. rewrite <- H at 2. destruct e; auto. lia.
Qed.

Lemma eformat_eq:
  forall u v a b, eformat (u,v) = eformat (a,b) -> ((u=a /\ v=b) \/ (u=b /\ v=a)).
Proof.
  intros. destruct (Z.le_ge_cases u v); destruct (Z.le_ge_cases a b).
  rewrite eformat1, eformat1 in H. apply pair_equal_spec in H. left; auto. simpl; auto. simpl; auto. simpl; auto.
  rewrite eformat1, eformat2 in H. simpl in H. apply pair_equal_spec in H. right; auto. simpl; auto. simpl; auto.
  rewrite eformat2, eformat1 in H. simpl in H. apply pair_equal_spec in H. right; split; apply H. simpl; auto. simpl; auto.
  rewrite eformat2, eformat2 in H. simpl in H. apply pair_equal_spec in H. left; split; apply H. simpl; auto. simpl; auto.
Qed.

Lemma eformat_symm:
  forall u v, eformat (u,v) = eformat (v,u).
Proof.
  intros. destruct (Z.lt_trichotomy u v).
  rewrite eformat1. rewrite eformat2. simpl; auto. simpl; lia. simpl; lia.
  destruct H.
  rewrite eformat1. rewrite eformat2. simpl; auto. simpl; lia. simpl; lia.
  rewrite eformat2'. rewrite eformat1. simpl; auto. simpl; lia. simpl; lia.
Qed.


End Mathematical_Undirected_AdjMat_Model.
